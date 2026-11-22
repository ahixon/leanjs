import ES.Driver
import ES.Builtins.Text.JSON

/-!
# Modules: Source Text Module Records

spec: https://tc39.es/ecma262/#sec-modules (16.2): loading (from the host's sources by path,
`State.moduleSources`), linking (InnerModuleLinking, InitializeEnvironment, ResolveExport),
namespaces (GetModuleNamespace), evaluation with top-level await (InnerModuleEvaluation,
ExecuteAsyncModule, AsyncModuleExecutionFulfilled/Rejected), `import()` and `import.meta`.

Module bodies with top-level await run as async coroutines (a hidden function object carries
their code); the others run synchronously.
-/

namespace ES

open Std (HashMap HashSet)

/-- Fuel for the recursions over the module graph (each level visits a different module or a
different (module, export name) pair, of which there are finitely many; the bound is far above
any graph a program loads). -/
def moduleDepth : Nat := 100000

def kStarDefault : JSStr := "*default*"
def kDefault : JSStr := "default"

/-! ## Static parts of a module -/

mutual
/-- Whether an expression contains `await` outside nested functions. -/
def exprAwait : Nat → Expr → Bool
  | 0, _ => false
  | k + 1, e => match e with
    | .await _ => true
    | .func _ => false
    | .cls c => (c.superClass.map (exprAwait k) |>.getD false) ||
        c.elems.any fun el => match el with
          | .method _ (.computed ke) _ | .field _ (.computed ke) _ _ => exprAwait k ke
          | _ => false
    | .template _ _ es => es.any (exprAwait k)
    | .tagged t _ _ es _ => exprAwait k t || es.any (exprAwait k)
    | .array els => els.any fun el => match el with | .expr e | .spread e => exprAwait k e | .hole => false
    | .object ps => ps.any fun p => match p with
      | .init key v _ => exprAwait k v || (match key with | .computed ke => exprAwait k ke | _ => false)
      | .spread e => exprAwait k e
      | .method (.computed ke) _ => exprAwait k ke
      | _ => false
    | .unary _ e | .update _ _ e | .paren e | .chain e | .privIn _ e => exprAwait k e
    | .binary _ l r | .logical _ l r => exprAwait k l || exprAwait k r
    | .assign _ t v => exprAwait k v || patAwait k t
    | .cond a b c => exprAwait k a || exprAwait k b || exprAwait k c
    | .call c args _ | .new c args => exprAwait k c || args.any fun a => match a with | .expr e | .spread e => exprAwait k e
    | .member o key _ => exprAwait k o || (match key with | .computed ke => exprAwait k ke | _ => false)
    | .superMember (.computed ke) => exprAwait k ke
    | .superCall args => args.any fun a => match a with | .expr e | .spread e => exprAwait k e
    | .importCall a b => exprAwait k a || (b.map (exprAwait k) |>.getD false)
    | .seq es => es.any (exprAwait k)
    | .yield a _ => a.map (exprAwait k) |>.getD false
    | _ => false

def patAwait : Nat → Pattern → Bool
  | 0, _ => false
  | k + 1, p => match p with
    | .expr e => exprAwait k e
    | .obj ps r => ps.any (fun pp => match pp with
        | .mk key t i => patAwait k t || (i.map (exprAwait k) |>.getD false) ||
            (match key with | .computed ke => exprAwait k ke | _ => false)) ||
        (r.map (patAwait k) |>.getD false)
    | .arr es r => es.any (fun el => match el with
        | some (.mk t i) => patAwait k t || (i.map (exprAwait k) |>.getD false)
        | none => false) || (r.map (patAwait k) |>.getD false)
    | .ident _ => false
end

/-- Whether a statement contains `await` outside nested functions (top-level await: HasTLA). -/
def containsAwait : Nat → Stmt → Bool
  | 0, _ => false
  | n + 1, s =>
    let ex := exprAwait 4096
    let pat := patAwait 4096
    let dcl (ds : Array VarDeclarator) := ds.any fun d => match d with
      | .mk p i => pat p || (i.map ex |>.getD false)
    match s with
    | .expr e | .throw e => ex e
    | .varDecl k ds => k == .awaitUsing || dcl ds
    | .classDecl c => ex (.cls c)
    | .block b => b.any (containsAwait n)
    | .ret e => e.map ex |>.getD false
    | .ifS t c a => ex t || containsAwait n c || (a.map (containsAwait n) |>.getD false)
    | .whileS t b | .doWhile b t => ex t || containsAwait n b
    | .forS i t u b =>
      (match i with | some (.decl k ds) => k == .awaitUsing || dcl ds | some (.expr e) => ex e | none => false) ||
      (t.map ex |>.getD false) || (u.map ex |>.getD false) || containsAwait n b
    | .forIn l r b => ex r || containsAwait n b ||
        (match l with | .pattern p => pat p | .decl _ p i => pat p || (i.map ex |>.getD false))
    | .forOf l r b isAwait => isAwait || ex r || containsAwait n b ||
        (match l with | .pattern p => pat p | .decl k p _ => k == .awaitUsing || pat p)
    | .tryS b h f => b.any (containsAwait n) ||
        (match h with | some (.mk p body) => (p.map pat |>.getD false) || body.any (containsAwait n) | none => false) ||
        (f.map (·.any (containsAwait n)) |>.getD false)
    | .switch d cs => ex d || cs.any fun c => match c with
        | .mk t body => (t.map ex |>.getD false) || body.any (containsAwait n)
    | .labeled _ b | .with _ b => containsAwait n b
    | .exportDecl (.decl s) => containsAwait n s
    | .exportDecl (.defaultExpr e) => ex e
    | .exportDecl (.defaultClass c) => ex (.cls c)
    | _ => false

/-- The import entries, export entries, and requested modules of a module body.
spec: https://tc39.es/ecma262/#sec-parsemodule (steps 4-10) -/
def moduleEntries (body : Array Stmt) :
    Array JSStr × Array ImportEntry × Array ExportEntry × Array ExportEntry × Array ExportEntry := Id.run do
  let mut requested : Array JSStr := #[]
  let mut imports : Array ImportEntry := #[]
  let mut exports : Array ExportEntry := #[]
  let addReq (rs : Array JSStr) (m : JSStr) := if rs.contains m then rs else rs.push m
  for s in body do
    match s with
    | .importDecl (.mk d ns named m _ _) =>
      requested := addReq requested m
      if let some d := d then imports := imports.push { moduleRequest := m, importName := some kDefault, localName := d }
      if let some ns := ns then imports := imports.push { moduleRequest := m, importName := none, localName := ns }
      for (imp, loc) in named do imports := imports.push { moduleRequest := m, importName := some imp, localName := loc }
    | .exportDecl d =>
      match d with
      | .named specs =>
        for (loc, exp) in specs do
          exports := exports.push { exportName := some exp, moduleRequest := none, importName := none, localName := some loc }
      | .namedFrom specs m _ =>
        requested := addReq requested m
        for (imp, exp) in specs do
          exports := exports.push { exportName := some exp, moduleRequest := some m, importName := some imp, localName := none }
      | .all asName m _ =>
        requested := addReq requested m
        match asName with
        | some nm => exports := exports.push { exportName := some nm, moduleRequest := some m, importName := some "*", localName := none }
        | none => exports := exports.push { exportName := none, moduleRequest := some m, importName := some "*-but-default", localName := none }
      | .decl st =>
        let names := match st with
          | .varDecl _ ds => ds.foldl (fun acc (dd : VarDeclarator) => match dd with | .mk p _ => acc ++ boundNames p) #[]
          | .funDecl f => match f.name with | some nm => #[nm] | none => #[]
          | .classDecl c => match c.name with | some nm => #[nm] | none => #[]
          | _ => #[]
        for nm in names do
          exports := exports.push { exportName := some nm, moduleRequest := none, importName := none, localName := some nm }
      | .defaultFunc f =>
        exports := exports.push { exportName := some kDefault, moduleRequest := none, importName := none, localName := some (f.name.getD kStarDefault) }
      | .defaultClass c =>
        exports := exports.push { exportName := some kDefault, moduleRequest := none, importName := none, localName := some (c.name.getD kStarDefault) }
      | .defaultExpr _ =>
        exports := exports.push { exportName := some kDefault, moduleRequest := none, importName := none, localName := some kStarDefault }
    | _ => pure ()
  -- 10. local exports that re-export imports become indirect
  let mut local_ : Array ExportEntry := #[]
  let mut indirect : Array ExportEntry := #[]
  let mut star : Array ExportEntry := #[]
  for ee in exports do
    match ee.moduleRequest with
    | none =>
      let ie? := imports.find? (fun ie => some ie.localName == ee.localName)
      match ie? with
      | none => local_ := local_.push ee
      | some ie =>
        match ie.importName with
        | none =>
          -- (a re-exported namespace import resolves to that namespace, so that two of them
          -- are not ambiguous)
          indirect := indirect.push { exportName := ee.exportName, moduleRequest := some ie.moduleRequest, importName := some "*", localName := none }
        | some imp => indirect := indirect.push { exportName := ee.exportName, moduleRequest := some ie.moduleRequest, importName := some imp, localName := none }
    | some _ =>
      if ee.importName == some "*-but-default" && ee.exportName.isNone then star := star.push ee
      else indirect := indirect.push ee
  return (requested, imports, local_, indirect, star)

/-! ## Loading -/

/-- Resolves a specifier against the referrer's path (relative paths; others as they are). -/
def resolveSpecifier (referrer : String) (spec : String) : String :=
  if spec.startsWith "./" || spec.startsWith "../" then
    let dir := (referrer.splitOn "/").dropLast
    let parts := spec.splitOn "/"
    let out := parts.foldl (fun (acc : List String) p =>
      if p == "." then acc else if p == ".." then acc.dropLast else acc ++ [p]) dir
    "/".intercalate out
  else spec

/-- HostLoadImportedModule's resolution and loading by an embedder: when the host has set `hostData["hostModules"]`,
a host request `module` with the referrer's path and the specifier, which the host answers with the module's path
(its source added to `moduleSources`) or a thrown exception (a resolution or fetch failure); otherwise
`resolveSpecifier` against the sources given in advance.
spec: https://tc39.es/ecma262/#sec-HostLoadImportedModule -/
def hostResolve (referrer spec : String) : M String := do
  if !(← readS (·.hostData.contains "hostModules")) then return resolveSpecifier referrer spec
  match ← M.request (.host "module" .undefined #[.str (JSStr.ofString referrer), .str (JSStr.ofString spec)]) with
  | .normal (.str p) | .ret (.str p) => pure p.toString
  | .throw e => M.throwV e
  | _ => throwType s!"Cannot find module '{spec}'"

def getModule (m : Nat) : M ModuleRec := do
  let r ← readS (·.modules[m]?)
  match r with
  | some r => pure r
  | none => M.halt "internal: bad module index"

def modifyModule (m : Nat) (f : ModuleRec → ModuleRec) : M Unit :=
  modify fun s => { s with modules := s.modules.modify m f }

/-- HostLoadImportedModule + ParseModule for a path (cached per path): the module's index. -/
def loadModule (path : String) : M Nat := do
  let existing ← readS fun s => s.modules.findIdx? (·.path == path)
  if let some i := existing then return i
  let src? ← readS (·.moduleSources.get? path)
  let some src := src? | throwType s!"Cannot find module '{path}'"
  -- JSON modules: a synthetic module whose default export is the parsed value
  -- spec: https://tc39.es/ecma262/#sec-parse-json-module
  if path.endsWith ".json" then
    let v ← Builtins.Text.jsonParse 0 .undefined #[.str (JSStr.ofString src)] .undefined
    let idx ← readS (·.modules.size)
    let script ← readS (·.scripts.size)
    let prog : Program := { body := #[], isModule := true, strict := true, source := src }
    let jsonExport : ExportEntry := {
      exportName := some kDefault, moduleRequest := none, importName := none, localName := some kStarDefault }
    modify fun s => { s with
      scripts := s.scripts.push { prog, realm := s.realm, path, module := some idx },
      modules := s.modules.push {
        script := script, path := path, status := "new", syntheticDefault := some v,
        localExports := #[jsonExport] } }
    return idx
  let prog ← match parseModule src with
    | .ok p => pure p
    | .error e => throwError .syntaxError e.msg
  let (requested, imports, local_, indirect, star) := moduleEntries prog.body
  let hasTLA := prog.body.any (containsAwait 100000)
  let idx ← readS (·.modules.size)
  let script ← readS (·.scripts.size)
  modify fun s => { s with
    scripts := s.scripts.push { prog, realm := s.realm, path, module := some idx },
    modules := s.modules.push {
      script := script, path := path, importEntries := imports, localExports := local_,
      indirectExports := indirect, starExports := star, hasTLA := hasTLA,
      requested := requested.map (·, 0), status := "new" } }
  pure idx

/-- LoadRequestedModules: loads the whole graph from `m` (synchronously; a module's requests
are resolved once, when its status leaves "new"). -/
def loadGraph : Nat → Nat → M Unit
  | 0, _ => throwRange "module graph too deep"
  | n + 1, m => do
    let mr ← getModule m
    if mr.status != "new" then return
    let reqs ← M.mapArr mr.requested fun (spec, _) => do
      let i ← loadModule (← hostResolve mr.path spec.toString)
      pure (spec, i)
    modifyModule m fun r => { r with requested := reqs, status := "unlinked" }
    M.forArr reqs fun (_, i) => loadGraph n i

def importedModule (mr : ModuleRec) (spec : JSStr) : M Nat :=
  match mr.requested.find? (·.1 == spec) with
  | some (_, i) => pure i
  | none => M.halt s!"internal: module request {spec} not loaded"

/-! ## Linking -/

/-- A ResolveExport result. -/
inductive Resolution where
  | none
  | ambiguous
  | binding (m : Nat) (name : Option JSStr)  -- name none: the namespace
  deriving Inhabited, BEq

/-- ResolveExport spec: https://tc39.es/ecma262/#sec-resolveexport -/
def resolveExport : Nat → Nat → JSStr → Array (Nat × JSStr) → M (Resolution × Array (Nat × JSStr))
  | 0, _, _, rs => pure (.none, rs)
  | n + 1, m, name, resolveSet => do
    -- 1-2.
    if resolveSet.any (fun (mm, nm) => mm == m && nm == name) then return (.none, resolveSet)
    let resolveSet := resolveSet.push (m, name)
    let mr ← getModule m
    -- 4.
    if let some e := mr.localExports.find? (·.exportName == some name) then
      return (.binding m e.localName, resolveSet)
    -- 5.
    if let some e := mr.indirectExports.find? (·.exportName == some name) then
      let im ← importedModule mr (e.moduleRequest.getD JSStr.empty)
      if e.importName == some "*" then return (.binding im none, resolveSet)
      return ← resolveExport n im (e.importName.getD JSStr.empty) resolveSet
    -- 6.
    if name == kDefault then return (.none, resolveSet)
    -- 7-8.
    M.foldArr mr.starExports (Resolution.none, resolveSet) fun (star, rs) e => do
      if star == .ambiguous then return (star, rs)
      let im ← importedModule mr (e.moduleRequest.getD JSStr.empty)
      let (res, rs) ← resolveExport n im name rs
      match res, star with
      | .ambiguous, _ => pure (.ambiguous, rs)
      | .none, _ => pure (star, rs)
      | r, .none => pure (r, rs)
      | .binding m1 b1, .binding m2 b2 => pure (if m1 != m2 || b1 != b2 then .ambiguous else star, rs)
      | _, _ => pure (star, rs)

/-- GetExportedNames spec: https://tc39.es/ecma262/#sec-getexportednames -/
def getExportedNames : Nat → Nat → Array Nat → M (Array JSStr × Array Nat)
  | 0, _, set => pure (#[], set)
  | n + 1, m, set => do
    if set.contains m then return (#[], set)
    let set := set.push m
    let mr ← getModule m
    let names := mr.localExports.filterMap (·.exportName) ++ mr.indirectExports.filterMap (·.exportName)
    M.foldArr mr.starExports (names, set) fun (names, set) e => do
      let im ← importedModule mr (e.moduleRequest.getD JSStr.empty)
      let (starNames, set) ← getExportedNames n im set
      pure (starNames.foldl (fun acc nm => if nm == kDefault || acc.contains nm then acc else acc.push nm) names, set)

/-- GetModuleNamespace (creating the namespace object: ModuleNamespaceCreate).
spec: https://tc39.es/ecma262/#sec-getmodulenamespace -/
def getModuleNamespace (m : Nat) : M ObjId := do
  let mr ← getModule m
  if let some ns := mr.ns then return ns
  let (names, _) ← getExportedNames moduleDepth m #[]
  let resolved ← M.foldArr names #[] fun acc nm => do
    match (← resolveExport moduleDepth m nm #[]).1 with
    | .binding tm bn => pure (acc.push (nm, tm, bn))
    | _ => pure acc
  let sorted := resolved.qsort (fun a b => a.1.lt b.1)
  let nsKind : Kind := .moduleNS m (sorted.map (·.1))
  let ns ← alloc { proto := .null, extensible := false, immutableProto := true, kind := nsKind }
  setOwn ns (.sym WK.toStringTag) (.data (.str "Module") false false false)
  modifyModule m fun r => { r with ns := some ns, nsBindings := sorted }
  -- (namespace re-exports need their target's namespace object)
  M.forArr sorted fun (_, tm, bn) => do
    if bn.isNone && tm != m then
      let _ ← getModuleNamespaceShallow tm
  pure ns
where
  getModuleNamespaceShallow (m : Nat) : M ObjId := do
    let mr ← getModule m
    if let some ns := mr.ns then return ns
    let (names, _) ← getExportedNames moduleDepth m #[]
    let resolved ← M.foldArr names #[] fun acc nm => do
      match (← resolveExport moduleDepth m nm #[]).1 with
      | .binding tm bn => pure (acc.push (nm, tm, bn))
      | _ => pure acc
    let sorted := resolved.qsort (fun a b => a.1.lt b.1)
    let nsKind : Kind := .moduleNS m (sorted.map (·.1))
    let ns ← alloc { proto := .null, extensible := false, immutableProto := true, kind := nsKind }
    setOwn ns (.sym WK.toStringTag) (.data (.str "Module") false false false)
    modifyModule m fun r => { r with ns := some ns, nsBindings := sorted }
    pure ns

/-- The context a module's code runs in. -/
def moduleCtx (m : Nat) : M Ctx := do
  let mr ← getModule m
  let some env := mr.env | M.halt "internal: module not linked"
  let realm ← readS fun s => (s.scripts[mr.script]?.map (·.realm)).getD s.realm
  pure { lex := env, var := env, strict := true, realm, script := mr.script }

/-- InitializeEnvironment spec: https://tc39.es/ecma262/#sec-source-text-module-record-initialize-environment -/
def initializeEnvironment (m : Nat) : M Unit := do
  let mr ← getModule m
  -- 1.
  M.forArr mr.indirectExports fun e => do
    match (← resolveExport moduleDepth m (e.exportName.getD JSStr.empty) #[]).1 with
    | .binding .. => pure ()
    | _ => throwError .syntaxError s!"The requested module does not provide an export named '{e.importName.getD JSStr.empty}'"
  -- 4.
  let ge ← readS (·.curRealm.globalEnv)
  let env ← allocEnv (.module {} {} (some ge))
  modifyModule m fun r => { r with env := some env }
  if let some v := mr.syntheticDefault then
    createImmutableBinding env kStarDefault true
    initializeBinding env kStarDefault v
    return
  -- 5.
  M.forArr mr.importEntries fun ie => do
    let im ← importedModule mr ie.moduleRequest
    match ie.importName with
    | none =>
      let ns ← getModuleNamespace im
      createImmutableBinding env ie.localName true
      initializeBinding env ie.localName (.obj ns)
    | some imp =>
      match (← resolveExport moduleDepth im imp #[]).1 with
      | .binding tm none =>
        let ns ← getModuleNamespace tm
        createImmutableBinding env ie.localName true
        initializeBinding env ie.localName (.obj ns)
      | .binding tm (some bn) =>
        modifyEnv env fun e => match e with
          | .module b imps o => .module b (imps.insert ie.localName (tm, some bn)) o
          | e => e
      | .ambiguous => throwError .syntaxError s!"The requested module contains conflicting star exports for name '{imp}'"
      | .none => throwError .syntaxError s!"The requested module does not provide an export named '{imp}'"
  -- 21-24.
  let prog ← readS fun s => (s.scripts[mr.script]?.map (·.prog)).getD default
  let body := prog.body
  let ctx ← moduleCtx m
  let varNames := (body.foldl (fun acc st => acc ++ varScopedN declDepth st) #[]).foldl
    (fun (acc : Array JSStr) d => acc ++ d.names) #[]
  M.forArr varNames fun vn => do
    if !(← hasBinding env vn) then
      createMutableBinding env vn false
      initializeBinding env vn .undefined
  -- 25-26.
  M.forArr body fun st => do
    let decls := stmtLexScoped false st
    M.forArr decls fun d => do
      let names := match st, d with
        | .exportDecl (.defaultFunc f), _ => #[f.name.getD kStarDefault]
        | .exportDecl (.defaultClass c), _ => #[c.name.getD kStarDefault]
        | _, d => d.names
      M.forArr names fun dn => do
        if d.isConstant then createImmutableBinding env dn true else createMutableBinding env dn false
        if let .func f := d then
          let fo ← instantiateFunction f env #[] ctx (funcNameKey f)
          initializeBinding env dn (.obj fo)
    if let .exportDecl (.defaultExpr _) := st then createMutableBinding env kStarDefault false

/-- InnerModuleLinking spec: https://tc39.es/ecma262/#sec-InnerModuleLinking -/
def innerModuleLinking : Nat → Nat → Array Nat → Nat → M (Array Nat × Nat)
  | 0, _, stack, index => pure (stack, index)
  | n + 1, m, stack, index => do
    let mr ← getModule m
    -- 2.
    if mr.status != "unlinked" then return (stack, index)
    -- 4-8.
    modifyModule m fun r => { r with status := "linking", dfsIndex := index, dfsAncestorIndex := index }
    let index := index + 1
    let stack := stack.push m
    -- 9.
    let (stack, index) ← M.foldArr mr.requested (stack, index) fun (stack, index) (_, rm) => do
      let (stack, index) ← innerModuleLinking n rm stack index
      let rr ← getModule rm
      if rr.status == "linking" then
        modifyModule m fun r => { r with dfsAncestorIndex := min r.dfsAncestorIndex rr.dfsAncestorIndex }
      pure (stack, index)
    -- 10.
    initializeEnvironment m
    -- 13.
    let mr ← getModule m
    if mr.dfsAncestorIndex == mr.dfsIndex then
      let pos := (stack.findIdx? (· == m)).getD 0
      M.forArr (stack.extract pos stack.size) fun rm => modifyModule rm fun r => { r with status := "linked" }
      return (stack.extract 0 pos, index)
    pure (stack, index)

/-- Link() spec: https://tc39.es/ecma262/#sec-moduledeclarationlinking -/
def linkModule (m : Nat) : M Unit := do
  match ← M.attempt (innerModuleLinking moduleDepth m #[] 0) with
  | .ok _ =>
    -- (every linked module's namespace object, created now: namespaces read nested namespaces)
    let n ← readS (·.modules.size)
    M.forArr (Array.range n) fun i => do
      let r ← getModule i
      if r.status != "new" && r.status != "unlinked" && r.ns.isNone then
        let _ ← getModuleNamespace i
  | .error e =>
    -- (modules left "linking" go back to "unlinked")
    modify fun s => { s with modules := s.modules.map fun r =>
      if r.status == "linking" then { r with status := "unlinked", env := none } else r }
    M.throwV e

/-! ## Evaluation -/

/-- ExecuteModule without a capability (a module without top-level await). -/
def executeModuleSync (m : Nat) : M Unit := do
  let ctx ← moduleCtx m
  let mr ← getModule m
  let body ← readS fun s => (s.scripts[mr.script]?.map (·.prog.body)).getD #[]
  let prev ← readS fun s => (s.realm, s.script)
  modify fun s => { s with realm := ctx.realm, script := ctx.script }
  let needDispose := (usingKinds (moduleLexicallyScoped body)).1
  let r ← M.attempt (withDisposeScope needDispose ctx fun c => evalStmts evalDepth c body)
  modify fun s => { s with realm := prev.1, script := prev.2 }
  match r with
  | .ok _ => pure ()
  | .error e => M.throwV e

/-- ExecuteModule with a capability (top-level await): the body as an async coroutine. -/
def executeModuleAsync (m : Nat) (cap : Capability) : M Unit := do
  let ctx ← moduleCtx m
  let mr ← getModule m
  let body ← readS fun s => (s.scripts[mr.script]?.map (·.prog.body)).getD #[]
  let code : Func := .mk none .normal true false #[] (.stmts body) { strict := true }
  let fd : FuncData := { code, env := ctx.lex, thisMode := .strict, realm := ctx.realm, script := ctx.script }
  let f ← alloc { proto := .null, kind := .func fd }
  let kd : Kind := .coroutine .suspendedStart f ctx.lex ctx.var true false
    #[cap.promise, cap.resolve, cap.reject]
  let co ← alloc { kind := kd }
  let _ ← M.request (.resume co (.normal .undefined))

/-- ExecuteAsyncModule spec: https://tc39.es/ecma262/#sec-execute-async-module -/
def executeAsyncModule (m : Nat) : M Unit := do
  let cap ← newIntrinsicPromise
  let onF ← makeBuiltinFn "AsyncModuleFulfilled" 0 JSStr.empty #[numV m]
  let onR ← makeBuiltinFn "AsyncModuleRejected" 1 JSStr.empty #[numV m]
  let .obj p := cap.promise | M.halt "internal"
  let _ ← performPromiseThen p (.obj onF) (.obj onR) none
  executeModuleAsync m cap

/-- AsyncModuleExecutionRejected spec: https://tc39.es/ecma262/#sec-async-module-execution-rejected -/
def asyncModuleRejected : Nat → Nat → Value → M Unit
  | 0, _, _ => pure ()
  | n + 1, m, err => do
    let mr ← getModule m
    if mr.status == "evaluated" then return
    modifyModule m fun r => { r with error := some err, status := "evaluated", asyncOrder := some 0 }
    M.forArr mr.asyncParents fun p => asyncModuleRejected n p err
    if let some (_, _, rej) := mr.topCapability then let _ ← call rej .undefined #[err]

/-- GatherAvailableAncestors spec: https://tc39.es/ecma262/#sec-gather-available-ancestors -/
def gatherAvailableAncestors : Nat → Nat → Array Nat → M (Array Nat)
  | 0, _, l => pure l
  | n + 1, m, execList => do
    let mr ← getModule m
    M.foldArr mr.asyncParents execList fun l p => do
      if l.contains p then return l
      let pr ← getModule p
      let root ← getModule (pr.cycleRoot.getD p)
      if root.error.isSome then return l
      modifyModule p fun r => { r with pendingAsyncDeps := r.pendingAsyncDeps - 1 }
      let pr ← getModule p
      if pr.pendingAsyncDeps == 0 then
        let l := l.push p
        if !pr.hasTLA then gatherAvailableAncestors n p l else pure l
      else pure l

/-- AsyncModuleExecutionFulfilled spec: https://tc39.es/ecma262/#sec-async-module-execution-fulfilled -/
def asyncModuleFulfilled (m : Nat) : M Unit := do
  let mr ← getModule m
  if mr.status == "evaluated" then return
  modifyModule m fun r => { r with asyncOrder := some 0, status := "evaluated" }
  if let some (_, res, _) := mr.topCapability then let _ ← call res .undefined #[.undefined]
  let execList ← gatherAvailableAncestors moduleDepth m #[]
  let orders ← M.mapArr execList fun i => do pure (((← getModule i).asyncOrder).getD 0, i)
  let sorted := (orders.qsort (fun a b => a.1 < b.1)).map (·.2)
  M.forArr sorted fun i => do
    let r ← getModule i
    if r.status == "evaluated" then return
    if r.hasTLA then executeAsyncModule i
    else
      match ← M.attempt (executeModuleSync i) with
      | .error e => asyncModuleRejected moduleDepth i e
      | .ok _ =>
        modifyModule i fun r => { r with status := "evaluated", asyncOrder := some 0 }
        let r ← getModule i
        if let some (_, res, _) := r.topCapability then let _ ← call res .undefined #[.undefined]

def asyncModuleFulfilledFn : BuiltinFn := fun self _ _ _ => do
  let s ← builtinSlots self
  let m := match s[0]! with | .num x => (Conv.toNat? x).getD 0 | _ => 0
  asyncModuleFulfilled m
  pure .undefined

def asyncModuleRejectedFn : BuiltinFn := fun self _ args _ => do
  let s ← builtinSlots self
  let m := match s[0]! with | .num x => (Conv.toNat? x).getD 0 | _ => 0
  asyncModuleRejected moduleDepth m (arg args 0)
  pure .undefined

/-- InnerModuleEvaluation spec: https://tc39.es/ecma262/#sec-innermoduleevaluation -/
def innerModuleEvaluation : Nat → Nat → Array Nat → Nat → M (Array Nat × Nat)
  | 0, _, stack, index => pure (stack, index)
  | n + 1, m, stack, index => do
    let mr ← getModule m
    -- 2.
    if mr.status == "evaluating-async" || mr.status == "evaluated" then
      match mr.error with
      | some e => M.throwV e
      | none => return (stack, index)
    -- 3.
    if mr.status == "evaluating" then return (stack, index)
    -- 5-9.
    modifyModule m fun r => { r with status := "evaluating", dfsIndex := index, dfsAncestorIndex := index, pendingAsyncDeps := 0 }
    let index := index + 1
    let stack := stack.push m
    -- 10.
    let (stack, index) ← M.foldArr mr.requested (stack, index) fun (stack, index) (_, rm) => do
      let (stack, index) ← innerModuleEvaluation n rm stack index
      let rr ← getModule rm
      if rr.status == "evaluating" then
        modifyModule m fun r => { r with dfsAncestorIndex := min r.dfsAncestorIndex rr.dfsAncestorIndex }
      else
        let root := rr.cycleRoot.getD rm
        let rootR ← getModule root
        if let some e := rootR.error then M.throwV e
        if rootR.asyncOrder.isSome && rootR.asyncOrder != some 0 then
          modifyModule m fun r => { r with pendingAsyncDeps := r.pendingAsyncDeps + 1 }
          modifyModule root fun r => { r with asyncParents := r.asyncParents.push m }
      pure (stack, index)
    -- 11-12.
    let mr ← getModule m
    if mr.pendingAsyncDeps > 0 || mr.hasTLA then
      let ord ← readS (·.asyncOrderCounter)
      modify fun s => { s with asyncOrderCounter := ord + 1 }
      modifyModule m fun r => { r with asyncOrder := some ord }
      if mr.pendingAsyncDeps == 0 then executeAsyncModule m
    else executeModuleSync m
    -- 15.
    let mr ← getModule m
    if mr.dfsAncestorIndex == mr.dfsIndex then
      let pos := (stack.findIdx? (· == m)).getD 0
      M.forArr (stack.extract pos stack.size) fun rm => modifyModule rm fun r =>
        { r with status := if r.asyncOrder.isSome && r.asyncOrder != some 0 then "evaluating-async" else "evaluated",
                 cycleRoot := some m }
      return (stack.extract 0 pos, index)
    pure (stack, index)

/-- Evaluate() spec: https://tc39.es/ecma262/#sec-moduleevaluation -/
def evaluateModule (m : Nat) : M Value := do
  let mr ← getModule m
  let m := if mr.status == "evaluating-async" || mr.status == "evaluated" then mr.cycleRoot.getD m else m
  let mr ← getModule m
  if let some (p, _, _) := mr.topCapability then return p
  let cap ← newIntrinsicPromise
  modifyModule m fun r => { r with topCapability := some (cap.promise, cap.resolve, cap.reject) }
  match ← M.attempt (innerModuleEvaluation moduleDepth m #[] 0) with
  | .error e =>
    -- (every module left on the stack is evaluated with the error)
    modify fun s => { s with modules := s.modules.map fun r =>
      if r.status == "evaluating" then { r with status := "evaluated", error := some e } else r }
    let _ ← call cap.reject .undefined #[e]
  | .ok _ =>
    let mr ← getModule m
    if mr.asyncOrder.isNone || mr.asyncOrder == some 0 then let _ ← call cap.resolve .undefined #[.undefined]
  pure cap.promise

/-- Loads, links and evaluates a module graph from a path; the evaluation promise. -/
def runModuleGraph (path : String) : M Value := do
  let m ← loadModule path
  loadGraph moduleDepth m
  linkModule m
  evaluateModule m

/-! ## import() and import.meta -/

/-- The path of the running script or module (the referrer). -/
def activeReferrerPath : M String := readS fun s => (s.scripts[s.script]?.map (·.path)).getD ""

/-- EvaluateImportCall + ContinueDynamicImport (the host loads synchronously).
spec: https://tc39.es/ecma262/#sec-import-call-runtime-semantics-evaluation -/
def dynamicImport (specifier options : Value) : M Value := do
  let cap ← newIntrinsicPromise
  let reject (e : Value) : M Value := do let _ ← call cap.reject .undefined #[e]; pure cap.promise
  let referrer ← activeReferrerPath
  -- 7-8.
  let spec ← match ← M.attempt (toStr specifier) with
    | .ok s => pure s
    | .error e => return ← reject e
  -- 9-10. (import attributes)
  if !options.isUndefined then
    let .obj oo := options | return ← reject (← makeError .typeError "The second argument of import() must be an object")
    match ← M.attempt (getProp oo (.str "with")) with
    | .error e => return ← reject e
    | .ok .undefined => pure ()
    | .ok (.obj wo) =>
      match ← M.attempt (enumerableOwnProperties wo 2) with
      | .error e => return ← reject e
      | .ok entries =>
        let bad ← M.foldArr entries false fun bad en => do
          if bad then return true
          let .obj eo := en | return true
          let v ← getProp eo (PropKey.ofNat 1)
          match v with | .str _ => return false | _ => return true
        if bad then return ← reject (← makeError .typeError "Import attribute values must be strings")
    | .ok _ => return ← reject (← makeError .typeError "The 'with' option must be an object")
  -- (HostLoadImportedModule, Link, Evaluate)
  let r ← M.attempt do
    let m ← loadModule (← hostResolve referrer spec.toString)
    loadGraph moduleDepth m
    linkModule m
    let p ← evaluateModule m
    pure (m, p)
  match r with
  | .error e => reject e
  | .ok (m, p) =>
    let onF ← makeBuiltinFn "DynamicImportFulfilled" 0 JSStr.empty #[numV m, cap.resolve]
    let .obj po := p | M.halt "internal"
    let _ ← performPromiseThen po (.obj onF) cap.reject none
    pure cap.promise

def dynamicImportFulfilled : BuiltinFn := fun self _ _ _ => do
  let s ← builtinSlots self
  let m := match s[0]! with | .num x => (Conv.toNat? x).getD 0 | _ => 0
  match ← M.attempt (getModuleNamespace m) with
  | .ok ns => call s[1]! .undefined #[.obj ns]
  | .error e => M.throwV e

/-- import.meta spec: https://tc39.es/ecma262/#sec-meta-properties-runtime-semantics-evaluation -/
def importMeta : M Value := do
  let m? ← readS fun s => (s.scripts[s.script]?.bind (·.module))
  let some m := m? | throwError .syntaxError "import.meta outside a module"
  let mr ← getModule m
  if let some o := mr.importMeta then return .obj o
  let o ← ordinaryObjectCreate .null
  -- (HostGetImportMetaProperties: an embedder's modules have a `url` and a `resolve` function, HTML's)
  -- spec: https://html.spec.whatwg.org/multipage/webappapis.html#hostgetimportmetaproperties
  if ← readS (·.hostData.contains "hostModules") then
    let url := Value.str (JSStr.ofString mr.path)
    setOwn o (.str "url") (.data url true true true)
    let f ← makeBuiltinFn "%ImportMetaResolve%" 1 (JSStr.ofString "resolve") #[url]
    setOwn o (.str "resolve") (.data (.obj f) true true true)
  modifyModule m fun r => { r with importMeta := some o }
  pure (.obj o)

/-- `import.meta.resolve(specifier)`: the embedder's resolution of the specifier against the module's URL (a host
request `resolve`, answered with the URL or a thrown TypeError).
spec: https://html.spec.whatwg.org/multipage/webappapis.html#hostgetimportmetaproperties (step 4) -/
def importMetaResolveFn : BuiltinFn := fun self _ args _ => do
  let base ← match (← builtinSlots self)[0]? with | some v => pure v | none => pure .undefined
  let spec ← toStr (arg args 0)
  match ← M.request (.host "resolve" .undefined #[base, .str spec]) with
  | .normal v | .ret v => pure v
  | .throw e => M.throwV e

def dynamicImportFn : BuiltinFn := fun _ _ args _ => dynamicImport (arg args 0) (arg args 1)
def importMetaFn : BuiltinFn := fun _ _ _ _ => importMeta

def moduleBuiltins : Array BuiltinDef := #[
  ⟨"%DynamicImport%", dynamicImportFn⟩, ⟨"%ImportMeta%", importMetaFn⟩, ⟨"%ImportMetaResolve%", importMetaResolveFn⟩,
  ⟨"AsyncModuleFulfilled", asyncModuleFulfilledFn⟩, ⟨"AsyncModuleRejected", asyncModuleRejectedFn⟩,
  ⟨"DynamicImportFulfilled", dynamicImportFulfilled⟩]

end ES
