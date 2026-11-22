import JSProofs.Object

/-!
# FunctionDeclarationInstantiation of a strict function, once for all functions (zippy docs/react-proofs.md)

For a strict function with simple parameters, no parameter expressions, no `arguments` object and no nested function
declarations (most functions of a production bundle such as React's): instantiation fills the function's own record
with its bindings (`fdiMap`: the parameters bound to the arguments, the `var`s to `undefined`, the lexical names
uninitialized) and changes nothing else (`fdi_strict`). The same statement holds for every such function: proofs
about a function's body start from it instead of instantiating each function by hand.
-/

open ES ES.M
open Std (HashMap)

namespace FDI

theorem pure_app {α : Type} (a : α) (s : State) : (Pure.pure a : M α) s = .ok a s := rfl

/-! ## Loops that only change one record's bindings -/

/-- A record of the shape `mk B` with bindings `B`. -/
theorem foldList_bindings {α : Type} (P : HashMap JSStr Binding → Prop) (l : List α) (f : Unit → α → M Unit)
    (g : α → HashMap JSStr Binding → HashMap JSStr Binding) (E : EnvId) (mk : HashMap JSStr Binding → Env)
    (s : State)
    (hstep : ∀ x B, x ∈ l → P B → f () x (s.setEnv E (mk B)) = .ok () (s.setEnv E (mk (g x B))))
    (hpres : ∀ x B, x ∈ l → P B → P (g x B)) :
    ∀ B, P B → foldList l () f (s.setEnv E (mk B)) = .ok () (s.setEnv E (mk (l.foldl (fun B x => g x B) B))) := by
  induction l with
  | nil => intro B _; simp
  | cons a l ih =>
    intro B hB
    simp only [foldList_cons, List.foldl_cons]
    rw [hstep a B List.mem_cons_self hB, bindRes_ok]
    exact ih (fun x B hx hP => hstep x B (List.mem_cons_of_mem a hx) hP)
      (fun x B hx hP => hpres x B (List.mem_cons_of_mem a hx) hP) (g a B) (hpres a B List.mem_cons_self hB)

/-! ## The bindings -/

/-- Step 21: each parameter name gets a mutable binding (once). -/
def createParam (pn : JSStr) (B : HashMap JSStr Binding) : HashMap JSStr Binding :=
  if B.contains pn then B else B.insert pn { deletable := false }

/-- Steps 24-25: parameter `i` is initialized to the `i`th argument (`undefined` when missing). -/
def bindParam (paramNames : Array JSStr) (args : Array Value) (i : Nat) (B : HashMap JSStr Binding) :
    HashMap JSStr Binding :=
  B.modify paramNames[i]! fun bd => { bd with value := some (args[i]?.getD .undefined) }

/-- Step 27: a `var` name that is not a parameter's gets a binding initialized to `undefined`. -/
def createVar (paramNames : Array JSStr) (vn : JSStr) (B : HashMap JSStr Binding) : HashMap JSStr Binding :=
  if !(paramNames.contains vn) && !(B.contains vn) then
    (B.insert vn { deletable := false }).modify vn fun bd => { bd with value := some .undefined }
  else B

/-- Steps 31-32: a lexically declared name gets an uninitialized binding (immutable and strict for `const`). -/
def createLex (dd : LexScoped) (dn : JSStr) (B : HashMap JSStr Binding) : HashMap JSStr Binding :=
  if dd.isConstant then B.insert dn { mutable := false, strict := true } else B.insert dn { deletable := false }

theorem createParam_contains_self (pn : JSStr) (B : HashMap JSStr Binding) : (createParam pn B).contains pn = true := by
  unfold createParam; by_cases h : B.contains pn = true <;> simp [h]

theorem createParam_contains_of (pn x : JSStr) (B : HashMap JSStr Binding) (hx : B.contains x = true) :
    (createParam pn B).contains x = true := by
  unfold createParam; by_cases h : B.contains pn = true <;> simp [h, hx]

theorem createParam_contains (l : List JSStr) (B : HashMap JSStr Binding) :
    ∀ x, (x ∈ l ∨ B.contains x = true) → (l.foldl (fun B pn => createParam pn B) B).contains x = true := by
  induction l generalizing B with
  | nil => intro x hx; simpa using hx
  | cons a l ih =>
    intro x hx
    apply ih
    rcases hx with hx | hx
    · rcases List.mem_cons.mp hx with rfl | hx
      · right; exact createParam_contains_self x B
      · left; exact hx
    · right; exact createParam_contains_of a x B hx

/-- The function's record's bindings after instantiation. -/
def fdiMap (paramNames : Array JSStr) (args : Array Value) (varNames : Array JSStr) (lexDecls : Array LexScoped) :
    HashMap JSStr Binding :=
  let B := paramNames.toList.foldl (fun B pn => createParam pn B) {}
  let B := (List.range paramNames.size).foldl (fun B i => bindParam paramNames args i B) B
  let B := varNames.toList.foldl (fun B vn => createVar paramNames vn B) B
  lexDecls.toList.foldl (fun B dd => dd.names.toList.foldl (fun B dn => createLex dd dn B) B) B

/-- The function's facts instantiation reads, for the functions `fdi_strict` covers. -/
structure Simple (d : FuncData) : Prop where
  strict : d.code.strict = true
  simple : d.code.info.simpleParams = true
  noExprs : d.code.info.paramsHaveExpressions = false
  noDups : d.code.info.fdi.hasDuplicates = false
  noArgs : d.code.info.fdi.argumentsNeeded = false
  noFuns : d.code.info.fdi.hasFunctions = false
  noAnnexB : d.code.info.fdi.hasAnnexB = false
  params : d.code.params = d.code.info.fdi.paramNames.map fun x => .mk (.ident x) none false

/-- The lexical declarations instantiation creates bindings for. -/
def lexDecls (d : FuncData) : Array LexScoped :=
  if d.code.info.fdi.hasLexical then topLevelLexicallyScoped (match d.code.body with | .stmts b => b | .expr _ => #[])
  else #[]

/-- The context a strict function's body runs in: everything in its own record `E`. -/
def fdiCtx (fo : ObjId) (d : FuncData) (E : EnvId) : Ctx :=
  { lex := E, var := E, priv := d.privEnv, strict := true, fn := some fo, realm := d.realm, script := d.script,
    annexB := funcIds #[], isAsync := d.code.isAsync }

section
variable (o : Option EnvId) (ts : ThisStatus) (tv : Value) (f' : ObjId) (nt : Value)

/-- A function record with bindings `B`. -/
abbrev mkF (B : HashMap JSStr Binding) : Env := .func B o ts tv f' nt

theorem entry_mkF (s : State) (E : EnvId) (B : HashMap JSStr Binding) (hE : E < s.envs.size) :
    (s.setEnv E (mkF o ts tv f' nt B)).envEntry E = mkF o ts tv f' nt B := by
  simp [hE]

theorem size_mkF (s : State) (E : EnvId) (B : HashMap JSStr Binding) (hE : E < s.envs.size) :
    E < (s.setEnv E (mkF o ts tv f' nt B)).envs.size := by simp [hE]

theorem hasBinding_mkF (s : State) (E : EnvId) (B : HashMap JSStr Binding) (x : JSStr) (hE : E < s.envs.size) :
    hasBinding E x (s.setEnv E (mkF o ts tv f' nt B)) = .ok (B.contains x) (s.setEnv E (mkF o ts tv f' nt B)) := by
  rw [hasBinding_declLike E x _ (size_mkF o ts tv f' nt s E B hE) (by rw [entry_mkF o ts tv f' nt s E B hE]; rfl),
    entry_mkF o ts tv f' nt s E B hE]
  rfl

theorem createMutableBinding_mkF (s : State) (E : EnvId) (B : HashMap JSStr Binding) (x : JSStr) (del : Bool)
    (hE : E < s.envs.size) :
    createMutableBinding E x del (s.setEnv E (mkF o ts tv f' nt B)) =
      .ok () (s.setEnv E (mkF o ts tv f' nt (B.insert x { deletable := del }))) := by
  rw [createMutableBinding_declLike E x del _ (size_mkF o ts tv f' nt s E B hE)
    (by rw [entry_mkF o ts tv f' nt s E B hE]; rfl), entry_mkF o ts tv f' nt s E B hE]
  simp

theorem createImmutableBinding_mkF (s : State) (E : EnvId) (B : HashMap JSStr Binding) (x : JSStr) (st : Bool)
    (hE : E < s.envs.size) :
    createImmutableBinding E x st (s.setEnv E (mkF o ts tv f' nt B)) =
      .ok () (s.setEnv E (mkF o ts tv f' nt (B.insert x { mutable := false, strict := st }))) := by
  simp only [createImmutableBinding]
  rw [modifyEnv_eq_setEnv _ E _ (size_mkF o ts tv f' nt s E B hE), entry_mkF o ts tv f' nt s E B hE]
  simp

theorem initializeBinding_mkF (s : State) (E : EnvId) (B : HashMap JSStr Binding) (x : JSStr) (v : Value)
    (hE : E < s.envs.size) :
    initializeBinding E x v (s.setEnv E (mkF o ts tv f' nt B)) =
      .ok () (s.setEnv E (mkF o ts tv f' nt (B.modify x fun bd => { bd with value := some v }))) := by
  rw [initializeBinding_declLike E x v _ (size_mkF o ts tv f' nt s E B hE)
    (by rw [entry_mkF o ts tv f' nt s E B hE]; rfl), entry_mkF o ts tv f' nt s E B hE]
  simp

/-- **FunctionDeclarationInstantiation of a strict function** (`Simple`): its record `E` gets `fdiMap`'s bindings,
nothing else changes, and the body's context is `fdiCtx`. -/
theorem fdi_strict (n : Nat) (fo : ObjId) (d : FuncData) (E : EnvId) (args : Array Value) (s : State)
    (hs : Simple d) (hn : 2 ≤ n) (hE : E < s.envs.size) (hf : s.fuel ≠ 0) :
    functionDeclarationInstantiation (n + 1) fo d E args (s.setEnv E (mkF o ts tv f' nt {})) =
      .ok (fdiCtx fo d E) (s.setEnv E (mkF o ts tv f' nt
        (fdiMap d.code.info.fdi.paramNames args d.code.info.fdi.varNames (lexDecls d)))) := by
  simp only [functionDeclarationInstantiation, hs.strict, hs.noExprs, hs.noDups, hs.noArgs, hs.noFuns,
    hs.noAnnexB, hs.params, Bool.true_or, Bool.false_eq_true, ↓reduceIte, M.bind_eq, M.bind_apply,
    M.bindRes_ok, Array.size_map, Bool.not_false, Bool.not_true, forArr_def, foldArr_eq,
    pure_app]
  -- (21: the parameters' bindings)
  rw [foldList_bindings (fun _ => True) _ _ (fun pn B => createParam pn B) E (mkF o ts tv f' nt) s
    (fun x B _ _ => by
      simp only [M.bind_apply, hasBinding_mkF o ts tv f' nt s E B x hE, M.bindRes_ok, createParam]
      cases hc : B.contains x <;>
        simp [createMutableBinding_mkF o ts tv f' nt s E B x false hE, pure_app])
    (fun _ _ _ _ => trivial) ∅ trivial]
  simp only [M.bindRes_ok, pure_app, M.bind_apply]
  -- (24-25: the parameters bound to the arguments)
  rw [foldList_bindings (fun B => ∀ x ∈ d.code.info.fdi.paramNames.toList, B.contains x = true) _ _
    (fun i B => bindParam d.code.info.fdi.paramNames args i B) E (mkF o ts tv f' nt) s
    (fun i B hi hB => by
      have hi' : i < d.code.info.fdi.paramNames.size := by simpa using hi
      have hget : (Array.map (fun x => Param.mk (Pattern.ident x) none false) d.code.info.fdi.paramNames)[i]! =
          Param.mk (Pattern.ident d.code.info.fdi.paramNames[i]!) none false := by
        simp [hi']
      have hmem : d.code.info.fdi.paramNames[i]! ∈ d.code.info.fdi.paramNames.toList := by
        simp [hi', Array.getElem_mem]
      simp only [hget, Bool.false_eq_true, ↓reduceIte, bindParam]
      rw [show (Pure.pure (args[i]?.getD Value.undefined) : M Value) = M.pure (args[i]?.getD Value.undefined)
        from rfl]
      rw [bindElement_ident n _ _ E _ _ hn (size_mkF o ts tv f' nt s E B hE)
        (by rw [entry_mkF o ts tv f' nt s E B hE]; rfl) (by rw [entry_mkF o ts tv f' nt s E B hE]; exact hB _ hmem)
        (by simpa using hf), entry_mkF o ts tv f' nt s E B hE]
      simp)
    (fun i B _ hB x hx => by simp only [bindParam]; simpa using hB x hx) _ ?hparams]
  case hparams => exact fun x hx => createParam_contains _ ∅ x (Or.inl hx)
  simp only [M.bindRes_ok, M.bind_apply]
  -- (27: the `var`s)
  rw [foldList_bindings (fun _ => True) _ _ (fun vn B => createVar d.code.info.fdi.paramNames vn B) E
    (mkF o ts tv f' nt) s
    (fun x B _ _ => by
      simp only [M.bind_apply, hasBinding_mkF o ts tv f' nt s E B x hE, M.bindRes_ok, createVar]
      cases hp : d.code.info.fdi.paramNames.contains x <;> cases hc : B.contains x <;>
        simp [createMutableBinding_mkF o ts tv f' nt s E B x false hE, initializeBinding_mkF, hE, pure_app])
    (fun _ _ _ _ => trivial) _ trivial]
  simp only [M.bindRes_ok, pure_app, M.bind_apply, foldList_nil]
  -- (31-32: the lexical declarations)
  rw [foldList_bindings (fun _ => True) _ _
    (fun dd B => dd.names.toList.foldl (fun B dn => createLex dd dn B) B) E (mkF o ts tv f' nt) s
    (fun dd B _ _ => by
      rw [foldList_bindings (fun _ => True) _ _ (fun dn B => createLex dd dn B) E (mkF o ts tv f' nt) s
        (fun x B _ _ => by
          unfold createLex
          cases hk : dd.isConstant <;>
            simp [createMutableBinding_mkF o ts tv f' nt s E B x false hE,
              createImmutableBinding_mkF o ts tv f' nt s E B x true hE])
        (fun _ _ _ _ => trivial) _ trivial])
    (fun _ _ _ _ => trivial) _ trivial]
  simp only [M.bindRes_ok, M.bind_apply, foldList_nil]
  simp only [fdiMap, fdiCtx, lexDecls, Array.toList_range]
  rfl

end

end FDI
