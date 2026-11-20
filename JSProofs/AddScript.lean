import JSProofs.Object
import JSProofs.AddCall
import JSProofs.ScriptGen
import JSProofs.Driver

/-!
# A whole program: `function add(a, b) { return a + b } add(1, 2);` evaluates to 3

(examples/add_call.js, generated into `Proofs/ScriptGen.lean`.) Three stages: GlobalDeclarationInstantiation
creates `add`'s function object and defines it on the global object; the script's statements run up to
the call, a request to the driver; the driver answers it with `AddCall.add_call`.

States are written with the named updates `State.allocObj`/`State.setProp` (Proofs/Object.lean), so
terms stay small; every proof here checks within the default heartbeat limit.
-/

open ES
open Std (HashMap)

namespace AddScript

theorem varScoped : topLevelVarScoped ScriptGen.script_stmts = #[.func ScriptGen.add_func] := by rfl
theorem lexScoped : topLevelLexicallyScoped ScriptGen.script_stmts = #[] := by rfl
theorem annexB : annexBFunctions ScriptGen.script_stmts #[] = #[] := by rfl

/-- The function object's data for `add` declared at the top level of the script. -/
def funcDataOf (t : State) (ge : EnvId) (ctx : Ctx) : FuncData :=
  { code := ScriptGen.add_func, env := ge, thisMode := .global,
    source := (Option.map (fun x => x.prog.source) t.scripts[ctx.script]?).getD "", realm := t.realm,
    script := ctx.script }

theorem kLength_ne_kName : PropKey.str kLength ≠ PropKey.str kName := by
  simp [kLength, kName]; decide

theorem proto_add (t : State) (fp : ObjId) (hfp : t.curRealm.intrinsics["%Function.prototype%"]? = some fp) :
    intrinsic (functionProtoName ScriptGen.add_func) t = .ok fp t := by
  have hasync : ScriptGen.add_func.isAsync = false := rfl
  have hgen : ScriptGen.add_func.isGenerator = false := rfl
  simp [intrinsic, hfp, functionProtoName, hasync, hgen]

/-- The state after InstantiateFunctionObject for `add`: the function object `fo = t.heap.size`
with `length` and `name`, its `prototype` object (`fo + 1`) with `constructor`, then `fo`'s
`prototype` and the sloppy-mode `arguments`/`caller`. -/
def instState (t : State) (ge : EnvId) (ctx : Ctx) (fp : ObjId) : State :=
  let fo := t.heap.size
  let t1 := t.allocObj { proto := .obj fp, kind := .func (funcDataOf t ge ctx) }
  let t2 := t1.setProp fo (.str kLength) (.data (numV 2) false false true)
  let t3 := t2.setProp fo (.str kName) (.data (.str "add") false false true)
  let t4 := t3.allocObj { proto := .obj t.curRealm.objectProto }
  let t5 := t4.setProp (fo + 1) (.str kConstructor) (.data (.obj fo) true false true)
  let t6 := t5.setProp fo (.str kPrototype) (.data (.obj (fo + 1)) true false false)
  let t7 := t6.setProp fo (.str "arguments") (.data .null false false false)
  t7.setProp fo (.str "caller") (.data .null false false false)

theorem step_create (t : State) (ge : EnvId) (ctx : Ctx) (fp : ObjId) :
    ordinaryFunctionCreate fp ScriptGen.add_func ge #[] ctx false t =
      .ok t.heap.size ((t.allocObj { proto := .obj fp, kind := .func (funcDataOf t ge ctx) }).setProp t.heap.size
        (.str kLength) (.data (numV 2) false false true)) := by
  have hstr : ScriptGen.add_func.strict = false := rfl
  have hargs : ScriptGen.add_func.info.expectedArgs = 2 := rfl
  simp [ordinaryFunctionCreate, alloc_eq, setOwn_eq, hstr, hargs, pure, M.pure, funcDataOf, -alloc_apply]

theorem step_name (t : State) (fo : ObjId) (h : fo < t.heap.size) (hk : (t.objEntry fo).kind.isPlain = true)
    (hx : (t.objEntry fo).extensible = true) (hn : (t.objEntry fo).props.get? (.str kName) = none) :
    setFunctionName fo (.str "add") none t = .ok () (t.setProp fo (.str kName) (.data (.str "add") false false true)) := by
  simp [setFunctionName, Obj'.defineOwnProperty_entry _ _ _ _ h hk, ordinaryDefineOwnProperty_new _ _ _ _ _ _ _ h hx hn,
    pure, M.pure]

theorem step_ctor (t : State) (fo : ObjId) :
    makeConstructor fo true none t =
      .ok () (((t.allocObj { proto := .obj t.curRealm.objectProto }).setProp t.heap.size (.str kConstructor)
        (.data (.obj fo) true false true)).setProp fo (.str kPrototype) (.data (.obj t.heap.size) true false false)) := by
  simp [makeConstructor, newObject_eq, setOwn_eq, pure, M.pure]

theorem step_legacy (t : State) (fo : ObjId) :
    addLegacyFunctionProps fo ScriptGen.add_func t =
      .ok () ((t.setProp fo (.str "arguments") (.data .null false false false)).setProp fo (.str "caller")
        (.data .null false false false)) := by
  have hstr : ScriptGen.add_func.strict = false := rfl
  have hasync : ScriptGen.add_func.isAsync = false := rfl
  have hgen : ScriptGen.add_func.isGenerator = false := rfl
  have hkind : ScriptGen.add_func.kind = .normal := rfl
  have hkn : (FuncKind.normal == FuncKind.normal) = true := by decide
  simp [addLegacyFunctionProps, setOwn_eq, hstr, hasync, hgen, hkind, hkn, pure, M.pure]

theorem instantiate_add (t : State) (ge : EnvId) (ctx : Ctx) (fp : ObjId)
    (hfp : t.curRealm.intrinsics["%Function.prototype%"]? = some fp) :
    instantiateFunction ScriptGen.add_func ge #[] ctx (.str "add") t = .ok t.heap.size (instState t ge ctx fp) := by
  have hasync : ScriptGen.add_func.isAsync = false := rfl
  have hgen : ScriptGen.add_func.isGenerator = false := rfl
  have hkind : ScriptGen.add_func.kind = .normal := rfl
  have hka : (FuncKind.normal == FuncKind.arrow) = false := by decide
  have hkn : (FuncKind.normal == FuncKind.normal) = true := by decide
  simp only [instantiateFunction, M.bind_eq, M.bind_apply, proto_add t fp hfp, M.bindRes_ok, hkind, hka]
  simp only [step_create, M.bindRes_ok]
  simp [step_name, State.setProp_entry_self, State.allocObj_entry_new, PropMap.get?_insert_ne _ _ _ _ kLength_ne_kName,
    hgen, hasync, hkn, step_ctor, step_legacy, instState, pure, M.pure]

/-- CreateGlobalFunctionBinding of a new name on an extensible ordinary global object: an own data
property (writable, enumerable, not configurable), defined and then set. -/
theorem createGlobalFunctionBinding_new (t : State) (g : ObjId) (n : JSStr) (v : Value)
    (hgs : g < t.heap.size) (hk : (t.objEntry g).kind = .ordinary)
    (hx : (t.objEntry g).extensible = true) (hp : (t.objEntry g).props.get? (.str n) = none) :
    createGlobalFunctionBinding g n v false t =
      .ok () ((t.setProp g (.str n) (.data v true true false)).setProp g (.str n) (.data v true true false)) := by
  have hk' : (t.objEntry g).kind.isPlain = true := by rw [hk]; rfl
  have hv := ordinaryDefineOwnProperty_value g (.str n) v v true false (t.setProp g (.str n) (.data v true true false))
    (by simp [hgs]) (by simp [State.setProp_entry_self, hgs])
  simp [createGlobalFunctionBinding, hv, Obj'.getOwnProperty_entry _ _ _ hgs hk', hp, definePropertyOrThrow,
    Obj'.defineOwnProperty_entry _ _ _ _ hgs hk', ordinaryDefineOwnProperty_new _ _ _ _ _ _ _ hgs hx hp, setProp,
    Obj'.set_entry_own, State.setProp_entry_self, hgs, hk, ordinaryDefineOwnProperty_value, pure, M.pure]

@[simp] theorem funcDataOf_code (t : State) (ge : EnvId) (ctx : Ctx) :
    (funcDataOf t ge ctx).code = ScriptGen.add_func := by simp only [funcDataOf]
@[simp] theorem funcDataOf_realm (t : State) (ge : EnvId) (ctx : Ctx) :
    (funcDataOf t ge ctx).realm = t.realm := by simp only [funcDataOf]
@[simp] theorem funcDataOf_thisMode (t : State) (ge : EnvId) (ctx : Ctx) :
    (funcDataOf t ge ctx).thisMode = .global := by simp only [funcDataOf]
@[simp] theorem funcDataOf_isClassCtor (t : State) (ge : EnvId) (ctx : Ctx) :
    (funcDataOf t ge ctx).isClassCtor = false := by simp only [funcDataOf]

/-- The function object's kind after InstantiateFunctionObject. -/
theorem instState_func (t : State) (ge : EnvId) (ctx : Ctx) (fp : ObjId) :
    ((instState t ge ctx fp).objEntry t.heap.size).kind = .func (funcDataOf t ge ctx) := by
  have hne2 : t.heap.size + 1 ≠ t.heap.size := Nat.succ_ne_self _
  simp only [instState]
  rw [State.setProp_entry_self, Obj.withProps_kind, State.setProp_entry_self, Obj.withProps_kind,
    State.setProp_entry_self, Obj.withProps_kind, State.setProp_entry_ne _ _ _ _ _ hne2, State.allocObj_entry_lt,
    State.setProp_entry_self, Obj.withProps_kind, State.setProp_entry_self, Obj.withProps_kind,
    State.allocObj_entry_new]
  all_goals simp
  all_goals exact Nat.lt_succ_of_lt (Nat.lt_succ_self _)

theorem instState_size (t : State) (ge : EnvId) (ctx : Ctx) (fp : ObjId) :
    (instState t ge ctx fp).heap.size = t.heap.size + 2 := by
  simp [instState]

/-- Existing objects are unchanged by InstantiateFunctionObject. -/
theorem instState_entry_lt (t : State) (ge : EnvId) (ctx : Ctx) (fp : ObjId) (i : ObjId) (hi : i < t.heap.size) :
    (instState t ge ctx fp).objEntry i = t.objEntry i := by
  have h1 : t.heap.size ≠ i := Nat.ne_of_gt hi
  have h2 : t.heap.size + 1 ≠ i := Nat.ne_of_gt (Nat.lt_succ_of_lt hi)
  have hi1 : i < t.heap.size + 1 := Nat.lt_succ_of_lt hi
  simp [instState, State.setProp_entry_ne _ _ _ _ _ h1, State.setProp_entry_ne _ _ _ _ _ h2,
    State.allocObj_entry_lt, hi, hi1]

@[simp] theorem instState_envs (t : State) (ge : EnvId) (ctx : Ctx) (fp : ObjId) :
    (instState t ge ctx fp).envs = t.envs := by simp [instState]
@[simp] theorem instState_fuel (t : State) (ge : EnvId) (ctx : Ctx) (fp : ObjId) :
    (instState t ge ctx fp).fuel = t.fuel := by simp [instState]

/-- The context and state after GlobalDeclarationInstantiation. -/
def gdiCtx (ctx : Ctx) : Ctx := { ctx with annexB := funcIds #[] }

def gdiState (t : State) (ge : EnvId) (g : ObjId) (ctx : Ctx) (fp : ObjId) : State :=
  let tA := instState t ge (gdiCtx ctx) fp
  let d : Property := .data (.obj t.heap.size) true true false
  (tA.setProp g (.str "add") d).setProp g (.str "add") d

/-- GlobalDeclarationInstantiation for the script: `add`'s function object is created (after the
existing objects) and bound on the global object. -/
theorem gdi (t : State) (ge : EnvId) (g : ObjId) (ctx : Ctx) (gb : HashMap JSStr Binding) (gtv : Value)
    (fp : ObjId) (hstrict : ctx.strict = false) (hge : ge < t.envs.size)
    (hE : t.envEntry ge = .global g gb gtv) (hgb : gb.contains "add" = false)
    (hgs : g < t.heap.size) (hk : (t.objEntry g).kind = .ordinary)
    (hx : (t.objEntry g).extensible = true) (hp : (t.objEntry g).props.get? (.str "add") = none)
    (hfp : t.curRealm.intrinsics["%Function.prototype%"]? = some fp) :
    globalDeclarationInstantiation ScriptGen.script_stmts ge g ctx t = .ok (gdiCtx ctx) (gdiState t ge g ctx fp) := by
  have hname : ScriptGen.add_func.name = some "add" := rfl
  have hk' : (t.objEntry g).kind.isPlain = true := by rw [hk]; rfl
  have hgA : g < (instState t ge (gdiCtx ctx) fp).heap.size := by
    rw [instState_size]; exact Nat.lt_succ_of_lt (Nat.lt_succ_of_lt hgs)
  have hAg : (instState t ge (gdiCtx ctx) fp).objEntry g = t.objEntry g := instState_entry_lt _ _ _ _ _ hgs
  have hcg := createGlobalFunctionBinding_new (instState t ge (gdiCtx ctx) fp) g "add" (.obj t.heap.size) hgA
    (by rw [hAg]; exact hk) (by rw [hAg]; exact hx) (by rw [hAg]; exact hp)
  have hctx : ({ ctx with strict := false, annexB := funcIds #[] } : Ctx) = gdiCtx ctx := by
    cases ctx; simp_all [gdiCtx]
  simp only [globalDeclarationInstantiation, varScoped, lexScoped, hstrict]
  simp [annexB, globalDeclRecHas, readEnv_entry _ _ _ hge, hE, hgb, canDeclareGlobalFunction,
    Obj'.getOwnProperty_entry _ _ _ hgs hk', Obj'.isExtensible_entry _ _ hgs hk', hx, hp, hname, VarScoped.names,
    pure, M.pure, funcNameKey, hctx, instantiate_add _ _ _ fp hfp, hcg]
  rfl

/-! ## Stage 2: the statements run up to the call -/

/-- The Numbers 1 and 2 as the generated code writes them. -/
abbrev one : F64 := F64.fin false 4503599627370496 (-52)
abbrev two : F64 := F64.fin false 4503599627370496 (-51)

/-- The script's statements, with `add` bound on the global object to the function object `fo`:
the function declaration does nothing (it was instantiated), and `add(1, 2)` asks the driver to call
`fo` with `this` undefined. When the call returns `v`, the statements complete normally with `v`. -/
theorem body_req (n : Nat) (u : State) (ge g fo : Nat) (ctx : Ctx) (gb : HashMap JSStr Binding) (gtv : Value)
    (d : FuncData) (hlex : ctx.lex = ge) (hstrict : ctx.strict = false) (hann : ctx.annexB = funcIds #[])
    (hge : ge < u.envs.size) (hE : u.envEntry ge = .global g gb gtv) (hgb : gb.contains "add" = false)
    (hgb' : gb[JSStr.ofString "add"]? = none) (hgs : g < u.heap.size) (hk : (u.objEntry g).kind = .ordinary)
    (hp : (u.objEntry g).props.get? (.str "add") = some (.data (.obj fo) true true false))
    (hfs : fo < u.heap.size) (hfk : (u.objEntry fo).kind = .func d) (hf : 3 ≤ u.fuel) :
    ∃ K, ScriptGen.script n ctx u = .req (.call (.obj fo) .undefined #[.num one, .num two]) u K ∧
      ∀ v t, K (.normal v) t = .ok (.normal (some v)) t := by
  obtain ⟨k, hk3⟩ : ∃ k, u.fuel = k + 3 := ⟨u.fuel - 3, by omega⟩
  have hk' : (u.objEntry g).kind.isPlain = true := by rw [hk]; rfl
  have hann0 : (funcIds #[]).contains ScriptGen.add_func.info.id = false := by simp [funcIds]
  have hgbm : (JSStr.ofString "add" ∈ gb) = False := by simp [Std.HashMap.mem_iff_contains, hgb]
  refine ⟨?K, ?h, ?_⟩
  case h =>
    conv =>
      lhs
      simp [ScriptGen.script, Sem.stmts, M.repeatFrom, hk3, M.loop, Sem.funDecl, hann, hann0, Sem.exprStmt,
        Sem.call, Sem.identRef, hlex, hstrict, resolveBinding, hasBinding, readEnv_entry _ _ _ hge, hE, hgb,
        Obj'.hasProperty_entry_own _ _ _ hgs hk', hp, getRefValue, getBindingValue, hgb', getProp,
        Obj'.get_entry_data _ _ _ _ hgs hk', refThisValue, Sem.args, Sem.lit, litValue, isCallable,
        readObj_entry' _ _ _ hfs, hfk, ES.call, pure, M.pure, Sem.inner, hgbm]
  intro v t
  simp [M.pure, pure, M.loopRes_inr]

/-! ## Stage 3: the whole script, with the driver -/

/-- The script's `add` is the same function as examples/add.js's (same source text). -/
theorem same_func : ScriptGen.add_func = AddGen.add_func := rfl

section gdiState
variable (t : State) (ge : EnvId) (g : ObjId) (ctx : Ctx) (fp : ObjId)

theorem gdiState_envs : (gdiState t ge g ctx fp).envs = t.envs := by simp [gdiState]
theorem gdiState_fuel : (gdiState t ge g ctx fp).fuel = t.fuel := by simp [gdiState, instState]
theorem gdiState_realms : (gdiState t ge g ctx fp).realms = t.realms := by simp [gdiState, instState]
theorem gdiState_realm : (gdiState t ge g ctx fp).realm = t.realm := by simp [gdiState, instState]
theorem gdiState_size : (gdiState t ge g ctx fp).heap.size = t.heap.size + 2 := by
  simp [gdiState, instState_size]

theorem gdiState_global (hgs : g < t.heap.size) :
    ((gdiState t ge g ctx fp).objEntry g).kind = (t.objEntry g).kind ∧
      ((gdiState t ge g ctx fp).objEntry g).props.get? (.str "add") =
        some (.data (.obj t.heap.size) true true false) := by
  have hgA : g < (instState t ge (gdiCtx ctx) fp).heap.size := by
    rw [instState_size]; exact Nat.lt_succ_of_lt (Nat.lt_succ_of_lt hgs)
  simp [gdiState, State.setProp_entry_self, hgA, instState_entry_lt _ _ _ _ _ hgs]

theorem gdiState_func (hgs : g < t.heap.size) :
    ((gdiState t ge g ctx fp).objEntry t.heap.size).kind = .func (funcDataOf t ge (gdiCtx ctx)) := by
  have hne : g ≠ t.heap.size := Nat.ne_of_lt hgs
  rw [gdiState, State.setProp_entry_ne _ _ _ _ _ hne, State.setProp_entry_ne _ _ _ _ _ hne, instState_func]

end gdiState

/-- The engine's Number addition: 1 + 2 = 3. -/
theorem one_add_two : Conv.addF one two = Conv.ofNat 3 := by decide

/-- **The whole program.** Run as the engine runs a script (ScriptEvaluation, its requests answered
by the driver), `function add(a, b) { return a + b } add(1, 2);` completes with the Number 3:
in any state whose current realm has an ordinary, extensible global object without an `add`
property, `%Function.prototype%`, and some fuel. -/
theorem add_script (eng : Engine) (s : State) (cs : Conts) (gb : HashMap JSStr Binding) (gtv : Value) (fp : ObjId)
    (hge : s.curRealm.globalEnv < s.envs.size)
    (hE : s.envEntry s.curRealm.globalEnv = .global s.curRealm.globalObj gb gtv)
    (hgb : gb.contains "add" = false) (hgb' : gb[JSStr.ofString "add"]? = none)
    (hgs : s.curRealm.globalObj < s.heap.size) (hk : (s.objEntry s.curRealm.globalObj).kind = .ordinary)
    (hx : (s.objEntry s.curRealm.globalObj).extensible = true)
    (hp : (s.objEntry s.curRealm.globalObj).props.get? (.str "add") = none)
    (hfp : s.curRealm.intrinsics["%Function.prototype%"]? = some fp) (hf : 4 ≤ s.fuel) :
    ∃ s', (runM eng (scriptEvaluation ScriptGen.program) s cs).1 = .ok (.num (Conv.ofNat 3)) s' := by
  rw [← one_add_two]
  -- ScriptEvaluation's first steps: the script record and its context
  let ge := s.curRealm.globalEnv
  let g := s.curRealm.globalObj
  let t : State := { s with scripts := s.scripts.push { prog := ScriptGen.program, realm := s.realm, path := "" }, script := s.scripts.size }
  let ctx0 : Ctx := { lex := ge, var := ge, strict := false, realm := s.realm, script := s.scripts.size }
  have htr : t.curRealm = s.curRealm := rfl
  have hge' : ge < t.envs.size := hge
  have hE' : t.envEntry ge = .global g gb gtv := hE
  have hgs' : g < t.heap.size := hgs
  -- stage 1
  have hgdi := gdi t ge g ctx0 gb gtv fp rfl hge' hE' hgb hgs' hk hx hp (by rw [htr]; exact hfp)
  obtain ⟨u, hu⟩ : ∃ u, gdiState t ge g ctx0 fp = u := ⟨_, rfl⟩
  rw [hu] at hgdi
  let fo := t.heap.size
  let d := funcDataOf t ge (gdiCtx ctx0)
  obtain ⟨hgk, hgp⟩ := gdiState_global t ge g ctx0 fp hgs'
  rw [hu] at hgk hgp
  have hfk : (u.objEntry fo).kind = .func d := by rw [← hu]; exact gdiState_func t ge g ctx0 fp hgs'
  have hue : u.envs = s.envs := by rw [← hu, gdiState_envs]
  have hur : u.realms = s.realms := by rw [← hu, gdiState_realms]
  have hufuel : u.fuel = s.fuel := by rw [← hu, gdiState_fuel]
  have husize : u.heap.size = s.heap.size + 2 := by rw [← hu, gdiState_size]
  have hgu : g < u.heap.size := by rw [husize]; exact Nat.lt_succ_of_lt (Nat.lt_succ_of_lt hgs)
  have hfu : fo < u.heap.size := by rw [husize]; exact Nat.lt_succ_of_lt (Nat.lt_succ_self _)
  have hgeu : ge < u.envs.size := by rw [hue]; exact hge
  have hEu : u.envEntry ge = .global g gb gtv := by simp only [State.envEntry, hue]; exact hE
  -- stage 2
  obtain ⟨K, hreq, hK⟩ := body_req 999968 u ge g fo (gdiCtx ctx0) gb gtv d rfl rfl rfl hgeu hEu hgb hgb' hgu
    (by rw [hgk]; exact hk) hgp hfu hfk (by rw [hufuel]; omega)
  have hscript : evalStmts evalDepth (gdiCtx ctx0) ScriptGen.script_stmts u = ScriptGen.script 999968 (gdiCtx ctx0) u := by
    rw [ScriptGen.script_eq]; rfl
  -- stage 3: the call, answered by the driver
  obtain ⟨u', hu'⟩ : ∃ u', ({ u with fuel := u.fuel - 1 } : State) = u' := ⟨_, rfl⟩
  have hu'r : u'.realms = s.realms := by rw [← hu']; exact hur
  have hu'e : u'.envs = s.envs := by rw [← hu']; exact hue
  have hu'f : u'.fuel = s.fuel - 1 := by rw [← hu', hufuel]
  have hcode : d.code = AddGen.add_func := by rw [funcDataOf_code, same_func]
  have hdr : d.realm = s.realm := by rw [funcDataOf_realm]
  have hrealm : (u'.realms[d.realm]!).globalEnv = ge := by rw [hu'r, hdr]; rfl
  obtain ⟨s'', hcall, -, -, -⟩ := AddCall.add_call_undef fo d u' one two g gb gtv hcode
    (funcDataOf_isClassCtor _ _ _) (funcDataOf_thisMode _ _ _)
    (by rw [hrealm, hu'e]; exact hge)
    (by rw [hrealm]; simp only [State.envEntry, hu'e]; exact hE)
    (by rw [hu'f]; omega)
  have himpl : callImpl eng (.obj fo) .undefined #[.num one, .num two] u = .ok (.num (Conv.addF one two)) s'' := by
    rw [callImpl_func eng fo d _ _ u hfu hfk (by rw [hufuel]; omega), hu']
    exact hcall
  have hbody : ScriptGen.program.body = ScriptGen.script_stmts := rfl
  have hstr : ScriptGen.program.strict = false := rfl
  refine ⟨s'', ?_⟩
  simp only [runM, callDepth, scriptEvaluation, M.bind_eq, M.bind_apply, M.readS_apply, M.bindRes_ok, M.modify_apply,
    hbody, hstr]
  rw [hgdi]
  simp only [M.bindRes_ok, M.bind_apply, hscript, hreq, M.bindRes_req]
  rw [drive_call_ok eng 3999 _ _ _ _ _ cs _ _ himpl]
  simp only [hK, M.bindRes_ok, Option.getD_some]
  simp only [pure, M.pure, drive_ok]

end AddScript
