import Proofs.AddScript

/-!
# InstantiateFunctionObject for simple functions

A non-strict, non-async, non-generator normal function named `nm`: the function object (with
`length`, `name`, `prototype`, and the sloppy-mode `arguments`/`caller`) and its `prototype` object,
allocated after the existing objects, which are unchanged.
-/

open ES

namespace Inst

/-- The facts about a function's code that creating its object uses. -/
def SimpleFn (fn : Func) (nm : JSStr) : Prop :=
  fn.strict = false ∧ fn.isAsync = false ∧ fn.isGenerator = false ∧ fn.kind = .normal ∧ fn.name = some nm

/-- The function object's data, created in script `sc` with environment `ge`. -/
def fnData (fn : Func) (t : State) (ge : EnvId) (sc : Nat) : FuncData :=
  { code := fn, env := ge, thisMode := .global,
    source := (Option.map (fun x => x.prog.source) t.scripts[sc]?).getD "", realm := t.realm, script := sc }

/-- The state after InstantiateFunctionObject. -/
def instStateFn (fn : Func) (nm : JSStr) (t : State) (ge : EnvId) (sc : Nat) (fp : ObjId) : State :=
  let fo := t.heap.size
  let t1 := t.allocObj { proto := .obj fp, kind := .func (fnData fn t ge sc) }
  let t2 := t1.setProp fo (.str kLength) (.data (numV fn.info.expectedArgs) false false true)
  let t3 := t2.setProp fo (.str kName) (.data (.str nm) false false true)
  let t4 := t3.allocObj { proto := .obj t.curRealm.objectProto }
  let t5 := t4.setProp (fo + 1) (.str kConstructor) (.data (.obj fo) true false true)
  let t6 := t5.setProp fo (.str kPrototype) (.data (.obj (fo + 1)) true false false)
  let t7 := t6.setProp fo (.str "arguments") (.data .null false false false)
  t7.setProp fo (.str "caller") (.data .null false false false)

section
variable (fn : Func) (nm : JSStr)

theorem proto_fn (hs : SimpleFn fn nm) (t : State) (fp : ObjId) (hfp : t.curRealm.intrinsics["%Function.prototype%"]? = some fp) :
    intrinsic (functionProtoName fn) t = .ok fp t := by
  obtain ⟨-, hasync, hgen, -, -⟩ := hs
  simp [intrinsic, hfp, functionProtoName, hasync, hgen]

theorem step_create_fn (hs : SimpleFn fn nm) (t : State) (ge : EnvId) (ctx : Ctx) (fp : ObjId) :
    ordinaryFunctionCreate fp fn ge #[] ctx false t =
      .ok t.heap.size ((t.allocObj { proto := .obj fp, kind := .func (fnData fn t ge ctx.script) }).setProp
        t.heap.size (.str kLength) (.data (numV fn.info.expectedArgs) false false true)) := by
  obtain ⟨hstr, -, -, -, -⟩ := hs
  simp [ordinaryFunctionCreate, alloc_eq, setOwn_eq, hstr, pure, M.pure, fnData, -alloc_apply]

theorem step_name_fn (t : State) (fo : ObjId) (h : fo < t.heap.size) (hk : (t.objEntry fo).kind.isPlain = true)
    (hx : (t.objEntry fo).extensible = true) (hn : (t.objEntry fo).props.get? (.str kName) = none) :
    setFunctionName fo (.str nm) none t = .ok () (t.setProp fo (.str kName) (.data (.str nm) false false true)) := by
  simp [setFunctionName, Obj'.defineOwnProperty_entry _ _ _ _ h hk, ordinaryDefineOwnProperty_new _ _ _ _ _ _ _ h hx hn,
    pure, M.pure]

theorem step_legacy_fn (hs : SimpleFn fn nm) (t : State) (fo : ObjId) :
    addLegacyFunctionProps fo fn t =
      .ok () ((t.setProp fo (.str "arguments") (.data .null false false false)).setProp fo (.str "caller")
        (.data .null false false false)) := by
  obtain ⟨hstr, hasync, hgen, hkind, -⟩ := hs
  have hkn : (FuncKind.normal == FuncKind.normal) = true := by decide
  simp [addLegacyFunctionProps, setOwn_eq, hstr, hasync, hgen, hkind, hkn, pure, M.pure]

theorem instantiate_fn (hs : SimpleFn fn nm) (t : State) (ge : EnvId) (ctx : Ctx) (fp : ObjId)
    (hfp : t.curRealm.intrinsics["%Function.prototype%"]? = some fp) :
    instantiateFunction fn ge #[] ctx (.str nm) t = .ok t.heap.size (instStateFn fn nm t ge ctx.script fp) := by
  have hs' := hs
  obtain ⟨hstr, hasync, hgen, hkind, -⟩ := hs
  have hka : (FuncKind.normal == FuncKind.arrow) = false := by decide
  have hkn : (FuncKind.normal == FuncKind.normal) = true := by decide
  simp only [instantiateFunction, M.bind_eq, M.bind_apply, proto_fn fn nm hs' t fp hfp, M.bindRes_ok, hkind, hka]
  simp only [step_create_fn fn nm hs', M.bindRes_ok]
  simp [step_name_fn nm, State.setProp_entry_self, State.allocObj_entry_new,
    PropMap.get?_insert_ne _ _ _ _ AddScript.kLength_ne_kName, hgen, hasync, hkn, AddScript.step_ctor,
    step_legacy_fn fn nm hs', instStateFn, pure, M.pure]

end

section
variable (fn : Func) (nm : JSStr) (t : State) (ge : EnvId) (sc : Nat) (fp : ObjId)

theorem instStateFn_size : (instStateFn fn nm t ge sc fp).heap.size = t.heap.size + 2 := by simp [instStateFn]
theorem instStateFn_envs : (instStateFn fn nm t ge sc fp).envs = t.envs := by simp [instStateFn]
theorem instStateFn_fuel : (instStateFn fn nm t ge sc fp).fuel = t.fuel := by simp [instStateFn]
theorem instStateFn_realms : (instStateFn fn nm t ge sc fp).realms = t.realms := by simp [instStateFn]
theorem instStateFn_realm : (instStateFn fn nm t ge sc fp).realm = t.realm := by simp [instStateFn]
theorem instStateFn_scripts : (instStateFn fn nm t ge sc fp).scripts = t.scripts := by simp [instStateFn]

theorem instStateFn_entry_lt (i : ObjId) (hi : i < t.heap.size) :
    (instStateFn fn nm t ge sc fp).objEntry i = t.objEntry i := by
  have h1 : t.heap.size ≠ i := Nat.ne_of_gt hi
  have h2 : t.heap.size + 1 ≠ i := Nat.ne_of_gt (Nat.lt_succ_of_lt hi)
  have hi1 : i < t.heap.size + 1 := Nat.lt_succ_of_lt hi
  simp [instStateFn, State.setProp_entry_ne _ _ _ _ _ h1, State.setProp_entry_ne _ _ _ _ _ h2,
    State.allocObj_entry_lt, hi, hi1]

theorem instStateFn_func :
    ((instStateFn fn nm t ge sc fp).objEntry t.heap.size).kind = .func (fnData fn t ge sc) := by
  have hne2 : t.heap.size + 1 ≠ t.heap.size := Nat.succ_ne_self _
  simp only [instStateFn]
  rw [State.setProp_entry_self, Obj.withProps_kind, State.setProp_entry_self, Obj.withProps_kind,
    State.setProp_entry_self, Obj.withProps_kind, State.setProp_entry_ne _ _ _ _ _ hne2, State.allocObj_entry_lt,
    State.setProp_entry_self, Obj.withProps_kind, State.setProp_entry_self, Obj.withProps_kind,
    State.allocObj_entry_new]
  all_goals simp
  all_goals exact Nat.lt_succ_of_lt (Nat.lt_succ_self _)

end

end Inst
