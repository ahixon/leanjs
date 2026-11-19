import Proofs.Object
import Proofs.AddCall
import Proofs.ScriptGen

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

end AddScript
