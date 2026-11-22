import JSProofs.JsTactic
import JSProofs.FuncExpr
import JSProofs.Destructure
import JSProofs.ObjRules

/-!
# More rules: calls of values, template literals, arrow functions (zippy docs/react-proofs.md)

What the counter component compiles to: `(0, import_react.useState)(0)` (a call of a value: `this` undefined), the
template literal `` `Count: ${n}` ``, and the arrow function `() => setN(n + 1)` as an object literal's property
(NamedEvaluation: named by its key).
-/

open ES ES.M HostRuns
open Std (HashMap)

namespace Logic

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ}

/-- **`(e)(args)`** where `e` is not a reference (`(0, f)(x)`): its value, `this` undefined, the arguments, then the
callee one level of calls down. -/
theorem wp_callValueC {n : Nat} {h : σ} {e : Sem.CExpr} {as : Array Sem.ArgD} {name : CalleeDesc} {ctx : Ctx}
    {s : State} {Q : Value → State → σ → Prop}
    (hw : WP eng answer (n + 1) h (e ctx) s fun fv w h1 =>
      ArgsWP eng answer (n + 1) ctx as.toList #[] h1 w fun args w2 h2 =>
        CallableC w2 fv ∧ WP eng answer n h2 (callImpl eng fv .undefined args) w2 Q) :
    WP eng answer (n + 1) h (Sem.call (Sem.valueRef e) (Sem.args as) false name ctx) s Q := by
  rw [wp_iff_wpr]
  simp only [Sem.call, Sem.valueRef, M.bind_eq, M.bind_apply]
  apply wpr_bind
  apply wp_mbind
  refine wp_mono hw fun fv w h1 q => ?_
  refine wp_of_eq rfl ?_
  rw [wp_iff_wpr]
  simp only [getRefValue, refThisValue, M.bind_apply, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  show WPR eng answer (n + 1) h1 (M.bindRes _ (M.pure fv w)) Q
  simp only [M.pure, M.bindRes_ok]
  show WPR eng answer (n + 1) h1 (M.bindRes _ (M.pure Value.undefined w)) Q
  simp only [M.pure, M.bindRes_ok]
  apply wpr_bind
  refine wp_mono (wp_args q) fun args w2 h2 ⟨hcl, hq⟩ => ?_
  rw [wp_iff_wpr]
  simp only [M.bind_apply, isCallable_of hcl, M.bindRes_ok, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [← wp_iff_wpr]
  exact wp_call hq

theorem toStr_num (x : F64) : toStr (.num x) = M.pure (numberToJSStr x) := by
  funext t; simp only [toStr, maxDepth_eq]; rfl

/-- **`` `a${e}b` ``**: `e`'s value as a string between the two pieces. -/
theorem wp_template1 {n : Nat} {h : σ} {a b : JSStr} {e : Sem.CExpr} {ctx : Ctx} {s : State}
    {Q : Value → State → σ → Prop}
    (hw : WP eng answer n h (e ctx) s fun v w h1 => WP eng answer n h1 (toStr v) w fun sv w2 h2 =>
      Q (.str (a ++ sv ++ b)) w2 h2) :
    WP eng answer n h (Sem.template #[some a, some b] #[e] ctx) s Q := by
  rw [wp_iff_wpr]
  simp only [Sem.template, M.bind_eq, M.bind_apply]
  have hr : Array.range #[e].size = [0].toArray := rfl
  rw [hr, M.foldArr_toArray]
  apply wpr_bind
  rw [foldList_cons_bind]
  apply wp_mbind
  show WP eng answer n h ((e ctx).bind fun v => (toStr v).bind fun s => Pure.pure (a ++ s ++ b)) s _
  apply wp_mbind
  refine wp_mono hw fun v w h1 q => ?_
  apply wp_mbind
  refine wp_mono q fun sv w2 h2 q' => ?_
  refine wp_of_eq rfl ?_
  rw [foldList_nil_pure]
  refine wp_of_eq rfl ?_
  refine wp_of_eq rfl ?_
  simpa using q'

/-- The function object's data for an arrow function in `ctx` (`this` lexical). -/
def arrowData (t : State) (f : Func) (ctx : Ctx) : FuncData := { closData t f ctx with thisMode := .lexical }

/-- The state after an arrow function expression named `nm` (NamedEvaluation): the function object, its `length`
and `name`; an arrow has no `prototype`. -/
def arrowState (t : State) (f : Func) (ctx : Ctx) (fp : ObjId) (nm : JSStr) : State :=
  ((t.allocObj { proto := .obj fp, kind := .func (arrowData t f ctx) }).setProp t.heap.size (.str kLength)
    (.data (numV f.info.expectedArgs) false false true)).setProp t.heap.size (.str kName)
    (.data (.str nm) false false true)

section
variable (t : State) (f : Func) (ctx : Ctx) (fp : ObjId) (nm : JSStr)

@[js_simp] theorem arrowState_curRealm : (arrowState t f ctx fp nm).curRealm = t.curRealm := rfl
@[js_simp] theorem arrowState_envs : (arrowState t f ctx fp nm).envs = t.envs := rfl
@[js_simp] theorem arrowState_envEntry (e : EnvId) : (arrowState t f ctx fp nm).envEntry e = t.envEntry e := rfl
@[js_simp] theorem arrowState_fuel : (arrowState t f ctx fp nm).fuel = t.fuel := rfl
@[js_simp] theorem arrowState_realm : (arrowState t f ctx fp nm).realm = t.realm := rfl
@[js_simp] theorem arrowState_realms : (arrowState t f ctx fp nm).realms = t.realms := rfl
@[js_simp] theorem arrowState_script : (arrowState t f ctx fp nm).script = t.script := rfl
@[js_simp] theorem arrowState_jobs : (arrowState t f ctx fp nm).jobs = t.jobs := rfl
@[js_simp] theorem arrowState_heap_size : (arrowState t f ctx fp nm).heap.size = t.heap.size + 1 := by
  simp [arrowState, State.setProp, State.allocObj]

@[js_simp] theorem arrowState_objEntry_lt {o : ObjId} (h : o < t.heap.size) :
    (arrowState t f ctx fp nm).objEntry o = t.objEntry o := by
  have h1 : t.heap.size ≠ o := Nat.ne_of_gt h
  simp only [arrowState]
  rw [State.setProp_entry_ne _ _ _ _ _ h1, State.setProp_entry_ne _ _ _ _ _ h1, State.allocObj_entry_lt _ _ _ h]

/-- The arrow function object: its kind, prototype, and `name`. -/
theorem arrowState_new :
    ((arrowState t f ctx fp nm).objEntry t.heap.size).kind = .func (arrowData t f ctx) ∧
    ((arrowState t f ctx fp nm).objEntry t.heap.size).proto = .obj fp ∧
    ((arrowState t f ctx fp nm).objEntry t.heap.size).props.get? (.str kName) =
      some (.data (.str nm) false false true) := by
  simp only [arrowState]
  refine ⟨?_, ?_, ?_⟩ <;>
  rw [State.setProp_entry_self _ _ _ _ (by simp [State.setProp, State.allocObj]),
    State.setProp_entry_self _ _ _ _ (by simp [State.allocObj]), State.allocObj_entry_new] <;>
  simp [ES.Obj.withProps_proto, PropMap.get?_insert]

theorem frame_arrowState : Frame {} t (arrowState t f ctx fp nm) := by
  simp only [arrowState]
  refine frame_setProp_new ?_ (by simp) _ _
  refine frame_setProp_new ?_ (by simp) _ _
  exact frame_allocObj (frame_refl _ _) _

end

/-- An arrow function: anonymous, strict, neither async nor a generator. -/
structure ArrowClosure (f : Func) : Prop where
  name : f.name = none
  kind : f.kind = .arrow
  async : f.isAsync = false
  gen : f.isGenerator = false
  strict : f.strict = true

theorem instantiate_arrow (t : State) (f : Func) (ctx : Ctx) (fp : ObjId) (nm : JSStr) (hf : ArrowClosure f)
    (hfp : t.curRealm.intrinsics["%Function.prototype%"]? = some fp) :
    instantiateFunctionExpr f ctx (some (.str nm)) t = .ok (.obj t.heap.size) (arrowState t f ctx fp nm) := by
  have hka : (FuncKind.arrow == FuncKind.arrow) = true := by decide
  have hkn : (FuncKind.arrow == FuncKind.normal) = false := by decide
  have hproto : intrinsic (functionProtoName f) t = .ok fp t := by
    simp [intrinsic, hfp, functionProtoName, hf.async, hf.gen]
  have hcreate : ordinaryFunctionCreate fp f ctx.lex ctx.priv ctx true t =
      .ok t.heap.size ((t.allocObj { proto := .obj fp, kind := .func (arrowData t f ctx) }).setProp t.heap.size
        (.str kLength) (.data (numV f.info.expectedArgs) false false true)) := by
    simp [ordinaryFunctionCreate, alloc_eq, setOwn_eq, Pure.pure, M.pure, arrowData, closData, -alloc_apply]
  have hname : ∀ u : State, t.heap.size < u.heap.size → (u.objEntry t.heap.size).kind.isPlain = true →
      (u.objEntry t.heap.size).extensible = true → (u.objEntry t.heap.size).props.get? (.str kName) = none →
      setFunctionName t.heap.size (.str nm) none u =
        .ok () (u.setProp t.heap.size (.str kName) (.data (.str nm) false false true)) := by
    intro u h hk hx hn
    simp [setFunctionName, Obj'.defineOwnProperty_entry _ _ _ _ h hk,
      ordinaryDefineOwnProperty_new _ _ _ _ _ _ _ h hx hn, Pure.pure, M.pure]
  have hlegacy : ∀ u : State, addLegacyFunctionProps t.heap.size f u = .ok () u := by
    intro u; simp [addLegacyFunctionProps, hf.strict, Pure.pure, M.pure]
  simp only [instantiateFunctionExpr, M.bind_eq, M.bind_apply, hproto, M.bindRes_ok, hf.name, hf.kind, hka]
  rw [show (some (PropKey.str nm)).getD (.str JSStr.empty) = .str nm from rfl]
  simp only [hcreate, M.bindRes_ok]
  simp [hname, State.setProp_entry_self, State.allocObj_entry_new, PropMap.get?_insert_ne _ _ _ _ kLength_ne_kName',
    hf.gen, hf.async, hkn, hlegacy, arrowState, Pure.pure, M.pure]

/-- **An arrow function as an object literal's property** `key: () => …` (NamedEvaluation with the key). -/
theorem wp_namedArrow {n k : Nat} {h : σ} {f : Func} {ctx : Ctx} {nm : JSStr} {s : State}
    {Q : Value → State → σ → Prop} (hf : ArrowClosure f)
    (hfp : (s.curRealm.intrinsics["%Function.prototype%"]?).isSome = true)
    (hq : Q (.obj s.heap.size) (arrowState s f ctx (funcProto s) nm) h) :
    WP eng answer n h (namedEval (k + 1) ctx (.func f) (.str nm)) s Q := by
  obtain ⟨fp, hfp'⟩ := Option.isSome_iff_exists.mp hfp
  have he : funcProto s = fp := by simp [funcProto, hfp']
  rw [he] at hq
  have hn : f.name.isNone = true := by simp [hf.name]
  simp only [namedEval, hn, ↓reduceIte]
  exact wp_of_eq (instantiate_arrow s f ctx fp nm hf hfp') hq

/-- **`"k" in o`** for an object whose prototype chain is plain: whether the chain has the key. -/
theorem wp_inPlain {n : Nat} {h : σ} {k : JSStr} {o : ObjId} {m : Nat} {s : State} {Q : Value → State → σ → Prop}
    (hc : PlainChain s m o (.str k)) (hm : m ≤ 9999) (hq : Q (.bool (ordLookup s m o (.str k)).isSome) s h) :
    WP eng answer n h (Sem.binaryOp .in (.str k) (.obj o)) s Q := by
  have hk : toPropertyKey (.str k) s = .ok (.str k) s := by
    simp only [toPropertyKey, maxDepth_eq]; rfl
  refine wp_of_eq ?_ hq
  simp only [Sem.binaryOp, M.bind_eq, M.bind_apply, hk, M.bindRes_ok, Obj'.hasProperty_chain s _ m o hc hm]
  rfl

/-- **`void e`**: `e`'s evaluation, then `undefined`. -/
theorem wp_void {n : Nat} {h : σ} {e : Sem.CExpr} {ctx : Ctx} {s : State} {Q : Value → State → σ → Prop}
    (hw : WP eng answer n h (e ctx) s fun _ w h1 => Q .undefined w h1) :
    WP eng answer n h (Sem.unary .void e ctx) s Q := by
  rw [wp_iff_wpr]
  simp only [Sem.unary, M.bind_eq, M.bind_apply]
  apply wpr_bind
  exact wp_mono hw fun _ w h1 q => wp_of_eq rfl q

/-- **`obj.k` for a key absent from `obj` and its prototype `p`, whose prototype is null** (`config.key` of an
object literal): `undefined`. -/
theorem wp_getMemberAbsent2 {n : Nat} {h : σ} {obj : Sem.CExpr} {k : JSStr} {ctx : Ctx} {s : State}
    {Q : Value → State → σ → Prop}
    (hw : WP eng answer n h (obj ctx) s fun bv w h1 => ∃ o p, bv = .obj o ∧ o < w.heap.size ∧
      (w.objEntry o).kind.isPlain = true ∧ (w.objEntry o).props.get? (.str k) = none ∧
      (w.objEntry o).proto = .obj p ∧ p < w.heap.size ∧ (w.objEntry p).kind.isPlain = true ∧
      (w.objEntry p).props.get? (.str k) = none ∧ (w.objEntry p).proto = .null ∧ Q .undefined w h1) :
    WP eng answer n h (Sem.getValue (Sem.memberRef obj (.name k) false) ctx) s Q := by
  apply wp_getMember
  refine wp_mono hw fun bv w h1 ⟨o, p, hb, ho, hok, hon, hop, hp, hpk, hpn, hpp, q⟩ => ?_
  have hc : PlainChain w 2 o (.str k) := ⟨ho, hok, fun _ => by rw [hop]; exact ⟨hp, hpk, fun _ => by rw [hpp]; trivial⟩⟩
  have hl : ordLookup w 2 o (.str k) = none := by simp [ordLookup, hon, hop, hpn, hpp]
  exact ⟨o, 2, hb, hc, by decide, by rw [hl]; rfl, by rw [hl]; exact q⟩

end

end Logic
