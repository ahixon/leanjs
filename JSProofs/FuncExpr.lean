import JSProofs.Loops2
import JSProofs.Object

/-!
# Function expressions (anonymous, strict) (zippy docs/react-proofs.md)

An anonymous strict `function () { … }` (React's callbacks: `scheduleMicrotask(function () { … })`) creates the
function object `t.heap.size` (its `length` and `name ""`) and its `prototype` object `t.heap.size + 1` (with
`constructor`): `closState`. Strict functions have no legacy `arguments`/`caller`.
-/

open ES HostRuns
open Std (HashMap)

namespace Logic

theorem kLength_ne_kName' : PropKey.str kLength ≠ PropKey.str kName := by
  simp [kLength, kName]

theorem makeConstructor_eq (t : State) (fo : ObjId) :
    makeConstructor fo true none t =
      .ok () (((t.allocObj { proto := .obj t.curRealm.objectProto }).setProp t.heap.size (.str kConstructor)
        (.data (.obj fo) true false true)).setProp fo (.str kPrototype) (.data (.obj t.heap.size) true false false)) := by
  simp [makeConstructor, newObject_eq, setOwn_eq, pure, M.pure]

/-- The function object's data for a function expression in `ctx`. -/
def closData (t : State) (f : Func) (ctx : Ctx) : FuncData :=
  { code := f, env := ctx.lex, privEnv := ctx.priv, thisMode := .strict,
    source := (Option.map (fun x => x.prog.source) t.scripts[ctx.script]?).getD "", realm := t.realm,
    script := ctx.script }

@[js_simp] theorem closData_code (t : State) (f : Func) (ctx : Ctx) : (closData t f ctx).code = f := rfl
@[js_simp] theorem closData_env (t : State) (f : Func) (ctx : Ctx) : (closData t f ctx).env = ctx.lex := rfl
@[js_simp] theorem closData_thisMode (t : State) (f : Func) (ctx : Ctx) : (closData t f ctx).thisMode = .strict := rfl
@[js_simp] theorem closData_isClassCtor (t : State) (f : Func) (ctx : Ctx) : (closData t f ctx).isClassCtor = false :=
  rfl
@[js_simp] theorem closData_realm (t : State) (f : Func) (ctx : Ctx) : (closData t f ctx).realm = t.realm := rfl
@[js_simp] theorem closData_privEnv (t : State) (f : Func) (ctx : Ctx) : (closData t f ctx).privEnv = ctx.priv := rfl
@[js_simp] theorem closData_script (t : State) (f : Func) (ctx : Ctx) : (closData t f ctx).script = ctx.script := rfl

/-- The state after a function expression: the function object and its `prototype` object. -/
def closState (t : State) (f : Func) (ctx : Ctx) (fp : ObjId) : State :=
  let fo := t.heap.size
  let t1 := t.allocObj { proto := .obj fp, kind := .func (closData t f ctx) }
  let t2 := t1.setProp fo (.str kLength) (.data (numV f.info.expectedArgs) false false true)
  let t3 := t2.setProp fo (.str kName) (.data (.str JSStr.empty) false false true)
  let t4 := t3.allocObj { proto := .obj t.curRealm.objectProto }
  let t5 := t4.setProp (fo + 1) (.str kConstructor) (.data (.obj fo) true false true)
  t5.setProp fo (.str kPrototype) (.data (.obj (fo + 1)) true false false)

/-- A function expression that is anonymous, strict, and a plain function. -/
structure PlainClosure (f : Func) : Prop where
  name : f.name = none
  kind : f.kind = .normal
  async : f.isAsync = false
  gen : f.isGenerator = false
  strict : f.strict = true

theorem instantiate_closure (t : State) (f : Func) (ctx : Ctx) (fp : ObjId) (hf : PlainClosure f)
    (hfp : t.curRealm.intrinsics["%Function.prototype%"]? = some fp) :
    instantiateFunctionExpr f ctx none t = .ok (.obj t.heap.size) (closState t f ctx fp) := by
  have hka : (FuncKind.normal == FuncKind.arrow) = false := by decide
  have hkn : (FuncKind.normal == FuncKind.normal) = true := by decide
  have hproto : intrinsic (functionProtoName f) t = .ok fp t := by
    simp [intrinsic, hfp, functionProtoName, hf.async, hf.gen]
  have hcreate : ordinaryFunctionCreate fp f ctx.lex ctx.priv ctx false t =
      .ok t.heap.size ((t.allocObj { proto := .obj fp, kind := .func (closData t f ctx) }).setProp t.heap.size
        (.str kLength) (.data (numV f.info.expectedArgs) false false true)) := by
    simp [ordinaryFunctionCreate, alloc_eq, setOwn_eq, hf.strict, pure, M.pure, closData, -alloc_apply]
  have hname : ∀ u : State, t.heap.size < u.heap.size → (u.objEntry t.heap.size).kind.isPlain = true →
      (u.objEntry t.heap.size).extensible = true → (u.objEntry t.heap.size).props.get? (.str kName) = none →
      setFunctionName t.heap.size (.str JSStr.empty) none u =
        .ok () (u.setProp t.heap.size (.str kName) (.data (.str JSStr.empty) false false true)) := by
    intro u h hk hx hn
    simp [setFunctionName, Obj'.defineOwnProperty_entry _ _ _ _ h hk,
      ordinaryDefineOwnProperty_new _ _ _ _ _ _ _ h hx hn, pure, M.pure]
  have hlegacy : ∀ u : State, addLegacyFunctionProps t.heap.size f u = .ok () u := by
    intro u; simp [addLegacyFunctionProps, hf.strict, pure, M.pure]
  simp only [instantiateFunctionExpr, M.bind_eq, M.bind_apply, hproto, M.bindRes_ok, hf.name, hf.kind, hka]
  rw [show (none : Option PropKey).getD (.str JSStr.empty) = .str JSStr.empty from rfl]
  simp only [hcreate, M.bindRes_ok]
  simp [hname, State.setProp_entry_self, State.allocObj_entry_new, PropMap.get?_insert_ne _ _ _ _ kLength_ne_kName',
    hf.gen, hf.async, hkn, makeConstructor_eq, hlegacy, closState, pure, M.pure]

@[js_simp] theorem bodyState_curRealm (s : State) (fo : ObjId) (d : FuncData) (t : Value) (args : Array Value) :
    (bodyState s fo d t args).curRealm = s.realms[d.realm]! := by
  simp [bodyState, entryState, State.curRealm, State.setEnv]

/-! What a function expression leaves alone: records, existing objects, fuel, realm. -/
section
variable (t : State) (f : Func) (ctx : Ctx) (fp : ObjId)

@[js_simp] theorem closState_curRealm : (closState t f ctx fp).curRealm = t.curRealm := rfl
@[js_simp] theorem closState_envs : (closState t f ctx fp).envs = t.envs := rfl
@[js_simp] theorem closState_envEntry (e : EnvId) : (closState t f ctx fp).envEntry e = t.envEntry e := rfl
@[js_simp] theorem closState_fuel : (closState t f ctx fp).fuel = t.fuel := rfl
@[js_simp] theorem closState_realm : (closState t f ctx fp).realm = t.realm := rfl
@[js_simp] theorem closState_realms : (closState t f ctx fp).realms = t.realms := rfl
@[js_simp] theorem closState_script : (closState t f ctx fp).script = t.script := rfl
@[js_simp] theorem closState_heap_size : (closState t f ctx fp).heap.size = t.heap.size + 2 := by
  simp [closState, State.setProp, State.allocObj]

theorem closState_objEntry_lt {o : ObjId} (h : o < t.heap.size) :
    (closState t f ctx fp).objEntry o = t.objEntry o := by
  have h1 : t.heap.size ≠ o := Nat.ne_of_gt h
  have h2 : t.heap.size + 1 ≠ o := Nat.ne_of_gt (Nat.lt_succ_of_lt h)
  simp only [closState]
  rw [State.setProp_entry_ne _ _ _ _ _ h1, State.setProp_entry_ne _ _ _ _ _ h2, State.allocObj_entry_lt _ _ _
    (by simp [State.setProp, State.allocObj]; exact Nat.lt_succ_of_lt h), State.setProp_entry_ne _ _ _ _ _ h1,
    State.setProp_entry_ne _ _ _ _ _ h1, State.allocObj_entry_lt _ _ _ h]

/-- The new function object's kind. -/
theorem closState_kind : ((closState t f ctx fp).objEntry t.heap.size).kind = .func (closData t f ctx) := by
  have hne2 : t.heap.size + 1 ≠ t.heap.size := Nat.succ_ne_self _
  simp only [closState]
  rw [State.setProp_entry_self _ _ _ _ (by simp [State.setProp, State.allocObj]; exact Nat.lt_succ_of_lt (Nat.lt_succ_self _)), Obj.withProps_kind,
    State.setProp_entry_ne _ _ _ _ _ hne2, State.allocObj_entry_lt _ _ _ (by simp [State.setProp, State.allocObj]),
    State.setProp_entry_self _ _ _ _ (by simp [State.setProp, State.allocObj]), Obj.withProps_kind,
    State.setProp_entry_self _ _ _ _ (by simp [State.allocObj]), Obj.withProps_kind, State.allocObj_entry_new]

theorem frame_closState : Frame {} t (closState t f ctx fp) := by
  simp only [closState]
  refine frame_setProp_new ?_ (by simp) _ _
  refine frame_setProp_new ?_ (by simp) _ _
  refine frame_allocObj ?_ _
  refine frame_setProp_new ?_ (by simp) _ _
  refine frame_setProp_new ?_ (by simp) _ _
  exact frame_allocObj (frame_refl _ _) _

end

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ}

/-- `Function.prototype` of the current realm (0 if there is none; the rule's premise rules that out). -/
def funcProto (t : State) : ObjId := (t.curRealm.intrinsics["%Function.prototype%"]?).getD 0

/-- **A function expression**: the new function object, in `closState`. -/
theorem wp_funcExpr {n : Nat} {h : σ} {f : Func} {ctx : Ctx} {s : State} {Q : Value → State → σ → Prop}
    (hf : PlainClosure f) (hfp : (s.curRealm.intrinsics["%Function.prototype%"]?).isSome = true)
    (hq : Q (.obj s.heap.size) (closState s f ctx (funcProto s)) h) : WP eng answer n h (Sem.func f none ctx) s Q := by
  obtain ⟨fp, hfp'⟩ := Option.isSome_iff_exists.mp hfp
  have he : funcProto s = fp := by simp [funcProto, hfp']
  rw [he] at hq
  exact wp_of_eq (instantiate_closure s f ctx fp hf hfp') hq
end

end Logic


namespace Logic

/-- Two writes in a row to the same record: the second (each carries the whole record). -/
@[js_simp] theorem setEnv_setEnv_same (s : State) (e : EnvId) (a b : Env) :
    (s.setEnv e a).setEnv e b = s.setEnv e b := by
  simp only [State.setEnv]
  congr 1
  apply Array.ext
  · simp
  · intro i h1 h2
    simp only [Array.getElem_modify]
    split <;> rfl

end Logic

namespace Logic

/-- A record write that collapsed two (`setEnv_setEnv_same`), framed as the two. -/
theorem frame_setEnv_split {fp : Footprint} {s u : State} {e : EnvId} {a b : Env}
    (h : Frame fp s ((u.setEnv e a).setEnv e b)) : Frame fp s (u.setEnv e b) := by
  rwa [setEnv_setEnv_same] at h

end Logic

namespace Logic

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ}

/-- **`-x`** of a Number. -/
theorem wp_negNum {n : Nat} {h : σ} {e : Sem.CExpr} {ctx : Ctx} {s : State} {Q : Value → State → σ → Prop}
    (hw : WP eng answer n h (e ctx) s fun v w h1 => match v with
      | .num x => Q (.num x.neg) w h1
      | _ => False) :
    WP eng answer n h (Sem.unary .neg e ctx) s Q := by
  rw [wp_iff_wpr]
  simp only [Sem.unary, M.bind_eq, M.bind_apply]
  refine wpr_bind (wp_mono hw fun v w h1 q => ?_)
  cases v <;> simp at q
  exact wp_of_eq (by simp [Sem.unaryOp, M.bind_eq, M.bind_apply, toNumeric_num, M.bindRes_ok]; rfl) q

/-- **`~x`** of a Number: the complement of its 32-bit integer. -/
theorem wp_bitNotNum {n : Nat} {h : σ} {e : Sem.CExpr} {ctx : Ctx} {s : State} {Q : Value → State → σ → Prop}
    (hw : WP eng answer n h (e ctx) s fun v w h1 => match v with
      | .num x => Q (intV (Conv.intNot (Conv.toInt32 x))) w h1
      | _ => False) :
    WP eng answer n h (Sem.unary .bitNot e ctx) s Q := by
  rw [wp_iff_wpr]
  simp only [Sem.unary, M.bind_eq, M.bind_apply]
  refine wpr_bind (wp_mono hw fun v w h1 q => ?_)
  cases v <;> simp at q
  exact wp_of_eq (by simp [Sem.unaryOp, M.bind_eq, M.bind_apply, toNumeric_num, M.bindRes_ok]; rfl) q

end

end Logic

namespace Logic

/-- `m'` agrees with `m` except at the names `ks`. -/
def OnlyAt (ks : List JSStr) (m m' : Std.HashMap JSStr Binding) : Prop := ∀ x, x ∉ ks → m'[x]? = m[x]?

theorem onlyAt_refl (ks : List JSStr) (m : Std.HashMap JSStr Binding) : OnlyAt ks m m := fun _ _ => rfl

theorem onlyAt_modify {ks : List JSStr} {m m' : Std.HashMap JSStr Binding} {k : JSStr} (hk : k ∈ ks)
    (f : Binding → Binding) (h : OnlyAt ks m m') : OnlyAt ks m (m'.modify k f) := fun x hx => by
  have hkx : (k == x) = false := by
    simp only [beq_eq_false_iff_ne]; exact fun e => hx (e ▸ hk)
  rw [Std.HashMap.getElem?_modify, hkx]; exact h x hx

theorem onlyAt_insert {ks : List JSStr} {m m' : Std.HashMap JSStr Binding} {k : JSStr} (hk : k ∈ ks)
    (b : Binding) (h : OnlyAt ks m m') : OnlyAt ks m (m'.insert k b) := fun x hx => by
  have hkx : (k == x) = false := by
    simp only [beq_eq_false_iff_ne]; exact fun e => hx (e ▸ hk)
  rw [Std.HashMap.getElem?_insert, hkx]; exact h x hx

/-- **A function record rewritten at names in the footprint** (a call's locals, several writes at once). -/
theorem frame_setEnv_func_onlyAt {fp : Footprint} {s u : State} {e : EnvId} (hF : Frame fp s u) (he : e < s.envs.size)
    {bm bm' : Std.HashMap JSStr Binding} {o : Option EnvId} {ts : ThisStatus} {tv : Value} {fo : ObjId} {nt : Value}
    (hent : u.envEntry e = .func bm o ts tv fo nt) (k0 : JSStr) (ks : List JSStr) (hks : ∀ x ∈ k0 :: ks, (e, x) ∈ fp.binds)
    (hm : OnlyAt (k0 :: ks) bm bm') : Frame fp s (u.setEnv e (.func bm' o ts tv fo nt)) := by
  have heu : e < u.envs.size := Nat.lt_of_lt_of_le he hF.envs_le
  refine {
    envs_le := by simpa using hF.envs_le
    heap_le := by simpa [State.setEnv] using hF.heap_le
    env_agree := fun i hi => ?_
    obj_agree := fun o' ho => by simpa [State.objEntry, State.setEnv] using hF.obj_agree o' ho
    env_eq := fun i hi hn => ?_
    obj_eq := fun o' ho hn => by simpa [State.objEntry, State.setEnv] using hF.obj_eq o' ho hn
    realms_eq := by simpa [State.setEnv] using hF.realms_eq
    jobs_prefix := by simpa [State.setEnv] using hF.jobs_prefix
    jobs_eq := fun hj => by simpa [State.setEnv] using hF.jobs_eq hj }
  · by_cases hei : e = i
    · subst hei
      rw [State.setEnv_envEntry_self _ _ _ heu]
      have hag := hF.env_agree e hi
      rw [hent] at hag
      unfold EnvAgree at hag ⊢
      cases hs : Scope.declLike? (s.envEntry e) with
      | none => rw [hs] at hag; rw [← hag] at hs; simp [Scope.declLike?] at hs
      | some p =>
        obtain ⟨bs, os⟩ := p
        rw [hs] at hag
        obtain ⟨bw, hw, hx⟩ := hag
        simp only [Scope.declLike?, Option.some.injEq, Prod.mk.injEq] at hw
        obtain ⟨rfl, rfl⟩ := hw
        refine ⟨bm', rfl, fun y hy => ?_⟩
        have hyk : y ∉ k0 :: ks := fun hm' => hy (hks y hm')
        rw [hm y hyk]; exact hx y hy
    · rw [setEnv_envEntry_ne _ _ _ _ hei]; exact hF.env_agree i hi
  · by_cases hei : e = i
    · subst hei; exact absurd (hks k0 List.mem_cons_self) (hn k0)
    · rw [setEnv_envEntry_ne _ _ _ _ hei]; exact hF.env_eq i hi hn

end Logic

namespace Logic

theorem forall_mem_of_all {fp : Footprint} {e : EnvId} {l : List JSStr}
    (h : l.all (fun x => fp.binds.contains (e, x)) = true) : ∀ x ∈ l, (e, x) ∈ fp.binds := by
  intro x hx
  have := List.all_eq_true.mp h x hx
  simpa using this

end Logic
