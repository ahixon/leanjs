import JSProofs.Throw
import JSProofs.Closure
import JSProofs.TWGen

/-!
# Nested calls: callees whose bodies make calls of their own

`Runs eng n r b w'`: `r` ends in `.ok b w'` after its call requests are answered, the driver running each
callee one level deeper (`drive eng (n − 1)`): either `r` is already `.ok b w'`, or a call request whose
callee drives to a value (or a throw), followed by the continuation. Unlike `Runs.RunsTo` it is inductive,
so it is closed under every way the engine wraps a result: binding (`runs_bind`), handlers
(`runs_tryCatch`); and it gives what driving at depth `n` yields (`drive_of_runs`).
-/

open ES ES.Conv SumProof

namespace Nested

/-- A result whose requests the driver answers (each callee driven at depth `n`), ending in `.ok b w'`. -/
inductive Runs (eng : Engine) {α : Type} : Nat → Res α → α → State → Prop
  | ok (n : Nat) (b : α) (w : State) : Runs eng n (.ok b w) b w
  | call (n : Nat) (f t : Value) (args : Array Value) (w : State) (K : Outcome → State → Res α) (x : Value)
      (w1 : State) (b : α) (w' : State) (h : ∀ cs, (drive eng n (callImpl eng f t args w) cs).1 = .ok x w1)
      (hk : Runs eng (n + 1) (K (.normal x) w1) b w') : Runs eng (n + 1) (.req (.call f t args) w K) b w'
  | callErr (n : Nat) (f t : Value) (args : Array Value) (w : State) (K : Outcome → State → Res α) (e : Value)
      (w1 : State) (b : α) (w' : State) (h : ∀ cs, (drive eng n (callImpl eng f t args w) cs).1 = .err e w1)
      (hk : Runs eng (n + 1) (K (.throw e) w1) b w') : Runs eng (n + 1) (.req (.call f t args) w K) b w'

theorem drive_succ_ok (eng : Engine) (n : Nat) {α : Type} (b : α) (w : State) (cs : Conts) :
    drive eng n (.ok b w) cs = (.ok b w, cs) := by cases n <;> simp [drive, driveWith]

/-- **What driving gives**: a result that runs to `b` drives (at its depth) to `.ok b w'`. -/
theorem drive_of_runs (eng : Engine) {α : Type} :
    ∀ (n : Nat) (r : Res α) (b : α) (w' : State), Runs eng n r b w' → ∀ cs, (drive eng n r cs).1 = .ok b w' := by
  intro n r b w' h
  induction h with
  | ok n b w => intro cs; rw [drive_succ_ok]
  | call n f t args w K x w1 b w' h hk ih =>
    intro cs
    rcases hd : drive eng n (callImpl eng f t args w) cs with ⟨r', cs'⟩
    have hr' : r' = .ok x w1 := by have := h cs; rw [hd] at this; exact this
    subst hr'
    simp only [drive, driveWith, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hd, outcomeOf]
    exact ih cs'
  | callErr n f t args w K e w1 b w' h hk ih =>
    intro cs
    rcases hd : drive eng n (callImpl eng f t args w) cs with ⟨r', cs'⟩
    have hr' : r' = .err e w1 := by have := h cs; rw [hd] at this; exact this
    subst hr'
    simp only [drive, driveWith, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hd, outcomeOf]
    exact ih cs'

/-- Binding a continuation to a result that runs. -/
theorem runs_bind (eng : Engine) {α β : Type} (k : α → M β) :
    ∀ (n : Nat) (r : Res α) (a : α) (w1 : State), Runs eng n r a w1 →
      ∀ (b : β) (w2 : State), Runs eng n (k a w1) b w2 → Runs eng n (M.bindRes k r) b w2 := by
  intro n r a w1 h
  induction h with
  | ok n b w => intro b' w2 hk; exact hk
  | call n f t args w K x w1 b w' h hk ih =>
    intro b2 w2 hk2
    exact .call n f t args w _ x w1 b2 w2 h (ih b2 w2 hk2)
  | callErr n f t args w K e w1 b w' h hk ih =>
    intro b2 w2 hk2
    exact .callErr n f t args w _ e w1 b2 w2 h (ih b2 w2 hk2)

/-- A handler around a result that runs normally changes nothing. -/
theorem runs_tryCatch (eng : Engine) {α : Type} (hd : Value → M α) :
    ∀ (n : Nat) (r : Res α) (a : α) (w : State), Runs eng n r a w → Runs eng n (M.tryCatchRes hd r) a w := by
  intro n r a w h
  induction h with
  | ok n b w => exact .ok n b w
  | call n f t args w K x w1 b w' h hk ih => exact .call n f t args w _ x w1 b w' h ih
  | callErr n f t args w K e w1 b w' h hk ih => exact .callErr n f t args w _ e w1 b w' h ih

/-- A callee that returns without requests of its own: the driver answers it at any depth. -/
theorem drive_callImpl_ok (eng : Engine) (n : Nat) (f t : Value) (args : Array Value) (w : State) (x : Value)
    (w1 : State) (h : callImpl eng f t args w = .ok x w1) :
    ∀ cs, (drive eng n (callImpl eng f t args w) cs).1 = .ok x w1 := by
  intro cs; rw [h, drive_succ_ok]

/-! ## Calls whose bodies run -/

theorem callECMA_undef_runs (eng : Engine) (m : Nat) {Q : State → Prop} (f : ObjId) (d : FuncData) (s : State) (args : Array Value) (v : Value)
    (go : ObjId) (gb : Std.HashMap JSStr Binding) (gtv : Value)
    (hcls : d.isClassCtor = false) (hmode : d.thisMode = .global) (hasync : d.code.isAsync = false)
    (hgen : d.code.isGenerator = false)
    (hge : (s.realms[d.realm]!).globalEnv < s.envs.size)
    (hgE : s.envEntry (s.realms[d.realm]!).globalEnv = .global go gb gtv)
    (hbody : ∀ t : State, s.envs.size < t.envs.size →
      t.envEntry s.envs.size = .func ∅ (some d.env) .initialized gtv f .undefined →
      (∀ e, e < s.envs.size → t.envEntry e = s.envEntry e) → t.heap = s.heap → t.fuel = s.fuel → t.realms = s.realms → t.realm = d.realm →
      ∃ t', Runs eng m (evalFunctionBody evalDepth f d s.envs.size args t) v t' ∧ Q t') :
    ∃ s', Runs eng m (callECMA f d .undefined args s) v s' ∧ s'.realm = s.realm ∧ s'.script = s.script ∧
      ∃ t', Q t' ∧ s'.heap = t'.heap ∧ s'.envs = t'.envs ∧ s'.fuel = t'.fuel ∧ s'.realms = t'.realms := by
  let ge := (s.realms[d.realm]!).globalEnv
  let s1 : State := { s with realm := d.realm, script := d.script }
  let env := s.envs.size
  let E0 : Env := .func {} (some d.env) .uninitialized .undefined f .undefined
  let s2 : State := { s1 with envs := s1.envs.push E0 }
  let s3 := s2.setEnv env (.func {} (some d.env) .initialized gtv f .undefined)
  have hgl : (ThisMode.global == ThisMode.lexical) = false := by decide
  have hgs : (ThisMode.global == ThisMode.strict) = false := by decide
  have hnew : newFunctionEnv f d .undefined s1 = .ok env s2 := by
    simp [hgl, newFunctionEnv, hmode, s2, s1, E0, env]
  have henv2 : env < s2.envs.size := by simp [s2, s1, env]
  have hge2 : ge < s2.envs.size := by simp [s2, s1]; exact Nat.lt_succ_of_lt hge
  have hgE2 : s2.envEntry ge = .global go gb gtv := by
    have hne : ge ≠ s.envs.size := Nat.ne_of_lt hge
    simp only [State.envEntry] at hgE ⊢
    simp [s2, s1, Array.getElem?_push, hne, ge] at hgE ⊢
    exact hgE
  have hbind : ordinaryCallBindThis d env .undefined s2 = .ok () s3 := by
    simp only [ordinaryCallBindThis, hmode]
    have hnn : (Value.undefined).isNullish = true := rfl
    have hui : (ThisStatus.uninitialized == ThisStatus.initialized) = false := by decide
    have hrl : (s2.realms[d.realm]!).globalEnv = ge := rfl
    simp [hgl, hgs, hnn, hui, M.bind_eq, M.bind_apply, bindThisValue, readEnv_entry _ _ _ henv2, pure, M.pure,
      modifyEnv_eq_setEnv _ _ _ henv2, s3, hrl, readEnv_entry _ _ _ hge2, hgE2]
    simp [hui, State.envEntry, s2, s1, E0, env, modifyEnv, State.setEnv]
  have henv3 : env < s3.envs.size := by simp [s3, s2, s1, env]
  have hE3 : s3.envEntry env = .func ∅ (some d.env) .initialized gtv f .undefined := by
    simp [s3, henv2]
  have hold : ∀ e, e < s.envs.size → s3.envEntry e = s.envEntry e := by
    intro e he
    have hne : env ≠ e := Nat.ne_of_gt he
    rw [State.setEnv_envEntry_ne _ _ _ _ hne]
    simp [State.envEntry, s2, s1, Array.getElem?_push, Nat.ne_of_lt he]
  obtain ⟨s4, hb, hQ⟩ : ∃ t', Runs eng m (evalFunctionBody evalDepth f d env args s3) v t' ∧ Q t' :=
    hbody s3 henv3 hE3 hold (by simp [s3, s2, s1, State.setEnv]) (by simp [s3, s2, s1]) (by simp [s3, s2, s1]) (by simp [s3, s2, s1])
  refine ⟨{ s4 with realm := s.realm, script := s.script }, ?_, rfl, rfl, s4, hQ, rfl, rfl, rfl, rfl⟩
  simp only [callECMA, hcls, inCallee, M.bind_eq, M.bind_apply, M.readS_apply, M.bindRes_ok, M.modify_apply]
  simp [M.bind_apply, hnew, hbind, hasync, hgen, M.attempt, M.tryCatch_apply, pure, M.pure, s1]
  refine runs_bind eng _ m _ (Except.ok v) s4 ?_ v _ ?_
  · exact runs_tryCatch eng _ m _ _ s4 (runs_bind eng _ m _ v s4 hb (Except.ok v) s4 (Runs.ok m _ _))
  · simp only [M.bind_eq, M.bind_apply, M.modify_apply, M.bindRes_ok, pure, M.pure]
    exact Runs.ok m _ _

/-! ## At the top: a call whose callee makes calls -/

theorem drivesTo_call_nested (eng : Engine) {α : Type} (f t : Value) (args : Array Value) (s : State) (k : Outcome → State → Res α)
    (x : Value) (s1 : State) (v : α) (s' : State)
    (h : ∀ cs, (drive eng 3999 (callImpl eng f t args s) cs).1 = .ok x s1)
    (hk : Script.DrivesTo eng (k (.normal x) s1) v s') : Script.DrivesTo eng (.req (.call f t args) s k) v s' := by
  intro cs
  simp only [Script.DrivesTo, callDepth] at hk ⊢
  rcases hd : drive eng 3999 (callImpl eng f t args s) cs with ⟨r', cs'⟩
  have hr' : r' = .ok x s1 := by have := h cs; rw [hd] at this; exact this
  subst hr'
  have hdr : ∀ {β : Type} (r : Res β) (cs : Conts), drive eng 4000 r cs = driveWith eng true (drive eng 3999) r cs :=
    fun _ _ => rfl
  have := hk cs'
  rw [hdr] at this ⊢
  simp only [driveWith, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hd, outcomeOf]
  exact this

theorem runsTo_call_nested (eng : Engine) {β : Type} (f t : Value) (args : Array Value) (w : State)
    (K : Outcome → State → Res β) (x : Value) (w1 : State) (b : β) (w' : State)
    (h : ∀ cs, (drive eng 3999 (callImpl eng f t args w) cs).1 = .ok x w1)
    (hk : _root_.Runs.RunsTo eng (K (.normal x) w1) b w') : _root_.Runs.RunsTo eng (.req (.call f t args) w K) b w' := by
  intro α k v s' hd
  show Script.DrivesTo eng (.req (.call f t args) w (fun o s => M.bindRes k (K o s))) v s'
  exact drivesTo_call_nested eng f t args w _ x w1 v s' h (hk α k v s' hd)

/-! ## `twice` -/

/-- A name on the global object, resolved from a function body's block `L` (outer: the function record `F`,
outer: the global record). -/
theorem resolveBinding_body_global (L F ge : EnvId) (n : JSStr) (strict : Bool) (s : State)
    (b1 b2 : Std.HashMap JSStr Binding) (ts : ThisStatus) (tv : Value) (fo : ObjId) (nt : Value) (g : ObjId)
    (gb : Std.HashMap JSStr Binding) (gtv : Value) (p : Property)
    (h1 : L < s.envs.size) (hE1 : s.envEntry L = .decl b1 (some F)) (hn1 : b1[n]? = none)
    (h2 : F < s.envs.size) (hE2 : s.envEntry F = .func b2 (some ge) ts tv fo nt) (hn2 : b2[n]? = none)
    (h : ge < s.envs.size) (hE : s.envEntry ge = .global g gb gtv) (hb : gb.contains n = false)
    (hbm : (n ∈ gb) = False) (hgs : g < s.heap.size) (hk : (s.objEntry g).kind.isPlain = true)
    (hp : (s.objEntry g).props.get? (.str n) = some p) (hf : 3 ≤ s.fuel) :
    resolveBinding L n strict s = .ok (.env (some ge) n strict) s := by
  obtain ⟨k, hk1⟩ : ∃ k, s.fuel = k + 3 := ⟨s.fuel - 3, by omega⟩
  rw [resolveBinding_loop, hk1, resolveBody_skip _ L F n strict s b1 h1 hE1 hn1,
    Closure.resolveBody_skip_func _ F ge n strict s b2 ts tv fo nt h2 hE2 hn2]
  simp [M.loop, resolveBody, M.bind_eq, M.bind_apply, hasBinding, readEnv_entry _ _ _ h, hE, hb, hbm,
    Obj'.hasProperty_entry_own _ _ _ hgs hk, hp, pure, M.pure]

/-- **`twice`'s body**, `x` bound in its function record `F` (outer: the global record, where `add` is the
function `fA` on the global object): asks the driver to call `add(x, x)`, and returns what that returns. -/
theorem twice_spec (nn : Nat) (ctx : Ctx) (s : State) (L F ge g fA : Nat) (x : Int) (gb : Std.HashMap JSStr Binding)
    (gtv : Value) (dA : FuncData) (b2 : Std.HashMap JSStr Binding) (ts : ThisStatus) (tv : Value) (fo : ObjId) (nt : Value)
    (hlex : ctx.lex = L) (hstr : ctx.strict = false) (hgen : ctx.isGen = false)
    (h1 : L < s.envs.size) (hE1 : s.envEntry L = .decl ∅ (some F))
    (h2 : F < s.envs.size) (hE2 : s.envEntry F = .func b2 (some ge) ts tv fo nt)
    (hb2 : b2[JSStr.ofString "add"]? = none) (hx : identValue L "x" false s = .ok (num x) s)
    (h : ge < s.envs.size) (hE : s.envEntry ge = .global g gb gtv) (hgb : gb.contains "add" = false)
    (hgb' : gb[JSStr.ofString "add"]? = none) (hgbm : (JSStr.ofString "add" ∈ gb) = False)
    (hgs : g < s.heap.size) (hk : (s.objEntry g).kind = .ordinary)
    (hp : (s.objEntry g).props.get? (.str "add") = some (.data (.obj fA) true true false))
    (hfs : fA < s.heap.size) (hfk : (s.objEntry fA).kind = .func dA) (hf : 4 ≤ s.fuel) :
    ∃ K, TWGen.twice nn ctx s = .req (.call (.obj fA) .undefined #[num x, num x]) s K ∧
      ∀ v t, K (.normal v) t = .ok (.ret v) t := by
  obtain ⟨j, hj⟩ : ∃ j, s.fuel = j + 3 := ⟨s.fuel - 3, by omega⟩
  have hk' : (s.objEntry g).kind.isPlain = true := by rw [hk]; rfl
  have hr := resolveBinding_body_global L F ge "add" false s ∅ b2 ts tv fo nt g gb gtv _ h1 hE1 (by simp) h2 hE2 hb2
    h hE hgb hgbm hgs hk' hp (by omega)
  refine ⟨?K, ?h, ?_⟩
  case h =>
    conv =>
      lhs
      simp [TWGen.twice, Sem.stmts, M.repeatFrom, hj, M.loop, Sem.ret, Sem.inner, Sem.call, Sem.identRef, hlex, hstr,
        hr, getRefValue, getBindingValue, readEnv_entry _ _ _ h, hE, hgb', hgbm, Obj'.hasProperty_entry_own _ _ _ hgs hk',
        hp, getProp, Obj'.get_entry_data _ _ _ _ hgs hk', ownDataValue, isOwnData, refThisValue, Sem.args, Sem.ident, hx,
        isCallable, readObj_entry' _ _ _ hfs, hfk, ES.call, pure, M.pure, M.bind_eq, M.bind_apply, M.bindRes_ok,
        M.bindRes_req, M.loopRes_req, hgen]
  intro v t
  simp [M.pure, pure, M.loopRes_inr, Compl.updateEmpty, hgen]

theorem twice_fdi (f : ObjId) (d : FuncData) (env : EnvId) (s : State) (x : F64) (tv : Value)
    (hcode : d.code = TWGen.twice_func) (henv : env < s.envs.size)
    (hE : s.envEntry env = .func ∅ (some d.env) .initialized tv f .undefined)
    (hf : s.fuel ≠ 0) :
    ∃ ctx s', functionDeclarationInstantiation 999999 f d env #[.num x] s = .ok ctx s' ∧
      s'.envEntry env = .func (Throw.pb1 x) (some d.env) .initialized tv f .undefined ∧
      ctx.lex = s.envs.size ∧ s'.envEntry ctx.lex = .decl ∅ (some env) ∧ ctx.var = env ∧
      ctx.strict = false ∧ ctx.isGen = false ∧ ctx.fn = some f ∧ s'.envs.size = s.envs.size + 1 ∧ s'.fuel = s.fuel ∧
      s'.heap = s.heap ∧ s'.realms = s.realms ∧ (∀ e, e < s.envs.size → e ≠ env → s'.envEntry e = s.envEntry e) := by
  have hr : Array.range 1 = [0].toArray := by decide
  have hbe : ∀ ctx x v b, b.contains x = true →
      bindElement 999998 ctx (.ident x) none (.init (some env)) (M.pure v)
          (s.setEnv env (.func b (some d.env) .initialized tv f .undefined)) =
        .ok () (s.setEnv env (.func (b.modify x fun bd => { bd with value := some v })
          (some d.env) .initialized tv f .undefined)) := by
    intro ctx x v b hb
    have := bindElement_ident 999998 ctx x env v (s.setEnv env (.func b (some d.env) .initialized tv f .undefined))
      (by omega) (by simpa using henv) (by simp [henv]) (by simpa [henv] using hb) (by simpa using hf)
    simpa [henv] using this
  refine ⟨?c, ?t, ?h, ?_⟩
  case h =>
    conv =>
      lhs
      simp only [functionDeclarationInstantiation, hcode]
      simp only [TWGen.twice_func, Func.strict, Func.params, Func.info, Func.body, Func.isAsync]
      simp [hr, hasBinding_declLike, createMutableBinding_declLike, hbe, newDeclEnv, pure,
        M.pure, hE, henv, hf]
  have hne : env ≠ s.envs.size := Nat.ne_of_lt henv
  simp [State.envEntry, State.setEnv, Array.getElem?_push, Array.getElem_push, Array.getElem_modify, henv, hne,
    Throw.pb1]
  intro e he hee
  simp [Nat.ne_of_lt he, Array.getElem?_modify, Ne.symm hee]

/-- **`twice`'s body** as a call runs it (its environment the global record `ge`, `add` the function `fA` on
the global object): runs, through the call of `add`, to `x + x`. -/
theorem twice_body (eng : Engine) (m : Nat) (f : ObjId) (d : FuncData) (env : EnvId) (s : State) (x : Int) (tv : Value)
    (ge g fA : Nat) (gb : Std.HashMap JSStr Binding) (gtv : Value) (dA : FuncData)
    (hcode : d.code = TWGen.twice_func) (henv : env < s.envs.size) (hdenv : d.env = ge)
    (hE : s.envEntry env = .func ∅ (some d.env) .initialized tv f .undefined)
    (hge : ge < s.envs.size) (hgne : ge ≠ env) (hgE : s.envEntry ge = .global g gb gtv)
    (hgb : gb.contains "add" = false) (hgb' : gb[JSStr.ofString "add"]? = none)
    (hgbm : (JSStr.ofString "add" ∈ gb) = False) (hgs : g < s.heap.size) (hk : (s.objEntry g).kind = .ordinary)
    (hp : (s.objEntry g).props.get? (.str "add") = some (.data (.obj fA) true true false))
    (hfs : fA < s.heap.size) (hfk : (s.objEntry fA).kind = .func dA)
    (hcA : dA.code = AddGen.add_func) (hclsA : dA.isClassCtor = false) (hmA : dA.thisMode = .global)
    (hrA : (s.realms[dA.realm]!).globalEnv = ge)
    (hx : x.natAbs < intBound) (hxx : (x + x).natAbs < intBound) (hf : 5 ≤ s.fuel) :
    ∃ t', Runs eng (m + 1) (evalFunctionBody evalDepth f d env #[num x] s) (num (x + x)) t' ∧
      t'.heap = s.heap ∧ t'.realms = s.realms ∧ s.envs.size ≤ t'.envs.size ∧
      (∀ e, e < s.envs.size → e ≠ env → t'.envEntry e = s.envEntry e) ∧ t'.fuel + 1 = s.fuel := by
  obtain ⟨ctx, s1, hfdi, hB, hlex, hL, hvar, hstr, hgen, hfn, hsize, hfuel, hheap, hrl, hfe⟩ :=
    twice_fdi f d env s (ofSmallInt x) tv hcode henv hE (by omega)
  have hl' : ctx.lex < s1.envs.size := by rw [hlex, hsize]; exact Nat.lt_succ_self _
  have he' : env < s1.envs.size := by rw [hsize]; exact Nat.lt_succ_of_lt henv
  have hxv : identValue ctx.lex "x" false s1 = .ok (num x) s1 :=
    identValue_decl_func ctx.lex env "x" false s1 (num x) _ { value := some (num x), deletable := false } _ _ _ _ _
      hl' hL he' hB (by simp [Throw.pb1, Std.HashMap.getElem?_modify]) rfl (by omega)
  have ho1 : ∀ y, s1.objEntry y = s.objEntry y := by intro y; simp [State.objEntry, hheap]
  have hge1 : ge < s1.envs.size := by rw [hsize]; exact Nat.lt_succ_of_lt hge
  have hgE1 : s1.envEntry ge = .global g gb gtv := by rw [hfe ge hge hgne]; exact hgE
  have hBg : s1.envEntry env = .func (Throw.pb1 (ofSmallInt x)) (some ge) .initialized tv f .undefined := by
    rw [hB, hdenv]
  have hpadd : (Throw.pb1 (ofSmallInt x))[JSStr.ofString "add"]? = none := by
    have hxa : (JSStr.ofString "x" = JSStr.ofString "add") = False := by simp; decide
    simp [Throw.pb1, Std.HashMap.getElem?_modify, Std.HashMap.getElem?_insert, hxa]
  obtain ⟨K, hreq, hK⟩ := twice_spec 999973 ctx s1 ctx.lex env ge g fA x gb gtv dA _ .initialized tv f .undefined
    rfl hstr hgen hl' hL he' hBg hpadd hxv hge1 hgE1 hgb hgb' hgbm (by rw [hheap]; exact hgs) (by rw [ho1]; exact hk)
    (by rw [ho1]; exact hp) (by rw [hheap]; exact hfs) (by rw [ho1]; exact hfk) (by omega)
  -- the call of `add`, one level down
  obtain ⟨s1', hs1'⟩ : ∃ y, ({ s1 with fuel := s1.fuel - 1 } : State) = y := ⟨_, rfl⟩
  have hgeA : (s1'.realms[dA.realm]!).globalEnv = ge := by
    rw [← hs1']; show (s1.realms[dA.realm]!).globalEnv = ge; rw [hrl]; exact hrA
  have hz1' : s1'.envs = s1.envs := by rw [← hs1']
  obtain ⟨s2, hc, -, hh2, hr2, hz2, he2, hf2⟩ := AddTwice.add_call fA dA s1' (ofSmallInt x) (ofSmallInt x) g gb gtv
    hcA hclsA hmA (by rw [hgeA, hz1']; exact hge1) (by rw [hgeA]; simp only [State.envEntry, hz1']; exact hgE1)
    (by rw [← hs1']; simp only; omega)
  have hsum : addF (ofSmallInt x) (ofSmallInt x) = ofSmallInt (x + x) := addF_int x x hx hx hxx
  rw [hsum] at hc
  have hdrive : ∀ cs, (drive eng m (callImpl eng (.obj fA) .undefined #[num x, num x] s1) cs).1 = .ok (num (x + x)) s2 :=
    drive_callImpl_ok eng m _ _ _ s1 _ s2 (by
      rw [callImpl_func eng fA dA _ _ s1 (by rw [hheap]; exact hfs) (by rw [ho1]; exact hfk) (by omega), hs1']; exact hc)
  refine ⟨s2, ?_, by rw [hh2, ← hs1']; exact hheap, by rw [hr2, ← hs1']; exact hrl, by rw [← hs1'] at hz2; simp at hz2; omega,
    fun e he hee => by rw [he2 e (by rw [hz1', hsize]; omega)]; simp only [State.envEntry, hz1']; exact hfe e he hee,
    by rw [hf2, ← hs1']; simp only; omega⟩
  have hbd : d.code.body = .stmts TWGen.twice_stmts := by rw [hcode]; rfl
  have hdisp : d.code.info.fdi.usesDispose = false := by rw [hcode]; rfl
  have hbody' : evalStmts (999973 + 26) ctx TWGen.twice_stmts s1 = .req (.call (.obj fA) .undefined #[num x, num x]) s1 K := by
    rw [← congrFun (TWGen.twice_eq 999973) ctx]; exact hreq
  simp only [evalDepth, evalFunctionBody, M.bind_eq, M.bind_apply, hfdi, M.bindRes_ok, hbd, hdisp, withDisposeScope,
    Bool.not_false, ↓reduceIte]
  rw [show (999999 : Nat) = 999973 + 26 from rfl, hbody']
  refine runs_bind eng _ (m + 1) _ (Compl.ret (num (x + x))) s2 ?_ _ _ (Runs.ok _ _ _)
  exact .call m _ _ _ s1 K _ s2 _ s2 hdrive (by rw [hK]; exact Runs.ok _ _ _)

/-- **The [[Call]] of `twice`** (`this` undefined) with an integer `x` (|x|, |x + x| below 2^26): runs, through
its own call of `add`, to `x + x`; the heap, the realms and the caller's environments are as they were. -/
theorem twice_call (eng : Engine) (f : ObjId) (d : FuncData) (s : State) (x : Int) (ge g fA : Nat)
    (gb : Std.HashMap JSStr Binding) (gtv : Value) (dA : FuncData)
    (hcode : d.code = TWGen.twice_func) (hcls : d.isClassCtor = false) (hmode : d.thisMode = .global)
    (hdenv : d.env = ge) (hrd : (s.realms[d.realm]!).globalEnv = ge)
    (hge : ge < s.envs.size) (hgE : s.envEntry ge = .global g gb gtv)
    (hgb : gb.contains "add" = false) (hgb' : gb[JSStr.ofString "add"]? = none)
    (hgbm : (JSStr.ofString "add" ∈ gb) = False) (hgs : g < s.heap.size) (hk : (s.objEntry g).kind = .ordinary)
    (hp : (s.objEntry g).props.get? (.str "add") = some (.data (.obj fA) true true false))
    (hfs : fA < s.heap.size) (hfk : (s.objEntry fA).kind = .func dA)
    (hcA : dA.code = AddGen.add_func) (hclsA : dA.isClassCtor = false) (hmA : dA.thisMode = .global)
    (hrA : (s.realms[dA.realm]!).globalEnv = ge)
    (hx : x.natAbs < intBound) (hxx : (x + x).natAbs < intBound) (hf : 5 ≤ s.fuel) :
    ∃ s', Runs eng 3999 (callECMA f d .undefined #[num x] s) (num (x + x)) s' ∧ s'.realm = s.realm ∧
      s'.heap = s.heap ∧ s'.realms = s.realms ∧ s.envs.size ≤ s'.envs.size ∧
      (∀ e, e < s.envs.size → s'.envEntry e = s.envEntry e) ∧ s'.fuel + 1 = s.fuel := by
  obtain ⟨s', h1, h2, -, t', ⟨q1, q2, q3, q4, q5⟩, hh, hen, hfe, hrs⟩ := callECMA_undef_runs eng 3999
    (Q := fun t => t.heap = s.heap ∧ t.realms = s.realms ∧ s.envs.size ≤ t.envs.size ∧
      (∀ e, e < s.envs.size → t.envEntry e = s.envEntry e) ∧ t.fuel + 1 = s.fuel)
    f d s #[num x] (num (x + x)) g gb gtv hcls hmode (by rw [hcode]; rfl) (by rw [hcode]; rfl) (by rw [hrd]; exact hge)
    (by rw [hrd]; exact hgE)
    (fun t hlt hEt hold hheap hfu hrl _ => by
      have ho : ∀ y, t.objEntry y = s.objEntry y := by intro y; simp [State.objEntry, hheap]
      obtain ⟨t', hb, hh', hr', hz', hfe', hfu'⟩ := twice_body eng 3998 f d s.envs.size t x gtv ge g fA gb gtv dA hcode hlt
        hdenv hEt (Nat.lt_trans hge hlt) (Nat.ne_of_lt hge) (by rw [hold ge hge]; exact hgE) hgb hgb' hgbm
        (by rw [hheap]; exact hgs) (by rw [ho]; exact hk) (by rw [ho]; exact hp) (by rw [hheap]; exact hfs)
        (by rw [ho]; exact hfk) hcA hclsA hmA (by rw [hrl]; exact hrA) hx hxx (by omega)
      exact ⟨t', hb, hh'.trans hheap, hr'.trans hrl, by omega,
        fun e he => (hfe' e (Nat.lt_trans he hlt) (Nat.ne_of_lt he)).trans (hold e he), by omega⟩)
  exact ⟨s', h1, h2, hh.trans q1, hrs.trans q2, by rw [hen]; exact q3,
    fun e he => by simp only [State.envEntry, hen]; exact q4 e he, by rw [hfe]; exact q5⟩

/-! ## The whole script -/

open Script

abbrev l21 : F64 := F64.fin false 5910974510923776 (-48)
theorem l21_eq : l21 = ofSmallInt 21 := by decide
abbrev callTwice : Sem.CStmt := Sem.exprStmt (Sem.call (Sem.identRef "twice")
  (Sem.args #[Sem.ArgD.expr (Sem.lit (Lit.num l21))]) false (CalleeDesc.ident "twice"))

theorem script_def (n : Nat) : TWGen.script n = Sem.stmts #[Sem.funDecl TWGen.add_func, Sem.funDecl TWGen.twice_func,
    callTwice] := rfl
theorem lexScoped : topLevelLexicallyScoped TWGen.script_stmts = #[] := by
  simp [topLevelLexicallyScoped, stmtLexScoped, TWGen.script_stmts]
theorem simple_add : Inst.SimpleFn TWGen.add_func "add" := ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem simple_twice : Inst.SimpleFn TWGen.twice_func "twice" := ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem add_same : TWGen.add_func = AddGen.add_func := rfl

def fs : List (Func × JSStr) := [(TWGen.add_func, "add"), (TWGen.twice_func, "twice")]

/-- **The whole program** (examples/twice.js): `twice(21)` calls `add(21, 21)` inside its body; the script
evaluates to 42. Started from a realm whose global object is an ordinary extensible object without `add` or
`twice`. -/
theorem tw_script (eng : Engine) (s : State) (cs : Conts) (gb : Std.HashMap JSStr Binding) (gtv : Value)
    (fp : ObjId) (hge : s.curRealm.globalEnv < s.envs.size)
    (hE : s.envEntry s.curRealm.globalEnv = .global s.curRealm.globalObj gb gtv)
    (hgba : gb.contains "add" = false) (hgbt : gb.contains "twice" = false)
    (hgs : s.curRealm.globalObj < s.heap.size) (hk : (s.objEntry s.curRealm.globalObj).kind = .ordinary)
    (hx : (s.objEntry s.curRealm.globalObj).extensible = true)
    (hpa : (s.objEntry s.curRealm.globalObj).props.get? (.str "add") = none)
    (hpt : (s.objEntry s.curRealm.globalObj).props.get? (.str "twice") = none)
    (hfp : s.curRealm.intrinsics["%Function.prototype%"]? = some fp) (hf : 20 ≤ s.fuel) :
    ∃ s', (runM eng (scriptEvaluation TWGen.program) s cs).1 = .ok (num 42) s' := by
  let ge := s.curRealm.globalEnv
  let g := s.curRealm.globalObj
  let c := scriptCtx s false
  -- the declarations
  obtain ⟨t0, ht0⟩ : ∃ y, (scriptStart s TWGen.program).setEnv ge (.global g (insertLets gb []) gtv) = y := ⟨_, rfl⟩
  have ho0 : ∀ y, t0.objEntry y = s.objEntry y := by intro y; rw [← ht0, State.setEnv_objEntry]; rfl
  have hz0 : t0.heap.size = s.heap.size := by rw [← ht0, State.setEnv_heap_size]; rfl
  have hge0 : ge < t0.envs.size := by rw [← ht0, State.setEnv_envs_size]; exact hge
  have hgood : GoodG g fp t0 := ⟨by rw [hz0]; exact hgs, by rw [ho0]; exact hk, by rw [ho0]; exact hx,
    by rw [← ht0, State.setEnv_curRealm]; exact hfp⟩
  obtain ⟨⟨-, hku, -, -⟩, heu, hfuu, hru, -, hszu, -, -, -, hnames, hfuns⟩ :=
    instAll_facts ge g s.scripts.size fp fs t0 hgood (by decide)
  obtain ⟨u, hu⟩ : ∃ y, instAll ge g s.scripts.size fp fs t0 = y := ⟨_, rfl⟩
  rw [hu] at hku heu hfuu hru hszu hnames hfuns
  have hfu0 : t0.fuel = s.fuel := by rw [← ht0, State.setEnv_fuel]; rfl
  have hrl0 : t0.realm = s.realm := by rw [← ht0, State.setEnv_realm]; rfl
  have hr0 : t0.realms = s.realms := by rw [← ht0, State.setEnv_realms]; rfl
  let fA := s.heap.size
  let fT := s.heap.size + 2
  obtain ⟨dA, hfAk, hcA, hrA, hmA, hclsA, -, -⟩ := hfuns 0 (by decide)
  obtain ⟨dT, hfTk, hcT, hrT, hmT, hclsT, -, hdT⟩ := hfuns 1 (by decide)
  rw [hz0] at hfAk hfTk hszu hnames
  simp only [fs, List.length_cons, List.length_nil] at hszu
  simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one] at hfAk hfTk
  have hpA : (u.objEntry g).props.get? (.str "add") = some (.data (.obj fA) true true false) := hnames 0 (by decide)
  have hpT : (u.objEntry g).props.get? (.str "twice") = some (.data (.obj fT) true true false) := hnames 1 (by decide)
  have hE1 : u.envEntry ge = .global g gb gtv := by
    have h1 : u.envEntry ge = t0.envEntry ge := by simp only [State.envEntry, heu]
    rw [h1, ← ht0, State.setEnv_envEntry_self _ _ _ (show ge < (scriptStart s TWGen.program).envs.size from hge)]
    simp [insertLets]
  have hgeu : ge < u.envs.size := by rw [heu]; exact hge0
  have hgu : g < u.heap.size := by rw [hszu]; exact Nat.lt_of_lt_of_le hgs (Nat.le_add_right _ _)
  have hfAu : fA < u.heap.size := by show s.heap.size < u.heap.size; rw [hszu]; omega
  have hfTu : fT < u.heap.size := by show s.heap.size + 2 < u.heap.size; rw [hszu]; omega
  have hgba' : gb[JSStr.ofString "add"]? = none := Std.HashMap.getElem?_eq_none (fun hm => by
    rw [Std.HashMap.mem_iff_contains, hgba] at hm; exact Bool.false_ne_true hm)
  have hgbt' : gb[JSStr.ofString "twice"]? = none := Std.HashMap.getElem?_eq_none (fun hm => by
    rw [Std.HashMap.mem_iff_contains, hgbt] at hm; exact Bool.false_ne_true hm)
  have hgbam : (JSStr.ofString "add" ∈ gb) = False := by simp [Std.HashMap.mem_iff_contains, hgba]
  have hgbtm : (JSStr.ofString "twice" ∈ gb) = False := by simp [Std.HashMap.mem_iff_contains, hgbt]
  -- `twice(21)` asks for its call
  obtain ⟨K0, h0, hK0⟩ := Stmts.call_expr_req (Sem.inner c) u ge g fT "twice" gb gtv dT [(Sem.lit (Lit.num l21), .num l21)]
    (by intro p hp; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp; rcases hp with rfl; rfl)
    rfl rfl hgeu hE1 hgbt hgbt' hgbtm hgu hku hpT hfTu hfTk (by rw [hfuu, hfu0]; omega)
  obtain ⟨K4, h4, hK4⟩ := Stmts.exprStmt_req _ c u _ K0 h0 hK0
  -- the call of `twice`, which calls `add` (one level deeper)
  obtain ⟨u', hu'⟩ : ∃ y, ({ u with fuel := u.fuel - 1 } : State) = y := ⟨_, rfl⟩
  have hr' : u'.realms = s.realms := by rw [← hu']; exact hru.trans hr0
  have hreal : ∀ d : FuncData, d.realm = t0.realm → (u'.realms[d.realm]!).globalEnv = ge := by
    intro d hd; rw [hr', hd, hrl0]; rfl
  have hz' : u'.envs = u.envs := by rw [← hu']
  have hou : ∀ y, u'.objEntry y = u.objEntry y := fun y => by rw [← hu']; rfl
  obtain ⟨s4, hrun, -⟩ := twice_call eng fT dT u' 21 ge g fA gb gtv dA hcT hclsT hmT hdT (hreal dT hrT)
    (by rw [hz']; exact hgeu) (by simp only [State.envEntry, hz']; exact hE1) hgba hgba' hgbam
    (by rw [← hu']; exact hgu) (by rw [hou]; exact hku) (by rw [hou]; exact hpA) (by rw [← hu']; exact hfAu)
    (by rw [hou]; exact hfAk) (hcA.trans add_same) hclsA hmA (hreal dA hrA) (by decide) (by decide)
    (by rw [← hu']; simp only; rw [hfuu, hfu0]; omega)
  have hnest : ∀ cs, (drive eng 3999 (callImpl eng (.obj fT) .undefined #[.num l21] u) cs).1 = .ok (num 42) s4 := by
    intro cs
    rw [l21_eq, callImpl_func eng fT dT _ _ u hfTu hfTk (by rw [hfuu, hfu0]; omega), hu']
    exact drive_of_runs eng 3999 _ _ _ hrun cs
  -- the script
  refine ⟨s4, script_value eng s cs TWGen.program fs [] gb gtv fp _ s4 rfl rfl
    (by rw [show TWGen.program.body = TWGen.script_stmts from rfl, lexScoped]; rfl) rfl
    (by intro p hp; simp only [fs, List.mem_cons, List.mem_nil_iff, or_false] at hp
        rcases hp with rfl | rfl
        · exact simple_add
        · exact simple_twice)
    (by decide) hge hE
    (by intro p hp; simp only [fs, List.mem_cons, List.mem_nil_iff, or_false] at hp; rcases hp with rfl | rfl <;> assumption)
    (by simp) hgs hk hx
    (by intro p hp; simp only [fs, List.mem_cons, List.mem_nil_iff, or_false] at hp; rcases hp with rfl | rfl <;> assumption)
    (by simp) hfp ?_⟩
  have hu0 : scriptState s TWGen.program fs [] gb gtv fp = u := by rw [← hu, ← ht0]; rfl
  have hscript : evalStmts evalDepth (scriptCtx s false) TWGen.program.body u = TWGen.script 999965 c u := by
    rw [TWGen.script_eq]; rfl
  have h4' : callTwice c u = .req (.call (.obj fT) .undefined #[.num l21]) u K4 := h4
  rw [hu0, hscript, script_def]
  refine _root_.Runs.script_runs eng _ _ _ (_root_.Runs.stmts_run eng c _ u _ s4 ?_ (by simp; rw [hfuu, hfu0]; omega))
  show _root_.Runs.StmtsRun eng c [Sem.funDecl TWGen.add_func, Sem.funDecl TWGen.twice_func, callTwice] u none
    (some (num 42)) s4
  refine .cons _ _ u u s4 none none _ (_root_.Runs.runs_funDecl eng _ c u rfl) ?_
  refine .cons _ _ u u s4 none none _ (_root_.Runs.runs_funDecl eng _ c u rfl) ?_
  refine .cons _ _ u s4 s4 (some (num 42)) none _ ?_ (.nil _ _)
  rw [h4']
  exact runsTo_call_nested eng _ _ _ u K4 _ s4 _ s4 hnest (by rw [hK4]; exact _root_.Runs.runsTo_ok eng _ _)

end Nested
