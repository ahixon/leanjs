import JSProofs.SumCall

/-!
# Plain calls `g(args)` (`this` undefined) of sloppy ECMAScript functions

`callECMA` makes a fresh function environment, binds `this` to the global environment's this value,
and runs the body in the callee's realm and script. If the body returns `v` from any such state
(heap and existing environments unchanged, the new function environment fresh), the call returns `v`.
-/

open ES

namespace Calls

theorem callECMA_undef {Q : State → Prop} (f : ObjId) (d : FuncData) (s : State) (args : Array Value) (v : Value)
    (go : ObjId) (gb : Std.HashMap JSStr Binding) (gtv : Value)
    (hcls : d.isClassCtor = false) (hmode : d.thisMode = .global) (hasync : d.code.isAsync = false)
    (hgen : d.code.isGenerator = false)
    (hge : (s.realms[d.realm]!).globalEnv < s.envs.size)
    (hgE : s.envEntry (s.realms[d.realm]!).globalEnv = .global go gb gtv)
    (hbody : ∀ t : State, s.envs.size < t.envs.size →
      t.envEntry s.envs.size = .func ∅ (some d.env) .initialized gtv f .undefined →
      (∀ e, e < s.envs.size → t.envEntry e = s.envEntry e) → t.heap = s.heap → t.fuel = s.fuel → t.realms = s.realms → t.realm = d.realm →
      ∃ t', evalFunctionBody evalDepth f d s.envs.size args t = .ok v t' ∧ Q t') :
    ∃ s', callECMA f d .undefined args s = .ok v s' ∧ s'.realm = s.realm ∧ s'.script = s.script ∧
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
  obtain ⟨s4, hb, hQ⟩ : ∃ t', evalFunctionBody evalDepth f d env args s3 = .ok v t' ∧ Q t' :=
    hbody s3 henv3 hE3 hold (by simp [s3, s2, s1, State.setEnv]) (by simp [s3, s2, s1]) (by simp [s3, s2, s1]) (by simp [s3, s2, s1])
  refine ⟨{ s4 with realm := s.realm, script := s.script }, ?_, rfl, rfl, s4, hQ, rfl, rfl, rfl, rfl⟩
  simp only [callECMA, hcls, inCallee, M.bind_eq, M.bind_apply, M.readS_apply, M.bindRes_ok, M.modify_apply]
  simp [M.bind_apply, hnew, hbind, hasync, hgen, hb, M.attempt, M.tryCatch_apply, pure, M.pure, s1]

/-- A plain call whose body throws `e`: the call throws `e` (the caller's realm and script restored). -/
theorem callECMA_undef_err {Q : State → Prop} (f : ObjId) (d : FuncData) (s : State) (args : Array Value) (v : Value)
    (go : ObjId) (gb : Std.HashMap JSStr Binding) (gtv : Value)
    (hcls : d.isClassCtor = false) (hmode : d.thisMode = .global) (hasync : d.code.isAsync = false)
    (hgen : d.code.isGenerator = false)
    (hge : (s.realms[d.realm]!).globalEnv < s.envs.size)
    (hgE : s.envEntry (s.realms[d.realm]!).globalEnv = .global go gb gtv)
    (hbody : ∀ t : State, s.envs.size < t.envs.size →
      t.envEntry s.envs.size = .func ∅ (some d.env) .initialized gtv f .undefined →
      (∀ e, e < s.envs.size → t.envEntry e = s.envEntry e) → t.heap = s.heap → t.fuel = s.fuel → t.realms = s.realms → t.realm = d.realm →
      ∃ t', evalFunctionBody evalDepth f d s.envs.size args t = .err v t' ∧ Q t') :
    ∃ s', callECMA f d .undefined args s = .err v s' ∧ s'.realm = s.realm ∧ s'.script = s.script ∧
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
  obtain ⟨s4, hb, hQ⟩ : ∃ t', evalFunctionBody evalDepth f d env args s3 = .err v t' ∧ Q t' :=
    hbody s3 henv3 hE3 hold (by simp [s3, s2, s1, State.setEnv]) (by simp [s3, s2, s1]) (by simp [s3, s2, s1]) (by simp [s3, s2, s1])
  refine ⟨{ s4 with realm := s.realm, script := s.script }, ?_, rfl, rfl, s4, hQ, rfl, rfl, rfl, rfl⟩
  simp only [callECMA, hcls, inCallee, M.bind_eq, M.bind_apply, M.readS_apply, M.bindRes_ok, M.modify_apply]
  simp [M.bind_apply, hnew, hbind, hasync, hgen, hb, M.attempt, M.tryCatch_apply, pure, M.pure, s1, M.throwV]

/-- A call `o.m(args)` (this an object `O`) of a sloppy function: as `callECMA_undef`, with `this = O`. -/
theorem callECMA_obj {Q : State → Prop} (f : ObjId) (d : FuncData) (s : State) (args : Array Value) (v : Value)
    (O : ObjId)
    (hcls : d.isClassCtor = false) (hmode : d.thisMode = .global) (hasync : d.code.isAsync = false)
    (hgen : d.code.isGenerator = false)
    (hbody : ∀ t : State, s.envs.size < t.envs.size →
      t.envEntry s.envs.size = .func ∅ (some d.env) .initialized (.obj O) f .undefined →
      (∀ e, e < s.envs.size → t.envEntry e = s.envEntry e) → t.heap = s.heap → t.fuel = s.fuel → t.realms = s.realms → t.realm = d.realm →
      ∃ t', evalFunctionBody evalDepth f d s.envs.size args t = .ok v t' ∧ Q t') :
    ∃ s', callECMA f d (.obj O) args s = .ok v s' ∧ s'.realm = s.realm ∧ s'.script = s.script ∧
      ∃ t', Q t' ∧ s'.heap = t'.heap ∧ s'.envs = t'.envs ∧ s'.fuel = t'.fuel ∧ s'.realms = t'.realms := by
  let s1 : State := { s with realm := d.realm, script := d.script }
  let env := s.envs.size
  let E0 : Env := .func {} (some d.env) .uninitialized .undefined f .undefined
  let s2 : State := { s1 with envs := s1.envs.push E0 }
  let s3 := s2.setEnv env (.func {} (some d.env) .initialized (.obj O) f .undefined)
  have hgl : (ThisMode.global == ThisMode.lexical) = false := by decide
  have hgs : (ThisMode.global == ThisMode.strict) = false := by decide
  have hnew : newFunctionEnv f d .undefined s1 = .ok env s2 := by
    simp [hgl, newFunctionEnv, hmode, s2, s1, E0, env]
  have henv2 : env < s2.envs.size := by simp [s2, s1, env]
  have hbind : ordinaryCallBindThis d env (.obj O) s2 = .ok () s3 := by
    simp only [ordinaryCallBindThis, hmode]
    have hnn : (Value.obj O).isNullish = false := rfl
    have hui : (ThisStatus.uninitialized == ThisStatus.initialized) = false := by decide
    simp [hgl, hgs, hnn, hui, M.bind_eq, M.bind_apply, bindThisValue, readEnv_entry _ _ _ henv2, pure, M.pure,
      modifyEnv_eq_setEnv _ _ _ henv2, s3, toObject]
    simp [hui, State.envEntry, s2, s1, E0, env, modifyEnv, State.setEnv]
  have henv3 : env < s3.envs.size := by simp [s3, s2, s1, env]
  have hE3 : s3.envEntry env = .func ∅ (some d.env) .initialized (.obj O) f .undefined := by
    simp [s3, henv2]
  have hold : ∀ e, e < s.envs.size → s3.envEntry e = s.envEntry e := by
    intro e he
    have hne : env ≠ e := Nat.ne_of_gt he
    rw [State.setEnv_envEntry_ne _ _ _ _ hne]
    simp [State.envEntry, s2, s1, Array.getElem?_push, Nat.ne_of_lt he]
  obtain ⟨s4, hb, hQ⟩ : ∃ t', evalFunctionBody evalDepth f d env args s3 = .ok v t' ∧ Q t' :=
    hbody s3 henv3 hE3 hold (by simp [s3, s2, s1, State.setEnv]) (by simp [s3, s2, s1]) (by simp [s3, s2, s1]) (by simp [s3, s2, s1])
  refine ⟨{ s4 with realm := s.realm, script := s.script }, ?_, rfl, rfl, s4, hQ, rfl, rfl, rfl, rfl⟩
  simp only [callECMA, hcls, inCallee, M.bind_eq, M.bind_apply, M.readS_apply, M.bindRes_ok, M.modify_apply]
  simp [M.bind_apply, hnew, hbind, hasync, hgen, hb, M.attempt, M.tryCatch_apply, pure, M.pure, s1]

end Calls
