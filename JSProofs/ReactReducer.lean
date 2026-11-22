import JSProofs.JsTactic
import JSProofs.Builtins
import JSProofs.ArrayLit
import JSProofs.URIGen

/-!
# React's `updateReducerImpl` for a click (zippy docs/react-proofs.md)

The counter's `useState` in the click's re-render: the hook's queue holds the click's one update (lane 2, no revert
lane, its state computed eagerly by `dispatchSetState`), circular; nothing in the base queue. The update moves to
the current hook's base queue, is processed (the render lanes include its lane), and the new state, which differs
from the old one, becomes the hook's state: `didReceiveUpdate` is set and `[state, dispatch]` returned.
-/

open ES ES.M HostRuns Logic
open Std (HashMap)

namespace ReactReducer

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ}

/-- **`Object.is(x, y)`**, exactly: nothing changes but one step of fuel. -/
theorem objectIs_exact {n : Nat} {h : σ} {fo : ObjId} {bd : BuiltinData} {t x y : Value} {s : State}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .builtin bd)
    (hfn : eng.builtins[bd.id]? = some objectIs) (hf : s.fuel ≠ 0) :
    WP eng answer n h (callImpl eng (.obj fo) t #[x, y]) s fun v w h' =>
      v = .bool (sameValue x y) ∧ w = s.withFuel (s.fuel - 1) ∧ h' = h := by
  rw [wp_iff_wpr, callImpl_builtin eng fo bd objectIs t _ s hlt hk hfn hf, ← wp_iff_wpr]
  apply wp_inCallee
  exact wp_of_eq rfl ⟨rfl, rfl, rfl⟩

theorem realm_setProp (s : State) (o : ObjId) (k : PropKey) (p : Property) : (s.setProp o k p).realm = s.realm := rfl
theorem realm_setEnv (s : State) (e : EnvId) (ev : Env) : (s.setEnv e ev).realm = s.realm := rfl
theorem realm_withFuel (s : State) (f : Nat) : (s.withFuel f).realm = s.realm := rfl
theorem realm_bodyState (s : State) (fo : ObjId) (d : FuncData) (t : Value) (args : Array Value) :
    (bodyState s fo d t args).realm = d.realm := rfl

theorem realms_setProp (s : State) (o : ObjId) (k : PropKey) (p : Property) : (s.setProp o k p).realms = s.realms := rfl
theorem realms_setEnv (s : State) (e : EnvId) (ev : Env) : (s.setEnv e ev).realms = s.realms := rfl
theorem realms_withFuel (s : State) (f : Nat) : (s.withFuel f).realms = s.realms := rfl
theorem realms_bodyState (s : State) (fo : ObjId) (d : FuncData) (t : Value) (args : Array Value) :
    (bodyState s fo d t args).realms = s.realms := rfl

theorem simpleR (d : FuncData) (hc : d.code = URIGen.updateReducerImpl_func) : FDI.Simple d := by
  constructor <;> rw [hc] <;> try rfl
  simp [URIGen.updateReducerImpl_func, Func.params, Func.info]

/-- The number 2 (`SyncLane`). -/
abbrev two : Value := .num (F64.fin false 4503599627370496 (-51))
/-- The number 0. -/
abbrev zero : Value := .num (F64.fin false 0 (-1074))

/-- What it writes (besides the new array): `didReceiveUpdate`, the hook's state and queues, the current hook's
base queue, the update queue's pending list and last rendered reducer and state. -/
def fpR (g : EnvId) (H H0 Q : ObjId) : Footprint :=
  ⟨[(g, "didReceiveUpdate")], [(H, .str "memoizedState"), (H, .str "baseState"), (H, .str "baseQueue"),
    (H0, .str "baseQueue"), (Q, .str "pending"), (Q, .str "lastRenderedReducer"), (Q, .str "lastRenderedState")],
    false⟩

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
set_option maxHeartbeats 1000000 in
set_option maxRecDepth 20000 in
/-- **`updateReducerImpl(hook, current, reducer)`** for the click's update. -/
theorem click_spec {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t : Value} {s : State}
    {bG : HashMap JSStr Binding} {oG : Option EnvId} {bdRL bdCE bdSD bdDR bdIs : Binding} {bdIsb : BuiltinData}
    {fIs H H0 Q U : ObjId} {r ms bs a vE dv : Value}
    {hq hb hm hs h0b qp qr ql qd ul ur ua ue uv un : Bool × Bool × Bool}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : 60 ≤ s.fuel)
    (hcode : d.code = URIGen.updateReducerImpl_func) (hcls : d.isClassCtor = false)
    (hmode : d.thisMode = .strict)
    (hG : d.env < s.envs.size) (hGe : Scope.declLike? (s.envEntry d.env) = some (bG, oG))
    (hGRL : bG[JSStr.ofString "renderLanes"]? = some bdRL) (hGRLv : bdRL.value = some two)
    (hGCE : bG[JSStr.ofString "currentEntangledLane"]? = some bdCE) (hGCEv : bdCE.value = some zero)
    (hGSD : bG[JSStr.ofString "shouldDoubleInvokeUserFnsInHooksDEV"]? = some bdSD)
    (hGSDv : bdSD.value = some (.bool false))
    (hGDR : bG[JSStr.ofString "didReceiveUpdate"]? = some bdDR) (hGDRm : bdDR.mutable = true)
    (hGDRi : bdDR.value.isSome = true)
    (hGIs : bG[JSStr.ofString "objectIs"]? = some bdIs) (hGIsv : bdIs.value = some (.obj fIs))
    (hIs : fIs < s.heap.size) (hIsk : (s.objEntry fIs).kind = .builtin bdIsb)
    (hIstab : eng.builtins[bdIsb.id]? = some objectIs)
    (hH : H < s.heap.size) (hHk : (s.objEntry H).kind.isPlain = true)
    (hHq : (s.objEntry H).props.get? (.str "queue") = some (.data (.obj Q) hq.1 hq.2.1 hq.2.2))
    (hHb : (s.objEntry H).props.get? (.str "baseQueue") = some (.data .null true hb.2.1 hb.2.2))
    (hHm : (s.objEntry H).props.get? (.str "memoizedState") = some (.data ms true hm.2.1 hm.2.2))
    (hHs : (s.objEntry H).props.get? (.str "baseState") = some (.data bs true hs.2.1 hs.2.2))
    (hH0 : H0 < s.heap.size) (hH0k : (s.objEntry H0).kind.isPlain = true)
    (hH0b : (s.objEntry H0).props.get? (.str "baseQueue") = some (.data .null true h0b.2.1 h0b.2.2))
    (hQ : Q < s.heap.size) (hQk : (s.objEntry Q).kind.isPlain = true)
    (hQp : (s.objEntry Q).props.get? (.str "pending") = some (.data (.obj U) true qp.2.1 qp.2.2))
    (hQr : (s.objEntry Q).props.get? (.str "lastRenderedReducer") = some (.data r true qr.2.1 qr.2.2))
    (hQl : (s.objEntry Q).props.get? (.str "lastRenderedState") = some (.data ms true ql.2.1 ql.2.2))
    (hQd : (s.objEntry Q).props.get? (.str "dispatch") = some (.data dv qd.1 qd.2.1 qd.2.2))
    (hU : U < s.heap.size) (hUk : (s.objEntry U).kind.isPlain = true)
    (hUl : (s.objEntry U).props.get? (.str "lane") = some (.data two ul.1 ul.2.1 ul.2.2))
    (hUr : (s.objEntry U).props.get? (.str "revertLane") = some (.data zero ur.1 ur.2.1 ur.2.2))
    (hUa : (s.objEntry U).props.get? (.str "action") = some (.data a ua.1 ua.2.1 ua.2.2))
    (hUe : (s.objEntry U).props.get? (.str "hasEagerState") = some (.data (.bool true) ue.1 ue.2.1 ue.2.2))
    (hUv : (s.objEntry U).props.get? (.str "eagerState") = some (.data vE uv.1 uv.2.1 uv.2.2))
    (hUn : (s.objEntry U).props.get? (.str "next") = some (.data (.obj U) un.1 un.2.1 un.2.2))
    (hdiff : sameValue vE ms = false)
    (d1 : H ≠ H0) (d2 : H ≠ Q) (d3 : H ≠ U) (d4 : H0 ≠ Q) (d5 : H0 ≠ U) (d6 : Q ≠ U)
    (d7 : fIs ≠ H) (d8 : fIs ≠ H0) (d9 : fIs ≠ Q) (d10 : fIs ≠ U) :
    WP eng answer (n + 1) h (callImpl eng (.obj fo) t #[.obj H, .obj H0, r]) s fun v w h' =>
      v = .obj s.heap.size ∧ Frame (fpR d.env H H0 Q) s w ∧ s.fuel ≤ w.fuel + 60 ∧ h' = h ∧
      ArrayObj s.heap.size 2 (fun j => if j = 1 then dv else if j = 0 then vE else .undefined) w ∧
      (w.objEntry s.heap.size).proto = .obj s.realms[d.realm]!.arrayProto ∧
      (w.objEntry s.heap.size).props.get? (.sym WK.iterator) = none ∧
      Scope.declLike? (w.envEntry d.env) = some (bG.modify (JSStr.ofString "didReceiveUpdate")
        (fun bd => { bd with value := some (.bool true) }), oG) ∧
      (w.objEntry H).props.get? (.str "memoizedState") = some (.data vE true hm.2.1 hm.2.2) ∧
      (w.objEntry H).props.get? (.str "baseState") = some (.data vE true hs.2.1 hs.2.2) ∧
      (w.objEntry H).props.get? (.str "baseQueue") = some (.data .null true hb.2.1 hb.2.2) ∧
      (w.objEntry H0).props.get? (.str "baseQueue") = some (.data (.obj U) true h0b.2.1 h0b.2.2) ∧
      (w.objEntry Q).props.get? (.str "pending") = some (.data .null true qp.2.1 qp.2.2) ∧
      (w.objEntry Q).props.get? (.str "lastRenderedReducer") = some (.data r true qr.2.1 qr.2.2) ∧
      (w.objEntry Q).props.get? (.str "lastRenderedState") = some (.data vE true ql.2.1 ql.2.2) := by
  apply wp_callGen URIGen.updateReducerImpl_eq (by decide) hlt hk (by omega) hcls hmode
    (by rw [hcode]; rfl) (by rw [hcode]; rfl) (simpleR d hcode) (by rw [hcode]; rfl) (by rw [hcode]; rfl)
  have hpn : d.code.info.fdi.paramNames = #[JSStr.ofString "hook", JSStr.ofString "current", JSStr.ofString "reducer"] := by
    rw [hcode]; rfl
  have hv : d.code.info.fdi.varNames = #[JSStr.ofString "queue", JSStr.ofString "baseQueue",
      JSStr.ofString "pendingQueue", JSStr.ofString "baseFirst", JSStr.ofString "newBaseQueueFirst",
      JSStr.ofString "newBaseQueueLast", JSStr.ofString "update", JSStr.ofString "didReadFromEntangledAsyncAction$64",
      JSStr.ofString "updateLane", JSStr.ofString "revertLane"] := by
    rw [hcode]; rfl
  have hl : FDI.lexDecls d = #[] := by simp [FDI.lexDecls, hcode, URIGen.updateReducerImpl_func, Func.info]
  have ha : d.code.isAsync = false := by rw [hcode]; rfl
  have hne : s.envs.size ≠ d.env := Nat.ne_of_gt hG
  have hG1 : d.env < s.envs.size + 1 := Nat.lt_succ_of_lt hG
  clear hcode
  simp only [URIGen.updateReducerImpl]
  js [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGRL, hGRLv, hGCE, hGCEv, hGSD, hGSDv, hGDR, hGDRm, hGDRi, hGIs, hGIsv, hIs, hIsk, hH, hHk, hHq, hHb, hHm, hHs, hH0, hH0k, hH0b, hQ, hQk, hQp, hQr, hQl, hQd, hU, hUk, hUl, hUr, hUa, hUe, hUv, hUn, hdiff, d1, d2, d3, d4, d5, d6, Ne.symm d1, Ne.symm d2, Ne.symm d3, Ne.symm d4, Ne.symm d5, Ne.symm d6, d7, d8, d9, d10, Ne.symm d7, Ne.symm d8, Ne.symm d9, Ne.symm d10, beq_self_eq_true, FDI.fdiCtx, Sem.inner]
  refine ⟨by js_norm [CallableC, hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGRL, hGRLv, hGCE, hGCEv, hGSD, hGSDv, hGDR, hGDRm, hGDRi, hGIs, hGIsv, hIs, hIsk, hH, hHk, hHq, hHb, hHm, hHs, hH0, hH0k, hH0b, hQ, hQk, hQp, hQr, hQl, hQd, hU, hUk, hUl, hUr, hUa, hUe, hUv, hUn, hdiff, d1, d2, d3, d4, d5, d6, Ne.symm d1, Ne.symm d2, Ne.symm d3, Ne.symm d4, Ne.symm d5, Ne.symm d6, d7, d8, d9, d10, Ne.symm d7, Ne.symm d8, Ne.symm d9, Ne.symm d10, beq_self_eq_true, FDI.fdiCtx, Sem.inner], ?_⟩
  refine wp_mono (objectIs_exact ?_ ?_ hIstab ?_) ?post
  all_goals first | (js_norm [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGRL, hGRLv, hGCE, hGCEv, hGSD, hGSDv, hGDR, hGDRm, hGDRi, hGIs, hGIsv, hIs, hIsk, hH, hHk, hHq, hHb, hHm, hHs, hH0, hH0k, hH0b, hQ, hQk, hQp, hQr, hQl, hQd, hU, hUk, hUl, hUr, hUa, hUe, hUv, hUn, hdiff, d1, d2, d3, d4, d5, d6, Ne.symm d1, Ne.symm d2, Ne.symm d3, Ne.symm d4, Ne.symm d5, Ne.symm d6, d7, d8, d9, d10, Ne.symm d7, Ne.symm d8, Ne.symm d9, Ne.symm d10, beq_self_eq_true, FDI.fdiCtx, Sem.inner]; done) | js_side | skip
  case post =>
  intro b w4 h4 ⟨hb, hw4, hh4⟩
  subst b w4 h4
  js [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGRL, hGRLv, hGCE, hGCEv, hGSD, hGSDv, hGDR, hGDRm, hGDRi, hGIs, hGIsv, hIs, hIsk, hH, hHk, hHq, hHb, hHm, hHs, hH0, hH0k, hH0b, hQ, hQk, hQp, hQr, hQl, hQd, hU, hUk, hUl, hUr, hUa, hUe, hUv, hUn, hdiff, d1, d2, d3, d4, d5, d6, Ne.symm d1, Ne.symm d2, Ne.symm d3, Ne.symm d4, Ne.symm d5, Ne.symm d6, d7, d8, d9, d10, Ne.symm d7, Ne.symm d8, Ne.symm d9, Ne.symm d10, beq_self_eq_true, FDI.fdiCtx, Sem.inner]

  refine wp_array2 (v1 := vE) (v2 := dv) ?e1 ?e2 ?fin
  case e1 =>
    js [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGRL, hGRLv, hGCE, hGCEv, hGSD, hGSDv, hGDR, hGDRm, hGDRi, hGIs, hGIsv, hIs, hIsk, hH, hHk, hHq, hHb, hHm, hHs, hH0, hH0k, hH0b, hQ, hQk, hQp, hQr, hQl, hQd, hU, hUk, hUl, hUr, hUa, hUe, hUv, hUn, hdiff, d1, d2, d3, d4, d5, d6, Ne.symm d1, Ne.symm d2, Ne.symm d3, Ne.symm d4, Ne.symm d5, Ne.symm d6, d7, d8, d9, d10, Ne.symm d7, Ne.symm d8, Ne.symm d9, Ne.symm d10, beq_self_eq_true, FDI.fdiCtx, Sem.inner, Nat.ne_of_lt hH, Nat.ne_of_gt hH, Nat.lt_succ_of_lt hH, Nat.ne_of_lt hQ, Nat.ne_of_gt hQ, Nat.lt_succ_of_lt hQ, emptyArrayState, arr1State]
  case e2 =>
    js [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGRL, hGRLv, hGCE, hGCEv, hGSD, hGSDv, hGDR, hGDRm, hGDRi, hGIs, hGIsv, hIs, hIsk, hH, hHk, hHq, hHb, hHm, hHs, hH0, hH0k, hH0b, hQ, hQk, hQp, hQr, hQl, hQd, hU, hUk, hUl, hUr, hUa, hUe, hUv, hUn, hdiff, d1, d2, d3, d4, d5, d6, Ne.symm d1, Ne.symm d2, Ne.symm d3, Ne.symm d4, Ne.symm d5, Ne.symm d6, d7, d8, d9, d10, Ne.symm d7, Ne.symm d8, Ne.symm d9, Ne.symm d10, beq_self_eq_true, FDI.fdiCtx, Sem.inner, Nat.ne_of_lt hH, Nat.ne_of_gt hH, Nat.lt_succ_of_lt hH, Nat.ne_of_lt hQ, Nat.ne_of_gt hQ, Nat.lt_succ_of_lt hQ, emptyArrayState, arr1State]
  case fin =>
    intro t' hA he hfu hz hFr hsym ho hr hp
    simp (config := { maxDischargeDepth := 6 }) only [js_simp, ↓reduceIte, ↓reduceDIte, hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGRL, hGRLv, hGCE, hGCEv, hGSD, hGSDv, hGDR, hGDRm, hGDRi, hGIs, hGIsv, hIs, hIsk, hH, hHk, hHq, hHb, hHm, hHs, hH0, hH0k, hH0b, hQ, hQk, hQp, hQr, hQl, hQd, hU, hUk, hUl, hUr, hUa, hUe, hUv, hUn, hdiff, d1, d2, d3, d4, d5, d6, Ne.symm d1, Ne.symm d2, Ne.symm d3, Ne.symm d4, Ne.symm d5, Ne.symm d6, d7, d8, d9, d10, Ne.symm d7, Ne.symm d8, Ne.symm d9, Ne.symm d10, beq_self_eq_true, FDI.fdiCtx, Sem.inner, State.curRealm, realm_setProp, realm_setEnv, realm_withFuel, realm_bodyState, realms_setProp, realms_setEnv, realms_withFuel, realms_bodyState] at hA hz hp hfu hsym
    clear ho he hr
    refine ⟨?v, frame_restore (frame_mono (frame_trans (fp1 := fpR d.env H H0 Q) ?F1 hFr) ?b1 ?b2 ?b3) s, by rw [hfu]; omega, rfl, hA, hp, hsym,
      ?dl, ?m1, ?m2, ?m3, ?m4, ?m5, ?m6, ?m7⟩
    case v => js_norm [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGRL, hGRLv, hGCE, hGCEv, hGSD, hGSDv, hGDR, hGDRm, hGDRi, hGIs, hGIsv, hIs, hIsk, hH, hHk, hHq, hHb, hHm, hHs, hH0, hH0k, hH0b, hQ, hQk, hQp, hQr, hQl, hQd, hU, hUk, hUl, hUr, hUa, hUe, hUv, hUn, hdiff, d1, d2, d3, d4, d5, d6, Ne.symm d1, Ne.symm d2, Ne.symm d3, Ne.symm d4, Ne.symm d5, Ne.symm d6, d7, d8, d9, d10, Ne.symm d7, Ne.symm d8, Ne.symm d9, Ne.symm d10, beq_self_eq_true, FDI.fdiCtx, Sem.inner]
    case F1 => simp only [fpR]; frame_go' [*, hne, Ne.symm hne, hG1]
    case b1 => intro p hp; simpa [Footprint.union] using hp
    case b2 => intro p hp; simpa [Footprint.union] using hp
    case b3 => intro _; rfl
    case dl => rw [envEntry_frame0 hFr (by js_norm [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGRL, hGRLv, hGCE, hGCEv, hGSD, hGSDv, hGDR, hGDRm, hGDRi, hGIs, hGIsv, hIs, hIsk, hH, hHk, hHq, hHb, hHm, hHs, hH0, hH0k, hH0b, hQ, hQk, hQp, hQr, hQl, hQd, hU, hUk, hUl, hUr, hUa, hUe, hUv, hUn, hdiff, d1, d2, d3, d4, d5, d6, Ne.symm d1, Ne.symm d2, Ne.symm d3, Ne.symm d4, Ne.symm d5, Ne.symm d6, d7, d8, d9, d10, Ne.symm d7, Ne.symm d8, Ne.symm d9, Ne.symm d10, beq_self_eq_true, FDI.fdiCtx, Sem.inner])]; js_norm [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGRL, hGRLv, hGCE, hGCEv, hGSD, hGSDv, hGDR, hGDRm, hGDRi, hGIs, hGIsv, hIs, hIsk, hH, hHk, hHq, hHb, hHm, hHs, hH0, hH0k, hH0b, hQ, hQk, hQp, hQr, hQl, hQd, hU, hUk, hUl, hUr, hUa, hUe, hUv, hUn, hdiff, d1, d2, d3, d4, d5, d6, Ne.symm d1, Ne.symm d2, Ne.symm d3, Ne.symm d4, Ne.symm d5, Ne.symm d6, d7, d8, d9, d10, Ne.symm d7, Ne.symm d8, Ne.symm d9, Ne.symm d10, beq_self_eq_true, FDI.fdiCtx, Sem.inner]
    all_goals (rw [objEntry_frame0 hFr (by js_norm [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGRL, hGRLv, hGCE, hGCEv, hGSD, hGSDv, hGDR, hGDRm, hGDRi, hGIs, hGIsv, hIs, hIsk, hH, hHk, hHq, hHb, hHm, hHs, hH0, hH0k, hH0b, hQ, hQk, hQp, hQr, hQl, hQd, hU, hUk, hUl, hUr, hUa, hUe, hUv, hUn, hdiff, d1, d2, d3, d4, d5, d6, Ne.symm d1, Ne.symm d2, Ne.symm d3, Ne.symm d4, Ne.symm d5, Ne.symm d6, d7, d8, d9, d10, Ne.symm d7, Ne.symm d8, Ne.symm d9, Ne.symm d10, beq_self_eq_true, FDI.fdiCtx, Sem.inner])]; js_norm [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGRL, hGRLv, hGCE, hGCEv, hGSD, hGSDv, hGDR, hGDRm, hGDRi, hGIs, hGIsv, hIs, hIsk, hH, hHk, hHq, hHb, hHm, hHs, hH0, hH0k, hH0b, hQ, hQk, hQp, hQr, hQl, hQd, hU, hUk, hUl, hUr, hUa, hUe, hUv, hUn, hdiff, d1, d2, d3, d4, d5, d6, Ne.symm d1, Ne.symm d2, Ne.symm d3, Ne.symm d4, Ne.symm d5, Ne.symm d6, d7, d8, d9, d10, Ne.symm d7, Ne.symm d8, Ne.symm d9, Ne.symm d10, beq_self_eq_true, FDI.fdiCtx, Sem.inner])

end

end ReactReducer
