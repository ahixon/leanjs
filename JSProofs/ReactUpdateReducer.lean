import JSProofs.ReactHooks
import JSProofs.ReactReducer
import JSProofs.URGen

/-!
# React's `updateReducer` for the click (zippy docs/react-proofs.md)

`updateReducer(reducer)`: `updateWorkInProgressHook()` (`ReactHooks.first_spec`: the current first hook cloned)
then `updateReducerImpl(hook, currentHook, reducer)` (`ReactReducer.click_spec`: the click's update processed).
-/

open ES ES.M HostRuns Logic ReactReducer
open Std (HashMap)

namespace ReactUpdateReducer

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ}

theorem simpleU (d : FuncData) (hc : d.code = URGen.updateReducer_func) : FDI.Simple d := by
  constructor <;> rw [hc] <;> try rfl
  simp [URGen.updateReducer_func, Func.params, Func.info]

/-- What it writes (besides the new hook and array): `updateWorkInProgressHook`'s and `updateReducerImpl`'s. -/
def fpU (g : EnvId) (C1 K H0 Q : ObjId) : Footprint := (ReactHooks.fpW g C1).union (fpR g K H0 Q)

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 20000 in
/-- **`updateReducer(reducer)`** for the click's re-render of the counter. -/
theorem click_spec {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t : Value} {s : State}
    {bG : HashMap JSStr Binding} {oG : Option EnvId}
    {bdC bdW bdF bdUW bdUR bdRL bdCE bdSD bdDR bdIs : Binding} {bdIsb : BuiltinData}
    {fW fR fIs C1 C0 H0 Q U : ObjId} {dW dR : FuncData} {r ms bs vE a dv : Value}
    {aw ae ac me mc nw ne nc w1 e1 c1 w2 e2 c2 e3 c3 w4 e4 c4 : Bool}
    {h0b qp qr ql qd ul ur ua ue uv un : Bool × Bool × Bool}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : 100 ≤ s.fuel)
    (hcode : d.code = URGen.updateReducer_func) (hcls : d.isClassCtor = false) (hmode : d.thisMode = .strict)
    (hG : d.env < s.envs.size) (hGe : Scope.declLike? (s.envEntry d.env) = some (bG, oG))
    -- (`updateWorkInProgressHook`'s module variables)
    (hGC : bG[JSStr.ofString "currentHook"]? = some bdC) (hGCm : bdC.mutable = true) (hGCv : bdC.value = some .null)
    (hGW : bG[JSStr.ofString "workInProgressHook"]? = some bdW) (hGWm : bdW.mutable = true)
    (hGWv : bdW.value = some .null)
    (hGF : bG[JSStr.ofString "currentlyRenderingFiber"]? = some bdF) (hGFv : bdF.value = some (.obj C1))
    -- (the two callees, functions of the same module)
    (hGUW : bG[JSStr.ofString "updateWorkInProgressHook"]? = some bdUW) (hGUWv : bdUW.value = some (.obj fW))
    (hW : fW < s.heap.size) (hWk : (s.objEntry fW).kind = .func dW)
    (hWcode : dW.code = UWHGen.updateWorkInProgressHook_func) (hWcls : dW.isClassCtor = false)
    (hWmode : dW.thisMode = .strict) (hWenv : dW.env = d.env)
    (hGUR : bG[JSStr.ofString "updateReducerImpl"]? = some bdUR) (hGURv : bdUR.value = some (.obj fR))
    (hR : fR < s.heap.size) (hRk : (s.objEntry fR).kind = .func dR)
    (hRcode : dR.code = URIGen.updateReducerImpl_func) (hRcls : dR.isClassCtor = false)
    (hRmode : dR.thisMode = .strict) (hRenv : dR.env = d.env)
    -- (`updateReducerImpl`'s module variables)
    (hGRL : bG[JSStr.ofString "renderLanes"]? = some bdRL) (hGRLv : bdRL.value = some two)
    (hGCE : bG[JSStr.ofString "currentEntangledLane"]? = some bdCE) (hGCEv : bdCE.value = some zero)
    (hGSD : bG[JSStr.ofString "shouldDoubleInvokeUserFnsInHooksDEV"]? = some bdSD)
    (hGSDv : bdSD.value = some (.bool false))
    (hGDR : bG[JSStr.ofString "didReceiveUpdate"]? = some bdDR) (hGDRm : bdDR.mutable = true)
    (hGDRi : bdDR.value.isSome = true)
    (hGIs : bG[JSStr.ofString "objectIs"]? = some bdIs) (hGIsv : bdIs.value = some (.obj fIs))
    (hIs : fIs < s.heap.size) (hIsk : (s.objEntry fIs).kind = .builtin bdIsb)
    (hIstab : eng.builtins[bdIsb.id]? = some objectIs)
    -- (the work in progress `C1`, its current `C0`, the current first hook `H0`, its queue `Q`, the update `U`)
    (hC1 : C1 < s.heap.size) (hC1k : (s.objEntry C1).kind.isPlain = true)
    (hC1a : (s.objEntry C1).props.get? (.str "alternate") = some (.data (.obj C0) aw ae ac))
    (hC1m : (s.objEntry C1).props.get? (.str "memoizedState") = some (.data .null true me mc))
    (hC0 : C0 < s.heap.size) (hC0k : (s.objEntry C0).kind.isPlain = true)
    (hC0m : (s.objEntry C0).props.get? (.str "memoizedState") = some (.data (.obj H0) nw ne nc))
    (hH0 : H0 < s.heap.size) (hH0k : (s.objEntry H0).kind.isPlain = true)
    (hHm : (s.objEntry H0).props.get? (.str "memoizedState") = some (.data ms w1 e1 c1))
    (hHb : (s.objEntry H0).props.get? (.str "baseState") = some (.data bs w2 e2 c2))
    (hHbq : (s.objEntry H0).props.get? (.str "baseQueue") = some (.data .null true e3 c3))
    (hHq : (s.objEntry H0).props.get? (.str "queue") = some (.data (.obj Q) w4 e4 c4))
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
    (d1 : C1 ≠ C0) (d2 : C1 ≠ H0) (d3 : C1 ≠ Q) (d4 : C1 ≠ U) (d5 : C1 ≠ fIs) (d6 : C1 ≠ fR)
    (d7 : H0 ≠ Q) (d8 : H0 ≠ U) (d9 : Q ≠ U) (d10 : fIs ≠ H0) (d11 : fIs ≠ Q) (d12 : fIs ≠ U) :
    WP eng answer (n + 2) h (callImpl eng (.obj fo) t #[r]) s fun v w h' =>
      v = .obj (s.heap.size + 1) ∧ Frame (fpU d.env C1 s.heap.size H0 Q) s w ∧ s.fuel ≤ w.fuel + 100 ∧ h' = h ∧
      ArrayObj (s.heap.size + 1) 2 (fun j => if j = 1 then dv else if j = 0 then vE else .undefined) w ∧
      (w.objEntry (s.heap.size + 1)).proto = .obj s.realms[dR.realm]!.arrayProto ∧
      (w.objEntry (s.heap.size + 1)).props.get? (.sym WK.iterator) = none ∧
      Scope.declLike? (w.envEntry d.env) = some ((((bG.modify (JSStr.ofString "currentHook")
        (fun bd => { bd with value := some (.obj H0) })).modify (JSStr.ofString "workInProgressHook")
        (fun bd => { bd with value := some (.obj s.heap.size) })).modify (JSStr.ofString "didReceiveUpdate")
        (fun bd => { bd with value := some (.bool true) })), oG) ∧
      (w.objEntry C1).props.get? (.str "memoizedState") = some (.data (.obj s.heap.size) true me mc) ∧
      (w.objEntry s.heap.size).kind.isPlain = true ∧
      (w.objEntry s.heap.size).props.get? (.str "memoizedState") = some (.data vE true true true) ∧
      (w.objEntry s.heap.size).props.get? (.str "baseState") = some (.data vE true true true) ∧
      (w.objEntry s.heap.size).props.get? (.str "baseQueue") = some (.data .null true true true) ∧
      (w.objEntry s.heap.size).props.get? (.str "queue") = some (.data (.obj Q) true true true) ∧
      (w.objEntry s.heap.size).props.get? (.str "next") = some (.data .null true true true) ∧
      (w.objEntry H0).props.get? (.str "baseQueue") = some (.data (.obj U) true e3 c3) ∧
      (w.objEntry Q).props.get? (.str "pending") = some (.data .null true qp.2.1 qp.2.2) ∧
      (w.objEntry Q).props.get? (.str "lastRenderedReducer") = some (.data r true qr.2.1 qr.2.2) ∧
      (w.objEntry Q).props.get? (.str "lastRenderedState") = some (.data vE true ql.2.1 ql.2.2) := by
  apply wp_callGen URGen.updateReducer_eq (by decide) hlt hk (by omega) hcls hmode
    (by rw [hcode]; rfl) (by rw [hcode]; rfl) (simpleU d hcode) (by rw [hcode]; rfl) (by rw [hcode]; rfl)
  have hpn : d.code.info.fdi.paramNames = #[JSStr.ofString "reducer"] := by rw [hcode]; rfl
  have hv : d.code.info.fdi.varNames = #[JSStr.ofString "hook"] := by rw [hcode]; rfl
  have hl : FDI.lexDecls d = #[] := by simp [FDI.lexDecls, hcode, URGen.updateReducer_func, Func.info]
  have ha : d.code.isAsync = false := by rw [hcode]; rfl
  have hne : s.envs.size ≠ d.env := Nat.ne_of_gt hG
  have hG1 : d.env < s.envs.size + 1 := Nat.lt_succ_of_lt hG
  clear hcode
  simp only [URGen.updateReducer]
  js [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGUW, hGUWv, hW, hWk, FDI.fdiCtx, Sem.inner]
  refine ⟨by js_norm [CallableC, hW, hWk, hG, hne, Ne.symm hne], ?_⟩
  -- (`updateWorkInProgressHook()`: the current first hook cloned at `s.heap.size`)
  refine wp_mono (ReactHooks.first_spec (fo := fW) (d := dW) (bG := bG) (oG := oG) (C1 := C1) (C0 := C0) (H0 := H0)
    (aw := aw) (ae := ae) (ac := ac) (me := me) (mc := mc) (mw := nw) (nw := ne) (ne := nc)
    ?_ ?_ ?_ hWcode hWcls hWmode ?_ ?_ hGC hGCm hGCv hGW hGWm hGWv hGF hGFv ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hHm hHb hHbq hHq d1 d2)
    ?post
  all_goals first
    | (js_norm [hW, hWk, hWenv, hG, hG1, hne, Ne.symm hne, hGe, hC1, hC1k, hC1a, hC1m, hC0, hC0k, hC0m, hH0, hH0k]; done)
    | (js_norm [hWenv, hG, hG1, hne, Ne.symm hne, hGe]; omega)
    | skip
  case post =>
  intro v1 w1 h1 ⟨hv1, hF1, hfu1, hh1, hdl1, hC1m1, hsz1, hKk, hKm, hKb, hKbq, hKq, hKn⟩
  subst v1 h1
  rw [hWenv] at hdl1 hF1
  simp (config := { maxDischargeDepth := 6 }) only [js_simp, ↓reduceIte] at hsz1 hKk hKm hKb hKbq hKq hKn hfu1 hdl1 hC1m1
  have hfp : ∀ o, o ≠ C1 → (ReactHooks.fpW d.env C1).props.all (fun p => p.1 != o) = true := by
    intro o ho; simp [ReactHooks.fpW, Ne.symm ho]
  have hE1 : s.envs.size < w1.envs.size := envs_frame hF1 (by js_norm)
  have hG2 : d.env < w1.envs.size := envs_frame hF1 (by js_norm [hG1])
  have hE1e : w1.envEntry s.envs.size = (bodyState s fo d t #[r]).envEntry s.envs.size :=
    envEntry_frame hF1 (by js_norm) (by simp [ReactHooks.fpW, hne, Ne.symm hne])
  have hH0e : w1.objEntry H0 = s.objEntry H0 := objEntry_frame hF1 (by js_norm [hH0]) (hfp H0 (Ne.symm d2))
  have hQe : w1.objEntry Q = s.objEntry Q := objEntry_frame hF1 (by js_norm [hQ]) (hfp Q (Ne.symm d3))
  have hUe' : w1.objEntry U = s.objEntry U := objEntry_frame hF1 (by js_norm [hU]) (hfp U (Ne.symm d4))
  have hIse : w1.objEntry fIs = s.objEntry fIs := objEntry_frame hF1 (by js_norm [hIs]) (hfp fIs (Ne.symm d5))
  have hRe : w1.objEntry fR = s.objEntry fR := objEntry_frame hF1 (by js_norm [hR]) (hfp fR (Ne.symm d6))
  have hH01 : H0 < w1.heap.size := by rw [hsz1]; exact Nat.lt_succ_of_lt hH0
  have hQ1 : Q < w1.heap.size := by rw [hsz1]; exact Nat.lt_succ_of_lt hQ
  have hU1 : U < w1.heap.size := by rw [hsz1]; exact Nat.lt_succ_of_lt hU
  have hIs1 : fIs < w1.heap.size := by rw [hsz1]; exact Nat.lt_succ_of_lt hIs
  have hR1 : fR < w1.heap.size := by rw [hsz1]; exact Nat.lt_succ_of_lt hR
  have hK1 : s.heap.size < w1.heap.size := by rw [hsz1]; exact Nat.lt_succ_self _
  js [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hE1, hE1e, hG2, hdl1, hGC, hGUR, hGURv, hR1, hRe, hRk, FDI.fdiCtx,
    Sem.inner]
  refine ⟨by js_norm [CallableC, hR1, hRe, hRk], ?_⟩
  -- (`updateReducerImpl(hook, currentHook, reducer)`: the click's update processed)
  refine wp_mono (ReactReducer.click_spec (fo := fR) (d := dR) (H := s.heap.size) (H0 := H0) (Q := Q) (U := U)
    (bG := (bG.modify (JSStr.ofString "currentHook") (fun bd => { bd with value := some (.obj H0) })).modify
      (JSStr.ofString "workInProgressHook") (fun bd => { bd with value := some (.obj s.heap.size) })) (oG := oG)
    (bdRL := bdRL) (bdCE := bdCE) (bdSD := bdSD) (bdDR := bdDR) (bdIs := bdIs)
    (fIs := fIs) (bdIsb := bdIsb) (r := r) (ms := ms) (bs := bs) (a := a) (vE := vE) (dv := dv)
    (hq := (true, true, true)) (hb := (true, true, true)) (hm := (true, true, true)) (hs := (true, true, true))
    (h0b := (true, e3, c3)) (qp := qp) (qr := qr) (ql := ql) (qd := qd) (ul := ul) (ur := ur) (ua := ua) (ue := ue)
    (uv := uv) (un := un)
    ?_ ?_ ?_ hRcode hRcls hRmode ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hIstab
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    hdiff ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) ?post2
  all_goals first
    | (js_norm [hRenv, hG2, hdl1, hGRL, hGRLv, hGCE, hGCEv, hGSD, hGSDv, hGDR, hGDRm, hGDRi, hGIs, hGIsv, hIs1, hIse, hIsk, hK1, hKk, hKq, hKbq, hKm, hKb, hH01, hH0e, hH0k, hHbq, hQ1, hQe, hQk, hQp, hQr, hQl, hQd, hU1, hUe', hUk, hUl, hUr, hUa, hUe, hUv, hUn, hR1, hRe, hRk, d7, d8, d9, d10, d11, d12, Ne.symm d7, Ne.symm d8, Ne.symm d9, Ne.symm d10, Ne.symm d11, Ne.symm d12, Nat.ne_of_lt hH0, Nat.ne_of_gt hH0, Nat.ne_of_lt hQ, Nat.ne_of_gt hQ, Nat.ne_of_lt hU, Nat.ne_of_gt hU, Nat.ne_of_lt hIs, Nat.ne_of_gt hIs, hne, Ne.symm hne]; done)
    | (js_norm [hRenv, hG2, hdl1, hGRL, hGRLv, hGCE, hGCEv, hGSD, hGSDv, hGDR, hGDRm, hGDRi, hGIs, hGIsv, hIs1, hIse, hIsk, hK1, hKk, hKq, hKbq, hKm, hKb, hH01, hH0e, hH0k, hHbq, hQ1, hQe, hQk, hQp, hQr, hQl, hQd, hU1, hUe', hUk, hUl, hUr, hUa, hUe, hUv, hUn, hR1, hRe, hRk, d7, d8, d9, d10, d11, d12, Ne.symm d7, Ne.symm d8, Ne.symm d9, Ne.symm d10, Ne.symm d11, Ne.symm d12, Nat.ne_of_lt hH0, Nat.ne_of_gt hH0, Nat.ne_of_lt hQ, Nat.ne_of_gt hQ, Nat.ne_of_lt hU, Nat.ne_of_gt hU, Nat.ne_of_lt hIs, Nat.ne_of_gt hIs, hne, Ne.symm hne]; omega)
    | skip
  case post2 =>
  intro v2 w2 h2 ⟨hv2, hF2, hfu2, hh2, hA2, hp2, hsym2, hdl2, hm2, hbs2, hbq2, hH0bq2, hQp2, hQr2, hQl2⟩
  subst v2 h2
  rw [hRenv] at hdl2 hF2
  simp (config := { maxDischargeDepth := 6 }) only [js_simp, ↓reduceIte, hsz1] at hA2 hp2 hfu2 hsym2
  have hF0 : Frame {} s (bodyState s fo d t #[r]) := frame_bodyState (frame_refl _ s) fo d t #[r]
  have hrl : w1.realms = s.realms := hF1.realms_eq
  refine ⟨by js_norm [hsz1], frame_restore (frame_mono (frame_trans (frame_setEnv_new (frame_trans hF0 hF1) (Nat.le_refl _) _) hF2) ?b1 ?b2 ?b3) s, ?fu, rfl, hA2, ?pr, hsym2,
    hdl2, ?c1, ?kk, hm2, hbs2, hbq2, ?kq, ?kn, hH0bq2, hQp2, hQr2, ?ql⟩
  case b1 => intro p hp; simpa [Footprint.union, fpU] using hp
  case b2 => intro p hp; simpa [Footprint.union, fpU] using hp
  case b3 => intro _; rfl
  case fu => omega
  case pr => rw [hp2]; simp [hrl]
  case c1 => rw [props_frame hF2 (by simp; rw [hsz1]; exact Nat.lt_succ_of_lt hC1) (by simp [fpR, d2, d3, Nat.ne_of_lt hC1])]; js_norm [hC1m1]
  case kk => rw [kind_frame hF2 (by simp; exact hK1)]; js_norm [hKk]
  case kq => rw [props_frame hF2 (by simp; exact hK1) (by simp [fpR])]; js_norm [hKq]
  case kn => rw [props_frame hF2 (by simp; exact hK1) (by simp [fpR])]; js_norm [hKn]
  case ql => exact hQl2

end

end ReactUpdateReducer
