import JSProofs.ReactUpdateReducer
import JSProofs.USDGen
import JSProofs.USGen

/-!
# `useState` in the click's re-render (zippy docs/react-proofs.md)

The dispatcher's `useState` (`HooksDispatcherOnUpdate.useState`: `return updateReducer(basicStateReducer)`) for the
counter's re-render after a click: `ReactUpdateReducer.click_spec` with `basicStateReducer` as the reducer.
-/

open ES ES.M HostRuns Logic ReactReducer ReactUpdateReducer
open Std (HashMap)

namespace ReactUseState

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ}

theorem simpleD (d : FuncData) (hc : d.code = USDGen.fn1_func) : FDI.Simple d := by
  constructor <;> rw [hc] <;> try rfl
  simp [USDGen.fn1_func, Func.params, Func.info]

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 20000 in
/-- **`HooksDispatcherOnUpdate.useState()`** for the click's re-render of the counter. -/
theorem dispatcher_spec {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {s : State}
    {bG : HashMap JSStr Binding} {oG : Option EnvId} {fD : ObjId} {dD : FuncData} {tD : Value} {argsD : Array Value} {bdU bdB : Binding}
    {bdC bdW bdF bdUW bdUR bdRL bdCE bdSD bdDR bdIs : Binding} {bdIsb : BuiltinData}
    {fW fR fIs C1 C0 H0 Q U : ObjId} {dW dR : FuncData} {r ms bs vE a dv : Value}
    {aw ae ac me mc nw ne nc w1 e1 c1 w2 e2 c2 e3 c3 w4 e4 c4 : Bool}
    {qp qr ql qd ul ur ua ue uv un : Bool × Bool × Bool}
    (hD : fD < s.heap.size) (hDk : (s.objEntry fD).kind = .func dD) (hDcode : dD.code = USDGen.fn1_func)
    (hDcls : dD.isClassCtor = false) (hDmode : dD.thisMode = .strict) (hDenv : dD.env = d.env)
    (hGU : bG[JSStr.ofString "updateReducer"]? = some bdU) (hGUv : bdU.value = some (.obj fo))
    (hGB : bG[JSStr.ofString "basicStateReducer"]? = some bdB) (hGBv : bdB.value = some r)
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : 110 ≤ s.fuel)
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
    WP eng answer (n + 3) h (callImpl eng (.obj fD) tD argsD) s fun v w h' =>
      v = .obj (s.heap.size + 1) ∧ Frame (fpU d.env C1 s.heap.size H0 Q) s w ∧ s.fuel ≤ w.fuel + 110 ∧ h' = h ∧
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
  apply wp_callGen USDGen.fn1_eq (by decide) hD hDk (by omega) hDcls hDmode
    (by rw [hDcode]; rfl) (by rw [hDcode]; rfl) (simpleD dD hDcode) (by rw [hDcode]; rfl) (by rw [hDcode]; rfl)
  have hpn : dD.code.info.fdi.paramNames = #[] := by rw [hDcode]; rfl
  have hv : dD.code.info.fdi.varNames = #[] := by rw [hDcode]; rfl
  have hl : FDI.lexDecls dD = #[] := by simp [FDI.lexDecls, hDcode, USDGen.fn1_func, Func.info]
  have ha : dD.code.isAsync = false := by rw [hDcode]; rfl
  have hne : s.envs.size ≠ d.env := Nat.ne_of_gt hG
  have hG1 : d.env < s.envs.size + 1 := Nat.lt_succ_of_lt hG
  clear hDcode
  simp only [USDGen.fn1]
  js [hpn, hv, hl, ha, hDenv, hG, hG1, hne, Ne.symm hne, hGe, hGU, hGUv, hGB, hGBv, hlt, hk, FDI.fdiCtx, Sem.inner]
  refine ⟨by js_norm [CallableC, hlt, hk], ?_⟩
  refine wp_mono (ReactUpdateReducer.click_spec (bG := bG) (oG := oG)
    (hlt := hlt) (hk := hk) (hf := by js_norm; omega) (hcode := hcode) (hcls := hcls) (hmode := hmode) (hG := by
    js_norm [hG, hG1]) (hGe := by js_norm [hGe, hne, Ne.symm hne]) (hGC := hGC) (hGCm := hGCm) (hGCv := hGCv) (hGW
    := hGW) (hGWm := hGWm) (hGWv := hGWv) (hGF := hGF) (hGFv := hGFv) (hGUW := hGUW) (hGUWv := hGUWv) (hW := hW)
    (hWk := hWk) (hWcode := hWcode) (hWcls := hWcls) (hWmode := hWmode) (hWenv := hWenv) (hGUR := hGUR) (hGURv :=
    hGURv) (hR := hR) (hRk := hRk) (hRcode := hRcode) (hRcls := hRcls) (hRmode := hRmode) (hRenv := hRenv) (hGRL
    := hGRL) (hGRLv := hGRLv) (hGCE := hGCE) (hGCEv := hGCEv) (hGSD := hGSD) (hGSDv := hGSDv) (hGDR := hGDR)
    (hGDRm := hGDRm) (hGDRi := hGDRi) (hGIs := hGIs) (hGIsv := hGIsv) (hIs := hIs) (hIsk := hIsk) (hIstab :=
    hIstab) (hC1 := hC1) (hC1k := hC1k) (hC1a := hC1a) (hC1m := hC1m) (hC0 := hC0) (hC0k := hC0k) (hC0m := hC0m)
    (hH0 := hH0) (hH0k := hH0k) (hHm := hHm) (hHb := hHb) (hHbq := hHbq) (hHq := hHq) (hQ := hQ) (hQk := hQk) (hQp
    := hQp) (hQr := hQr) (hQl := hQl) (hQd := hQd) (hU := hU) (hUk := hUk) (hUl := hUl) (hUr := hUr) (hUa := hUa)
    (hUe := hUe) (hUv := hUv) (hUn := hUn) (hdiff := hdiff) (d1 := d1) (d2 := d2) (d3 := d3) (d4 := d4) (d5 := d5)
    (d6 := d6) (d7 := d7) (d8 := d8) (d9 := d9) (d10 := d10) (d11 := d11) (d12 := d12)) ?post
  intro v w h1 ⟨hv, hF, hfu, hh, hA, hp, hsym, hdl, hm, hkk, hkm, hkb, hkbq, hkq, hkn, hH0b, hQp, hQr, hQl⟩
  simp (config := { maxDischargeDepth := 6 }) only [js_simp, ↓reduceIte] at hv hfu hA hp hsym hm hkk hkm hkb hkbq hkq hkn hH0b hQp hQr hQl
  have hbz : (bodyState s fD dD tD argsD).heap.size = s.heap.size := by js_norm
  rw [hbz] at hF
  rw [realms_bodyState] at hp
  exact ⟨hv, frame_restore (frame_mono (frame_trans (frame_bodyState (frame_refl ({} : Footprint) s) fD dD tD argsD) hF)
    (fun p hp => by simpa [Footprint.union] using hp) (fun p hp => by simpa [Footprint.union] using hp)
    (fun _ => rfl)) s, by omega, hh, hA, hp, hsym, hdl, hm, hkk, hkm, hkb, hkbq, hkq, hkn, hH0b, hQp, hQr, hQl⟩

theorem simpleS (d : FuncData) (hc : d.code = USGen.fn0_func) : FDI.Simple d := by
  constructor <;> rw [hc] <;> try rfl
  simp [USGen.fn0_func, Func.params, Func.info]

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 20000 in
/-- **`useState(x)`** (`react`'s export: `ReactSharedInternals.H.useState(x)`) for the click's re-render of the
counter, `H` being the update dispatcher. -/
theorem click_spec {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {s : State}
    {bG : HashMap JSStr Binding} {oG : Option EnvId} {fD : ObjId} {dD : FuncData} {fS RSI HD : ObjId} {dS : FuncData} {tS x : Value} {bR : HashMap JSStr Binding}
    {oR : Option EnvId} {bdRSI : Binding} {rw re rc uw ue' uc : Bool} {bdU bdB : Binding}
    {bdC bdW bdF bdUW bdUR bdRL bdCE bdSD bdDR bdIs : Binding} {bdIsb : BuiltinData}
    {fW fR fIs C1 C0 H0 Q U : ObjId} {dW dR : FuncData} {r ms bs vE a dv : Value}
    {aw ae ac me mc nw ne nc w1 e1 c1 w2 e2 c2 e3 c3 w4 e4 c4 : Bool}
    {qp qr ql qd ul ur ua ue uv un : Bool × Bool × Bool}
    (hS : fS < s.heap.size) (hSk : (s.objEntry fS).kind = .func dS) (hScode : dS.code = USGen.fn0_func)
    (hScls : dS.isClassCtor = false) (hSmode : dS.thisMode = .strict)
    -- (`react`'s module scope: `ReactSharedInternals`, whose `H` is the update dispatcher `HD`)
    (hSG : dS.env < s.envs.size) (hSGe : Scope.declLike? (s.envEntry dS.env) = some (bR, oR))
    (hRSI : bR[JSStr.ofString "ReactSharedInternals"]? = some bdRSI) (hRSIv : bdRSI.value = some (.obj RSI))
    (hI : RSI < s.heap.size) (hIk : (s.objEntry RSI).kind.isPlain = true)
    (hIH : (s.objEntry RSI).props.get? (.str "H") = some (.data (.obj HD) rw re rc))
    (hHD : HD < s.heap.size) (hHDk : (s.objEntry HD).kind.isPlain = true)
    (hHDu : (s.objEntry HD).props.get? (.str "useState") = some (.data (.obj fD) uw ue' uc))
    (hD : fD < s.heap.size) (hDk : (s.objEntry fD).kind = .func dD) (hDcode : dD.code = USDGen.fn1_func)
    (hDcls : dD.isClassCtor = false) (hDmode : dD.thisMode = .strict) (hDenv : dD.env = d.env)
    (hGU : bG[JSStr.ofString "updateReducer"]? = some bdU) (hGUv : bdU.value = some (.obj fo))
    (hGB : bG[JSStr.ofString "basicStateReducer"]? = some bdB) (hGBv : bdB.value = some r)
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : 120 ≤ s.fuel)
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
    WP eng answer (n + 4) h (callImpl eng (.obj fS) tS #[x]) s fun v w h' =>
      v = .obj (s.heap.size + 1) ∧ Frame (fpU d.env C1 s.heap.size H0 Q) s w ∧ s.fuel ≤ w.fuel + 120 ∧ h' = h ∧
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
  apply wp_callGen USGen.fn0_eq (by decide) hS hSk (by omega) hScls hSmode
    (by rw [hScode]; rfl) (by rw [hScode]; rfl) (simpleS dS hScode) (by rw [hScode]; rfl) (by rw [hScode]; rfl)
  have hpn : dS.code.info.fdi.paramNames = #[JSStr.ofString "initialState"] := by rw [hScode]; rfl
  have hv : dS.code.info.fdi.varNames = #[] := by rw [hScode]; rfl
  have hl : FDI.lexDecls dS = #[] := by simp [FDI.lexDecls, hScode, USGen.fn0_func, Func.info]
  have ha : dS.code.isAsync = false := by rw [hScode]; rfl
  have hne : s.envs.size ≠ d.env := Nat.ne_of_gt hG
  have hG1 : d.env < s.envs.size + 1 := Nat.lt_succ_of_lt hG
  have hneS : s.envs.size ≠ dS.env := Nat.ne_of_gt hSG
  have hSG1 : dS.env < s.envs.size + 1 := Nat.lt_succ_of_lt hSG
  clear hScode
  simp only [USGen.fn0]
  js [hpn, hv, hl, ha, hSG, hSG1, hneS, Ne.symm hneS, hSGe, hRSI, hRSIv, hI, hIk, hIH, hHD, hHDk, hHDu, hD, hDk,
    FDI.fdiCtx, Sem.inner]
  refine ⟨by js_norm [CallableC, hD, hDk], ?_⟩
  refine wp_mono (dispatcher_spec (bG := bG) (oG := oG)
    (hD := hD) (hDk := hDk) (hDcode := hDcode) (hDcls := hDcls) (hDmode := hDmode) (hDenv := hDenv) (hGU := hGU)
    (hGUv := hGUv) (hGB := hGB) (hGBv := hGBv) (hlt := hlt) (hk := hk) (hf := by js_norm; omega) (hcode := hcode)
    (hcls := hcls) (hmode := hmode) (hG := by js_norm [hG, hG1]) (hGe := by js_norm [hGe, hne, Ne.symm hne]) (hGC
    := hGC) (hGCm := hGCm) (hGCv := hGCv) (hGW := hGW) (hGWm := hGWm) (hGWv := hGWv) (hGF := hGF) (hGFv := hGFv)
    (hGUW := hGUW) (hGUWv := hGUWv) (hW := hW) (hWk := hWk) (hWcode := hWcode) (hWcls := hWcls) (hWmode := hWmode)
    (hWenv := hWenv) (hGUR := hGUR) (hGURv := hGURv) (hR := hR) (hRk := hRk) (hRcode := hRcode) (hRcls := hRcls)
    (hRmode := hRmode) (hRenv := hRenv) (hGRL := hGRL) (hGRLv := hGRLv) (hGCE := hGCE) (hGCEv := hGCEv) (hGSD :=
    hGSD) (hGSDv := hGSDv) (hGDR := hGDR) (hGDRm := hGDRm) (hGDRi := hGDRi) (hGIs := hGIs) (hGIsv := hGIsv) (hIs
    := hIs) (hIsk := hIsk) (hIstab := hIstab) (hC1 := hC1) (hC1k := hC1k) (hC1a := hC1a) (hC1m := hC1m) (hC0 :=
    hC0) (hC0k := hC0k) (hC0m := hC0m) (hH0 := hH0) (hH0k := hH0k) (hHm := hHm) (hHb := hHb) (hHbq := hHbq) (hHq
    := hHq) (hQ := hQ) (hQk := hQk) (hQp := hQp) (hQr := hQr) (hQl := hQl) (hQd := hQd) (hU := hU) (hUk := hUk)
    (hUl := hUl) (hUr := hUr) (hUa := hUa) (hUe := hUe) (hUv := hUv) (hUn := hUn) (hdiff := hdiff) (d1 := d1) (d2
    := d2) (d3 := d3) (d4 := d4) (d5 := d5) (d6 := d6) (d7 := d7) (d8 := d8) (d9 := d9) (d10 := d10) (d11 := d11)
    (d12 := d12)) ?post
  intro v w h1 ⟨hv, hF, hfu, hh, hA, hp, hsym, hdl, hm, hkk, hkm, hkb, hkbq, hkq, hkn, hH0b, hQp, hQr, hQl⟩
  simp (config := { maxDischargeDepth := 6 }) only [js_simp, ↓reduceIte] at hv hfu hA hp hsym hm hkk hkm hkb hkbq hkq hkn hH0b hQp hQr hQl
  have hbz : (bodyState s fS dS tS #[x]).heap.size = s.heap.size := by js_norm
  rw [hbz] at hF
  rw [realms_bodyState] at hp
  exact ⟨hv, frame_restore (frame_mono (frame_trans (frame_bodyState (frame_refl ({} : Footprint) s) fS dS tS #[x]) hF)
    (fun p hp => by simpa [Footprint.union] using hp) (fun p hp => by simpa [Footprint.union] using hp)
    (fun _ => rfl)) s, by omega, hh, hA, hp, hsym, hdl, hm, hkk, hkm, hkb, hkbq, hkq, hkn, hH0b, hQp, hQr, hQl⟩

end

end ReactUseState
