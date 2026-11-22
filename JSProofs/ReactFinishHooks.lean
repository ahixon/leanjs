import JSProofs.JsTactic
import JSProofs.FRHGen

/-!
# React's `finishRenderingHooks` after the counter's render (zippy docs/react-proofs.md)

`finishRenderingHooks(current)` after a render that used the one hook (`currentHook.next` null) and received an
update (`didReceiveUpdate` true, so the context check is skipped): `ReactSharedInternals.H` back to
`ContextOnlyDispatcher`, the render's module variables reset.
-/

open ES ES.M HostRuns Logic
open Std (HashMap)

namespace ReactFinishHooks

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ}

theorem simpleF (d : FuncData) (hc : d.code = FRHGen.finishRenderingHooks_func) : FDI.Simple d := by
  constructor <;> rw [hc] <;> try rfl
  simp [FRHGen.finishRenderingHooks_func, Func.params, Func.info]

/-- What it writes: `ReactSharedInternals.H` and the render's module variables. -/
def fpF (g : EnvId) (RSI : ObjId) : Footprint :=
  ⟨[(g, "renderLanes"), (g, "currentlyRenderingFiber"), (g, "currentHook"), (g, "workInProgressHook"),
    (g, "didScheduleRenderPhaseUpdate"), (g, "thenableIndexCounter"), (g, "thenableState")], [(RSI, .str "H")], false⟩

/-- The module's variables after it, in the order it writes them. -/
def resetMap (bG : HashMap JSStr Binding) : HashMap JSStr Binding :=
  ((((((bG.modify (JSStr.ofString "renderLanes") (fun bd => { bd with value := some (.num (F64.fin false 0 (-1074))) })).modify
    (JSStr.ofString "currentlyRenderingFiber") (fun bd => { bd with value := some .null })).modify
    (JSStr.ofString "currentHook") (fun bd => { bd with value := some .null })).modify
    (JSStr.ofString "workInProgressHook") (fun bd => { bd with value := some .null })).modify
    (JSStr.ofString "didScheduleRenderPhaseUpdate") (fun bd => { bd with value := some (.bool false) })).modify
    (JSStr.ofString "thenableIndexCounter") (fun bd => { bd with value := some (.num (F64.fin false 0 (-1074))) })).modify
    (JSStr.ofString "thenableState") (fun bd => { bd with value := some .null })

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 20000 in
/-- **`finishRenderingHooks(current)`** after the counter's render. -/
theorem spec {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t cur : Value} {s : State}
    {bG : HashMap JSStr Binding} {oG : Option EnvId}
    {bdRS bdCO bdCH bdRL bdWH bdCF bdDS bdTI bdTS bdDR : Binding} {RSI H0 : ObjId} {vCO vH : Value}
    {re rc nw ne nc : Bool}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : 30 ≤ s.fuel)
    (hcode : d.code = FRHGen.finishRenderingHooks_func) (hcls : d.isClassCtor = false) (hmode : d.thisMode = .strict)
    (hG : d.env < s.envs.size) (hGe : Scope.declLike? (s.envEntry d.env) = some (bG, oG))
    (hGRS : bG[JSStr.ofString "ReactSharedInternals"]? = some bdRS) (hGRSv : bdRS.value = some (.obj RSI))
    (hGCO : bG[JSStr.ofString "ContextOnlyDispatcher"]? = some bdCO) (hGCOv : bdCO.value = some vCO)
    (hGCH : bG[JSStr.ofString "currentHook"]? = some bdCH) (hGCHm : bdCH.mutable = true)
    (hGCHv : bdCH.value = some (.obj H0))
    (hGRL : bG[JSStr.ofString "renderLanes"]? = some bdRL) (hGRLm : bdRL.mutable = true)
    (hGRLi : bdRL.value.isSome = true)
    (hGWH : bG[JSStr.ofString "workInProgressHook"]? = some bdWH) (hGWHm : bdWH.mutable = true)
    (hGWHi : bdWH.value.isSome = true)
    (hGCF : bG[JSStr.ofString "currentlyRenderingFiber"]? = some bdCF) (hGCFm : bdCF.mutable = true)
    (hGCFi : bdCF.value.isSome = true)
    (hGDS : bG[JSStr.ofString "didScheduleRenderPhaseUpdate"]? = some bdDS) (hGDSm : bdDS.mutable = true)
    (hGDSi : bdDS.value.isSome = true)
    (hGTI : bG[JSStr.ofString "thenableIndexCounter"]? = some bdTI) (hGTIm : bdTI.mutable = true)
    (hGTIi : bdTI.value.isSome = true)
    (hGTS : bG[JSStr.ofString "thenableState"]? = some bdTS) (hGTSm : bdTS.mutable = true)
    (hGTSi : bdTS.value.isSome = true)
    (hGDR : bG[JSStr.ofString "didReceiveUpdate"]? = some bdDR) (hGDRv : bdDR.value = some (.bool true))
    (hRSI : RSI < s.heap.size) (hRSIk : (s.objEntry RSI).kind.isPlain = true)
    (hRSIH : (s.objEntry RSI).props.get? (.str "H") = some (.data vH true re rc))
    (hH0 : H0 < s.heap.size) (hH0k : (s.objEntry H0).kind.isPlain = true)
    (hH0n : (s.objEntry H0).props.get? (.str "next") = some (.data .null nw ne nc))
    (hcur : cur ≠ .null) (dRH : RSI ≠ H0) :
    WP eng answer (n + 1) h (callImpl eng (.obj fo) t #[cur]) s fun v w h' =>
      v = .undefined ∧ Frame (fpF d.env RSI) s w ∧ s.fuel ≤ w.fuel + 30 ∧ h' = h ∧ w.realm = s.realm ∧
      Scope.declLike? (w.envEntry d.env) = some (resetMap bG, oG) ∧
      (w.objEntry RSI).props.get? (.str "H") = some (.data vCO true re rc) := by
  apply wp_callGen FRHGen.finishRenderingHooks_eq (by decide) hlt hk (by omega) hcls hmode
    (by rw [hcode]; rfl) (by rw [hcode]; rfl) (simpleF d hcode) (by rw [hcode]; rfl) (by rw [hcode]; rfl)
  have hpn : d.code.info.fdi.paramNames = #[JSStr.ofString "current"] := by rw [hcode]; rfl
  have hv : d.code.info.fdi.varNames = #[JSStr.ofString "didRenderTooFewHooks"] := by rw [hcode]; rfl
  have hl : FDI.lexDecls d = #[] := by simp [FDI.lexDecls, hcode, FRHGen.finishRenderingHooks_func, Func.info]
  have ha : d.code.isAsync = false := by rw [hcode]; rfl
  have hne : s.envs.size ≠ d.env := Nat.ne_of_gt hG
  have hG1 : d.env < s.envs.size + 1 := Nat.lt_succ_of_lt hG
  clear hcode
  simp only [FRHGen.finishRenderingHooks]
  js [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGRS, hGRSv, hGCO, hGCOv, hGCH, hGCHm, hGCHv, hGRL, hGRLm,
    hGRLi, hGWH, hGWHm, hGWHi, hGCF, hGCFm, hGCFi, hGDS, hGDSm, hGDSi, hGTI, hGTIm, hGTIi, hGTS, hGTSm, hGTSi, hGDR,
    hGDRv, hRSI, hRSIk, hRSIH, hH0, hH0k, hH0n, hcur, dRH, Ne.symm dRH, FDI.fdiCtx, Sem.inner]
  all_goals (repeat' apply And.intro)
  all_goals first
    | rfl | omega | (simp only [js_simp]; omega) | (simp only [fpF]; frame_go' [*, hne, Ne.symm hne, hG1]; done)
    | (js_norm [*, resetMap]; done) | skip

end

end ReactFinishHooks
