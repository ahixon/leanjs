import JSProofs.ReactNoEffects
import JSProofs.Setter
import JSProofs.ReactHostContainer
import JSProofs.Rebase

/-!
# flushLayoutEffects for the click's commit (zippy docs/react-proofs.md)

`flushLayoutEffects()` at status 2 with layout flags in the finished tree: status 0, the transition and priority
cleared and `executionContext |= 4` around `commitLayoutEffectOnFiber(root, finishedWork.alternate, finishedWork)` (a
contract: it writes nothing), restored in the `finally`, then status 3.
-/

open ES ES.M HostRuns Logic
open Std (HashMap)

namespace ReactFlushLayout

/-- What `flushLayoutEffects` writes. -/
def FPL (g : EnvId) (RSI RDSI : ObjId) : Footprint :=
  ⟨[(g, JSStr.ofString "pendingEffectsStatus"), (g, JSStr.ofString "executionContext")],
   [(RSI, .str (JSStr.ofString "T")), (RDSI, .str (JSStr.ofString "p"))], false⟩

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ}

set_option maxRecDepth 40000 in
set_option maxHeartbeats 8000000 in
theorem fle_spec {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t : Value} {s : State}
    {bG : HashMap JSStr Binding} {oG : Option EnvId}
    {bdS bdR bdF bdT bdD bdE bdC : Binding}
    {FR R RSI RDSI fC : ObjId} {av tv pv : Value} {rf sf ec : F64}
    {rfw rfe rfc sfw sfe sfc aw ae ac te tc pe pc : Bool} {KC : Nat}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : KC + 300 ≤ s.fuel)
    (hcode : d.code = FLEGen.flushLayoutEffects_func) (hcls : d.isClassCtor = false) (hmode : d.thisMode = .strict)
    (hG : d.env < s.envs.size) (hGe : Scope.declLike? (s.envEntry d.env) = some (bG, oG))
    (hGS : bG[JSStr.ofString "pendingEffectsStatus"]? = some bdS)
    (hGSv : bdS.value = some (.num (F64.fin false 4503599627370496 (-51)))) (hGSm : bdS.mutable = true)
    (hGR : bG[JSStr.ofString "pendingEffectsRoot"]? = some bdR) (hGRv : bdR.value = some (.obj FR))
    (hGF : bG[JSStr.ofString "pendingFinishedWork"]? = some bdF) (hGFv : bdF.value = some (.obj R))
    (hGT : bG[JSStr.ofString "ReactSharedInternals"]? = some bdT) (hGTv : bdT.value = some (.obj RSI))
    (hGD : bG[JSStr.ofString "ReactDOMSharedInternals"]? = some bdD) (hGDv : bdD.value = some (.obj RDSI))
    (hGE : bG[JSStr.ofString "executionContext"]? = some bdE) (hGEv : bdE.value = some (.num ec)) (hGEm : bdE.mutable = true)
    (hGC : bG[JSStr.ofString "commitLayoutEffectOnFiber"]? = some bdC) (hGCv : bdC.value = some (.obj fC))
    (hR : R < s.heap.size) (hRk : (s.objEntry R).kind.isPlain = true)
    (hRf : (s.objEntry R).props.get? (.str (JSStr.ofString "flags")) = some (.data (.num rf) rfw rfe rfc))
    (hRs : (s.objEntry R).props.get? (.str (JSStr.ofString "subtreeFlags")) = some (.data (.num sf) sfw sfe sfc))
    (hRa : (s.objEntry R).props.get? (.str (JSStr.ofString "alternate")) = some (.data av aw ae ac))
    (hsf : isStrictlyEqual (.num (F64.fin false 0 (-1074)))
      (.num (numberBinOp .bitAnd sf (F64.fin false 4822457999425536 (-39)))) = false)
    (hRSI : RSI < s.heap.size) (hRSIk : (s.objEntry RSI).kind.isPlain = true)
    (hRSIt : (s.objEntry RSI).props.get? (.str (JSStr.ofString "T")) = some (.data tv true te tc))
    (hRDSI : RDSI < s.heap.size) (hRDSIk : (s.objEntry RDSI).kind.isPlain = true)
    (hRDSIp : (s.objEntry RDSI).props.get? (.str (JSStr.ofString "p")) = some (.data pv true pe pc))
    (hCo : fC < s.heap.size) (hCc : ∃ dd, (s.objEntry fC).kind = .func dd)
    (dTD : RSI ≠ RDSI) (dTR : RSI ≠ R) (dDR : RDSI ≠ R) (dTC : RSI ≠ fC) (dDC : RDSI ≠ fC)
    (hC : ∀ w h1, Frame (FPL d.env RSI RDSI) s w → KC ≤ w.fuel →
      WP eng answer (n + 1) h1 (callImpl eng (.obj fC) .undefined #[.obj FR, av, .obj R]) w fun v w' h' =>
        Frame {} w w' ∧ w.fuel ≤ w'.fuel + KC ∧ h' = h1) :
    WP eng answer (n + 2) h (callImpl eng (.obj fo) t #[]) s fun v w h' =>
      v = .undefined ∧ s.fuel ≤ w.fuel + KC + 300 ∧ Frame (FPL d.env RSI RDSI) s w ∧ h' = h := by
  apply wp_callGen FLEGen.flushLayoutEffects_eq (by decide) hlt hk (by omega) hcls hmode
    (by rw [hcode]; rfl) (by rw [hcode]; rfl) (ReactNoEffects.simple_layout d hcode) (by rw [hcode]; rfl)
    (by rw [hcode]; rfl)
  have hpn : d.code.info.fdi.paramNames = #[] := by rw [hcode]; rfl
  have hv : d.code.info.fdi.varNames = #[JSStr.ofString "root", JSStr.ofString "finishedWork",
    JSStr.ofString "rootHasLayoutEffect", JSStr.ofString "previousPriority", JSStr.ofString "prevExecutionContext"] := by
    rw [hcode]; rfl
  have hl : FDI.lexDecls d = #[] := by simp [FDI.lexDecls, hcode, FLEGen.flushLayoutEffects_func, Func.info]
  have ha : d.code.isAsync = false := by rw [hcode]; rfl
  have e1 : d.env ≠ s.envs.size := Nat.ne_of_lt hG
  have e1' : s.envs.size ≠ d.env := Ne.symm e1
  have e4 : d.env < s.envs.size + 1 := Nat.lt_succ_of_lt hG
  have e2 : d.env ≠ s.envs.size + 1 := Nat.ne_of_lt e4
  have e2' : s.envs.size + 1 ≠ d.env := Ne.symm e2
  have e5 : d.env < s.envs.size + 1 + 1 := Nat.lt_succ_of_lt e4
  obtain ⟨dC, hCk⟩ := hCc
  clear hcode
  simp only [FLEGen.flushLayoutEffects]
  js_until [] [e1, e1', e2, e2', e4, e5, hG, hGe, hGS, hGSv, hGSm, hGR, hGRv, hGF, hGFv, hGT, hGTv, hGD, hGDv, hGE, hGEv, hGEm, hGC, hGCv, hR, hRk, hRf, hRs, hRa, hsf, hRSI, hRSIk, hRSIt, hRDSI, hRDSIk, hRDSIp, hCo, dTD, Ne.symm dTD, dTR, Ne.symm dTR, dDR, Ne.symm dDR, dTC, Ne.symm dTC, dDC, Ne.symm dDC, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  refine ⟨by js_norm [CallableC, hCo, hCk, dTC, Ne.symm dTC, dDC, Ne.symm dDC], ?_⟩
  refine wp_mono (hC _ _ ?fr ?fu) ?_
  case fu => simp; omega
  case fr =>
    unfold FPL
    have hdS : (Scope.declLike? (s.envEntry d.env)).isSome = true := by rw [hGe]; rfl
    refine frame_setEnv_with_in ?_ hG ?h1 ?d1 (by simp) _
    case h1 =>
      simp only [setEnv_envEntry_ne _ _ _ _ e1', setProp_envEntry]
      exact setEnv_envEntry_self _ _ _ (by simp; omega)
    case d1 => simp only [declLike_isSome_withBindings]; exact hdS
    refine frame_setEnv_new ?_ (by simp) _
    refine frame_setProp_in ?_ hRDSI (by simp) _
    refine frame_setEnv_new ?_ (by simp) _
    refine frame_setProp_in ?_ hRSI (by simp) _
    refine frame_setEnv_new ?_ (by simp) _
    refine frame_setEnv_with_in ?base hG ?h2 hdS ?in2 _
    case h2 => exact bodyState_envEntry_lt (s := s) (fo := fo) (d := d) (t := t) (args := #[]) _ hG
    case in2 => simp
    case base => frame_go' []
  rintro v1 w1 h1 ⟨hF1, hfu1, rfl⟩
  have hfw1 : 100 ≤ w1.fuel := by simp at hfu1; omega
  have hfr1 : s.fuel ≤ w1.fuel + KC + 20 := by simp at hfu1; omega
  have hE1 := envEntry_frame0 hF1 (e := s.envs.size) (by simp)
  have hEd1 := envEntry_frame0 hF1 (e := d.env) (by simp; omega)
  have hS1 : s.envs.size < w1.envs.size := Nat.lt_of_lt_of_le (by simp) hF1.envs_le
  have hGd1 : d.env < w1.envs.size := Nat.lt_trans hG hS1
  have hT1 := objEntry_frame0 hF1 (o := RSI) (by simpa using hRSI)
  have hD1 := objEntry_frame0 hF1 (o := RDSI) (by simpa using hRDSI)
  have hTl1 : RSI < w1.heap.size := Nat.lt_of_lt_of_le (by simpa using hRSI) hF1.heap_le
  have hDl1 : RDSI < w1.heap.size := Nat.lt_of_lt_of_le (by simpa using hRDSI) hF1.heap_le
  js_until [] [hfw1, hE1, hEd1, hS1, hGd1, hT1, hD1, hTl1, hDl1, e1, e1', e2, e2', e4, e5, hG, hGe, hGS, hGSv, hGSm, hGR, hGRv, hGF, hGFv, hGT, hGTv, hGD, hGDv, hGE, hGEv, hGEm, hGC, hGCv, hR, hRk, hRf, hRs, hRa, hsf, hRSI, hRSIk, hRSIt, hRDSI, hRDSIk, hRDSIp, hCo, dTD, Ne.symm dTD, dTR, Ne.symm dTR, dDR, Ne.symm dDR, dTC, Ne.symm dTC, dDC, Ne.symm dDC, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  refine ⟨by omega, ?_⟩
  unfold FPL
  have hdS : (Scope.declLike? (s.envEntry d.env)).isSome = true := by rw [hGe]; rfl
  refine frame_restore ?_ s
  refine frame_setEnv_with_in ?_ hG ?k1 ?k2 (by simp) _
  case k1 =>
    simp only [setProp_envEntry]
    exact setEnv_envEntry_self _ _ _ hGd1
  case k2 => simp only [declLike_isSome_withBindings]; exact hdS
  refine frame_setProp_in ?_ hRSI (by simp) _
  refine frame_setProp_in ?_ hRDSI (by simp) _
  refine frame_setEnv_with_in ?_ hG ?k3 ?k4 (by simp) _
  case k3 => rw [hEd1]; exact setEnv_envEntry_self _ _ _ (by simp; omega)
  case k4 => simp only [declLike_isSome_withBindings]; exact hdS
  refine frame_then_empty ?_ hF1
  have hdS' : (Scope.declLike? (s.envEntry d.env)).isSome = true := by rw [hGe]; rfl
  refine frame_setEnv_with_in ?_ hG ?h1 ?d1 (by simp) _
  case h1 =>
    simp only [setEnv_envEntry_ne _ _ _ _ e1', setProp_envEntry]
    exact setEnv_envEntry_self _ _ _ (by simp; omega)
  case d1 => simp only [declLike_isSome_withBindings]; exact hdS'
  refine frame_setEnv_new ?_ (by simp) _
  refine frame_setProp_in ?_ hRDSI (by simp) _
  refine frame_setEnv_new ?_ (by simp) _
  refine frame_setProp_in ?_ hRSI (by simp) _
  refine frame_setEnv_new ?_ (by simp) _
  refine frame_setEnv_with_in ?base hG ?h2 hdS' ?in2 _
  case h2 => exact bodyState_envEntry_lt (s := s) (fo := fo) (d := d) (t := t) (args := #[]) _ hG
  case in2 => simp
  case base => frame_go' []


end

end ReactFlushLayout
