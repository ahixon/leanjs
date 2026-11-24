import JSProofs.CMPRGen
import JSProofs.CRWRGen
import JSProofs.ReactCommitRootFn
import JSProofs.Loops3

/-!
# completeRoot and completeRootWhenReady for the click (zippy docs/react-proofs.md)

`completeRoot(root, finishedWork, SyncLane, …)` with no effects pending, outside a render or commit, the root no
longer the work-in-progress root: the pending commit cancelled, `flushPendingEffects()` once (nothing pending), the
pending root, finished work, lanes, transitions and recoverable errors recorded, then `commitRoot` (a contract given
those bindings). `completeRootWhenReady`: not view-transition eligible and nothing suspensey in the tree, so straight
to `completeRoot`.
-/

open ES ES.M HostRuns Logic
open Std (HashMap)
open ReactFacts (BindIs PropIs)

namespace ReactCommitEntry

/-- What `completeRoot` itself writes. -/
def FPE (g : EnvId) (FR : ObjId) : Footprint :=
  ⟨[(g, JSStr.ofString "pendingFinishedWork"), (g, JSStr.ofString "pendingEffectsRoot"),
    (g, JSStr.ofString "pendingEffectsLanes"), (g, JSStr.ofString "pendingPassiveTransitions"),
    (g, JSStr.ofString "pendingRecoverableErrors")], [(FR, .str (JSStr.ofString "cancelPendingCommit"))], false⟩

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ} {HI : σ → Prop}

theorem simple_cr (d : FuncData) (hc : d.code = CMPRGen.completeRoot_func) : FDI.Simple d := by
  constructor <;> rw [hc] <;> try rfl
  simp [CMPRGen.completeRoot_func, Func.params, Func.info]

set_option maxRecDepth 40000 in
set_option maxHeartbeats 8000000 in
theorem cpr_spec {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t : Value} {s : State}
    {bG : HashMap JSStr Binding} {oG : Option EnvId}
    {bPE bS bE bWR bFW bER bEL bPT bRE bCM : Binding}
    {FR A C fPE fCM : ObjId} {lanes re tr di sl ul srl ds es sst : Value} {ec : F64}
    {cw ce cc qw qe qc : Bool} {cv : Value}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d)
    (hcode : d.code = CMPRGen.completeRoot_func) (hcls : d.isClassCtor = false) (hmode : d.thisMode = .strict)
    (hG : d.env < s.envs.size) (hGe : Scope.declLike? (s.envEntry d.env) = some (bG, oG))
    (gPE : bG[JSStr.ofString "flushPendingEffects"]? = some bPE) (gPEv : bPE.value = some (.obj fPE))
    (gS : bG[JSStr.ofString "pendingEffectsStatus"]? = some bS)
    (gSv : bS.value = some (.num (F64.fin false 0 (-1074)))) (gSm : bS.mutable = true)
    (gE : bG[JSStr.ofString "executionContext"]? = some bE) (gEv : bE.value = some (.num ec))
    (hec : numberBinOp .bitAnd ec (F64.fin false 6755399441055744 (-50)) = F64.fin false 0 (-1074))
    (gWR : bG[JSStr.ofString "workInProgressRoot"]? = some bWR) (gWRv : bWR.value = some .null)
    (gFW : bG[JSStr.ofString "pendingFinishedWork"]? = some bFW) (gFWm : bFW.mutable = true)
    (gFWv : bFW.value.isSome = true)
    (gER : bG[JSStr.ofString "pendingEffectsRoot"]? = some bER) (gERm : bER.mutable = true)
    (gERv : bER.value.isSome = true)
    (gEL : bG[JSStr.ofString "pendingEffectsLanes"]? = some bEL) (gELm : bEL.mutable = true)
    (gELv : bEL.value.isSome = true)
    (gPT : bG[JSStr.ofString "pendingPassiveTransitions"]? = some bPT) (gPTm : bPT.mutable = true)
    (gPTv : bPT.value.isSome = true)
    (gRE : bG[JSStr.ofString "pendingRecoverableErrors"]? = some bRE) (gREm : bRE.mutable = true)
    (gREv : bRE.value.isSome = true)
    (gCM : bG[JSStr.ofString "commitRoot"]? = some bCM) (gCMv : bCM.value = some (.obj fCM))
    (hFR : FR < s.heap.size) (hFRk : (s.objEntry FR).kind.isPlain = true)
    (hFRp : (s.objEntry FR).props.get? (.str (JSStr.ofString "cancelPendingCommit")) = some (.data cv true cw cc))
    (hFRc : (s.objEntry FR).props.get? (.str (JSStr.ofString "current")) = some (.data (.obj C) qw qe qc))
    (hAC : A ≠ C)
    (hPEo : fPE < s.heap.size) (hPEc : ∃ dd, (s.objEntry fPE).kind = .func dd)
    (hCMo : fCM < s.heap.size) (hCMc : ∃ dd, (s.objEntry fCM).kind = .func dd)
    (dPF : fPE ≠ FR) (dCF : fCM ≠ FR)
    {K : Nat} (hK : 2 * K + 200 ≤ s.fuel) {P : State → σ → Prop}
    (hPEf : ∀ w h1, Frame (FPE d.env FR) s w → K ≤ w.fuel →
      WP eng answer (n + 1) h1 (callImpl eng (.obj fPE) .undefined #[]) w fun v w' h' =>
        Frame {} w w' ∧ w.fuel ≤ w'.fuel + K ∧ h' = h1)
    (hCMf : ∀ w h1, Frame (FPE d.env FR) s w → HI h1 →
      BindIs w d.env (JSStr.ofString "pendingFinishedWork") (.obj A) →
      BindIs w d.env (JSStr.ofString "pendingEffectsRoot") (.obj FR) →
      BindIs w d.env (JSStr.ofString "pendingEffectsLanes") lanes →
      BindIs w d.env (JSStr.ofString "pendingRecoverableErrors") re →
      ReactFacts.PropHas w FR (JSStr.ofString "cancelPendingCommit") .null → K ≤ w.fuel →
      WP eng answer (n + 1) h1 (callImpl eng (.obj fCM) .undefined #[.obj FR, .obj A, lanes, sl, ul, srl, sst]) w
        fun v w' h' => w.fuel ≤ w'.fuel + K ∧ P w' h') (hHI : HI h) :
    WP eng answer (n + 2) h (callImpl eng (.obj fo) t #[.obj FR, .obj A, lanes, re, tr, di, sl, ul, srl, ds, es, sst])
      s fun v w h' => v = .undefined ∧ s.fuel ≤ w.fuel + 2 * K + 200 ∧ ∃ w0, P w0 h' ∧ Frame {} w0 w := by
  apply wp_callGen CMPRGen.completeRoot_eq (by decide) hlt hk (by omega) hcls hmode
    (by rw [hcode]; rfl) (by rw [hcode]; rfl) (simple_cr d hcode) (by rw [hcode]; rfl) (by rw [hcode]; rfl)
  have hpn : d.code.info.fdi.paramNames = #[JSStr.ofString "root", JSStr.ofString "finishedWork",
    JSStr.ofString "lanes", JSStr.ofString "recoverableErrors", JSStr.ofString "transitions",
    JSStr.ofString "didIncludeRenderPhaseUpdate", JSStr.ofString "spawnedLane", JSStr.ofString "updatedLanes",
    JSStr.ofString "suspendedRetryLanes", JSStr.ofString "didSkipSuspendedSiblings", JSStr.ofString "exitStatus",
    JSStr.ofString "suspendedState"] := by rw [hcode]; rfl
  have hv : d.code.info.fdi.varNames = #[] := by rw [hcode]; rfl
  have hl : FDI.lexDecls d = #[] := by simp [FDI.lexDecls, hcode, CMPRGen.completeRoot_func, Func.info]
  have ha : d.code.isAsync = false := by rw [hcode]; rfl
  have e1 : d.env ≠ s.envs.size := Nat.ne_of_lt hG
  have e1' : s.envs.size ≠ d.env := Ne.symm e1
  have e4 : d.env < s.envs.size + 1 := Nat.lt_succ_of_lt hG
  obtain ⟨dPE, hPEk⟩ := hPEc
  clear hcode
  simp only [CMPRGen.completeRoot]
  js_until [] [e1, e1', e4, hG, hGe, hFR, hFRk, hFRp, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  refine ⟨by js_norm [CallableC, hPEo, hPEk, dPF, Ne.symm dPF], ?_⟩
  refine wp_mono (hPEf _ _ ?fr1 (by simp [State.withFuel]; omega)) ?_
  case fr1 =>
    unfold FPE
    refine frame_withFuel ?_ _
    refine frame_setProp_in ?_ hFR (by simp) _
    frame_go' []
  rintro v1 w1 h1 ⟨hF1, hfu1, rfl⟩
  have hfw1 : K + 150 ≤ w1.fuel := by simp [State.withFuel] at hfu1; omega
  have hE1 := envEntry_frame0 hF1 (e := s.envs.size) (by simp [State.withFuel])
  have hEd1 := envEntry_frame0 hF1 (e := d.env) (by simp [State.withFuel]; omega)
  have hS1 : s.envs.size < w1.envs.size := Nat.lt_of_lt_of_le (by simp [State.withFuel]) hF1.envs_le
  have hGd1 : d.env < w1.envs.size := Nat.lt_trans hG hS1
  have hob1 : ∀ o, o < s.heap.size → w1.objEntry o = _ := fun o ho => objEntry_frame0 hF1 (by simpa [State.withFuel] using ho)
  have hlt1 : ∀ o, o < s.heap.size → o < w1.heap.size := fun o ho => Nat.lt_of_lt_of_le (by simpa [State.withFuel] using ho) hF1.heap_le
  obtain ⟨dCM, hCMk⟩ := hCMc
  have hAC' : isStrictlyEqual (.obj A) (.obj C) = false := by simp [isStrictlyEqual, sameValue, hAC]
  js_until [] [hfw1, hE1, hEd1, hS1, hGd1, hob1 FR hFR, hob1 fCM hCMo, hlt1 FR hFR, hlt1 fCM hCMo, gPE, gPEv, gS, gSv, gSm, gE, gEv, hec, gWR, gWRv, gFW, gFWm, gFWv, gER, gERm, gERv, gEL, gELm, gELv, gPT, gPTm, gPTv, gRE, gREm, gREv, gCM, gCMv, hFRc, hAC, hAC', hCMk, dCF, Ne.symm dCF, e1, e1', e4, hG, hGe, hFR, hFRk, hFRp, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  refine ⟨by js_norm [CallableC, hlt1 fCM hCMo, hob1 fCM hCMo, hCMk, dCF, Ne.symm dCF], ?_⟩
  refine wp_mono (hCMf _ _ ?fr2 hHI ?b1 ?b2 ?b3 ?b4 ?b5 (by simp; omega)) ?_
  case fr2 =>
    unfold FPE
    refine frame_setEnv_split (frame_setEnv_with_in ?_ hG (setEnv_envEntry_self _ _ _ (by first | exact hGd1 | (simp; omega))) (by simp only [declLike_isSome_withBindings]; rw [hGe]; rfl) (by simp) _)
    refine frame_setEnv_split (frame_setEnv_with_in ?_ hG (setEnv_envEntry_self _ _ _ (by first | exact hGd1 | (simp; omega))) (by simp only [declLike_isSome_withBindings]; rw [hGe]; rfl) (by simp) _)
    refine frame_setEnv_split (frame_setEnv_with_in ?_ hG (setEnv_envEntry_self _ _ _ (by first | exact hGd1 | (simp; omega))) (by simp only [declLike_isSome_withBindings]; rw [hGe]; rfl) (by simp) _)
    refine frame_setEnv_split (frame_setEnv_with_in ?_ hG (setEnv_envEntry_self _ _ _ (by first | exact hGd1 | (simp; omega))) (by simp only [declLike_isSome_withBindings]; rw [hGe]; rfl) (by simp) _)
    refine frame_setEnv_with_in ?_ hG ?q1 (by rw [hGe]; rfl) (by simp) _
    case q1 =>
      rw [hEd1]; simp only [State.withFuel, setProp_envEntry]
      exact bodyState_envEntry_lt (s := s) (fo := fo) (d := d) (t := t)
        (args := #[.obj FR, .obj A, lanes, re, tr, di, sl, ul, srl, ds, es, sst]) _ hG
    refine frame_then_empty ?_ hF1
    refine frame_withFuel ?_ _
    refine frame_setProp_in ?_ hFR (by simp) _
    frame_go' []
  case b5 =>
    refine ⟨true, cw, cc, ?_⟩
    simp only [js_simp, hob1 FR hFR]
    simp [hFR]
  case b1 =>
    unfold BindIs
    rw [setEnv_envEntry_self _ _ _ (by first | exact hGd1 | (simp; omega))]
    simp only [declLike_withBindings', hGe, Option.map]
    simp [Std.HashMap.getElem?_modify, gFW, gFWm]
  case b2 =>
    unfold BindIs
    rw [setEnv_envEntry_self _ _ _ (by first | exact hGd1 | (simp; omega))]
    simp only [declLike_withBindings', hGe, Option.map]
    simp [Std.HashMap.getElem?_modify, gER, gERm]
  case b3 =>
    unfold BindIs
    rw [setEnv_envEntry_self _ _ _ (by first | exact hGd1 | (simp; omega))]
    simp only [declLike_withBindings', hGe, Option.map]
    simp [Std.HashMap.getElem?_modify, gEL, gELm]
  case b4 =>
    unfold BindIs
    rw [setEnv_envEntry_self _ _ _ (by first | exact hGd1 | (simp; omega))]
    simp only [declLike_withBindings', hGe, Option.map]
    simp [Std.HashMap.getElem?_modify, gRE, gREm]
  rintro v2 w2 h2 ⟨hfu2, hP⟩
  js_until [] []
  exact ⟨by simp [State.withFuel, bodyState, entryState] at hfu1 hfu2 ⊢; omega, w2, hP, (by first | exact frame_refl _ _ | exact frame_restore (frame_refl _ _) _ | exact frame_withFuel (frame_refl _ _) _ | exact frame_restore (frame_withFuel (frame_refl _ _) _) _ | exact frame_withFuel (frame_restore (frame_refl _ _) _) _)⟩


theorem simple_crw (d : FuncData) (hc : d.code = CRWRGen.completeRootWhenReady_func) : FDI.Simple d := by
  constructor <;> rw [hc] <;> try rfl
  simp [CRWRGen.completeRootWhenReady_func, Func.params, Func.info]

set_option maxRecDepth 40000 in
set_option maxHeartbeats 8000000 in
theorem crw_spec {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t : Value} {s : State}
    {bG : HashMap JSStr Binding} {oG : Option EnvId} {bCR : Binding}
    {FR A fCR : ObjId} {x1 x2 x3 x4 x5 x6 x7 c1 c2 c3 tv : Value} {sf : F64}
    {tw te tc sw se sc : Bool}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d)
    (hcode : d.code = CRWRGen.completeRootWhenReady_func) (hcls : d.isClassCtor = false)
    (hmode : d.thisMode = .strict)
    (hG : d.env < s.envs.size) (hGe : Scope.declLike? (s.envEntry d.env) = some (bG, oG))
    (gCR : bG[JSStr.ofString "completeRoot"]? = some bCR) (gCRv : bCR.value = some (.obj fCR))
    (hFR : FR < s.heap.size) (hFRk : (s.objEntry FR).kind.isPlain = true)
    (hFRt : (s.objEntry FR).props.get? (.str (JSStr.ofString "timeoutHandle")) = some (.data tv true te tc))
    (hA : A < s.heap.size) (hAk : (s.objEntry A).kind.isPlain = true)
    (hAs : (s.objEntry A).props.get? (.str (JSStr.ofString "subtreeFlags")) = some (.data (.num sf) sw se sc))
    (hsf1 : numberBinOp .bitAnd sf (F64.fin false 4503599627370496 (-39)) = F64.fin false 0 (-1074))
    (hsf2 : isStrictlyEqual (.num (F64.fin false 4505798650626048 (-28)))
      (.num (numberBinOp .bitAnd sf (F64.fin false 4505798650626048 (-28)))) = false)
    (hCRo : fCR < s.heap.size) (hCRc : ∃ dd, (s.objEntry fCR).kind = .func dd) (dCF : fCR ≠ FR)
    (dFA : FR ≠ A)
    {K : Nat} (hK : K + 100 ≤ s.fuel) {P : State → σ → Prop}
    (hCRf : ∀ w h1, Frame ⟨[], [(FR, .str (JSStr.ofString "timeoutHandle"))], false⟩ s w → HI h1 →
      ReactFacts.PropHas w FR (JSStr.ofString "timeoutHandle") (.num (F64.fin false 4503599627370496 (-52)).neg) →
      K ≤ w.fuel →
      WP eng answer (n + 1) h1 (callImpl eng (.obj fCR) .undefined #[.obj FR, .obj A,
        .num (F64.fin false 4503599627370496 (-51)), x1, x2, x3, x4, x5, x6, x7,
        .num (F64.fin false 5629499534213120 (-50)), .null]) w
        fun v w' h' => w.fuel ≤ w'.fuel + K ∧ P w' h') (hHI : HI h) :
    WP eng answer (n + 2) h (callImpl eng (.obj fo) t #[.obj FR, .obj A, x1, x2, x3,
      .num (F64.fin false 4503599627370496 (-51)), x4, x5, x6, x7, .num (F64.fin false 5629499534213120 (-50)),
      c1, c2, c3]) s fun v w h' => v = .undefined ∧ s.fuel ≤ w.fuel + K + 100 ∧ ∃ w0, P w0 h' ∧ Frame {} w0 w := by
  apply wp_callGen CRWRGen.completeRootWhenReady_eq (by decide) hlt hk (by omega) hcls hmode
    (by rw [hcode]; rfl) (by rw [hcode]; rfl) (simple_crw d hcode) (by rw [hcode]; rfl) (by rw [hcode]; rfl)
  have hpn : d.code.info.fdi.paramNames = #[JSStr.ofString "root", JSStr.ofString "finishedWork",
    JSStr.ofString "recoverableErrors", JSStr.ofString "transitions", JSStr.ofString "didIncludeRenderPhaseUpdate",
    JSStr.ofString "lanes", JSStr.ofString "spawnedLane", JSStr.ofString "updatedLanes",
    JSStr.ofString "suspendedRetryLanes", JSStr.ofString "didSkipSuspendedSiblings", JSStr.ofString "exitStatus",
    JSStr.ofString "suspendedCommitReason", JSStr.ofString "completedRenderStartTime",
    JSStr.ofString "completedRenderEndTime"] := by rw [hcode]; rfl
  have hv : d.code.info.fdi.varNames = #[JSStr.ofString "subtreeFlags", JSStr.ofString "isViewTransitionEligible"] := by
    rw [hcode]; rfl
  have hl : FDI.lexDecls d = #[] := by simp [FDI.lexDecls, hcode, CRWRGen.completeRootWhenReady_func, Func.info]
  have ha : d.code.isAsync = false := by rw [hcode]; rfl
  have e1 : d.env ≠ s.envs.size := Nat.ne_of_lt hG
  have e1' : s.envs.size ≠ d.env := Ne.symm e1
  have e4 : d.env < s.envs.size + 1 := Nat.lt_succ_of_lt hG
  obtain ⟨dCR, hCRk⟩ := hCRc
  clear hcode
  simp only [CRWRGen.completeRootWhenReady]
  js_until [] [e1, e1', e4, hG, hGe, gCR, gCRv, hFR, hFRk, hFRt, hA, hAk, hAs, hsf1, hsf2, hCRo, hCRk, dCF, Ne.symm dCF, dFA, Ne.symm dFA, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  refine ⟨by js_norm [CallableC, hCRo, hCRk, dCF, Ne.symm dCF], ?_⟩
  refine wp_mono (hCRf _ _ ?fr hHI ?th (by simp; omega)) ?_
  case th =>
    refine ⟨true, te, tc, ?_⟩
    simp only [js_simp]
    simp [hFR]
  case fr =>
    refine frame_setEnv_new ?_ (Nat.le_refl _) _
    refine frame_setProp_in ?_ hFR (by simp) _
    frame_go' []
  rintro v1 w1 h1 ⟨hfu1, hP⟩
  js_until [] []
  exact ⟨by simp [bodyState, entryState] at hfu1 ⊢; omega, w1, hP, (by first | exact frame_refl _ _ | exact frame_restore (frame_refl _ _) _ | exact frame_withFuel (frame_refl _ _) _ | exact frame_restore (frame_withFuel (frame_refl _ _) _) _ | exact frame_withFuel (frame_restore (frame_refl _ _) _) _)⟩

end

end ReactCommitEntry
