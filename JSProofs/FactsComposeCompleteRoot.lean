import JSProofs.FactsComposeCommitRoot
import JSProofs.ReactCommitEntry

/-! completeRoot with commitRoot and flushPendingEffects, and completeRootWhenReady with completeRoot, composed in Lean: commitRoot by `cmr_comp`, flushPendingEffects by `pending_none`. -/

facts_form ReactCommitEntry.cpr_spec

namespace ReactCommitEntry
open ES Logic ReactFacts

facts_compose cpr_comp {EA XA dom RSI RDSI : ObjId} {kP : JSStr} {R1 R2 : State → σ → Prop} {gP : EnvId}
    {bFSR bEn : Binding} {fEn : ObjId} := cpr_spec
    (n := n + 10) (K := 29400)
    (lanes := .num (F64.fin false 4503599627370496 (-51))) (re := .null)
    (sl := .num (F64.fin false 0 (-1074))) (ul := .num (F64.fin false 0 (-1074))) (srl := .num (F64.fin false 0 (-1074)))
    (P := fun w h => (∃ w0, ((∃ w0 : State, (∃ w0 h0, R1 w0 h0) ∧ (∃ w0, R2 w0 h) ∧ HI h) ∧
        ReactSpawned.Done w0 d.env oG FR bFSR bEn fEn) ∧ Frame {} w0 w) ∧
      Frame ((FPE d.env FR).union
        ((((((ReactCommitRootFn.FPC d.env FR RSI RDSI).union (ReactMarkFinished.FPM FR EA XA)).union
          (ReactBeforeMutation.FB d.env)).union
          (((ReactFlushMutation.FPRE d.env RSI RDSI).union ((ReactCommitRoot.F0 d.env).union
            (Footprint.union ⟨[(d.env, JSStr.ofString "offscreenDirectParentIsHidden")], [], false⟩
              ⟨[(d.env, JSStr.ofString "viewTransitionMutationContext")], [(dom, .str kP)], false⟩))).union
            ⟨[(d.env, JSStr.ofString "selectionInformation"), (d.env, JSStr.ofString "eventsEnabled"),
              (d.env, JSStr.ofString "_enabled")], [(FR, .str (JSStr.ofString "current"))], false⟩)).union
          (ReactFlushLayout.FPL d.env RSI RDSI)).union
          ((ReactSpawned.FPA d.env gP FR).union (ReactEnsureCall.fpEn d.env)))) s w)
  | hPEf => ReactNoEffects.pending_none with u_d.env = d.env by
      rintro v w' h' ⟨-, hF, hfu, rfl⟩
      exact ⟨hF, by omega, rfl⟩
  | hCMf => ReactCommitRootFn.cmr_comp (EA := EA) (XA := XA) (dom := dom) (kP := kP) (R1 := R1) (R2 := R2)
      (gP := gP) (bFSR := bFSR) (bEn := bEn) (fEn := fEn) (RSI := RSI) (RDSI := RDSI) (oG := oG)
      with u_d.env = d.env by
      have he := hob.get.2
      rintro v w' h' ⟨-, hfu, hP, hFc⟩
      rw [he] at hP hFc
      exact ⟨by omega, hP, frame_trans ‹Frame _ s _› hFc⟩

facts_form crw_spec

facts_compose crw_comp {EA XA dom RSI RDSI : ObjId} {kP : JSStr} {R1 R2 : State → σ → Prop} {gP : EnvId}
    {bFSR bEn : Binding} {fEn : ObjId} := crw_spec
    (n := n + 11) (K := 59400) (x1 := .null)
    (x4 := .num (F64.fin false 0 (-1074))) (x5 := .num (F64.fin false 0 (-1074))) (x6 := .num (F64.fin false 0 (-1074)))
    (P := fun w h => (∃ s1 w0, Frame ⟨[], [(FR, .str (JSStr.ofString "timeoutHandle"))], false⟩ s s1 ∧
        ((∃ w1, ((∃ w0 : State, (∃ w0 h0, R1 w0 h0) ∧ (∃ w0, R2 w0 h) ∧ HI h) ∧
          ReactSpawned.Done w1 d.env oG FR bFSR bEn fEn) ∧ Frame {} w1 w0) ∧
          Frame ((FPE d.env FR).union ((((((ReactCommitRootFn.FPC d.env FR RSI RDSI).union (ReactMarkFinished.FPM FR EA XA)).union
          (ReactBeforeMutation.FB d.env)).union
          (((ReactFlushMutation.FPRE d.env RSI RDSI).union ((ReactCommitRoot.F0 d.env).union
            (Footprint.union ⟨[(d.env, JSStr.ofString "offscreenDirectParentIsHidden")], [], false⟩
              ⟨[(d.env, JSStr.ofString "viewTransitionMutationContext")], [(dom, .str kP)], false⟩))).union
            ⟨[(d.env, JSStr.ofString "selectionInformation"), (d.env, JSStr.ofString "eventsEnabled"),
              (d.env, JSStr.ofString "_enabled")], [(FR, .str (JSStr.ofString "current"))], false⟩)).union
          (ReactFlushLayout.FPL d.env RSI RDSI)).union
          ((ReactSpawned.FPA d.env gP FR).union (ReactEnsureCall.fpEn d.env)))) s1 w0) ∧ Frame {} w0 w) ∧
      Frame (Footprint.union ⟨[], [(FR, .str (JSStr.ofString "timeoutHandle"))], false⟩
        (((FPE d.env FR).union ((((((ReactCommitRootFn.FPC d.env FR RSI RDSI).union (ReactMarkFinished.FPM FR EA XA)).union
          (ReactBeforeMutation.FB d.env)).union
          (((ReactFlushMutation.FPRE d.env RSI RDSI).union ((ReactCommitRoot.F0 d.env).union
            (Footprint.union ⟨[(d.env, JSStr.ofString "offscreenDirectParentIsHidden")], [], false⟩
              ⟨[(d.env, JSStr.ofString "viewTransitionMutationContext")], [(dom, .str kP)], false⟩))).union
            ⟨[(d.env, JSStr.ofString "selectionInformation"), (d.env, JSStr.ofString "eventsEnabled"),
              (d.env, JSStr.ofString "_enabled")], [(FR, .str (JSStr.ofString "current"))], false⟩)).union
          (ReactFlushLayout.FPL d.env RSI RDSI)).union
          ((ReactSpawned.FPA d.env gP FR).union (ReactEnsureCall.fpEn d.env)))).union {})) s w)
  | hCRf => cpr_comp (EA := EA) (XA := XA) (dom := dom) (kP := kP) (R1 := R1) (R2 := R2) (gP := gP) (bFSR := bFSR)
      (bEn := bEn) (fEn := fEn) (RSI := RSI) (RDSI := RDSI) (oG := oG) with u_d.env = d.env by
      have he := hob.get.2
      rintro v w' h' ⟨-, hfu, w0, hPc, hF0⟩
      rw [he] at hPc
      have hw := ‹Frame _ s w›
      exact ⟨by omega, ⟨w, w0, hw, hPc, hF0⟩, frame_trans hw (frame_trans hPc.2 hF0)⟩

end ReactCommitEntry
