import JSProofs.CMRGen
import JSProofs.Setter
import JSProofs.ReactHostContainer
import JSProofs.Rebase
import JSProofs.ReactFacts

/-!
# commitRoot for the click (zippy docs/react-proofs.md)

`commitRoot(root, finishedWork, SyncLane, …)` with no lanes left: `markRootFinished`, no transition types, no
passive effects (the callback node and priority cleared), the before-mutation pass (the tree has Update flags) with
the transition and priority cleared and `executionContext |= 4` around it, status 1, then `flushMutationEffects()`,
`flushLayoutEffects()` and `flushSpawnedWork()`. The callees are contracts: each given the frame accumulated so far
(`F_k`), returning its own and the next; the passes hand each other what the next needs (`Q1`, `Q2`).
-/

open ES ES.M HostRuns Logic
open Std (HashMap)
open ReactFacts (BindIs PropIs SelInfo PropHas)

namespace ReactCommitRootFn

/-- What `commitRoot` itself writes. -/
def FPC (g : EnvId) (FR RSI RDSI : ObjId) : Footprint :=
  ⟨[(g, JSStr.ofString "pendingEffectsRemainingLanes"), (g, JSStr.ofString "pendingViewTransitionEvents"),
    (g, JSStr.ofString "pendingTransitionTypes"), (g, JSStr.ofString "shouldStartViewTransition"),
    (g, JSStr.ofString "executionContext"), (g, JSStr.ofString "pendingEffectsStatus")],
   [(FR, .str (JSStr.ofString "callbackNode")), (FR, .str (JSStr.ofString "callbackPriority")),
    (RSI, .str (JSStr.ofString "T")), (RDSI, .str (JSStr.ofString "p"))], false⟩

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ}

theorem simple (d : FuncData) (hc : d.code = CMRGen.commitRoot_func) : FDI.Simple d := by
  constructor <;> rw [hc] <;> try rfl
  simp [CMRGen.commitRoot_func, Func.params, Func.info]

set_option maxRecDepth 40000 in
set_option maxHeartbeats 8000000 in
theorem cmr_spec {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t : Value} {s : State}
    {bG : HashMap JSStr Binding} {oG : Option EnvId}
    {bRL bCU bM bVE bTT bSV bT bD bE bB bS bME bLE bSP : Binding}
    {FR R RSI RDSI fM fB fME fLE fSP E : ObjId} {sl ul srl sst tv pv ev0 : Value} {rs rf ec : F64}
    {rlw rle rlc rcw rce rcc rsw rse rsc rfw rfe rfc cne cnc cpe cpc te tc pe pc : Bool} {cnw cpw : Value}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d)
    (hcode : d.code = CMRGen.commitRoot_func) (hcls : d.isClassCtor = false) (hmode : d.thisMode = .strict)
    (hG : d.env < s.envs.size) (hGe : Scope.declLike? (s.envEntry d.env) = some (bG, oG))
    (gRL : bG[JSStr.ofString "pendingEffectsRemainingLanes"]? = some bRL) (gRLm : bRL.mutable = true)
    (gRLv : bRL.value.isSome = true)
    (gCU : bG[JSStr.ofString "concurrentlyUpdatedLanes"]? = some bCU)
    (gCUv : bCU.value = some (.num (F64.fin false 0 (-1074))))
    (gM : bG[JSStr.ofString "markRootFinished"]? = some bM) (gMv : bM.value = some (.obj fM))
    (gVE : bG[JSStr.ofString "pendingViewTransitionEvents"]? = some bVE) (gVEm : bVE.mutable = true)
    (gVEv : bVE.value.isSome = true)
    (gTT : bG[JSStr.ofString "pendingTransitionTypes"]? = some bTT) (gTTm : bTT.mutable = true)
    (gTTv : bTT.value.isSome = true)
    (gSV : bG[JSStr.ofString "shouldStartViewTransition"]? = some bSV) (gSVm : bSV.mutable = true)
    (gSVv : bSV.value.isSome = true)
    (gT : bG[JSStr.ofString "ReactSharedInternals"]? = some bT) (gTv : bT.value = some (.obj RSI))
    (gD : bG[JSStr.ofString "ReactDOMSharedInternals"]? = some bD) (gDv : bD.value = some (.obj RDSI))
    (gE : bG[JSStr.ofString "executionContext"]? = some bE) (gEv : bE.value = some (.num ec)) (gEm : bE.mutable = true)
    (gB : bG[JSStr.ofString "commitBeforeMutationEffects"]? = some bB) (gBv : bB.value = some (.obj fB))
    (gS : bG[JSStr.ofString "pendingEffectsStatus"]? = some bS) (gSm : bS.mutable = true)
    (gSv : bS.value.isSome = true)
    (gME : bG[JSStr.ofString "flushMutationEffects"]? = some bME) (gMEv : bME.value = some (.obj fME))
    (gLE : bG[JSStr.ofString "flushLayoutEffects"]? = some bLE) (gLEv : bLE.value = some (.obj fLE))
    (gSP : bG[JSStr.ofString "flushSpawnedWork"]? = some bSP) (gSPv : bSP.value = some (.obj fSP))
    (hR : R < s.heap.size) (hRk : (s.objEntry R).kind.isPlain = true)
    (hRl : (s.objEntry R).props.get? (.str (JSStr.ofString "lanes")) =
      some (.data (.num (F64.fin false 0 (-1074))) rlw rle rlc))
    (hRc : (s.objEntry R).props.get? (.str (JSStr.ofString "childLanes")) =
      some (.data (.num (F64.fin false 0 (-1074))) rcw rce rcc))
    (hRs : (s.objEntry R).props.get? (.str (JSStr.ofString "subtreeFlags")) = some (.data (.num rs) rsw rse rsc))
    (hRf : (s.objEntry R).props.get? (.str (JSStr.ofString "flags")) = some (.data (.num rf) rfw rfe rfc))
    (hrs : numberBinOp .bitAnd rs (F64.fin false 5638295627235328 (-39)) = F64.fin false 0 (-1074))
    (hrf : numberBinOp .bitAnd rf (F64.fin false 5638295627235328 (-39)) = F64.fin false 0 (-1074))
    (hrs2 : isStrictlyEqual (.num (F64.fin false 0 (-1074)))
      (.num (numberBinOp .bitAnd rs (F64.fin false 7629511185137664 (-39)))) = false)
    (hFR : FR < s.heap.size) (hFRk : (s.objEntry FR).kind.isPlain = true)
    (hFRn : (s.objEntry FR).props.get? (.str (JSStr.ofString "callbackNode")) = some (.data cnw true cne cnc))
    (hFRp : (s.objEntry FR).props.get? (.str (JSStr.ofString "callbackPriority")) = some (.data cpw true cpe cpc))
    (hRSI : RSI < s.heap.size) (hRSIk : (s.objEntry RSI).kind.isPlain = true)
    (hRSIt : (s.objEntry RSI).props.get? (.str (JSStr.ofString "T")) = some (.data tv true te tc))
    (hRDSI : RDSI < s.heap.size) (hRDSIk : (s.objEntry RDSI).kind.isPlain = true)
    (hRDSIp : (s.objEntry RDSI).props.get? (.str (JSStr.ofString "p")) = some (.data pv true pe pc))
    (hMo : fM < s.heap.size) (hMc : ∃ dd, (s.objEntry fM).kind = .func dd)
    (hBo : fB < s.heap.size) (hBc : ∃ dd, (s.objEntry fB).kind = .func dd)
    (hMEo : fME < s.heap.size) (hMEc : ∃ dd, (s.objEntry fME).kind = .func dd)
    (hLEo : fLE < s.heap.size) (hLEc : ∃ dd, (s.objEntry fLE).kind = .func dd)
    (hSPo : fSP < s.heap.size) (hSPc : ∃ dd, (s.objEntry fSP).kind = .func dd)
    (dRF : R ≠ FR) (dTD : RSI ≠ RDSI) (dTF : RSI ≠ FR) (dDF : RDSI ≠ FR) (dTR : RSI ≠ R) (dDR : RDSI ≠ R)
    (dBF : fB ≠ FR) (dBT : fB ≠ RSI) (dBD : fB ≠ RDSI) (dMF : fME ≠ FR) (dMT : fME ≠ RSI) (dMD : fME ≠ RDSI)
    (dLF : fLE ≠ FR) (dLT : fLE ≠ RSI) (dLD : fLE ≠ RDSI) (dSF : fSP ≠ FR) (dST : fSP ≠ RSI) (dSD : fSP ≠ RDSI)
    {K : Nat} (hK : 5 * K + 400 ≤ s.fuel)
    {fpM : Footprint}
    (hMf : ∀ w h1, Frame (FPC d.env FR RSI RDSI) s w → K ≤ w.fuel →
      WP eng answer (n + 1) h1 (callImpl eng (.obj fM) .undefined #[.obj FR, .num (F64.fin false 4503599627370496 (-51)),
        .num (F64.fin false 0 (-1074)), sl, ul, srl]) w fun v w' h' =>
        Frame fpM w w' ∧ Frame ((FPC d.env FR RSI RDSI).union fpM) s w' ∧ w.fuel ≤ w'.fuel + K ∧ h' = h1 ∧
        PropHas w' FR (JSStr.ofString "pendingLanes") (.num (F64.fin false 0 (-1074))))
    (hfpM : ∀ p, p ∈ fpM.binds → p.1 ≠ d.env ∧ p.1 < s.envs.size)
    (hfpMp : ∀ p, p ∈ fpM.props → p.1 ≠ R ∧ p.1 ≠ RSI ∧ p.1 ≠ RDSI ∧ p.1 ≠ fB ∧ p.1 ≠ fME ∧ p.1 ≠ fLE ∧ p.1 ≠ fSP ∧
      (p.1 = FR → p.2 ≠ .str (JSStr.ofString "callbackNode") ∧ p.2 ≠ .str (JSStr.ofString "callbackPriority")))
    {fpB fpME fpLE fpSP : Footprint} {Q1 Q2 Q3 : State → σ → Prop}
    (hBf : ∀ w h1, Frame ((FPC d.env FR RSI RDSI).union fpM) s w → K ≤ w.fuel →
      WP eng answer (n + 1) h1 (callImpl eng (.obj fB) .undefined #[.obj FR, .obj R,
        .num (F64.fin false 4503599627370496 (-51))]) w fun v w' h' =>
        Frame fpB w w' ∧ Frame (((FPC d.env FR RSI RDSI).union fpM).union fpB) s w' ∧ w.fuel ≤ w'.fuel + K ∧ h' = h1 ∧
        SelInfo w' d.env E ev0 s.heap.size)
    (hfpB : ∀ p, p ∈ fpB.binds → p.1 < s.envs.size ∧ (p.1 = d.env → p.2 ∉ [JSStr.ofString "executionContext",
      JSStr.ofString "pendingEffectsStatus", JSStr.ofString "shouldStartViewTransition",
      JSStr.ofString "flushMutationEffects", JSStr.ofString "flushLayoutEffects", JSStr.ofString "flushSpawnedWork",
      JSStr.ofString "ReactSharedInternals", JSStr.ofString "ReactDOMSharedInternals", JSStr.ofString "pendingViewTransitionEvents", JSStr.ofString "pendingTransitionTypes"]))
    (hfpBp : ∀ p, p ∈ fpB.props → p.1 ≠ RSI ∧ p.1 ≠ RDSI ∧ p.1 ≠ fME ∧ p.1 ≠ fLE ∧ p.1 ≠ fSP ∧
      p ≠ (FR, .str (JSStr.ofString "pendingLanes")))
    (hMEf : ∀ w h1, Frame (((FPC d.env FR RSI RDSI).union fpM).union fpB) s w →
      BindIs w d.env (JSStr.ofString "pendingEffectsStatus") (.num (F64.fin false 4503599627370496 (-52))) →
      BindIs w d.env (JSStr.ofString "executionContext") (.num ec) →
      PropIs w RSI (JSStr.ofString "T") tv → PropIs w RDSI (JSStr.ofString "p") pv →
      SelInfo w d.env E ev0 s.heap.size → K ≤ w.fuel →
      WP eng answer (n + 1) h1 (callImpl eng (.obj fME) .undefined #[]) w fun v w' h' =>
        Frame fpME w w' ∧ Frame ((((FPC d.env FR RSI RDSI).union fpM).union fpB).union fpME) s w' ∧ w.fuel ≤ w'.fuel + K ∧ Q1 w' h')
    (hfpME : ∀ p, p ∈ fpME.binds → p.1 < s.envs.size ∧ (p.1 = d.env → p.2 ∉ [JSStr.ofString "flushLayoutEffects",
      JSStr.ofString "flushSpawnedWork", JSStr.ofString "pendingViewTransitionEvents", JSStr.ofString "pendingTransitionTypes"]))
    (hfpMEp : ∀ p, p ∈ fpME.props → p.1 ≠ fLE ∧ p.1 ≠ fSP ∧ p ≠ (FR, .str (JSStr.ofString "pendingLanes")))
    (hLEf : ∀ w h1, Frame ((((FPC d.env FR RSI RDSI).union fpM).union fpB).union fpME) s w → Q1 w h1 → K ≤ w.fuel →
      WP eng answer (n + 1) h1 (callImpl eng (.obj fLE) .undefined #[]) w fun v w' h' =>
        Frame fpLE w w' ∧ Frame (((((FPC d.env FR RSI RDSI).union fpM).union fpB).union fpME).union fpLE) s w' ∧ w.fuel ≤ w'.fuel + K ∧ Q2 w' h')
    (hfpLE : ∀ p, p ∈ fpLE.binds → p.1 < s.envs.size ∧ (p.1 = d.env → p.2 ∉ [JSStr.ofString "flushSpawnedWork",
      JSStr.ofString "pendingViewTransitionEvents", JSStr.ofString "pendingTransitionTypes"]))
    (hfpLEp : ∀ p, p ∈ fpLE.props → p.1 ≠ fSP ∧ p ≠ (FR, .str (JSStr.ofString "pendingLanes")))
    (hSPf : ∀ w h1, Frame (((((FPC d.env FR RSI RDSI).union fpM).union fpB).union fpME).union fpLE) s w → Q2 w h1 →
      PropHas w FR (JSStr.ofString "pendingLanes") (.num (F64.fin false 0 (-1074))) →
      BindIs w d.env (JSStr.ofString "pendingViewTransitionEvents") .null →
      BindIs w d.env (JSStr.ofString "pendingTransitionTypes") .null → K ≤ w.fuel →
      WP eng answer (n + 1) h1 (callImpl eng (.obj fSP) .undefined #[]) w fun v w' h' =>
        Frame ((((((FPC d.env FR RSI RDSI).union fpM).union fpB).union fpME).union fpLE).union fpSP) s w' ∧ w.fuel ≤ w'.fuel + K ∧ Q3 w' h') :
    WP eng answer (n + 2) h (callImpl eng (.obj fo) t #[.obj FR, .obj R, .num (F64.fin false 4503599627370496 (-51)),
      sl, ul, srl, sst]) s fun v w h' =>
      v = .undefined ∧ s.fuel ≤ w.fuel + 5 * K + 400 ∧ (∃ w0, Q3 w0 h' ∧ Frame {} w0 w) ∧ Frame ((((((FPC d.env FR RSI RDSI).union fpM).union fpB).union fpME).union fpLE).union fpSP) s w := by
  apply wp_callGen CMRGen.commitRoot_eq (by decide) hlt hk (by omega) hcls hmode
    (by rw [hcode]; rfl) (by rw [hcode]; rfl) (simple d hcode) (by rw [hcode]; rfl) (by rw [hcode]; rfl)
  have hpn : d.code.info.fdi.paramNames = #[JSStr.ofString "root", JSStr.ofString "finishedWork",
    JSStr.ofString "lanes", JSStr.ofString "spawnedLane", JSStr.ofString "updatedLanes",
    JSStr.ofString "suspendedRetryLanes", JSStr.ofString "suspendedState"] := by rw [hcode]; rfl
  have hv : d.code.info.fdi.varNames = #[JSStr.ofString "remainingLanes"] := by rw [hcode]; rfl
  have hl : FDI.lexDecls d = #[] := by simp [FDI.lexDecls, hcode, CMRGen.commitRoot_func, Func.info]
  have ha : d.code.isAsync = false := by rw [hcode]; rfl
  have e1 : d.env ≠ s.envs.size := Nat.ne_of_lt hG
  have e1' : s.envs.size ≠ d.env := Ne.symm e1
  have e4 : d.env < s.envs.size + 1 := Nat.lt_succ_of_lt hG
  obtain ⟨dM, hMk⟩ := hMc
  clear hcode
  simp only [CMRGen.commitRoot]
  js_until [] [e1, e1', e4, hG, hGe, gRL, gRLm, gRLv, gCU, gCUv, gM, gMv, hMo, hMk, hR, hRk, hRl, hRc, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  refine ⟨by js_norm [CallableC, hMo, hMk], ?_⟩
  refine wp_mono (hMf _ _ ?fr1 (by simp; omega)) ?_
  case fr1 =>
    unfold FPC
    have hdS : (Scope.declLike? (s.envEntry d.env)).isSome = true := by rw [hGe]; rfl
    refine frame_setEnv_new ?_ (Nat.le_refl _) _
    refine frame_setEnv_with_in ?_ hG ?q1 hdS (by simp) _
    case q1 =>
      rw [setEnv_envEntry_ne _ _ _ _ e1']
      exact bodyState_envEntry_lt (s := s) (fo := fo) (d := d) (t := t)
        (args := #[.obj FR, .obj R, .num (F64.fin false 4503599627370496 (-51)), sl, ul, srl, sst]) _ hG
    refine frame_setEnv_new ?_ (Nat.le_refl _) _
    frame_go' []
  rintro v1 w1 h1 ⟨hF1, hFs1, hfu1, rfl, hPL1⟩
  have hfw1 : 4 * K + 300 ≤ w1.fuel := by simp at hfu1; omega
  have hE1 := envEntry_frame hF1 (e := s.envs.size) (by simp)
    (List.all_eq_true.mpr fun p hp => by have := (hfpM p hp).2; simp; exact Nat.ne_of_lt this)
  have hEd1 := envEntry_frame hF1 (e := d.env) (by simp; omega)
    (List.all_eq_true.mpr fun p hp => by have := (hfpM p hp).1; simp; exact this)
  have hS1 : s.envs.size < w1.envs.size := Nat.lt_of_lt_of_le (by simp) hF1.envs_le
  have hGd1 : d.env < w1.envs.size := Nat.lt_trans hG hS1
  have hlt1 : ∀ o, o < s.heap.size → o < w1.heap.size := fun o ho =>
    Nat.lt_of_lt_of_le (by simpa using ho) hF1.heap_le
  have hob1 : ∀ o, o < s.heap.size → (∀ p, p ∈ fpM.props → p.1 ≠ o) → w1.objEntry o = s.objEntry o :=
    fun o ho hn => by
      rw [hF1.obj_eq o (by simpa using ho) (fun k hk => hn _ hk rfl)]; simp
  have hR1 := hob1 R hR (fun p hp => (hfpMp p hp).1)
  have hT1 := hob1 RSI hRSI (fun p hp => (hfpMp p hp).2.1)
  have hD1 := hob1 RDSI hRDSI (fun p hp => (hfpMp p hp).2.2.1)
  have hB1 := hob1 fB hBo (fun p hp => (hfpMp p hp).2.2.2.1)
  have hFRk1 : (w1.objEntry FR).kind = (s.objEntry FR).kind := by rw [kind_frame hF1 (by simpa using hFR)]; simp
  have hFRn1 : (w1.objEntry FR).props.get? (.str (JSStr.ofString "callbackNode")) = some (.data cnw true cne cnc) := by
    rw [props_frame hF1 (by simpa using hFR) (by
      simpa using fun hm => ((hfpMp _ hm).2.2.2.2.2.2.2 rfl).1 rfl)]; simpa using hFRn
  have hFRp1 : (w1.objEntry FR).props.get? (.str (JSStr.ofString "callbackPriority")) = some (.data cpw true cpe cpc) := by
    rw [props_frame hF1 (by simpa using hFR) (by
      simpa using fun hm => ((hfpMp _ hm).2.2.2.2.2.2.2 rfl).2 rfl)]; simpa using hFRp
  obtain ⟨dB, hBk⟩ := hBc
  js_until [] [hfw1, hE1, hEd1, hS1, hGd1, hR1, hT1, hD1, hB1, hFRk1, hFRn1, hFRp1, hlt1 R hR, hlt1 FR hFR, hlt1 RSI hRSI, hlt1 RDSI hRDSI, hlt1 fB hBo, gVE, gVEm, gVEv, gTT, gTTm, gTTv, gSV, gSVm, gSVv, gT, gTv, gD, gDv, gE, gEv, gEm, gB, gBv, hRs, hRf, hrs, hrf, hrs2, hFRk, hRSIk, hRSIt, hRDSIk, hRDSIp, dRF, Ne.symm dRF, dTD, Ne.symm dTD, dTF, Ne.symm dTF, dDF, Ne.symm dDF, dTR, Ne.symm dTR, dDR, Ne.symm dDR, hBk, e1, e1', e4, hG, hGe, gRL, gRLm, gRLv, gCU, gCUv, gM, gMv, hMo, hMk, hR, hRk, hRl, hRc, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  refine ⟨by js_norm [CallableC, hlt1 fB hBo, hB1, hBk, dBF, dBT, dBD, Ne.symm dBF, Ne.symm dBT, Ne.symm dBD], ?_⟩
  refine wp_mono (hBf _ _ ?fr2 (by simp; omega)) ?_
  case fr2 =>
    unfold FPC
    have hdS : (Scope.declLike? (s.envEntry d.env)).isSome = true := by rw [hGe]; rfl
    refine frame_setEnv_with_in ?_ hG ?a1 ?a2 (by simp [Footprint.union]) _
    case a1 => simp only [setEnv_envEntry_ne _ _ _ _ e1', setProp_envEntry]; exact setEnv_envEntry_self _ _ _ (by first | exact hGd1 | (simp; omega))
    case a2 => simp only [declLike_isSome_withBindings]; exact hdS
    refine frame_setEnv_new ?_ (Nat.le_refl _) _
    refine frame_setProp_in ?_ hRDSI (by simp [Footprint.union]) _
    refine frame_setEnv_new ?_ (Nat.le_refl _) _
    refine frame_setProp_in ?_ hRSI (by simp [Footprint.union]) _
    refine frame_setEnv_new ?_ (Nat.le_refl _) _
    refine frame_setEnv_with_in ?_ hG ?b1 ?b2 (by simp [Footprint.union]) _
    case b1 => simp only [setEnv_envEntry_ne _ _ _ _ e1', setProp_envEntry]; exact setEnv_envEntry_self _ _ _ (by first | exact hGd1 | (simp; omega))
    case b2 => simp only [declLike_isSome_withBindings]; exact hdS
    refine frame_setProp_in ?_ hFR (by simp [Footprint.union]) _
    refine frame_setProp_in ?_ hFR (by simp [Footprint.union]) _
    refine frame_setEnv_new ?_ (Nat.le_refl _) _
    refine frame_setEnv_split (frame_setEnv_with_in ?_ hG (setEnv_envEntry_self _ _ _ ?c1) ?c2 ?c3 _)
    case c1 => first | exact hGd1 | (simp; omega)
    case c2 => simp only [declLike_isSome_withBindings]; exact hdS
    case c3 => simp [Footprint.union]
    refine frame_setEnv_with_in ?_ hG ?c4 ?c5 (by simp [Footprint.union]) _
    case c5 => simp only [declLike_isSome_withBindings]; exact hdS
    case c4 =>
      rw [hEd1, setEnv_envEntry_ne _ _ _ _ e1']
      exact setEnv_envEntry_self _ _ _ (by first | exact hGd1 | (simp; omega))
    exact hFs1
  rintro v2 w2 h2 ⟨hF2, hFs2, hfu2, rfl, hSel2⟩
  have hfw2 : 3 * K + 200 ≤ w2.fuel := by simp at hfu2; omega
  have hE2 := envEntry_frame hF2 (e := s.envs.size) (by simp; omega)
    (List.all_eq_true.mpr fun p hp => by have := (hfpB p hp).1; simp; exact Nat.ne_of_lt this)
  obtain ⟨bw2, hd2, hbw2⟩ := declLike_frame hF2 (e := d.env) (by simp; omega) (by
    rw [setEnv_envEntry_self _ _ _ (by first | exact hGd1 | (simp; omega))]
    simp only [declLike_withBindings', hGe, Option.map]
    rfl)
  have hnB : ∀ x, x ∈ [JSStr.ofString "executionContext", JSStr.ofString "pendingEffectsStatus",
      JSStr.ofString "shouldStartViewTransition", JSStr.ofString "flushMutationEffects",
      JSStr.ofString "flushLayoutEffects", JSStr.ofString "flushSpawnedWork", JSStr.ofString "ReactSharedInternals",
      JSStr.ofString "ReactDOMSharedInternals", JSStr.ofString "pendingViewTransitionEvents",
      JSStr.ofString "pendingTransitionTypes"] → (d.env, x) ∉ fpB.binds := fun x hx hm => (hfpB _ hm).2 rfl hx
  have bVE := hbw2 _ (hnB (JSStr.ofString "pendingViewTransitionEvents") (by simp))
  have bTT := hbw2 _ (hnB (JSStr.ofString "pendingTransitionTypes") (by simp))
  have hVE2 : BindIs w2 d.env (JSStr.ofString "pendingViewTransitionEvents") .null := by
    unfold BindIs; rw [hd2]; simp [bVE, Std.HashMap.getElem?_modify, gVE, gVEm]
  have hTT2 : BindIs w2 d.env (JSStr.ofString "pendingTransitionTypes") .null := by
    unfold BindIs; rw [hd2]; simp [bTT, Std.HashMap.getElem?_modify, gTT, gTTm]
  have hPL2 : PropHas w2 FR (JSStr.ofString "pendingLanes") (.num (F64.fin false 0 (-1074))) := by
    refine PropHas.frame ?_ hF2 (by simpa using hlt1 FR hFR) (fun hm => (hfpBp _ hm).2.2.2.2.2 rfl)
    refine PropHas.setEnv ?_ _ _
    refine PropHas.setEnv ?_ _ _
    refine PropHas.setProp_ne ?_ (Or.inl dDF) _
    refine PropHas.setEnv ?_ _ _
    refine PropHas.setProp_ne ?_ (Or.inl dTF) _
    refine PropHas.setEnv ?_ _ _
    refine PropHas.setEnv ?_ _ _
    refine PropHas.setProp_ne ?_ (Or.inr (by decide)) _
    refine PropHas.setProp_ne ?_ (Or.inr (by decide)) _
    refine PropHas.setEnv ?_ _ _
    refine PropHas.setEnv ?_ _ _
    exact hPL1
  have b1 := hbw2 _ (hnB (JSStr.ofString "executionContext") (by simp))
  have b2 := hbw2 _ (hnB (JSStr.ofString "pendingEffectsStatus") (by simp))
  have b3 := hbw2 _ (hnB (JSStr.ofString "shouldStartViewTransition") (by simp))
  have b4 := hbw2 _ (hnB (JSStr.ofString "flushMutationEffects") (by simp))
  have b5 := hbw2 _ (hnB (JSStr.ofString "ReactSharedInternals") (by simp))
  have b6 := hbw2 _ (hnB (JSStr.ofString "ReactDOMSharedInternals") (by simp))
  have hS2 : s.envs.size < w2.envs.size := Nat.lt_of_lt_of_le (by simp; omega) hF2.envs_le
  have hGd2 : d.env < w2.envs.size := Nat.lt_trans hG hS2
  have hlt2 : ∀ o, o < s.heap.size → o < w2.heap.size := fun o ho =>
    Nat.lt_of_lt_of_le (by simpa using hlt1 o ho) hF2.heap_le
  have hT2 : (w2.objEntry RSI).kind = (s.objEntry RSI).kind ∧
      (w2.objEntry RSI).props.get? (.str (JSStr.ofString "T")) = some (.data .null true te tc) := by
    rw [hF2.obj_eq RSI (by simpa using hlt1 RSI hRSI) (fun k hk => (hfpBp _ hk).1 rfl)]
    simp only [setProp_objEntry, setEnv_objEntry]
    simp [dTF, Ne.symm dTF, dTD, Ne.symm dTD, hT1, hlt1 RSI hRSI, hRSIt]
  have hD2 : (w2.objEntry RDSI).kind = (s.objEntry RDSI).kind ∧
      (w2.objEntry RDSI).props.get? (.str (JSStr.ofString "p")) =
        some (.data (.num (F64.fin false 4503599627370496 (-51))) true pe pc) := by
    rw [hF2.obj_eq RDSI (by simpa using hlt1 RDSI hRDSI) (fun k hk => (hfpBp _ hk).2.1 rfl)]
    simp only [setProp_objEntry, setEnv_objEntry]
    simp [dDF, Ne.symm dDF, dTD, Ne.symm dTD, hD1, hlt1 RDSI hRDSI, hRDSIp]
  have hME2 : w2.objEntry fME = s.objEntry fME := by
    rw [hF2.obj_eq fME (by simpa using hlt1 fME hMEo) (fun k hk => (hfpBp _ hk).2.2.1 rfl)]
    simp only [setProp_objEntry, setEnv_objEntry]
    simp [Ne.symm dMF, Ne.symm dMT, Ne.symm dMD]
    exact hob1 fME hMEo (fun p hp => (hfpMp p hp).2.2.2.2.1)
  js_until [] [hfw2, hE2, hd2, b1, b2, b3, b4, b5, b6, hS2, hGd2, hT2.1, hT2.2, hD2.1, hD2.2, hME2, hlt2 RSI hRSI, hlt2 RDSI hRDSI, hlt2 fME hMEo, Std.HashMap.getElem?_modify, gS, gSm, gSv, gME, gMEv, hfw1, hE1, hEd1, hS1, hGd1, hR1, hT1, hD1, hB1, hFRk1, hFRn1, hFRp1, hlt1 R hR, hlt1 FR hFR, hlt1 RSI hRSI, hlt1 RDSI hRDSI, hlt1 fB hBo, gVE, gVEm, gVEv, gTT, gTTm, gTTv, gSV, gSVm, gSVv, gT, gTv, gD, gDv, gE, gEv, gEm, gB, gBv, hRs, hRf, hrs, hrf, hrs2, hFRk, hRSIk, hRSIt, hRDSIk, hRDSIp, dRF, Ne.symm dRF, dTD, Ne.symm dTD, dTF, Ne.symm dTF, dDF, Ne.symm dDF, dTR, Ne.symm dTR, dDR, Ne.symm dDR, hBk, e1, e1', e4, hG, hGe, gRL, gRLm, gRLv, gCU, gCUv, gM, gMv, hMo, hMk, hR, hRk, hRl, hRc, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  obtain ⟨dME, hMEk⟩ := hMEc
  refine ⟨by js_norm [CallableC, hlt2 fME hMEo, hME2, hMEk, dMF, dMT, dMD, Ne.symm dMF, Ne.symm dMT, Ne.symm dMD], ?_⟩
  refine wp_mono (hMEf _ _ ?fr3 ?bs ?be ?pt ?pp ?sel (by simp; omega)) ?_
  case sel =>
    exact SelInfo.setEnv_modify (SelInfo.setProp (SelInfo.setProp (SelInfo.setEnv_modify hSel2 hGd2 rfl (by simp))
      hRDSI _ _) hRSI _ _) (by simpa using hGd2)
      (by simp only [setProp_envEntry]; exact setEnv_envEntry_self _ _ _ hGd2) (by simp)
  case fr3 =>
    unfold FPC
    have hd2' : (Scope.declLike? (w2.envEntry d.env)).isSome = true := by rw [hd2]; rfl
    refine frame_setEnv_with_in ?_ hG ?f1 ?f2 (by simp [Footprint.union]) _
    case f1 => simp only [setProp_envEntry]; exact setEnv_envEntry_self _ _ _ hGd2
    case f2 => simp only [declLike_isSome_withBindings]; exact hd2'
    refine frame_setProp_in ?_ hRSI (by simp [Footprint.union]) _
    refine frame_setProp_in ?_ hRDSI (by simp [Footprint.union]) _
    refine frame_setEnv_with_in hFs2 hG rfl hd2' (by simp [Footprint.union, FPC]) _
  case bs =>
    unfold BindIs
    rw [setEnv_envEntry_self _ _ _ (by simpa using hGd2)]
    simp only [declLike_withBindings', hd2, Option.map]
    simp [Std.HashMap.getElem?_modify, b2, gS, gSm]
  case be =>
    unfold BindIs
    rw [setEnv_envEntry_self _ _ _ (by simpa using hGd2)]
    simp only [declLike_withBindings', hd2, Option.map]
    simp [Std.HashMap.getElem?_modify, b1, gE, gEm, gEv]
  case pt =>
    refine ⟨te, tc, ?_⟩
    simp only [setProp_objEntry, setEnv_objEntry]
    simp [dTD, Ne.symm dTD, hlt2 RSI hRSI, hT2.2]
  case pp =>
    refine ⟨pe, pc, ?_⟩
    simp only [setProp_objEntry, setEnv_objEntry]
    simp [dTD, Ne.symm dTD, hlt2 RDSI hRDSI, hD2.2]
  rintro v3 w3 h3 ⟨hF3, hFs3, hfu3, hQ1⟩
  have hfw3 : 2 * K + 100 ≤ w3.fuel := by simp at hfu3; omega
  have hE3 := envEntry_frame hF3 (e := s.envs.size) (by simp; omega)
    (List.all_eq_true.mpr fun p hp => by have := (hfpME p hp).1; simp; exact Nat.ne_of_lt this)
  obtain ⟨bw3, hd3, hbw3⟩ := declLike_frame hF3 (e := d.env) (by simp; omega) (by
    rw [setEnv_envEntry_self _ _ _ (by simpa using hGd2)]
    simp only [declLike_withBindings', hd2, Option.map]
    rfl)
  have c1 := hbw3 (JSStr.ofString "flushLayoutEffects") (fun hm => (hfpME _ hm).2 rfl (by simp))
  have c2 := hbw3 (JSStr.ofString "flushSpawnedWork") (fun hm => (hfpME _ hm).2 rfl (by simp))
  have b7 := hbw2 _ (hnB (JSStr.ofString "flushLayoutEffects") (by simp))
  have b8 := hbw2 _ (hnB (JSStr.ofString "flushSpawnedWork") (by simp))
  have hS3 : s.envs.size < w3.envs.size := Nat.lt_of_lt_of_le (by simp; omega) hF3.envs_le
  have hobj3 : ∀ o, o < s.heap.size → o ≠ RSI → o ≠ RDSI → o ≠ FR → (∀ p, p ∈ fpM.props → p.1 ≠ o) →
      (∀ p, p ∈ fpB.props → p.1 ≠ o) → (∀ p, p ∈ fpME.props → p.1 ≠ o) → w3.objEntry o = s.objEntry o := by
    intro o ho h1 h2 h3 hm hb hme
    rw [hF3.obj_eq o (by simpa using hlt2 o ho) (fun k hk => hme _ hk rfl)]
    simp only [setProp_objEntry, setEnv_objEntry]
    simp [Ne.symm h1, Ne.symm h2]
    rw [hF2.obj_eq o (by simpa using hlt1 o ho) (fun k hk => hb _ hk rfl)]
    simp only [setProp_objEntry, setEnv_objEntry]
    simp [Ne.symm h1, Ne.symm h2, Ne.symm h3]
    exact hob1 o ho hm
  have hLE3 := hobj3 fLE hLEo dLT dLD dLF (fun p hp => (hfpMp p hp).2.2.2.2.2.1) (fun p hp => (hfpBp p hp).2.2.2.1)
    (fun p hp => (hfpMEp p hp).1)
  obtain ⟨dLE, hLEk⟩ := hLEc
  have hlt3 : ∀ o, o < s.heap.size → o < w3.heap.size := fun o ho =>
    Nat.lt_of_lt_of_le (by simpa using hlt2 o ho) hF3.heap_le
  have hGd3 : d.env < w3.envs.size := Nat.lt_trans hG hS3
  js_until [] [hGd3, hE3, hd3, c1, c2, b7, b8, hS3, hLE3, hlt3 fLE hLEo, hLEk, Std.HashMap.getElem?_modify, gLE, gLEv, gSP, gSPv, hfw2, hE2, hd2, b1, b2, b3, b4, b5, b6, hS2, hGd2, hT2.1, hT2.2, hD2.1, hD2.2, hME2, hlt2 RSI hRSI, hlt2 RDSI hRDSI, hlt2 fME hMEo, Std.HashMap.getElem?_modify, gS, gSm, gSv, gME, gMEv, hfw1, hE1, hEd1, hS1, hGd1, hR1, hT1, hD1, hB1, hFRk1, hFRn1, hFRp1, hlt1 R hR, hlt1 FR hFR, hlt1 RSI hRSI, hlt1 RDSI hRDSI, hlt1 fB hBo, gVE, gVEm, gVEv, gTT, gTTm, gTTv, gSV, gSVm, gSVv, gT, gTv, gD, gDv, gE, gEv, gEm, gB, gBv, hRs, hRf, hrs, hrf, hrs2, hFRk, hRSIk, hRSIt, hRDSIk, hRDSIp, dRF, Ne.symm dRF, dTD, Ne.symm dTD, dTF, Ne.symm dTF, dDF, Ne.symm dDF, dTR, Ne.symm dTR, dDR, Ne.symm dDR, hBk, e1, e1', e4, hG, hGe, gRL, gRLm, gRLv, gCU, gCUv, gM, gMv, hMo, hMk, hR, hRk, hRl, hRc, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  refine ⟨by js_norm [CallableC, hLE3, hLEk, hlt3 fLE hLEo], wp_mono (hLEf _ _ hFs3 hQ1 (by omega)) ?_⟩
  rintro v4 w4 h4 ⟨hF4, hFs4, hfu4, hQ2⟩
  have hPL3 : PropHas w3 FR (JSStr.ofString "pendingLanes") (.num (F64.fin false 0 (-1074))) := by
    refine PropHas.frame ?_ hF3 (by simpa using hlt2 FR hFR) (fun hm => (hfpMEp _ hm).2.2 rfl)
    refine PropHas.setEnv ?_ _ _
    refine PropHas.setProp_ne ?_ (Or.inl dTF) _
    refine PropHas.setProp_ne ?_ (Or.inl dDF) _
    refine PropHas.setEnv ?_ _ _
    exact hPL2
  have hPL4 := PropHas.frame hPL3 hF4 (hlt3 FR hFR) (fun hm => (hfpLEp _ hm).2 rfl)
  have hVT3 : ∀ x, x = JSStr.ofString "pendingViewTransitionEvents" ∨ x = JSStr.ofString "pendingTransitionTypes" →
      BindIs w2 d.env x .null → BindIs w3 d.env x .null := by
    intro x hx hb
    refine BindIs.frame ?_ hF3 (by simpa using hGd2) (fun hm => (hfpME _ hm).2 rfl (by rcases hx with rfl | rfl <;> simp))
    exact BindIs.setEnv_modify (BindIs.setProp (BindIs.setProp (BindIs.setEnv_modify hb hGd2 rfl
      (by rcases hx with rfl | rfl <;> decide)) _ _ _) _ _ _) (by simpa using hGd2)
      (by simp only [setProp_envEntry]; exact setEnv_envEntry_self _ _ _ hGd2) (by rcases hx with rfl | rfl <;> decide)
  have hVE4 := BindIs.frame (hVT3 _ (Or.inl rfl) hVE2) hF4 hGd3 (fun hm => (hfpLE _ hm).2 rfl (by simp))
  have hTT4 := BindIs.frame (hVT3 _ (Or.inr rfl) hTT2) hF4 hGd3 (fun hm => (hfpLE _ hm).2 rfl (by simp))
  have hE4 := envEntry_frame hF4 (e := s.envs.size) hS3
    (List.all_eq_true.mpr fun p hp => by have := (hfpLE p hp).1; simp; exact Nat.ne_of_lt this)
  obtain ⟨bw4, hd4, hbw4⟩ := declLike_frame hF4 (e := d.env) hGd3 hd3
  have c3 := hbw4 (JSStr.ofString "flushSpawnedWork") (fun hm => (hfpLE _ hm).2 rfl (by simp))
  have hS4 : s.envs.size < w4.envs.size := Nat.lt_of_lt_of_le hS3 hF4.envs_le
  have hGd4 : d.env < w4.envs.size := Nat.lt_trans hG hS4
  have hSP4 : w4.objEntry fSP = s.objEntry fSP := by
    rw [hF4.obj_eq fSP (hlt3 fSP hSPo) (fun k hk => (hfpLEp _ hk).1 rfl)]
    exact hobj3 fSP hSPo dST dSD dSF (fun p hp => (hfpMp p hp).2.2.2.2.2.2.1) (fun p hp => (hfpBp p hp).2.2.2.2.1)
      (fun p hp => (hfpMEp p hp).2.1)
  have hlt4 : ∀ o, o < s.heap.size → o < w4.heap.size := fun o ho => Nat.lt_of_lt_of_le (hlt3 o ho) hF4.heap_le
  obtain ⟨dSP, hSPk⟩ := hSPc
  have hfw4 : K + 50 ≤ w4.fuel := by omega
  js_until [] [hfw4, hGd4, hE4, hd4, c2, c3, b8, hS4, hSP4, hlt4 fSP hSPo, hSPk, hGd3, hE3, hd3, c1, c2, b7, b8, hS3, hLE3, hlt3 fLE hLEo, hLEk, Std.HashMap.getElem?_modify, gLE, gLEv, gSP, gSPv, hfw2, hE2, hd2, b1, b2, b3, b4, b5, b6, hS2, hGd2, hT2.1, hT2.2, hD2.1, hD2.2, hME2, hlt2 RSI hRSI, hlt2 RDSI hRDSI, hlt2 fME hMEo, Std.HashMap.getElem?_modify, gS, gSm, gSv, gME, gMEv, hfw1, hE1, hEd1, hS1, hGd1, hR1, hT1, hD1, hB1, hFRk1, hFRn1, hFRp1, hlt1 R hR, hlt1 FR hFR, hlt1 RSI hRSI, hlt1 RDSI hRDSI, hlt1 fB hBo, gVE, gVEm, gVEv, gTT, gTTm, gTTv, gSV, gSVm, gSVv, gT, gTv, gD, gDv, gE, gEv, gEm, gB, gBv, hRs, hRf, hrs, hrf, hrs2, hFRk, hRSIk, hRSIt, hRDSIk, hRDSIp, dRF, Ne.symm dRF, dTD, Ne.symm dTD, dTF, Ne.symm dTF, dDF, Ne.symm dDF, dTR, Ne.symm dTR, dDR, Ne.symm dDR, hBk, e1, e1', e4, hG, hGe, gRL, gRLm, gRLv, gCU, gCUv, gM, gMv, hMo, hMk, hR, hRk, hRl, hRc, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  refine ⟨by js_norm [CallableC, hSP4, hSPk, hlt4 fSP hSPo], wp_mono (hSPf _ _ hFs4 hQ2 hPL4 hVE4 hTT4 (by omega)) ?_⟩
  rintro v5 w5 h5 ⟨hFs5, hfu5, hQ3⟩
  js_until [] []
  refine ⟨by simp [bodyState, entryState] at hfu1 hfu2 hfu3 hfu4 hfu5 ⊢; omega, ⟨w5, hQ3, frame_restore (frame_refl _ _) s⟩, frame_restore hFs5 s⟩

end

end ReactCommitRootFn
