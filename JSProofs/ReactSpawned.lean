import JSProofs.ReactNoEffects
import JSProofs.Setter
import JSProofs.ReactHostContainer
import JSProofs.Rebase
import JSProofs.ReactFacts

/-!
# flushSpawnedWork for the click's commit (zippy docs/react-proofs.md)

`flushSpawnedWork()` at status 3 after the sync lane's commit: no passive effects (status 0, the pending root and work
cleared, the root's pooled cache released), paint requested, no DevTools hook, no recoverable errors or view
transition events, then `flushPendingEffects()` (nothing pending), `ensureRootIsScheduled(root)`, the nested-update
count reset (no lanes left) and `flushSyncWorkAcrossRoots_impl(0, false)`. The callees are contracts.
-/

open ES ES.M HostRuns Logic
open Std (HashMap)
open ReactFacts (BindIs)

namespace ReactSpawned

/-- What `flushSpawnedWork` itself writes. -/
def FPS (g : EnvId) : Footprint :=
  ⟨[(g, JSStr.ofString "pendingEffectsStatus"), (g, JSStr.ofString "pendingViewTransition"),
    (g, JSStr.ofString "pendingFinishedWork"), (g, JSStr.ofString "pendingEffectsRoot"),
    (g, JSStr.ofString "legacyErrorBoundariesThatAlreadyFailed"), (g, JSStr.ofString "pendingTransitionTypes"),
    (g, JSStr.ofString "nestedUpdateCount"), (g, JSStr.ofString "rootWithNestedUpdates")], [], false⟩

/-- With `requestPaint`'s write (the scheduler's `needsPaint`): what precedes the pooled cache's release. -/
def FP1 (g gP : EnvId) : Footprint :=
  (FPS g).union ⟨[(gP, JSStr.ofString "needsPaint")], [], false⟩

/-- With the callees' writes other than `ensureRootIsScheduled`'s: the scheduler's `needsPaint`, the root's
`pooledCacheLanes`. -/
def FPA (g gP : EnvId) (FR : ObjId) : Footprint :=
  (FPS g).union ⟨[(gP, JSStr.ofString "needsPaint")], [(FR, .str (JSStr.ofString "pooledCacheLanes"))], false⟩

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ}

set_option maxRecDepth 40000 in
set_option maxHeartbeats 8000000 in
theorem fsp_spec {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t : Value} {s : State}
    {bG : HashMap JSStr Binding} {oG : Option EnvId}
    {bS bVT bRP bER bFW bEL bRE bRel bLB bLP bIH bVE bTT bPE bEn bNC bRN bFS : Binding}
    {FR R fRP fRel fLP fPE fEn fFS : ObjId} {vt tt : Value} {rs rf : F64}
    {rsw rse rsc rfw rfe rfc snw sne snc plw ple plc : Bool}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d)
    (hcode : d.code = FSPGen.flushSpawnedWork_func) (hcls : d.isClassCtor = false) (hmode : d.thisMode = .strict)
    (hG : d.env < s.envs.size) (hGe : Scope.declLike? (s.envEntry d.env) = some (bG, oG))
    (gS : bG[JSStr.ofString "pendingEffectsStatus"]? = some bS) (gSm : bS.mutable = true)
    (gSv : bS.value = some (.num (F64.fin false 6755399441055744 (-51))))
    (gVT : bG[JSStr.ofString "pendingViewTransition"]? = some bVT) (gVTm : bVT.mutable = true)
    (gVTv : bVT.value = some vt)
    (gRP : bG[JSStr.ofString "requestPaint"]? = some bRP) (gRPv : bRP.value = some (.obj fRP))
    (gER : bG[JSStr.ofString "pendingEffectsRoot"]? = some bER) (gERm : bER.mutable = true)
    (gERv : bER.value = some (.obj FR))
    (gFW : bG[JSStr.ofString "pendingFinishedWork"]? = some bFW) (gFWm : bFW.mutable = true)
    (gFWv : bFW.value = some (.obj R))
    (gEL : bG[JSStr.ofString "pendingEffectsLanes"]? = some bEL)
    (gELv : bEL.value = some (.num (F64.fin false 4503599627370496 (-51))))
    (gRE : bG[JSStr.ofString "pendingRecoverableErrors"]? = some bRE) (gREv : bRE.value = some .null)
    (gRel : bG[JSStr.ofString "releaseRootPooledCache"]? = some bRel) (gRelv : bRel.value = some (.obj fRel))
    (gLB : bG[JSStr.ofString "legacyErrorBoundariesThatAlreadyFailed"]? = some bLB) (gLBm : bLB.mutable = true)
    (gLBv : bLB.value.isSome = true)
    (gLP : bG[JSStr.ofString "lanesToEventPriority"]? = some bLP) (gLPv : bLP.value = some (.obj fLP))
    (gIH : bG[JSStr.ofString "injectedHook"]? = some bIH) (gIHv : bIH.value = some .null)
    (gVE : bG[JSStr.ofString "pendingViewTransitionEvents"]? = some bVE) (gVEv : bVE.value = some .null)
    (gTT : bG[JSStr.ofString "pendingTransitionTypes"]? = some bTT) (gTTm : bTT.mutable = true)
    (gTTv : bTT.value = some tt)
    (gPE : bG[JSStr.ofString "flushPendingEffects"]? = some bPE) (gPEv : bPE.value = some (.obj fPE))
    (gEn : bG[JSStr.ofString "ensureRootIsScheduled"]? = some bEn) (gEnv : bEn.value = some (.obj fEn))
    (gNC : bG[JSStr.ofString "nestedUpdateCount"]? = some bNC) (gNCm : bNC.mutable = true)
    (gNCv : bNC.value.isSome = true)
    (gRN : bG[JSStr.ofString "rootWithNestedUpdates"]? = some bRN) (gRNm : bRN.mutable = true)
    (gRNv : bRN.value.isSome = true)
    (gFS : bG[JSStr.ofString "flushSyncWorkAcrossRoots_impl"]? = some bFS) (gFSv : bFS.value = some (.obj fFS))
    (hR : R < s.heap.size) (hRk : (s.objEntry R).kind.isPlain = true)
    (hRs : (s.objEntry R).props.get? (.str (JSStr.ofString "subtreeFlags")) = some (.data (.num rs) rsw rse rsc))
    (hRf : (s.objEntry R).props.get? (.str (JSStr.ofString "flags")) = some (.data (.num rf) rfw rfe rfc))
    (hrs : numberBinOp .bitAnd rs (F64.fin false 5638295627235328 (-39)) = F64.fin false 0 (-1074))
    (hrf : numberBinOp .bitAnd rf (F64.fin false 5638295627235328 (-39)) = F64.fin false 0 (-1074))
    (hRn : (s.objEntry R).props.get? (.str (JSStr.ofString "stateNode")) = some (.data (.obj FR) snw sne snc))
    (hFR : FR < s.heap.size) (hFRk : (s.objEntry FR).kind.isPlain = true)
    (hFRl : (s.objEntry FR).props.get? (.str (JSStr.ofString "pendingLanes")) =
      some (.data (.num (F64.fin false 0 (-1074))) plw ple plc))
    (hRPo : fRP < s.heap.size) (hRPc : ∃ dd, (s.objEntry fRP).kind = .func dd)
    (hRelo : fRel < s.heap.size) (hRelc : ∃ dd, (s.objEntry fRel).kind = .func dd)
    (hLPo : fLP < s.heap.size) (hLPc : ∃ dd, (s.objEntry fLP).kind = .func dd)
    (hPEo : fPE < s.heap.size) (hPEc : ∃ dd, (s.objEntry fPE).kind = .func dd)
    (hEno : fEn < s.heap.size) (hEnc : ∃ dd, (s.objEntry fEn).kind = .func dd)
    (hFSo : fFS < s.heap.size) (hFSc : ∃ dd, (s.objEntry fFS).kind = .func dd)
    (dRF : R ≠ FR) (dLF : fLP ≠ FR) (dPF : fPE ≠ FR) (dEF : fEn ≠ FR) (dSF : fFS ≠ FR)
    {K : Nat} {gP : EnvId} (hgP : gP ≠ d.env) (hgPs : gP < s.envs.size) (hK : 6 * K + 400 ≤ s.fuel)
    {fpE : Footprint}
    (hRP : ∀ w h1, Frame (FPS d.env) s w → K ≤ w.fuel →
      WP eng answer (n + 1) h1 (callImpl eng (.obj fRP) .undefined #[]) w fun v w' h' =>
        Frame ⟨[(gP, JSStr.ofString "needsPaint")], [], false⟩ w w' ∧ Frame (FP1 d.env gP) s w' ∧
        w.fuel ≤ w'.fuel + K ∧ h' = h1)
    (hRel : ∀ w h1, Frame (FP1 d.env gP) s w → K ≤ w.fuel →
      WP eng answer (n + 1) h1 (callImpl eng (.obj fRel) .undefined #[.obj FR, .num (F64.fin false 0 (-1074))]) w
        fun v w' h' => Frame ⟨[], [(FR, .str (JSStr.ofString "pooledCacheLanes"))], false⟩ w w' ∧
          Frame (FPA d.env gP FR) s w' ∧ w.fuel ≤ w'.fuel + K ∧ h' = h1)
    (hLP : ∀ w h1, Frame (FPA d.env gP FR) s w → K ≤ w.fuel →
      WP eng answer (n + 1) h1 (callImpl eng (.obj fLP) .undefined #[.num (F64.fin false 4503599627370496 (-51))]) w
        fun v w' h' => Frame {} w w' ∧ w.fuel ≤ w'.fuel + K ∧ h' = h1)
    (hPE : ∀ w h1, Frame (FPA d.env gP FR) s w →
      BindIs w d.env (JSStr.ofString "pendingEffectsStatus") (.num (F64.fin false 0 (-1074))) →
      BindIs w d.env (JSStr.ofString "pendingViewTransition") .null → K ≤ w.fuel →
      WP eng answer (n + 1) h1 (callImpl eng (.obj fPE) .undefined #[]) w
        fun v w' h' => Frame {} w w' ∧ w.fuel ≤ w'.fuel + K ∧ h' = h1)
    (hEn : ∀ w h1, Frame (FPA d.env gP FR) s w → K ≤ w.fuel →
      WP eng answer (n + 1) h1 (callImpl eng (.obj fEn) .undefined #[.obj FR]) w
        fun v w' h' => Frame fpE w w' ∧ Frame ((FPA d.env gP FR).union fpE) s w' ∧ w.fuel ≤ w'.fuel + K ∧ h' = h1)
    (hfpE : ∀ p, p ∈ fpE.binds → p.1 < s.envs.size ∧ (p.1 = d.env → p.2 ∉ [JSStr.ofString "nestedUpdateCount",
      JSStr.ofString "rootWithNestedUpdates", JSStr.ofString "flushSyncWorkAcrossRoots_impl"]))
    (hfpEp : ∀ p, p ∈ fpE.props → p.1 ≠ FR ∧ p.1 ≠ fFS)
    (hFSs : ∀ w h1, Frame ((FPA d.env gP FR).union fpE) s w → K ≤ w.fuel →
      WP eng answer (n + 1) h1 (callImpl eng (.obj fFS) .undefined #[.num (F64.fin false 0 (-1074)), .bool false]) w
        fun v w' h' => Frame {} w w' ∧ w.fuel ≤ w'.fuel + K ∧ h' = h1) :
    WP eng answer (n + 2) h (callImpl eng (.obj fo) t #[]) s fun v w h' =>
      v = .undefined ∧ s.fuel ≤ w.fuel + 6 * K + 400 ∧ h' = h ∧ Frame ((FPA d.env gP FR).union fpE) s w := by
  apply wp_callGen FSPGen.flushSpawnedWork_eq (by decide) hlt hk (by omega) hcls hmode
    (by rw [hcode]; rfl) (by rw [hcode]; rfl) (ReactNoEffects.simple_spawned d hcode) (by rw [hcode]; rfl)
    (by rw [hcode]; rfl)
  have hpn : d.code.info.fdi.paramNames = #[] := by rw [hcode]; rfl
  have hv : d.code.info.fdi.varNames = #[JSStr.ofString "committedViewTransition", JSStr.ofString "root",
    JSStr.ofString "finishedWork", JSStr.ofString "lanes", JSStr.ofString "recoverableErrors",
    JSStr.ofString "passiveSubtreeMask", JSStr.ofString "onRecoverableError", JSStr.ofString "i",
    JSStr.ofString "recoverableError"] := by rw [hcode]; rfl
  have hl : FDI.lexDecls d = #[] := by simp [FDI.lexDecls, hcode, FSPGen.flushSpawnedWork_func, Func.info]
  have ha : d.code.isAsync = false := by rw [hcode]; rfl
  have e1 : d.env ≠ s.envs.size := Nat.ne_of_lt hG
  have e1' : s.envs.size ≠ d.env := Ne.symm e1
  have e4 : d.env < s.envs.size + 1 := Nat.lt_succ_of_lt hG
  obtain ⟨dRP, hRPk⟩ := hRPc
  clear hcode
  simp only [FSPGen.flushSpawnedWork]
  js_until [] [e1, e1', e4, hG, hGe, gS, gSm, gSv, gVT, gVTm, gVTv, gRP, gRPv, hRPo, hRPk, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  refine ⟨by js_norm [CallableC, hRPo, hRPk], ?_⟩
  refine wp_mono (hRP _ _ ?fr (by simp; omega)) ?_
  case fr =>
    unfold FPS
    have hdS : (Scope.declLike? (s.envEntry d.env)).isSome = true := by rw [hGe]; rfl
    refine frame_setEnv_with_in ?_ hG ?h1 ?d1 (by simp [Footprint.union]) _
    case h1 =>
      simp only [setEnv_envEntry_ne _ _ _ _ e1']
      exact setEnv_envEntry_self _ _ _ (by simp; omega)
    case d1 => simp only [declLike_isSome_withBindings]; exact hdS
    refine frame_setEnv_new ?_ (by simp) _
    refine frame_setEnv_with_in ?base hG ?h2 hdS ?in2 _
    case h2 => exact bodyState_envEntry_lt (s := s) (fo := fo) (d := d) (t := t) (args := #[]) _ hG
    case in2 => simp [Footprint.union]
    case base => frame_go' []
  rintro v1 w1 h1 ⟨hF1, hFs1, hfu1, rfl⟩
  have hfw1 : 5 * K + 300 ≤ w1.fuel := by simp at hfu1; omega
  have hE1 := envEntry_frame hF1 (e := s.envs.size) (by simp) (by simp; exact Nat.ne_of_lt hgPs)
  have hEd1 := envEntry_frame hF1 (e := d.env) (by simp; omega) (by simp [hgP])
  have hS1 : s.envs.size < w1.envs.size := Nat.lt_of_lt_of_le (by simp) hF1.envs_le
  have hGd1 : d.env < w1.envs.size := Nat.lt_trans hG hS1
  have hob1 : ∀ o, o < s.heap.size → w1.objEntry o = s.objEntry o := fun o ho => by
    rw [obj_eq_np hF1 rfl (by simpa using ho)]; simp
  have hlt1 : ∀ o, o < s.heap.size → o < w1.heap.size := fun o ho =>
    Nat.lt_of_lt_of_le (by simpa using ho) hF1.heap_le
  js_until [] [hfw1, hE1, hEd1, hS1, hGd1, hob1 R hR, hob1 FR hFR, hob1 fRel hRelo, hlt1 R hR, hlt1 FR hFR, hlt1 fRel hRelo, gER, gERm, gERv, gFW, gFWm, gFWv, gEL, gELv, gRE, gREv, gRel, gRelv, hR, hRk, hRs, hRf, hrs, hrf, hFR, hFRk, hFRl, e1, e1', e4, hG, hGe, gS, gSm, gSv, gVT, gVTm, gVTv, gRP, gRPv, hRPo, hRPk, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  obtain ⟨dRel, hRelk⟩ := hRelc
  refine ⟨by js_norm [CallableC, hlt1 fRel hRelo, hob1 fRel hRelo, hRelk], ?_⟩
  refine wp_mono (hRel _ _ ?fr2 (by simp; omega)) ?_
  case fr2 =>
    unfold FP1 FPS
    have hdS : (Scope.declLike? (s.envEntry d.env)).isSome = true := by rw [hGe]; rfl
    refine frame_setEnv_split (frame_setEnv_with_in ?_ hG (setEnv_envEntry_self _ _ _ ?q1) ?q2 ?q3 _)
    case q1 => simp; omega
    case q2 => simp only [declLike_isSome_withBindings]; exact hdS
    case q3 => simp [Footprint.union]
    refine frame_setEnv_split (frame_setEnv_with_in ?_ hG (setEnv_envEntry_self _ _ _ ?q4) ?q5 ?q6 _)
    case q4 => simp; omega
    case q5 => simp only [declLike_isSome_withBindings]; exact hdS
    case q6 => simp [Footprint.union]
    refine frame_setEnv_with_in ?_ hG ?q7 ?q8 (by simp [Footprint.union]) _
    case q7 =>
      rw [setEnv_envEntry_ne _ _ _ _ e1', hEd1]
      exact setEnv_envEntry_self _ _ _ (by simp; omega)
    case q8 => simp only [declLike_isSome_withBindings]; exact hdS
    exact frame_setEnv_new hFs1 (Nat.le_refl _) _
  rintro v2 w2 h2 ⟨hF2, hFs2, hfu2, rfl⟩
  have hfw2 : 4 * K + 200 ≤ w2.fuel := by simp at hfu2; omega
  have hE2 := envEntry_frame hF2 (e := s.envs.size) (by simp; omega) (by simp)
  have hEd2 := envEntry_frame hF2 (e := d.env) (by simp; omega) (by simp)
  have hS2 : s.envs.size < w2.envs.size := Nat.lt_of_lt_of_le (by simp; omega) hF2.envs_le
  have hGd2 : d.env < w2.envs.size := Nat.lt_trans hG hS2
  have hob2 : ∀ o, o < s.heap.size → o ≠ FR → w2.objEntry o = s.objEntry o := fun o ho hne => by
    rw [hF2.obj_eq o (by simpa using hlt1 o ho) (fun k hk => by simp at hk; exact hne hk.1)]
    simp [hob1 o ho]
  have hlt2 : ∀ o, o < s.heap.size → o < w2.heap.size := fun o ho =>
    Nat.lt_of_lt_of_le (by simpa using hlt1 o ho) hF2.heap_le
  have hFRk2 : (w2.objEntry FR).kind = (s.objEntry FR).kind := by
    rw [kind_frame hF2 (by simpa using hlt1 FR hFR)]; simp [hob1 FR hFR]
  have hFRl2 : (w2.objEntry FR).props.get? (.str (JSStr.ofString "pendingLanes")) =
      some (.data (.num (F64.fin false 0 (-1074))) plw ple plc) := by
    rw [props_frame hF2 (by simpa using hlt1 FR hFR) (by simp)]; simp [hob1 FR hFR, hFRl]
  js_until [] [hfw2, hE2, hEd2, hS2, hGd2, hFRk2, hFRl2, hob2 R hR dRF, hob2 fLP hLPo dLF, hlt2 R hR, hlt2 FR hFR, hlt2 fLP hLPo, gLB, gLBm, gLBv, gLP, gLPv, hfw1, hE1, hEd1, hS1, hGd1, hob1 R hR, hob1 FR hFR, hob1 fRel hRelo, hlt1 R hR, hlt1 FR hFR, hlt1 fRel hRelo, gER, gERm, gERv, gFW, gFWm, gFWv, gEL, gELv, gRE, gREv, gRel, gRelv, hR, hRk, hRs, hRf, hrs, hrf, hFR, hFRk, hFRl, e1, e1', e4, hG, hGe, gS, gSm, gSv, gVT, gVTm, gVTv, gRP, gRPv, hRPo, hRPk, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  obtain ⟨dLP, hLPk⟩ := hLPc
  refine ⟨by js_norm [CallableC, hlt2 fLP hLPo, hob2 fLP hLPo dLF, hLPk], ?_⟩
  refine wp_mono (hLP _ _ ?fr3 (by simp; omega)) ?_
  case fr3 =>
    unfold FPA FPS
    have hdS : (Scope.declLike? (s.envEntry d.env)).isSome = true := by rw [hGe]; rfl
    refine frame_setEnv_with_in ?_ hG ?q1 ?q2 (by simp [Footprint.union]) _
    case q1 =>
      rw [setEnv_envEntry_ne _ _ _ _ e1', hEd2]
      exact setEnv_envEntry_self _ _ _ (by simp; omega)
    case q2 => simp only [declLike_isSome_withBindings]; exact hdS
    exact frame_setEnv_new hFs2 (Nat.le_refl _) _
  rintro v3 w3 h3 ⟨hF3, hfu3, rfl⟩
  have hfw3 : 3 * K + 150 ≤ w3.fuel := by simp at hfu3; omega
  have hE3 := envEntry_frame0 hF3 (e := s.envs.size) (by simp; omega)
  have hEd3 := envEntry_frame0 hF3 (e := d.env) (by simp; omega)
  have hS3 : s.envs.size < w3.envs.size := Nat.lt_of_lt_of_le (by simp; omega) hF3.envs_le
  have hGd3 : d.env < w3.envs.size := Nat.lt_trans hG hS3
  have hob3 : ∀ o, o < w2.heap.size → w3.objEntry o = w2.objEntry o := fun o ho => by
    rw [objEntry_frame0 hF3 (by simpa using ho)]; simp
  have hlt3 : ∀ o, o < s.heap.size → o < w3.heap.size := fun o ho =>
    Nat.lt_of_lt_of_le (by simpa using hlt2 o ho) hF3.heap_le
  have hFs3 : Frame (FPA d.env gP FR) s w3 := by
    refine frame_then_empty ?_ hF3
    unfold FPA FPS
    have hdS : (Scope.declLike? (s.envEntry d.env)).isSome = true := by rw [hGe]; rfl
    refine frame_setEnv_with_in ?_ hG ?q1 ?q2 (by simp [Footprint.union]) _
    case q1 =>
      rw [setEnv_envEntry_ne _ _ _ _ e1', hEd2]
      exact setEnv_envEntry_self _ _ _ (by simp; omega)
    case q2 => simp only [declLike_isSome_withBindings]; exact hdS
    exact frame_setEnv_new hFs2 (Nat.le_refl _) _
  js_until [] [hfw3, hE3, hEd3, hS3, hGd3, hob3 FR (hlt2 FR hFR), hob3 R (hlt2 R hR), hob3 fPE (hlt2 fPE hPEo), hlt3 R hR, hlt3 FR hFR, hlt3 fPE hPEo, hob2 R hR dRF, hob2 fPE hPEo dPF, hFRk2, hFRl2, hlt2 R hR, hlt2 FR hFR, hob1 R hR, gIH, gIHv, gVE, gVEv, gTT, gTTm, gTTv, gPE, gPEv, hfw2, hE2, hEd2, hS2, hGd2, hFRk2, hFRl2, hob2 R hR dRF, hob2 fLP hLPo dLF, hlt2 R hR, hlt2 FR hFR, hlt2 fLP hLPo, gLB, gLBm, gLBv, gLP, gLPv, hfw1, hE1, hEd1, hS1, hGd1, hob1 R hR, hob1 FR hFR, hob1 fRel hRelo, hlt1 R hR, hlt1 FR hFR, hlt1 fRel hRelo, gER, gERm, gERv, gFW, gFWm, gFWv, gEL, gELv, gRE, gREv, gRel, gRelv, hR, hRk, hRs, hRf, hrs, hrf, hFR, hFRk, hFRl, e1, e1', e4, hG, hGe, gS, gSm, gSv, gVT, gVTm, gVTv, gRP, gRPv, hRPo, hRPk, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  obtain ⟨dPE, hPEk⟩ := hPEc
  refine ⟨by js_norm [CallableC, hlt3 fPE hPEo, hob3 fPE (hlt2 fPE hPEo), hob2 fPE hPEo dPF, hPEk], ?_⟩
  refine wp_mono (hPE _ _ ?fr4 ?st4 ?vt4 (by simp; omega)) ?_
  case st4 =>
    unfold BindIs
    rw [setEnv_envEntry_self _ _ _ (by first | exact hGd3 | (simp; omega))]
    simp only [declLike_withBindings', hGe, Option.map]
    simp [Std.HashMap.getElem?_modify, gS, gSm]
  case vt4 =>
    unfold BindIs
    rw [setEnv_envEntry_self _ _ _ (by first | exact hGd3 | (simp; omega))]
    simp only [declLike_withBindings', hGe, Option.map]
    simp [Std.HashMap.getElem?_modify, gVT, gVTm]
  case fr4 =>
    unfold FPA FPS
    have hdS : (Scope.declLike? (s.envEntry d.env)).isSome = true := by rw [hGe]; rfl
    refine frame_setEnv_with_in ?_ hG ?q1 ?q2 (by simp [Footprint.union]) _
    case q1 =>
      rw [setEnv_envEntry_ne _ _ _ _ e1', hEd3]
      exact setEnv_envEntry_self _ _ _ (by simp; omega)
    case q2 => simp only [declLike_isSome_withBindings]; exact hdS
    exact frame_setEnv_new hFs3 (Nat.le_refl _) _
  rintro v4 w4 h4 ⟨hF4, hfu4, rfl⟩
  have hfw4 : 2 * K + 100 ≤ w4.fuel := by simp at hfu4; omega
  have hE4 := envEntry_frame0 hF4 (e := s.envs.size) (by simp; omega)
  have hEd4 := envEntry_frame0 hF4 (e := d.env) (by simp; omega)
  have hS4 : s.envs.size < w4.envs.size := Nat.lt_of_lt_of_le (by simp; omega) hF4.envs_le
  have hGd4 : d.env < w4.envs.size := Nat.lt_trans hG hS4
  have hob4 : ∀ o, o < w3.heap.size → w4.objEntry o = w3.objEntry o := fun o ho => by
    rw [objEntry_frame0 hF4 (by simpa using ho)]; simp
  have hlt4 : ∀ o, o < s.heap.size → o < w4.heap.size := fun o ho =>
    Nat.lt_of_lt_of_le (by simpa using hlt3 o ho) hF4.heap_le
  have hFs4 : Frame (FPA d.env gP FR) s w4 := by
    refine frame_then_empty ?_ hF4
    unfold FPA FPS
    have hdS : (Scope.declLike? (s.envEntry d.env)).isSome = true := by rw [hGe]; rfl
    refine frame_setEnv_with_in ?_ hG ?q1 ?q2 (by simp [Footprint.union]) _
    case q1 =>
      rw [setEnv_envEntry_ne _ _ _ _ e1', hEd3]
      exact setEnv_envEntry_self _ _ _ (by simp; omega)
    case q2 => simp only [declLike_isSome_withBindings]; exact hdS
    exact frame_setEnv_new hFs3 (Nat.le_refl _) _
  js_until [] [hfw4, hE4, hEd4, hS4, hGd4, hob4 FR (hlt3 FR hFR), hob4 fEn (hlt3 fEn hEno), hob3 fEn (hlt2 fEn hEno), hob2 fEn hEno dEF, hlt4 FR hFR, hlt4 fEn hEno, hob3 FR (hlt2 FR hFR), hFRk2, hFRl2, gEn, gEnv, hfw3, hE3, hEd3, hS3, hGd3, hob3 FR (hlt2 FR hFR), hob3 R (hlt2 R hR), hob3 fPE (hlt2 fPE hPEo), hlt3 R hR, hlt3 FR hFR, hlt3 fPE hPEo, hob2 R hR dRF, hob2 fPE hPEo dPF, hFRk2, hFRl2, hlt2 R hR, hlt2 FR hFR, hob1 R hR, gIH, gIHv, gVE, gVEv, gTT, gTTm, gTTv, gPE, gPEv, hfw2, hE2, hEd2, hS2, hGd2, hFRk2, hFRl2, hob2 R hR dRF, hob2 fLP hLPo dLF, hlt2 R hR, hlt2 FR hFR, hlt2 fLP hLPo, gLB, gLBm, gLBv, gLP, gLPv, hfw1, hE1, hEd1, hS1, hGd1, hob1 R hR, hob1 FR hFR, hob1 fRel hRelo, hlt1 R hR, hlt1 FR hFR, hlt1 fRel hRelo, gER, gERm, gERv, gFW, gFWm, gFWv, gEL, gELv, gRE, gREv, gRel, gRelv, hR, hRk, hRs, hRf, hrs, hrf, hFR, hFRk, hFRl, e1, e1', e4, hG, hGe, gS, gSm, gSv, gVT, gVTm, gVTv, gRP, gRPv, hRPo, hRPk, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  obtain ⟨dEn, hEnk⟩ := hEnc
  refine ⟨by js_norm [CallableC, hlt4 fEn hEno, hob4 fEn (hlt3 fEn hEno), hob3 fEn (hlt2 fEn hEno), hob2 fEn hEno dEF, hEnk], ?_⟩
  refine wp_mono (hEn _ _ hFs4 (by omega)) ?_
  rintro v5 w5 h5 ⟨hF5, hFs5, hfu5, rfl⟩
  have hfw5 : K + 50 ≤ w5.fuel := by omega
  have hE5 := envEntry_frame hF5 (e := s.envs.size) hS4
    (List.all_eq_true.mpr fun p hp => by have := (hfpE p hp).1; simp; exact Nat.ne_of_lt this)
  obtain ⟨bw5, hd5, hbw5⟩ := declLike_frame hF5 (e := d.env) hGd4 (by
    rw [hEd4, setEnv_envEntry_self _ _ _ (by simp; omega)]
    simp only [declLike_withBindings', hGe, Option.map]
    rfl)
  have hnf : ∀ x, x ∈ [JSStr.ofString "nestedUpdateCount", JSStr.ofString "rootWithNestedUpdates",
      JSStr.ofString "flushSyncWorkAcrossRoots_impl"] → (d.env, x) ∉ fpE.binds := fun x hx hm =>
    (hfpE _ hm).2 rfl hx
  have hb1 := hbw5 _ (hnf (JSStr.ofString "nestedUpdateCount") (by simp))
  have hb2 := hbw5 _ (hnf (JSStr.ofString "rootWithNestedUpdates") (by simp))
  have hb3 := hbw5 _ (hnf (JSStr.ofString "flushSyncWorkAcrossRoots_impl") (by simp))
  have hS5 : s.envs.size < w5.envs.size := Nat.lt_of_lt_of_le hS4 hF5.envs_le
  have hGd5 : d.env < w5.envs.size := Nat.lt_trans hG hS5
  have hFRk5 : (w5.objEntry FR).kind = (s.objEntry FR).kind := by
    rw [kind_frame hF5 (hlt4 FR hFR), hob4 FR (hlt3 FR hFR), hob3 FR (hlt2 FR hFR)]; exact hFRk2
  have hFRl5 : (w5.objEntry FR).props.get? (.str (JSStr.ofString "pendingLanes")) =
      some (.data (.num (F64.fin false 0 (-1074))) plw ple plc) := by
    rw [props_frame hF5 (hlt4 FR hFR) (by simpa using fun hm => (hfpEp _ hm).1 rfl),
      hob4 FR (hlt3 FR hFR), hob3 FR (hlt2 FR hFR)]; exact hFRl2
  have hFS5 : w5.objEntry fFS = s.objEntry fFS := by
    rw [hF5.obj_eq fFS (hlt4 fFS hFSo) (fun k hk => (hfpEp _ hk).2 rfl), hob4 fFS (hlt3 fFS hFSo),
      hob3 fFS (hlt2 fFS hFSo), hob2 fFS hFSo dSF]
  have hlt5 : ∀ o, o < s.heap.size → o < w5.heap.size := fun o ho => Nat.lt_of_lt_of_le (hlt4 o ho) hF5.heap_le
  js_until [] [hfw5, hE5, hd5, hb1, hb2, hb3, hS5, hGd5, hFRk5, hFRl5, hFS5, hlt5 FR hFR, hlt5 fFS hFSo, Std.HashMap.getElem?_modify, gNC, gNCm, gNCv, gRN, gRNm, gRNv, gFS, gFSv, hfw4, hE4, hEd4, hS4, hGd4, hob4 FR (hlt3 FR hFR), hob4 fEn (hlt3 fEn hEno), hob3 fEn (hlt2 fEn hEno), hob2 fEn hEno dEF, hlt4 FR hFR, hlt4 fEn hEno, hob3 FR (hlt2 FR hFR), hFRk2, hFRl2, gEn, gEnv, hfw3, hE3, hEd3, hS3, hGd3, hob3 FR (hlt2 FR hFR), hob3 R (hlt2 R hR), hob3 fPE (hlt2 fPE hPEo), hlt3 R hR, hlt3 FR hFR, hlt3 fPE hPEo, hob2 R hR dRF, hob2 fPE hPEo dPF, hFRk2, hFRl2, hlt2 R hR, hlt2 FR hFR, hob1 R hR, gIH, gIHv, gVE, gVEv, gTT, gTTm, gTTv, gPE, gPEv, hfw2, hE2, hEd2, hS2, hGd2, hFRk2, hFRl2, hob2 R hR dRF, hob2 fLP hLPo dLF, hlt2 R hR, hlt2 FR hFR, hlt2 fLP hLPo, gLB, gLBm, gLBv, gLP, gLPv, hfw1, hE1, hEd1, hS1, hGd1, hob1 R hR, hob1 FR hFR, hob1 fRel hRelo, hlt1 R hR, hlt1 FR hFR, hlt1 fRel hRelo, gER, gERm, gERv, gFW, gFWm, gFWv, gEL, gELv, gRE, gREv, gRel, gRelv, hR, hRk, hRs, hRf, hrs, hrf, hFR, hFRk, hFRl, e1, e1', e4, hG, hGe, gS, gSm, gSv, gVT, gVTm, gVTv, gRP, gRPv, hRPo, hRPk, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  obtain ⟨dFS, hFSk⟩ := hFSc
  refine ⟨by js_norm [CallableC, hlt5 fFS hFSo, hFS5, hFSk], ?_⟩
  refine wp_mono (hFSs _ _ ?fr6 (by simp; omega)) ?_
  case fr6 =>
    unfold FPA FPS
    have hd5' : (Scope.declLike? (w5.envEntry d.env)).isSome = true := by rw [hd5]; rfl
    refine frame_setEnv_split (frame_setEnv_with_in ?_ hG (setEnv_envEntry_self _ _ _ ?q1) ?q2 ?q3 _)
    case q1 => simp; omega
    case q2 => simp only [declLike_isSome_withBindings]; exact hd5'
    case q3 => simp [Footprint.union]
    refine frame_setEnv_with_in ?_ hG ?q4 hd5' (by simp [Footprint.union]) _
    case q4 => exact setEnv_envEntry_ne _ _ _ _ e1'
    exact frame_setEnv_new hFs5 (Nat.le_refl _) _
  rintro v6 w6 h6 ⟨hF6, hfu6, rfl⟩
  have hE6 := envEntry_frame0 hF6 (e := s.envs.size) (by simp; omega)
  have hS6 : s.envs.size < w6.envs.size := Nat.lt_of_lt_of_le (by simp; omega) hF6.envs_le
  js_until [] [hE6, hS6, hfw5, hE5, hd5, hb1, hb2, hb3, hS5, hGd5, hFRk5, hFRl5, hFS5, hlt5 FR hFR, hlt5 fFS hFSo, Std.HashMap.getElem?_modify, gNC, gNCm, gNCv, gRN, gRNm, gRNv, gFS, gFSv, hfw4, hE4, hEd4, hS4, hGd4, hob4 FR (hlt3 FR hFR), hob4 fEn (hlt3 fEn hEno), hob3 fEn (hlt2 fEn hEno), hob2 fEn hEno dEF, hlt4 FR hFR, hlt4 fEn hEno, hob3 FR (hlt2 FR hFR), hFRk2, hFRl2, gEn, gEnv, hfw3, hE3, hEd3, hS3, hGd3, hob3 FR (hlt2 FR hFR), hob3 R (hlt2 R hR), hob3 fPE (hlt2 fPE hPEo), hlt3 R hR, hlt3 FR hFR, hlt3 fPE hPEo, hob2 R hR dRF, hob2 fPE hPEo dPF, hFRk2, hFRl2, hlt2 R hR, hlt2 FR hFR, hob1 R hR, gIH, gIHv, gVE, gVEv, gTT, gTTm, gTTv, gPE, gPEv, hfw2, hE2, hEd2, hS2, hGd2, hFRk2, hFRl2, hob2 R hR dRF, hob2 fLP hLPo dLF, hlt2 R hR, hlt2 FR hFR, hlt2 fLP hLPo, gLB, gLBm, gLBv, gLP, gLPv, hfw1, hE1, hEd1, hS1, hGd1, hob1 R hR, hob1 FR hFR, hob1 fRel hRelo, hlt1 R hR, hlt1 FR hFR, hlt1 fRel hRelo, gER, gERm, gERv, gFW, gFWm, gFWv, gEL, gELv, gRE, gREv, gRel, gRelv, hR, hRk, hRs, hRf, hrs, hrf, hFR, hFRk, hFRl, e1, e1', e4, hG, hGe, gS, gSm, gSv, gVT, gVTm, gVTv, gRP, gRPv, hRPo, hRPk, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  refine ⟨by simp [bodyState, entryState] at hfu1 hfu2 hfu3 hfu4 hfu6 ⊢; omega, frame_restore (frame_then_empty ?_ hF6) s⟩
  unfold FPA FPS
  have hd5' : (Scope.declLike? (w5.envEntry d.env)).isSome = true := by rw [hd5]; rfl
  refine frame_setEnv_split (frame_setEnv_with_in ?_ hG (setEnv_envEntry_self _ _ _ ?q1) ?q2 ?q3 _)
  case q1 => simp; omega
  case q2 => simp only [declLike_isSome_withBindings]; exact hd5'
  case q3 => simp [Footprint.union]
  refine frame_setEnv_with_in ?_ hG ?q4 hd5' (by simp [Footprint.union]) _
  case q4 => exact setEnv_envEntry_ne _ _ _ _ e1'
  exact frame_setEnv_new hFs5 (Nat.le_refl _) _


end

end ReactSpawned
