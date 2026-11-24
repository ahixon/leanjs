import JSProofs.FMEGen
import JSProofs.Setter
import JSProofs.ReactHostContainer
import JSProofs.Rebase
import JSProofs.ReactFacts

/-!
# flushMutationEffects for the click's commit (zippy docs/react-proofs.md)

`flushMutationEffects()` with effects pending (status 1) and mutation flags in the tree: the transition and priority
cleared around `commitMutationEffectsOnFiber(finishedWork, root, lanes)` (`executionContext |= 4`), the focused element
the same before and after (`getActiveElementDeep`: no selection to restore), events re-enabled, everything restored in
the `finally`, `root.current = finishedWork`, status 2. The two calls' contracts are premises.
-/

open ES ES.M HostRuns Logic
open Std (HashMap)
open ReactFacts (BindIs PropIs)

namespace ReactFlushMutation

/-- What `flushMutationEffects` writes before the mutation pass. -/
def FPRE (g : EnvId) (RSI RDSI : ObjId) : Footprint :=
  ⟨[(g, JSStr.ofString "pendingEffectsStatus"), (g, JSStr.ofString "rootViewTransitionAffected"),
    (g, JSStr.ofString "inUpdateViewTransition"), (g, JSStr.ofString "executionContext")],
   [(RSI, .str (JSStr.ofString "T")), (RDSI, .str (JSStr.ofString "p"))], false⟩

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ} {HI : σ → Prop}

theorem simple (d : FuncData) (hc : d.code = FMEGen.flushMutationEffects_func) : FDI.Simple d := by
  constructor <;> rw [hc] <;> try rfl
  simp [FMEGen.flushMutationEffects_func, Func.params, Func.info]

set_option maxRecDepth 40000 in
set_option maxHeartbeats 8000000 in
theorem fme_spec {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t : Value} {s : State}
    {bG : HashMap JSStr Binding} {oG : Option EnvId}
    {bdS bdR bdF bdL bdT bdD bdE bdU bdA bdC bdSI bdGD bdEn bdEv : Binding}
    {FR R RSI RDSI SI Cont E fC fGD : ObjId} {lv tv pv srv evv : Value} {rf sf ec : F64}
    {rfw rfe rfc sfw sfe sfc tw te tc pw pe pc cw ce cc ow oe oc fw fe fc rw re rc : Bool}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : 500 ≤ s.fuel)
    (hcode : d.code = FMEGen.flushMutationEffects_func) (hcls : d.isClassCtor = false) (hmode : d.thisMode = .strict)
    (hG : d.env < s.envs.size) (hGe : Scope.declLike? (s.envEntry d.env) = some (bG, oG))
    (hGS : bG[JSStr.ofString "pendingEffectsStatus"]? = some bdS) (hGSv : bdS.value = some (.num (F64.fin false 4503599627370496 (-52))))
    (hGSm : bdS.mutable = true)
    (hGR : bG[JSStr.ofString "pendingEffectsRoot"]? = some bdR) (hGRv : bdR.value = some (.obj FR))
    (hGF : bG[JSStr.ofString "pendingFinishedWork"]? = some bdF) (hGFv : bdF.value = some (.obj R))
    (hGL : bG[JSStr.ofString "pendingEffectsLanes"]? = some bdL) (hGLv : bdL.value = some lv)
    (hGT : bG[JSStr.ofString "ReactSharedInternals"]? = some bdT) (hGTv : bdT.value = some (.obj RSI))
    (hGD : bG[JSStr.ofString "ReactDOMSharedInternals"]? = some bdD) (hGDv : bdD.value = some (.obj RDSI))
    (hGE : bG[JSStr.ofString "executionContext"]? = some bdE) (hGEv : bdE.value = some (.num ec)) (hGEm : bdE.mutable = true)
    (hGU : bG[JSStr.ofString "inUpdateViewTransition"]? = some bdU) (hGUm : bdU.mutable = true) (hGUi : bdU.value.isSome = true)
    (hGA : bG[JSStr.ofString "rootViewTransitionAffected"]? = some bdA) (hGAm : bdA.mutable = true) (hGAi : bdA.value.isSome = true)
    (hGC : bG[JSStr.ofString "commitMutationEffectsOnFiber"]? = some bdC) (hGCv : bdC.value = some (.obj fC))
    (hGSI : bG[JSStr.ofString "selectionInformation"]? = some bdSI) (hGSIv : bdSI.value = some (.obj SI))
    (hGSIm : bdSI.mutable = true)
    (hGGD : bG[JSStr.ofString "getActiveElementDeep"]? = some bdGD) (hGGDv : bdGD.value = some (.obj fGD))
    (hGEn : bG[JSStr.ofString "_enabled"]? = some bdEn) (hGEnm : bdEn.mutable = true) (hGEni : bdEn.value.isSome = true)
    (hGEv' : bG[JSStr.ofString "eventsEnabled"]? = some bdEv) (hGEvv : bdEv.value = some evv) (hGEvm : bdEv.mutable = true)
    (hR : R < s.heap.size) (hRk : (s.objEntry R).kind.isPlain = true)
    (hRf : (s.objEntry R).props.get? (.str (JSStr.ofString "flags")) = some (.data (.num rf) rfw rfe rfc))
    (hRs : (s.objEntry R).props.get? (.str (JSStr.ofString "subtreeFlags")) = some (.data (.num sf) sfw sfe sfc))
    (hsf : isStrictlyEqual (.num (F64.fin false 0 (-1074)))
      (.num (numberBinOp .bitAnd sf (F64.fin false 7629511185137664 (-39)))) = false)
    (hRSI : RSI < s.heap.size) (hRSIk : (s.objEntry RSI).kind.isPlain = true)
    (hRSIt : (s.objEntry RSI).props.get? (.str (JSStr.ofString "T")) = some (.data tv true te tc))
    (hRDSI : RDSI < s.heap.size) (hRDSIk : (s.objEntry RDSI).kind.isPlain = true)
    (hRDSIp : (s.objEntry RDSI).props.get? (.str (JSStr.ofString "p")) = some (.data pv true pe pc))
    (hFR : FR < s.heap.size) (hFRk : (s.objEntry FR).kind.isPlain = true)
    (hFRc : (s.objEntry FR).props.get? (.str (JSStr.ofString "containerInfo")) = some (.data (.obj Cont) cw ce cc))
    (hFRcur : ∃ v0, (s.objEntry FR).props.get? (.str (JSStr.ofString "current")) = some (.data v0 true ow oe))
    (hSI : SI < s.heap.size) (hSIk : (s.objEntry SI).kind.isPlain = true)
    (hSIf : (s.objEntry SI).props.get? (.str (JSStr.ofString "focusedElem")) = some (.data (.obj E) fw fe fc))
    (hSIr : (s.objEntry SI).props.get? (.str (JSStr.ofString "selectionRange")) = some (.data srv rw re rc))
    (hCo : fC < s.heap.size) (hCc : ∃ dd, (s.objEntry fC).kind = .func dd)
    (hGDo : fGD < s.heap.size) (hGDc : ∃ dd, (s.objEntry fGD).kind = .func dd)
    (dTD : RSI ≠ RDSI) (dTF : RSI ≠ FR) (dDF : RDSI ≠ FR) (dTS : RSI ≠ SI) (dDS : RDSI ≠ SI) (dFS : FR ≠ SI)
    (dTR : RSI ≠ R) (dDR : RDSI ≠ R) (dTC : RSI ≠ fC) (dDC : RDSI ≠ fC) (dTG : RSI ≠ fGD) (dDG : RDSI ≠ fGD)
    {KC : Nat} {fpC : Footprint} {PC : State → σ → Prop}
    (hC : ∀ w h1, Frame (FPRE d.env RSI RDSI) s w → HI h1 → KC ≤ w.fuel →
      WP eng answer (n + 1) h1 (callImpl eng (.obj fC) .undefined #[.obj R, .obj FR, lv]) w fun v w' h' =>
        v = .undefined ∧ w.fuel ≤ w'.fuel + KC ∧ PC w' h' ∧ HI h' ∧ Frame fpC w w')
    (hfC : KC + 700 ≤ s.fuel)
    (hfpC : ∀ p, p ∈ fpC.binds → p.1 = d.env ∧ p.2 ∉ [JSStr.ofString "selectionInformation",
      JSStr.ofString "getActiveElementDeep", JSStr.ofString "eventsEnabled", JSStr.ofString "_enabled",
      JSStr.ofString "executionContext", JSStr.ofString "ReactDOMSharedInternals", JSStr.ofString "ReactSharedInternals",
      JSStr.ofString "pendingEffectsStatus"])
    (hfpCp : ∀ p, p ∈ fpC.props → p.1 ≠ SI ∧ p.1 ≠ RSI ∧ p.1 ≠ RDSI ∧ p.1 ≠ FR ∧ p.1 ≠ fGD)
    (hGDC : ∀ w h1, Frame ((FPRE d.env RSI RDSI).union fpC) s w → HI h1 → 200 ≤ w.fuel →
      WP eng answer (n + 1) h1 (callImpl eng (.obj fGD) .undefined #[.obj Cont]) w fun v w' h' =>
        v = .obj E ∧ Frame {} w w' ∧ w.fuel ≤ w'.fuel + 200 ∧ h' = h1) (hHI : HI h) :
    WP eng answer (n + 2) h (callImpl eng (.obj fo) t #[]) s fun v w h' =>
      v = .undefined ∧ s.fuel ≤ w.fuel + KC + 700 ∧ (∃ w0, PC w0 h') ∧ HI h' ∧
      Frame (((FPRE d.env RSI RDSI).union fpC).union ⟨[(d.env, JSStr.ofString "selectionInformation"),
        (d.env, JSStr.ofString "eventsEnabled"), (d.env, JSStr.ofString "_enabled")],
        [(FR, .str (JSStr.ofString "current"))], false⟩) s w ∧
      BindIs w d.env (JSStr.ofString "pendingEffectsStatus") (.num (F64.fin false 4503599627370496 (-51))) ∧
      BindIs w d.env (JSStr.ofString "executionContext") (.num ec) ∧
      PropIs w RSI (JSStr.ofString "T") tv ∧ PropIs w RDSI (JSStr.ofString "p") pv := by
  apply wp_callGen FMEGen.flushMutationEffects_eq (by decide) hlt hk (by omega) hcls hmode
    (by rw [hcode]; rfl) (by rw [hcode]; rfl) (simple d hcode) (by rw [hcode]; rfl) (by rw [hcode]; rfl)
  have hpn : d.code.info.fdi.paramNames = #[] := by rw [hcode]; rfl
  have hv : d.code.info.fdi.varNames = #[JSStr.ofString "root", JSStr.ofString "finishedWork", JSStr.ofString "lanes",
    JSStr.ofString "rootMutationHasEffect", JSStr.ofString "previousPriority", JSStr.ofString "prevExecutionContext",
    JSStr.ofString "curFocusedElem", JSStr.ofString "priorFocusedElem", JSStr.ofString "priorSelectionRange",
    JSStr.ofString "start", JSStr.ofString "end", JSStr.ofString "doc", JSStr.ofString "win",
    JSStr.ofString "selection", JSStr.ofString "length", JSStr.ofString "start$jscomp$0",
    JSStr.ofString "end$jscomp$0", JSStr.ofString "startMarker", JSStr.ofString "endMarker", JSStr.ofString "range",
    JSStr.ofString "info"] := by rw [hcode]; rfl
  have hl : FDI.lexDecls d = #[] := by simp [FDI.lexDecls, hcode, FMEGen.flushMutationEffects_func, Func.info]
  have ha : d.code.isAsync = false := by rw [hcode]; rfl
  have e1 : d.env ≠ s.envs.size := Nat.ne_of_lt hG
  have e1' : s.envs.size ≠ d.env := Ne.symm e1
  have e4 : d.env < s.envs.size + 1 := Nat.lt_succ_of_lt hG
  have e2 : d.env ≠ s.envs.size + 1 := Nat.ne_of_lt e4
  have e2' : s.envs.size + 1 ≠ d.env := Ne.symm e2
  have e5 : d.env < s.envs.size + 1 + 1 := Nat.lt_succ_of_lt e4
  obtain ⟨dC, hCk⟩ := hCc
  obtain ⟨dGD, hGDk⟩ := hGDc
  obtain ⟨v0, hFRcur'⟩ := hFRcur
  clear hcode
  simp only [FMEGen.flushMutationEffects]
  js_until [] [e1, e1', e2, e2', e4, e5, hG, hGe, hGS, hGSv, hGSm, hGR, hGRv, hGF, hGFv, hGL, hGLv, hGT, hGTv, hGD, hGDv, hGE, hGEv, hGEm, hGU, hGUm, hGUi, hGA, hGAm, hGAi, hGC, hGCv, hR, hRk, hRf, hRs, hsf, dTD, Ne.symm dTD, dTF, Ne.symm dTF, dDF, Ne.symm dDF, dTS, Ne.symm dTS, dDS, Ne.symm dDS, dFS, Ne.symm dFS, dTR, Ne.symm dTR, dDR, Ne.symm dDR, dTC, Ne.symm dTC, dDC, Ne.symm dDC, dTG, Ne.symm dTG, dDG, Ne.symm dDG, hRSI, hRSIk, hRSIt, hRDSI, hRDSIk, hRDSIp, hCo, hCk, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  refine ⟨by js_norm [CallableC, hCo, hCk, dTC, Ne.symm dTC, dDC, Ne.symm dDC], ?_⟩
  refine wp_mono (hC _ _ ?_ hHI ?_) ?_
  · unfold FPRE; frame_go' [*]
  · simp; omega
  rintro v1 w1 h1 ⟨rfl, hfu1, hP1, hHI1, hF1⟩
  have hEa := envEntry_frame hF1 (e := s.envs.size) (by js_norm [e1, e1', e2, e2', e4, e5, hG, hGe, hGS, hGSv, hGSm, hGR, hGRv, hGF, hGFv, hGL, hGLv, hGT, hGTv, hGD, hGDv, hGE, hGEv, hGEm, hGU, hGUm, hGUi, hGA, hGAm, hGAi, hGC, hGCv, hR, hRk, hRf, hRs, hsf, dTD, Ne.symm dTD, dTF, Ne.symm dTF, dDF, Ne.symm dDF, dTS, Ne.symm dTS, dDS, Ne.symm dDS, dFS, Ne.symm dFS, dTR, Ne.symm dTR, dDR, Ne.symm dDR, dTC, Ne.symm dTC, dDC, Ne.symm dDC, dTG, Ne.symm dTG, dDG, Ne.symm dDG, hRSI, hRSIk, hRSIt, hRDSI, hRDSIk, hRDSIp, hCo, hCk, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner])
    (List.all_eq_true.mpr fun p hp => by simp [(hfpC p hp).1, e1])
  have hSb : s.envs.size < w1.envs.size := Nat.lt_of_lt_of_le (by js_norm [e1, e1', e2, e2', e4, e5, hG, hGe, hGS, hGSv, hGSm, hGR, hGRv, hGF, hGFv, hGL, hGLv, hGT, hGTv, hGD, hGDv, hGE, hGEv, hGEm, hGU, hGUm, hGUi, hGA, hGAm, hGAi, hGC, hGCv, hR, hRk, hRf, hRs, hsf, dTD, Ne.symm dTD, dTF, Ne.symm dTF, dDF, Ne.symm dDF, dTS, Ne.symm dTS, dDS, Ne.symm dDS, dFS, Ne.symm dFS, dTR, Ne.symm dTR, dDR, Ne.symm dDR, dTC, Ne.symm dTC, dDC, Ne.symm dDC, dTG, Ne.symm dTG, dDG, Ne.symm dDG, hRSI, hRSIk, hRSIt, hRDSI, hRDSIk, hRDSIp, hCo, hCk, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]) hF1.envs_le
  have hGd : d.env < w1.envs.size := Nat.lt_trans hG hSb
  obtain ⟨bw, hd1, hbw⟩ := declLike_frame hF1 (e := d.env) (by js_norm [e1, e1', e2, e2', e4, e5, hG, hGe, hGS, hGSv, hGSm, hGR, hGRv, hGF, hGFv, hGL, hGLv, hGT, hGTv, hGD, hGDv, hGE, hGEv, hGEm, hGU, hGUm, hGUi, hGA, hGAm, hGAi, hGC, hGCv, hR, hRk, hRf, hRs, hsf, dTD, Ne.symm dTD, dTF, Ne.symm dTF, dDF, Ne.symm dDF, dTS, Ne.symm dTS, dDS, Ne.symm dDS, dFS, Ne.symm dFS, dTR, Ne.symm dTR, dDR, Ne.symm dDR, dTC, Ne.symm dTC, dDC, Ne.symm dDC, dTG, Ne.symm dTG, dDG, Ne.symm dDG, hRSI, hRSIk, hRSIt, hRDSI, hRDSIk, hRDSIp, hCo, hCk, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]) (by js_norm [e1, e1', e2, e2', e4, e5, hG, hGe, hGS, hGSv, hGSm, hGR, hGRv, hGF, hGFv, hGL, hGLv, hGT, hGTv, hGD, hGDv, hGE, hGEv, hGEm, hGU, hGUm, hGUi, hGA, hGAm, hGAi, hGC, hGCv, hR, hRk, hRf, hRs, hsf, dTD, Ne.symm dTD, dTF, Ne.symm dTF, dDF, Ne.symm dDF, dTS, Ne.symm dTS, dDS, Ne.symm dDS, dFS, Ne.symm dFS, dTR, Ne.symm dTR, dDR, Ne.symm dDR, dTC, Ne.symm dTC, dDC, Ne.symm dDC, dTG, Ne.symm dTG, dDG, Ne.symm dDG, hRSI, hRSIk, hRSIt, hRDSI, hRDSIk, hRDSIp, hCo, hCk, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]; rfl)
  have hfw1 : 550 ≤ w1.fuel := by simp [bodyState, entryState] at hfu1; omega
  have hfr1 : s.fuel ≤ w1.fuel + KC + 60 := by simp [bodyState, entryState] at hfu1; omega
  have hobj : ∀ o, o = SI ∨ o = RSI ∨ o = RDSI ∨ o = FR ∨ o = fGD → w1.objEntry o = _ := fun o ho =>
    hF1.obj_eq o (by rcases ho with rfl | rfl | rfl | rfl | rfl <;> js_norm [hSI, hFR, hGDo, e1, e1', e2, e2', e4, e5, hG, hGe, hGS, hGSv, hGSm, hGR, hGRv, hGF, hGFv, hGL, hGLv, hGT, hGTv, hGD, hGDv, hGE, hGEv, hGEm, hGU, hGUm, hGUi, hGA, hGAm, hGAi, hGC, hGCv, hR, hRk, hRf, hRs, hsf, dTD, Ne.symm dTD, dTF, Ne.symm dTF, dDF, Ne.symm dDF, dTS, Ne.symm dTS, dDS, Ne.symm dDS, dFS, Ne.symm dFS, dTR, Ne.symm dTR, dDR, Ne.symm dDR, dTC, Ne.symm dTC, dDC, Ne.symm dDC, dTG, Ne.symm dTG, dDG, Ne.symm dDG, hRSI, hRSIk, hRSIt, hRDSI, hRDSIk, hRDSIp, hCo, hCk, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner])
      (fun k hk => by have := hfpCp _ hk; rcases ho with rfl | rfl | rfl | rfl | rfl <;> simp_all)
  have hb0 := hbw (JSStr.ofString "selectionInformation") (fun hm => (hfpC _ hm).2 (by simp))
  have hb1 := hbw (JSStr.ofString "getActiveElementDeep") (fun hm => (hfpC _ hm).2 (by simp))
  have hb2 := hbw (JSStr.ofString "eventsEnabled") (fun hm => (hfpC _ hm).2 (by simp))
  have hb3 := hbw (JSStr.ofString "_enabled") (fun hm => (hfpC _ hm).2 (by simp))
  have hb4 := hbw (JSStr.ofString "executionContext") (fun hm => (hfpC _ hm).2 (by simp))
  have hb5 := hbw (JSStr.ofString "ReactDOMSharedInternals") (fun hm => (hfpC _ hm).2 (by simp))
  have hb6 := hbw (JSStr.ofString "ReactSharedInternals") (fun hm => (hfpC _ hm).2 (by simp))
  have hb7 := hbw (JSStr.ofString "pendingEffectsStatus") (fun hm => (hfpC _ hm).2 (by simp))
  have hFs1 : Frame ((FPRE d.env RSI RDSI).union fpC) s w1 := frame_trans (by unfold FPRE; frame_go' [*]) hF1
  have hlt1 : ∀ o, o < s.heap.size → o < w1.heap.size := fun o ho => Nat.lt_of_lt_of_le ho hFs1.heap_le
  js_until [] [hlt1 FR hFR, hlt1 SI hSI, hlt1 RSI hRSI, hlt1 RDSI hRDSI, hlt1 fGD hGDo, hEa, hSb, hGd, hd1, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hobj SI (by simp), hobj RSI (by simp), hobj RDSI (by simp), hobj FR (by simp), hobj fGD (by simp), hfw1, hGSI, hGSIv, hGGD, hGGDv, hSI, hSIk, hSIf, hSIr, hFRc, hFR, hFRk, hGDo, hGDk, e1, e1', e2, e2', e4, e5, hG, hGe, hGS, hGSv, hGSm, hGR, hGRv, hGF, hGFv, hGL, hGLv, hGT, hGTv, hGD, hGDv, hGE, hGEv, hGEm, hGU, hGUm, hGUi, hGA, hGAm, hGAi, hGC, hGCv, hR, hRk, hRf, hRs, hsf, dTD, Ne.symm dTD, dTF, Ne.symm dTF, dDF, Ne.symm dDF, dTS, Ne.symm dTS, dDS, Ne.symm dDS, dFS, Ne.symm dFS, dTR, Ne.symm dTR, dDR, Ne.symm dDR, dTC, Ne.symm dTC, dDC, Ne.symm dDC, dTG, Ne.symm dTG, dDG, Ne.symm dDG, hRSI, hRSIk, hRSIt, hRDSI, hRDSIk, hRDSIp, hCo, hCk, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  refine ⟨by js_norm [CallableC, hlt1 FR hFR, hlt1 SI hSI, hlt1 RSI hRSI, hlt1 RDSI hRDSI, hlt1 fGD hGDo, hEa, hSb, hGd, hd1, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hobj SI (by simp), hobj RSI (by simp), hobj RDSI (by simp), hobj FR (by simp), hobj fGD (by simp), hfw1, hGSI, hGSIv, hGGD, hGGDv, hSI, hSIk, hSIf, hSIr, hFRc, hFR, hFRk, hGDo, hGDk, e1, e1', e2, e2', e4, e5, hG, hGe, hGS, hGSv, hGSm, hGR, hGRv, hGF, hGFv, hGL, hGLv, hGT, hGTv, hGD, hGDv, hGE, hGEv, hGEm, hGU, hGUm, hGUi, hGA, hGAm, hGAi, hGC, hGCv, hR, hRk, hRf, hRs, hsf, dTD, Ne.symm dTD, dTF, Ne.symm dTF, dDF, Ne.symm dDF, dTS, Ne.symm dTS, dDS, Ne.symm dDS, dFS, Ne.symm dFS, dTR, Ne.symm dTR, dDR, Ne.symm dDR, dTC, Ne.symm dTC, dDC, Ne.symm dDC, dTG, Ne.symm dTG, dDG, Ne.symm dDG, hRSI, hRSIk, hRSIt, hRDSI, hRDSIk, hRDSIp, hCo, hCk, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner], ?_⟩
  refine wp_mono (hGDC _ _ (frame_setEnv_new hFs1 (by simp) _) hHI1 (by simp; omega)) ?_
  rintro v2 w2 h2 ⟨rfl, hF2, hfu2, rfl⟩
  have hE2 := envEntry_frame0 hF2 (e := s.envs.size) (by simp; omega)
  have hE2d := envEntry_frame0 hF2 (e := d.env) (by simp; omega)
  have hS2 : s.envs.size < w2.envs.size := Nat.lt_of_lt_of_le (by simp; omega) hF2.envs_le
  have hGd2 : d.env < w2.envs.size := Nat.lt_trans hG hS2
  have hob2 : ∀ o, o < w1.heap.size → w2.objEntry o = w1.objEntry o := fun o ho => by
    rw [objEntry_frame0 hF2 (by simpa using ho)]; simp
  have hlt2 : ∀ o, o < w1.heap.size → o < w2.heap.size := fun o ho => Nat.lt_of_lt_of_le (by simpa using ho) hF2.heap_le
  have hfw2 : 300 ≤ w2.fuel := by simp at hfu2; omega
  have hfr2 : w1.fuel ≤ w2.fuel + 200 := by simp at hfu2; omega
  have hFs2 : Frame ((FPRE d.env RSI RDSI).union fpC) s w2 :=
    frame_then_empty (frame_setEnv_new hFs1 (by simp) _) hF2
  have hEE : isStrictlyEqual (.obj E) (.obj E) = true := by simp [isStrictlyEqual, sameValue]
  js_until [] [hEE, hE2, hE2d, hS2, hGd2, hob2 SI (hlt1 SI hSI), hob2 RSI (hlt1 RSI hRSI), hob2 RDSI (hlt1 RDSI hRDSI), hob2 FR (hlt1 FR hFR), hlt2 SI (hlt1 SI hSI), hlt2 RSI (hlt1 RSI hRSI), hlt2 RDSI (hlt1 RDSI hRDSI), hlt2 FR (hlt1 FR hFR), hfw2, hlt1 FR hFR, hlt1 SI hSI, hlt1 RSI hRSI, hlt1 RDSI hRDSI, hlt1 fGD hGDo, hEa, hSb, hGd, hd1, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hobj SI (by simp), hobj RSI (by simp), hobj RDSI (by simp), hobj FR (by simp), hobj fGD (by simp), hfw1, hGSI, hGSIv, hGGD, hGGDv, hSI, hSIk, hSIf, hSIr, hFRc, hFR, hFRk, hGDo, hGDk, e1, e1', e2, e2', e4, e5, hG, hGe, hGS, hGSv, hGSm, hGR, hGRv, hGF, hGFv, hGL, hGLv, hGT, hGTv, hGD, hGDv, hGE, hGEv, hGEm, hGU, hGUm, hGUi, hGA, hGAm, hGAi, hGC, hGCv, hR, hRk, hRf, hRs, hsf, dTD, Ne.symm dTD, dTF, Ne.symm dTF, dDF, Ne.symm dDF, dTS, Ne.symm dTS, dDS, Ne.symm dDS, dFS, Ne.symm dFS, dTR, Ne.symm dTR, dDR, Ne.symm dDR, dTC, Ne.symm dTC, dDC, Ne.symm dDC, dTG, Ne.symm dTG, dDG, Ne.symm dDG, hRSI, hRSIk, hRSIt, hRDSI, hRDSIk, hRDSIp, hCo, hCk, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  refine ⟨by omega, ⟨w1, hP1⟩, ?_, ?st2, ?ec2, ?pt2, ?pp2⟩
  case st2 =>
    unfold BindIs
    rw [restore_envEntry, setEnv_envEntry_self _ _ _ (by simp; omega)]
    simp only [declLike_withBindings', hd1, Option.map]
    simp [Std.HashMap.getElem?_modify, hb7, hGS, hGSm]
  case ec2 =>
    unfold BindIs
    rw [restore_envEntry, setEnv_envEntry_self _ _ _ (by simp; omega)]
    simp only [declLike_withBindings', hd1, Option.map]
    simp [Std.HashMap.getElem?_modify, hb4, hGE, hGEm]
  case pt2 =>
    refine ⟨te, tc, ?_⟩
    simp only [restore_objEntry, setEnv_objEntry, setProp_objEntry]
    simp [dTF, Ne.symm dTF, dTD, Ne.symm dTD, hlt2 RSI (hlt1 RSI hRSI)]
  case pp2 =>
    refine ⟨pe, pc, ?_⟩
    simp only [restore_objEntry, setEnv_objEntry, setProp_objEntry]
    simp [dDF, Ne.symm dDF, dTD, Ne.symm dTD, hlt2 RDSI (hlt1 RDSI hRDSI)]
  have hdS : (Scope.declLike? (w2.envEntry d.env)).isSome = true := by
    rw [hE2d]; simp [setEnv_envEntry_ne _ _ _ _ e1']; rw [hd1]; rfl
  refine frame_restore ?_ s
  refine frame_setEnv_with_in (x := JSStr.ofString "pendingEffectsStatus") ?_ hG ?hentA ?hdsA (by simp [Footprint.union, FPRE]) _
  case hentA => simp [hGd2]
  case hdsA =>
    simp only [declLike_isSome_withBindings]
    rw [hd1]; rfl
  refine frame_setProp_in ?_ hFR (by simp [Footprint.union]) _
  refine frame_setProp_in ?_ hRSI (by simp [Footprint.union, FPRE]) _
  refine frame_setProp_in ?_ hRDSI (by simp [Footprint.union, FPRE]) _
  refine frame_setEnv_split (frame_setEnv_with_in (x := JSStr.ofString "executionContext") ?_ hG
    (setEnv_envEntry_self _ _ _ (by simpa using hGd2))
    (by simp only [declLike_isSome_withBindings]; rw [hd1]; rfl) (by simp [Footprint.union, FPRE]) _)
  refine frame_setEnv_split (frame_setEnv_with_in (x := JSStr.ofString "selectionInformation") ?_ hG
    (setEnv_envEntry_self _ _ _ (by simpa using hGd2))
    (by simp only [declLike_isSome_withBindings]; rw [hd1]; rfl) (by simp [Footprint.union, FPRE]) _)
  refine frame_setEnv_split (frame_setEnv_with_in (x := JSStr.ofString "eventsEnabled") ?_ hG
    (setEnv_envEntry_self _ _ _ (by simpa using hGd2))
    (by simp only [declLike_isSome_withBindings]; rw [hd1]; rfl) (by simp [Footprint.union, FPRE]) _)
  refine frame_setEnv_with_in (x := JSStr.ofString "_enabled") (frame_setEnv_new (frame_mono hFs2 (fun p hp => List.mem_append.mpr (Or.inl hp))
      (fun p hp => List.mem_append.mpr (Or.inl hp)) (fun hj => by simp [Footprint.union] at hj ⊢; exact hj)) (Nat.le_refl _) _) hG ?_
    (by rw [hd1]; rfl) (by simp [Footprint.union, FPRE]) _
  rw [setEnv_envEntry_ne _ _ _ _ e1', hE2d, setEnv_envEntry_ne _ _ _ _ e1']

end

end ReactFlushMutation
