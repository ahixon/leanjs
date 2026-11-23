import JSProofs.CBMCSwitch
import JSProofs.CBMGen
import JSProofs.Setter
import JSProofs.ReactHostContainer
import JSProofs.Rebase
import JSProofs.Loops5
import JSProofs.Loops4
import JSProofs.Switch

/-!
# The before-mutation pass for the click's commit (zippy docs/react-proofs.md)

`commitBeforeMutationEffects_complete(false)` from the host root fiber (no Snapshot flag, no sibling, no parent):
nothing, `nextEffect` null (`cbmc_root`).
-/

open ES ES.M HostRuns Logic
open Std (HashMap)

namespace ReactBeforeMutation

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ}

theorem simpleC (d : FuncData) (hc : d.code = CBMCGen.commitBeforeMutationEffects_complete_func) : FDI.Simple d := by
  constructor <;> rw [hc] <;> try rfl
  simp [CBMCGen.commitBeforeMutationEffects_complete_func, Func.params, Func.info]

set_option maxRecDepth 40000 in
set_option maxHeartbeats 8000000 in
theorem cbmc_root {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t : Value} {s : State}
    {bG : HashMap JSStr Binding} {oG : Option EnvId} {bdN : Binding} {R : ObjId} {av : Value} {fl : F64}
    {aw ae ac fw fe fc tw te tc sw se sc rw re rc : Bool}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : 200 ≤ s.fuel)
    (hcode : d.code = CBMCGen.commitBeforeMutationEffects_complete_func) (hcls : d.isClassCtor = false)
    (hmode : d.thisMode = .strict)
    (hG : d.env < s.envs.size) (hGe : Scope.declLike? (s.envEntry d.env) = some (bG, oG))
    (hGN : bG[JSStr.ofString "nextEffect"]? = some bdN) (hGNv : bdN.value = some (.obj R)) (hGNm : bdN.mutable = true)
    (hR : R < s.heap.size) (hRk : (s.objEntry R).kind.isPlain = true)
    (hRa : (s.objEntry R).props.get? (.str (JSStr.ofString "alternate")) = some (.data av aw ae ac))
    (hRf : (s.objEntry R).props.get? (.str (JSStr.ofString "flags")) = some (.data (.num fl) fw fe fc))
    (hRt : (s.objEntry R).props.get? (.str (JSStr.ofString "tag")) =
      some (.data (.num (F64.fin false 6755399441055744 (-51))) tw te tc))
    (hRs : (s.objEntry R).props.get? (.str (JSStr.ofString "sibling")) = some (.data .null sw se sc))
    (hRr : (s.objEntry R).props.get? (.str (JSStr.ofString "return")) = some (.data .null rw re rc))
    (h1024 : numberBinOp .bitAnd fl (F64.fin false 4503599627370496 (-42)) = F64.fin false 0 (-1074)) :
    WP eng answer (n + 1) h (callImpl eng (.obj fo) t #[.bool false]) s fun v w h' =>
      v = .undefined ∧ s.fuel ≤ w.fuel + 200 ∧ h' = h ∧
      Frame ⟨[(d.env, JSStr.ofString "nextEffect")], [], false⟩ s w ∧
      ∃ bm, Scope.declLike? (w.envEntry d.env) = some (bm, oG) ∧
        (∃ bd, bm[JSStr.ofString "nextEffect"]? = some bd ∧ bd.value = some .null) ∧
        ∀ x, x ≠ JSStr.ofString "nextEffect" → bm[x]? = bG[x]? := by
  apply wp_callGen CBMCGen.commitBeforeMutationEffects_complete_eq (by decide) hlt hk (by omega) hcls hmode
    (by rw [hcode]; rfl) (by rw [hcode]; rfl) (simpleC d hcode) (by rw [hcode]; rfl) (by rw [hcode]; rfl)
  have hpn : d.code.info.fdi.paramNames = #[JSStr.ofString "isViewTransitionEligible$jscomp$0"] := by rw [hcode]; rfl
  have hv : d.code.info.fdi.varNames = #[JSStr.ofString "fiber", JSStr.ofString "isViewTransitionEligible",
    JSStr.ofString "current", JSStr.ofString "flags", JSStr.ofString "instance", JSStr.ofString "resolvedPrevProps"] := by
    rw [hcode]; rfl
  have hl : FDI.lexDecls d = #[] := by
    simp [FDI.lexDecls, hcode, CBMCGen.commitBeforeMutationEffects_complete_func, Func.info]
  have ha : d.code.isAsync = false := by rw [hcode]; rfl
  have e1 : d.env ≠ s.envs.size := Nat.ne_of_lt hG
  have e1' : s.envs.size ≠ d.env := Ne.symm e1
  have e4 : d.env < s.envs.size + 1 := Nat.lt_succ_of_lt hG
  have e2 : d.env ≠ s.envs.size + 1 := Nat.ne_of_lt e4
  have e2' : s.envs.size + 1 ≠ d.env := Ne.symm e2
  have e5 : d.env < s.envs.size + 1 + 1 := Nat.lt_succ_of_lt e4
  clear hcode
  simp only [CBMCGen.commitBeforeMutationEffects_complete]
  js_until [] [e1, e1', e2, e2', e4, e5, hG, hGe, hGN, hGNv, hGNm, hR, hRk, hRa, hRf, hRt, hRs, hRr, h1024, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  refine wp_forNone ?_
  js_until [] [e1, e1', e2, e2', e4, e5, hG, hGe, hGN, hGNv, hGNm, hR, hRk, hRa, hRf, hRt, hRs, hRr, h1024, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  refine ⟨by omega, by frame_go' [*], _, rfl, ⟨_, Std.HashMap.getElem?_modify_self.trans (by rw [hGN]; rfl), rfl⟩,
    fun x hx => by simp [Std.HashMap.getElem?_modify, Ne.symm hx]⟩

theorem envEntry_withFuel' (s : State) (f : Nat) (e : EnvId) : (s.withFuel f).envEntry e = s.envEntry e := rfl
theorem envs_withFuel' (s : State) (f : Nat) : (s.withFuel f).envs = s.envs := rfl

theorem simple (d : FuncData) (hc : d.code = CBMGen.commitBeforeMutationEffects_func) : FDI.Simple d := by
  constructor <;> rw [hc] <;> try rfl
  simp [CBMGen.commitBeforeMutationEffects_func, Func.params, Func.info]

/-- What `commitBeforeMutationEffects` writes before its walk. -/
def FB (g : EnvId) : Footprint :=
  ⟨[(g, JSStr.ofString "eventsEnabled"), (g, JSStr.ofString "selectionInformation"), (g, JSStr.ofString "_enabled"),
    (g, JSStr.ofString "nextEffect"), (g, JSStr.ofString "appearingViewTransitions")], [], false⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 8000000 in
theorem cbm_spec {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t : Value} {s : State}
    {bG : HashMap JSStr Binding} {oG : Option EnvId}
    {bdEv bdEn bdGD bdHS bdSI bdNE bdCC bdAV : Binding} {FR R Cont E Rc K fGD fHS fCC : ObjId} {ev0 : Value}
    {lanes sf : F64} {cw ce cc aw ae ac tw te tc kw ke kc sw se sc : Bool}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : 1000 ≤ s.fuel)
    (hcode : d.code = CBMGen.commitBeforeMutationEffects_func) (hcls : d.isClassCtor = false)
    (hmode : d.thisMode = .strict)
    (hG : d.env < s.envs.size) (hGe : Scope.declLike? (s.envEntry d.env) = some (bG, oG))
    (hGEv : bG[JSStr.ofString "eventsEnabled"]? = some bdEv) (hGEvm : bdEv.mutable = true) (hGEvi : bdEv.value.isSome = true)
    (hGEn : bG[JSStr.ofString "_enabled"]? = some bdEn) (hGEnv : bdEn.value = some ev0) (hGEnm : bdEn.mutable = true)
    (hGGD : bG[JSStr.ofString "getActiveElementDeep"]? = some bdGD) (hGGDv : bdGD.value = some (.obj fGD))
    (hGHS : bG[JSStr.ofString "hasSelectionCapabilities"]? = some bdHS) (hGHSv : bdHS.value = some (.obj fHS))
    (hGSI : bG[JSStr.ofString "selectionInformation"]? = some bdSI) (hGSIm : bdSI.mutable = true)
    (hGSIi : bdSI.value.isSome = true)
    (hGNE : bG[JSStr.ofString "nextEffect"]? = some bdNE) (hGNEm : bdNE.mutable = true) (hGNEi : bdNE.value.isSome = true)
    (hGCC : bG[JSStr.ofString "commitBeforeMutationEffects_complete"]? = some bdCC) (hGCCv : bdCC.value = some (.obj fCC))
    (hGAV : bG[JSStr.ofString "appearingViewTransitions"]? = some bdAV) (hGAVm : bdAV.mutable = true)
    (hGAVi : bdAV.value.isSome = true)
    (hFR : FR < s.heap.size) (hFRk : (s.objEntry FR).kind.isPlain = true)
    (hFRc : (s.objEntry FR).props.get? (.str (JSStr.ofString "containerInfo")) = some (.data (.obj Cont) cw ce cc))
    (hR : R < s.heap.size) (hRk : (s.objEntry R).kind.isPlain = true)
    (hRa : (s.objEntry R).props.get? (.str (JSStr.ofString "alternate")) = some (.data (.obj Rc) aw ae ac))
    (hRt : (s.objEntry R).props.get? (.str (JSStr.ofString "tag")) =
      some (.data (.num (F64.fin false 6755399441055744 (-51))) tw te tc))
    (hRc : (s.objEntry R).props.get? (.str (JSStr.ofString "child")) = some (.data (.obj K) kw ke kc))
    (hRs : (s.objEntry R).props.get? (.str (JSStr.ofString "subtreeFlags")) = some (.data (.num sf) sw se sc))
    (hsf : isStrictlyEqual (.num (F64.fin false 0 (-1074)))
      (.num (numberBinOp .bitAnd sf (F64.fin false 4503599627370496 (-42)))) = true)
    (hlanes : isStrictlyEqual (.num (numberBinOp .bitAnd lanes (F64.fin false 5629495239245824 (-24)))) (.num lanes) = false)
    (hGDo : fGD < s.heap.size) (hGDc : ∃ dd, (s.objEntry fGD).kind = .func dd)
    (hHSo : fHS < s.heap.size) (hHSc : ∃ dd, (s.objEntry fHS).kind = .func dd)
    (hCCo : fCC < s.heap.size) (hCCc : ∃ dd, (s.objEntry fCC).kind = .func dd)
    (hGDC : ∀ w h1, Frame (FB d.env) s w → 200 ≤ w.fuel →
      WP eng answer (n + 1) h1 (callImpl eng (.obj fGD) .undefined #[.obj Cont]) w fun v w' h' =>
        v = .obj E ∧ Frame {} w w' ∧ w.fuel ≤ w'.fuel + 200 ∧ h' = h1)
    (hHSC : ∀ w h1, Frame (FB d.env) s w → 100 ≤ w.fuel →
      WP eng answer (n + 1) h1 (callImpl eng (.obj fHS) .undefined #[.obj E]) w fun v w' h' =>
        v = .bool false ∧ Frame {} w w' ∧ w.fuel ≤ w'.fuel + 80 ∧ h' = h1)
    (hCCC : ∀ w h1, Frame (FB d.env) s w → 200 ≤ w.fuel →
      (∀ bm o, Scope.declLike? (w.envEntry d.env) = some (bm, o) →
        ∃ bd, bm[JSStr.ofString "nextEffect"]? = some bd ∧ bd.value = some (.obj R) ∧ bd.mutable = true) →
      WP eng answer (n + 1) h1 (callImpl eng (.obj fCC) .undefined #[.bool false]) w fun v w' h' =>
        v = .undefined ∧ w.fuel ≤ w'.fuel + 200 ∧ h' = h1 ∧
        Frame ⟨[(d.env, JSStr.ofString "nextEffect")], [], false⟩ w w' ∧ Frame (FB d.env) s w' ∧
        ∀ bm o, Scope.declLike? (w'.envEntry d.env) = some (bm, o) →
          ∃ bd, bm[JSStr.ofString "nextEffect"]? = some bd ∧ bd.value = some .null) :
    WP eng answer (n + 2) h (callImpl eng (.obj fo) t #[.obj FR, .obj R, .num lanes]) s fun v w h' =>
      v = .undefined ∧ h' = h ∧ Frame (FB d.env) s w ∧ s.fuel ≤ w.fuel + 1000 := by
  apply wp_callGen CBMGen.commitBeforeMutationEffects_eq (by decide) hlt hk (by omega) hcls hmode
    (by rw [hcode]; rfl) (by rw [hcode]; rfl) (simple d hcode) (by rw [hcode]; rfl) (by rw [hcode]; rfl)
  have hpn : d.code.info.fdi.paramNames = #[JSStr.ofString "root", JSStr.ofString "firstChild",
    JSStr.ofString "committedLanes"] := by rw [hcode]; rfl
  have hv : d.code.info.fdi.varNames = #[JSStr.ofString "JSCompiler_temp", JSStr.ofString "selection",
    JSStr.ofString "anchorOffset", JSStr.ofString "focusNode", JSStr.ofString "length", JSStr.ofString "start",
    JSStr.ofString "end", JSStr.ofString "indexWithinAnchor", JSStr.ofString "indexWithinFocus", JSStr.ofString "node",
    JSStr.ofString "parentNode", JSStr.ofString "next"] := by rw [hcode]; rfl
  have hl : FDI.lexDecls d = #[] := by simp [FDI.lexDecls, hcode, CBMGen.commitBeforeMutationEffects_func, Func.info]
  have ha : d.code.isAsync = false := by rw [hcode]; rfl
  have e1 : d.env ≠ s.envs.size := Nat.ne_of_lt hG
  have e1' : s.envs.size ≠ d.env := Ne.symm e1
  have e4 : d.env < s.envs.size + 1 := Nat.lt_succ_of_lt hG
  obtain ⟨dGD, hGDk⟩ := hGDc
  obtain ⟨dHS, hHSk⟩ := hHSc
  obtain ⟨dCC, hCCk⟩ := hCCc
  clear hcode
  simp only [CBMGen.commitBeforeMutationEffects]
  js_until [] [e1, e1', e4, hG, hGe, hGEv, hGEvm, hGEvi, hGEn, hGEnv, hGEnm, hGGD, hGGDv, hFR, hFRk, hFRc, hGDo, hGDk, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  refine ⟨by js_norm [CallableC, e1, e1', e4, hG, hGe, hGEv, hGEvm, hGEvi, hGEn, hGEnv, hGEnm, hGGD, hGGDv, hFR, hFRk, hFRc, hGDo, hGDk, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner], wp_mono (hGDC _ _ (by unfold FB; frame_go' [*]) (by js_norm [e1, e1', e4, hG, hGe, hGEv, hGEvm, hGEvi, hGEn, hGEnv, hGEnm, hGGD, hGGDv, hFR, hFRk, hFRc, hGDo, hGDk, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]; omega)) ?_⟩
  rintro v1 w1 h1 ⟨rfl, hF1, hfu1, rfl⟩
  have hE1 := envEntry_frame0 hF1 (e := s.envs.size) (by js_norm [e1, e1', e4, hG, hGe, hGEv, hGEvm, hGEvi, hGEn, hGEnv, hGEnm, hGGD, hGGDv, hFR, hFRk, hFRc, hGDo, hGDk, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner])
  have hEd1 := envEntry_frame0 hF1 (e := d.env) (by js_norm [e1, e1', e4, hG, hGe, hGEv, hGEvm, hGEvi, hGEn, hGEnv, hGEnm, hGGD, hGGDv, hFR, hFRk, hFRc, hGDo, hGDk, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner])
  have hS1 : s.envs.size < w1.envs.size := Nat.lt_of_lt_of_le (by js_norm [e1, e1', e4, hG, hGe, hGEv, hGEvm, hGEvi, hGEn, hGEnv, hGEnm, hGGD, hGGDv, hFR, hFRk, hFRc, hGDo, hGDk, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]) hF1.envs_le
  have hGd1 : d.env < w1.envs.size := Nat.lt_trans hG hS1
  have hfw1 : 700 ≤ w1.fuel := by simp [bodyState, entryState] at hfu1; omega
  have hFs1 : Frame (FB d.env) s w1 := frame_then_empty (by unfold FB; frame_go' [*]) hF1
  have hob1 : ∀ o, o < s.heap.size → w1.objEntry o = s.objEntry o := fun o ho => obj_eq_np hFs1 rfl ho
  have hlt1 : ∀ o, o < s.heap.size → o < w1.heap.size := fun o ho => Nat.lt_of_lt_of_le ho hFs1.heap_le
  js_until [] [hE1, hEd1, hS1, hGd1, hfw1, hob1 R hR, hob1 fHS hHSo, hob1 fCC hCCo, hob1 FR hFR, hlt1 R hR, hlt1 fHS hHSo, hlt1 fCC hCCo, hGHS, hGHSv, hHSk, hGCC, hGCCv, hCCk, hGSI, hGSIm, hGSIi, hGNE, hGNEm, hGNEi, hGAV, hGAVm, hGAVi, hRk, hRa, hRt, hRc, hRs, hsf, hlanes, e1, e1', e4, hG, hGe, hGEv, hGEvm, hGEvi, hGEn, hGEnv, hGEnm, hGGD, hGGDv, hFR, hFRk, hFRc, hGDo, hGDk, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  refine ⟨by js_norm [CallableC, hE1, hEd1, hS1, hGd1, hfw1, hob1 R hR, hob1 fHS hHSo, hob1 fCC hCCo, hob1 FR hFR, hlt1 R hR, hlt1 fHS hHSo, hlt1 fCC hCCo, hGHS, hGHSv, hHSk, hGCC, hGCCv, hCCk, hGSI, hGSIm, hGSIi, hGNE, hGNEm, hGNEi, hGAV, hGAVm, hGAVi, hRk, hRa, hRt, hRc, hRs, hsf, hlanes, e1, e1', e4, hG, hGe, hGEv, hGEvm, hGEvi, hGEn, hGEnv, hGEnm, hGGD, hGGDv, hFR, hFRk, hFRc, hGDo, hGDk, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner], wp_mono (hHSC _ _ (frame_setEnv_new hFs1 (Nat.le_refl _) _) (by simp; omega)) ?_⟩
  rintro v2 w2 h2 ⟨rfl, hF2, hfu2, rfl⟩
  have hE2 := envEntry_frame0 hF2 (e := s.envs.size) (by simp; omega)
  have hEd2 := envEntry_frame0 hF2 (e := d.env) (by simp; omega)
  have hS2 : s.envs.size < w2.envs.size := Nat.lt_of_lt_of_le (by simp; omega) hF2.envs_le
  have hGd2 : d.env < w2.envs.size := Nat.lt_trans hG hS2
  have hfw2 : 500 ≤ w2.fuel := by simp at hfu2; omega
  have hFs2 : Frame (FB d.env) s w2 := frame_then_empty (frame_setEnv_new hFs1 (Nat.le_refl _) _) hF2
  have hob2 : ∀ o, o < s.heap.size → w2.objEntry o = s.objEntry o := fun o ho => obj_eq_np hFs2 rfl ho
  have hlt2 : ∀ o, o < s.heap.size → o < w2.heap.size := fun o ho => Nat.lt_of_lt_of_le ho hFs2.heap_le
  have hRne : w2.heap.size ≠ R := Nat.ne_of_gt (hlt2 R hR)
  have hCne : w2.heap.size ≠ fCC := Nat.ne_of_gt (hlt2 fCC hCCo)
  have hRlt' : R < w2.heap.size + 1 := Nat.lt_succ_of_lt (hlt2 R hR)
  have hClt' : fCC < w2.heap.size + 1 := Nat.lt_succ_of_lt (hlt2 fCC hCCo)
  js_until [] [hRne, Ne.symm hRne, hCne, Ne.symm hCne, hRlt', hClt', hE2, hEd2, hS2, hGd2, hfw2, hob2 R hR, hob2 fCC hCCo, hlt2 R hR, hlt2 fCC hCCo, hE1, hEd1, hS1, hGd1, hfw1, hob1 R hR, hob1 fHS hHSo, hob1 fCC hCCo, hob1 FR hFR, hlt1 R hR, hlt1 fHS hHSo, hlt1 fCC hCCo, hGHS, hGHSv, hHSk, hGCC, hGCCv, hCCk, hGSI, hGSIm, hGSIi, hGNE, hGNEm, hGNEi, hGAV, hGAVm, hGAVi, hRk, hRa, hRt, hRc, hRs, hsf, hlanes, e1, e1', e4, hG, hGe, hGEv, hGEvm, hGEvi, hGEn, hGEnv, hGEnm, hGGD, hGGDv, hFR, hFRk, hFRc, hGDo, hGDk, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  refine wp_forExpr ?_
  js_until [] [hRne, Ne.symm hRne, hCne, Ne.symm hCne, hRlt', hClt', hE2, hEd2, hS2, hGd2, hfw2, hob2 R hR, hob2 fCC hCCo, hlt2 R hR, hlt2 fCC hCCo, hE1, hEd1, hS1, hGd1, hfw1, hob1 R hR, hob1 fHS hHSo, hob1 fCC hCCo, hob1 FR hFR, hlt1 R hR, hlt1 fHS hHSo, hlt1 fCC hCCo, hGHS, hGHSv, hHSk, hGCC, hGCCv, hCCk, hGSI, hGSIm, hGSIi, hGNE, hGNEm, hGNEi, hGAV, hGAVm, hGAVi, hRk, hRa, hRt, hRc, hRs, hsf, hlanes, e1, e1', e4, hG, hGe, hGEv, hGEvm, hGEvi, hGEn, hGEnv, hGEnm, hGGD, hGGDv, hFR, hFRk, hFRc, hGDo, hGDk, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  refine ⟨by js_norm [CallableC, hRne, Ne.symm hRne, hCne, Ne.symm hCne, hRlt', hClt', hE2, hEd2, hS2, hGd2, hfw2, hob2 R hR, hob2 fCC hCCo, hlt2 R hR, hlt2 fCC hCCo, hE1, hEd1, hS1, hGd1, hfw1, hob1 R hR, hob1 fHS hHSo, hob1 fCC hCCo, hob1 FR hFR, hlt1 R hR, hlt1 fHS hHSo, hlt1 fCC hCCo, hGHS, hGHSv, hHSk, hGCC, hGCCv, hCCk, hGSI, hGSIm, hGSIi, hGNE, hGNEm, hGNEi, hGAV, hGAVm, hGAVi, hRk, hRa, hRt, hRc, hRs, hsf, hlanes, e1, e1', e4, hG, hGe, hGEv, hGEvm, hGEvi, hGEn, hGEnv, hGEnm, hGGD, hGGDv, hFR, hFRk, hFRc, hGDo, hGDk, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner], wp_mono (hCCC _ _ ?frC (by simp [State.withFuel, State.allocObj, State.withHeap, State.setProp]; omega) ?nev) ?_⟩
  case frC =>
    have hle2 : s.heap.size ≤ w2.heap.size := hFs2.heap_le
    have hdS : (Scope.declLike? (s.envEntry d.env)).isSome = true := by rw [hGe]; rfl
    unfold FB at hFs2 ⊢
    repeat (first
      | exact hFs2
      | refine frame_withFuel ?_ _
      | refine frame_setEnv_new ?_ (Nat.le_refl _) _
      | refine frame_setProp_new ?_ hle2 _ _
      | refine frame_allocObj ?_ _
      | (refine frame_setEnv_with_in ?_ hG ?ea ?eb ?ec _
         case ea => (simp only [setEnv_envEntry_ne _ _ _ _ e1', envEntry_withFuel', setProp_envEntry, allocObj_envEntry, hEd2, hEd1]; first | rfl | (rw [setEnv_envEntry_self _ _ _ (by simp [envs_withFuel'] <;> omega)]; done))
         case eb => simp only [declLike_isSome_withBindings]; exact hdS
         case ec => simp)
      | (refine frame_setEnv_split (frame_setEnv_with_in ?_ hG (setEnv_envEntry_self _ _ _ ?ed) ?ee ?ef _)
         case ed => simp [envs_withFuel'] <;> omega
         case ee => simp only [declLike_isSome_withBindings]; exact hdS
         case ef => simp))
  

  case nev =>
    intro bm o hd
    simp only [setEnv_envEntry_ne _ _ _ _ e1', envEntry_withFuel', setProp_envEntry, allocObj_envEntry] at hd
    rw [setEnv_envEntry_self _ _ _ (by simp [envs_withFuel'] <;> omega)] at hd
    simp only [declLike_withBindings (declLike_withBindings (declLike_withBindings (declLike_withBindings hGe _) _) _) _,
      Option.some.injEq, Prod.mk.injEq] at hd
    obtain ⟨rfl, rfl⟩ := hd
    simp [Std.HashMap.getElem?_modify, hGNE, hGNEm]
  rintro v3 w3 h3 ⟨rfl, hfu3, rfl, hF3, hFs3, hN3⟩
  have hE3 := envEntry_frame hF3 (e := s.envs.size) (by simp [envs_withFuel']; omega)
    (List.all_eq_true.mpr fun p hp => by simp at hp; simp [hp, e1])
  have hS3 : s.envs.size < w3.envs.size := Nat.lt_of_lt_of_le (by simp [envs_withFuel']; omega) hF3.envs_le
  have hGd3 : d.env < w3.envs.size := Nat.lt_trans hG hS3
  obtain ⟨bw3, hd3, hbw3⟩ := declLike_frame hF3 (e := d.env) (by simp [envs_withFuel']; omega)
    (by simp only [setEnv_envEntry_ne _ _ _ _ e1', envEntry_withFuel', setProp_envEntry, allocObj_envEntry]
        rw [setEnv_envEntry_self _ _ _ (by simp [envs_withFuel'] <;> omega)]
        simp only [declLike_withBindings (declLike_withBindings (declLike_withBindings (declLike_withBindings hGe _) _) _) _]
        rfl)
  obtain ⟨bdN3, hbN3, hbN3v⟩ := hN3 _ _ hd3
  have hbAV := hbw3 (JSStr.ofString "appearingViewTransitions") (by simp)
  have hfw3 : 50 ≤ w3.fuel := by simp [State.withFuel, State.allocObj, State.withHeap, State.setProp] at hfu3; omega
  js_until [] [hE3, hS3, hGd3, hd3, hbN3, hbN3v, hbAV, hfw3, Std.HashMap.getElem?_modify, hRne, Ne.symm hRne, hCne, Ne.symm hCne, hRlt', hClt', hE2, hEd2, hS2, hGd2, hfw2, hob2 R hR, hob2 fCC hCCo, hlt2 R hR, hlt2 fCC hCCo, hE1, hEd1, hS1, hGd1, hfw1, hob1 R hR, hob1 fHS hHSo, hob1 fCC hCCo, hob1 FR hFR, hlt1 R hR, hlt1 fHS hHSo, hlt1 fCC hCCo, hGHS, hGHSv, hHSk, hGCC, hGCCv, hCCk, hGSI, hGSIm, hGSIi, hGNE, hGNEm, hGNEi, hGAV, hGAVm, hGAVi, hRk, hRa, hRt, hRc, hRs, hsf, hlanes, e1, e1', e4, hG, hGe, hGEv, hGEvm, hGEvi, hGEn, hGEnv, hGEnm, hGGD, hGGDv, hFR, hFRk, hFRc, hGDo, hGDk, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  refine ⟨frame_restore (frame_setEnv_with_in (frame_withFuel hFs3 _) hG ?k1 ?k2 (by simp [FB]) _) s, ?fu⟩
  case k1 => rfl
  case k2 => rw [hd3]; rfl
  case fu =>
    simp [State.withFuel, State.allocObj, State.withHeap, State.setProp, bodyState, entryState] at hfu1 hfu2 hfu3 ⊢
    omega


end

end ReactBeforeMutation
