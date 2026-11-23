import JSProofs.CMESwitch
import JSProofs.Setter
import JSProofs.ReactHostContainer

/-!
# commitMutationEffectsOnFiber for the button (zippy docs/react-proofs.md)

The host component case (tag 5) for a fiber with only the Update flag among those the case tests: the children
traversed (`recursivelyTraverseMutationEffects`, with `offscreenDirectParentIsHidden` false around it), the
reconciliation effects, then `commitHostUpdate(fiber, memoizedProps, current.memoizedProps)`. The callees' contracts are
premises.
-/

open ES ES.M HostRuns Logic
open Std (HashMap)

namespace ReactCommitButton

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ}

theorem simple (d : FuncData) (hc : d.code = CMEGen.commitMutationEffectsOnFiber_func) : FDI.Simple d := by
  constructor <;> rw [hc] <;> try rfl
  simp [CMEGen.commitMutationEffectsOnFiber_func, Func.params, Func.info]

set_option maxRecDepth 40000 in
set_option maxHeartbeats 8000000 in
theorem cme_button {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t : Value} {s : State}
    {rv lv : Value} {B Bc : ObjId} {fl : F64}
    {aw ae ac fw fe fc tw te tc : Bool}
    {bG : HashMap JSStr Binding} {oG : Option EnvId} {bdO bdRT bdRE bdCH : Binding} {vO : Value}
    {fRT fRE fCH : ObjId} {dom NP LP : ObjId} {fpH : Footprint} {PH : State → σ → Prop}
    {sw se sc mw me mc cw ce cc : Bool}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : 3500 ≤ s.fuel)
    (hcode : d.code = CMEGen.commitMutationEffectsOnFiber_func) (hcls : d.isClassCtor = false)
    (hmode : d.thisMode = .strict)
    (hB : B < s.heap.size) (hBk : (s.objEntry B).kind.isPlain = true)
    (hBa : (s.objEntry B).props.get? (.str (JSStr.ofString "alternate")) = some (.data (.obj Bc) aw ae ac))
    (hBf : (s.objEntry B).props.get? (.str (JSStr.ofString "flags")) = some (.data (.num fl) fw fe fc))
    (hBt : (s.objEntry B).props.get? (.str (JSStr.ofString "tag")) =
      some (.data (.num (F64.fin false 5629499534213120 (-50))) tw te tc))
    (hG : d.env < s.envs.size) (hGe : Scope.declLike? (s.envEntry d.env) = some (bG, oG))
    (hGO : bG[JSStr.ofString "offscreenDirectParentIsHidden"]? = some bdO) (hGOv : bdO.value = some vO)
    (hGOm : bdO.mutable = true)
    (hGRT : bG[JSStr.ofString "recursivelyTraverseMutationEffects"]? = some bdRT) (hGRTv : bdRT.value = some (.obj fRT))
    (hGRE : bG[JSStr.ofString "commitReconciliationEffects"]? = some bdRE) (hGREv : bdRE.value = some (.obj fRE))
    (hGCH : bG[JSStr.ofString "commitHostUpdate"]? = some bdCH) (hGCHv : bdCH.value = some (.obj fCH))
    (hRTo : fRT < s.heap.size) (hRTc : ∃ dd, (s.objEntry fRT).kind = .func dd)
    (hRT : ∀ w h1, Frame ⟨[(d.env, JSStr.ofString "offscreenDirectParentIsHidden")], [], false⟩ s w → 100 ≤ w.fuel →
      WP eng answer (n + 1) h1 (callImpl eng (.obj fRT) .undefined #[rv, .obj B, lv]) w fun v w' h' =>
        Frame {} w w' ∧ w.fuel ≤ w'.fuel + 40 ∧ h' = h1)
    (hREo : fRE < s.heap.size) (hREc : ∃ dd, (s.objEntry fRE).kind = .func dd)
    (hRE : ∀ w h1, Frame ⟨[(d.env, JSStr.ofString "offscreenDirectParentIsHidden")], [], false⟩ s w → 100 ≤ w.fuel →
      WP eng answer (n + 1) h1 (callImpl eng (.obj fRE) .undefined #[.obj B]) w fun v w' h' =>
        Frame {} w w' ∧ w.fuel ≤ w'.fuel + 40 ∧ h' = h1)
    (h512 : numberBinOp .bitAnd fl (F64.fin false 4503599627370496 (-43)) = F64.fin false 0 (-1074))
    (h32 : numberBinOp .bitAnd fl (F64.fin false 4503599627370496 (-47)) = F64.fin false 0 (-1074))
    (h4 : (!((numberBinOp .bitAnd fl (F64.fin false 4503599627370496 (-50))).isZero ||
      numberBinOp .bitAnd fl (F64.fin false 4503599627370496 (-50)) == F64.nan)) = true)
    (h1024 : numberBinOp .bitAnd fl (F64.fin false 4503599627370496 (-42)) = F64.fin false 0 (-1074))
    (hBs : (s.objEntry B).props.get? (.str (JSStr.ofString "stateNode")) = some (.data (.obj dom) sw se sc))
    (hBm : (s.objEntry B).props.get? (.str (JSStr.ofString "memoizedProps")) = some (.data (.obj NP) mw me mc))
    (hBc : Bc < s.heap.size) (hBck : (s.objEntry Bc).kind.isPlain = true)
    (hBcm : (s.objEntry Bc).props.get? (.str (JSStr.ofString "memoizedProps")) = some (.data (.obj LP) cw ce cc))
    (hCHo : fCH < s.heap.size) (hCHc : ∃ dd, (s.objEntry fCH).kind = .func dd)
    (hCH : ∀ w h1, Frame ⟨[(d.env, JSStr.ofString "offscreenDirectParentIsHidden")], [], false⟩ s w → 3000 ≤ w.fuel →
      WP eng answer (n + 1) h1 (callImpl eng (.obj fCH) .undefined #[.obj B, .obj NP, .obj LP]) w fun v w' h' =>
        v = .undefined ∧ w.fuel ≤ w'.fuel + 2100 ∧ PH w' h' ∧ Frame fpH w w')
    (hfpH : ∀ p, p ∈ fpH.binds → p.1 = d.env)
    (hPHst : ∀ w w' h', PH w h' → w'.heap = w.heap → (∀ e, e < s.envs.size → w'.envEntry e = w.envEntry e) →
      PH w' h') :
    WP eng answer (n + 2) h (callImpl eng (.obj fo) t #[.obj B, rv, lv]) s fun v w h' =>
      v = .undefined ∧ s.fuel ≤ w.fuel + 2300 ∧ PH w h' ∧
      Frame ((Footprint.union ⟨[(d.env, JSStr.ofString "offscreenDirectParentIsHidden")], [], false⟩ fpH)) s w := by
  apply wp_callGen CMEGen.commitMutationEffectsOnFiber_eq (by decide) hlt hk (by omega) hcls hmode
    (by rw [hcode]; rfl) (by rw [hcode]; rfl) (simple d hcode) (by rw [hcode]; rfl) (by rw [hcode]; rfl)
  have hpn : d.code.info.fdi.paramNames = #[JSStr.ofString "finishedWork", JSStr.ofString "root",
    JSStr.ofString "lanes"] := by rw [hcode]; rfl
  have hv : d.code.info.fdi.varNames = #[JSStr.ofString "current", JSStr.ofString "flags", JSStr.ofString "ii",
    JSStr.ofString "_eventPayloads$ii2", JSStr.ofString "prevOffscreenSubtreeIsHidden",
    JSStr.ofString "prevOffscreenSubtreeWasHidden", JSStr.ofString "prevOffscreenDirectParentIsHidden$166"] := by
    rw [hcode]; rfl
  have hl : FDI.lexDecls d = #[] := by
    simp [FDI.lexDecls, hcode, CMEGen.commitMutationEffectsOnFiber_func, Func.info]
  have ha : d.code.isAsync = false := by rw [hcode]; rfl
  have e1 : d.env ≠ s.envs.size := Nat.ne_of_lt hG
  have e4 : d.env < s.envs.size + 1 := Nat.lt_succ_of_lt hG
  have e5 : d.env < s.envs.size + 1 + 1 := Nat.lt_succ_of_lt e4
  have e2 : d.env ≠ s.envs.size + 1 := Nat.ne_of_lt e4
  have e1' : s.envs.size ≠ d.env := Ne.symm e1
  have e2' : s.envs.size + 1 ≠ d.env := Ne.symm e2
  obtain ⟨dRT, hRTk⟩ := hRTc
  obtain ⟨dRE, hREk⟩ := hREc
  obtain ⟨dCH, hCHk⟩ := hCHc
  clear hcode
  simp only [CMEGen.commitMutationEffectsOnFiber]
  iterate 15 (first | js_go | js_norm [hB, hBk, hBa, hBf, hBt, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner] | js_split)
  refine wp_switchC CMESwitch.lex ?_
  js_until [] [e1, e2, e4, e5, Ne.symm e1, Ne.symm e2, hG, hGe, hGO, hGOv, hGOm, hGRT, hGRTv, hRTo, hRTk, hB, hBk, hBa, hBf, hBt, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  refine ⟨by js_norm [CallableC, e1, e2, e4, e5, Ne.symm e1, Ne.symm e2, hG, hGe, hGO, hGOv, hGOm, hGRT, hGRTv, hRTo, hRTk, hB, hBk, hBa, hBf, hBt, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner], ?_⟩
  refine wp_mono (hRT _ _ (by frame_go' [*]) (by js_norm [e1, e2, e4, e5, Ne.symm e1, Ne.symm e2, hG, hGe, hGO, hGOv, hGOm, hGRT, hGRTv, hRTo, hRTk, hB, hBk, hBa, hBf, hBt, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]; omega)) ?_
  rintro v1 w1 h1 ⟨hF1, hfu1, rfl⟩
  have hEa := envEntry_frame0 hF1 (e := s.envs.size) (by js_norm [e1, e2, e4, e5, Ne.symm e1, Ne.symm e2, hG, hGe, hGO, hGOv, hGOm, hGRT, hGRTv, hRTo, hRTk, hB, hBk, hBa, hBf, hBt, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner])
  have hEb := envEntry_frame0 hF1 (e := s.envs.size + 1) (by js_norm [e1, e2, e4, e5, Ne.symm e1, Ne.symm e2, hG, hGe, hGO, hGOv, hGOm, hGRT, hGRTv, hRTo, hRTk, hB, hBk, hBa, hBf, hBt, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner])
  have hEc := envEntry_frame0 hF1 (e := d.env) (by js_norm [e1, e2, e4, e5, Ne.symm e1, Ne.symm e2, hG, hGe, hGO, hGOv, hGOm, hGRT, hGRTv, hRTo, hRTk, hB, hBk, hBa, hBf, hBt, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner])
  have hSa : s.envs.size + 1 < w1.envs.size := Nat.lt_of_lt_of_le (by js_norm [e1, e2, e4, e5, Ne.symm e1, Ne.symm e2, hG, hGe, hGO, hGOv, hGOm, hGRT, hGRTv, hRTo, hRTk, hB, hBk, hBa, hBf, hBt, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]) hF1.envs_le
  have hSb : s.envs.size < w1.envs.size := by omega
  have hGd : d.env < w1.envs.size := Nat.lt_trans hG hSb
  have hB1 : w1.objEntry B = s.objEntry B := by rw [objEntry_frame0 hF1 (by js_norm [e1, e2, e4, e5, Ne.symm e1, Ne.symm e2, hG, hGe, hGO, hGOv, hGOm, hGRT, hGRTv, hRTo, hRTk, hB, hBk, hBa, hBf, hBt, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner])]; js_norm [e1, e2, e4, e5, Ne.symm e1, Ne.symm e2, hG, hGe, hGO, hGOv, hGOm, hGRT, hGRTv, hRTo, hRTk, hB, hBk, hBa, hBf, hBt, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  have hBlt1 : B < w1.heap.size := Nat.lt_of_lt_of_le (by js_norm [hREo, hB, e1]) hF1.heap_le
  have hfw1 : 3400 ≤ w1.fuel := by simp [bodyState, entryState] at hfu1; omega
  have hfr1 : s.fuel ≤ w1.fuel + 60 := by simp [bodyState, entryState] at hfu1; omega
  have hRE1 : w1.objEntry fRE = s.objEntry fRE := by rw [objEntry_frame0 hF1 (by js_norm [hREo, e1, e2, e4, e5, Ne.symm e1, Ne.symm e2, hG, hGe, hGO, hGOv, hGOm, hGRT, hGRTv, hRTo, hRTk, hB, hBk, hBa, hBf, hBt, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner])]; js_norm [e1, e2, e4, e5, Ne.symm e1, Ne.symm e2, hG, hGe, hGO, hGOv, hGOm, hGRT, hGRTv, hRTo, hRTk, hB, hBk, hBa, hBf, hBt, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  have hRElt1 : fRE < w1.heap.size := Nat.lt_of_lt_of_le (by js_norm [hREo, hB, e1]) hF1.heap_le
  have hFs1 : Frame ⟨[(d.env, JSStr.ofString "offscreenDirectParentIsHidden")], [], false⟩ s w1 :=
    frame_mono (frame_trans (fp1 := ⟨[(d.env, JSStr.ofString "offscreenDirectParentIsHidden")], [], false⟩) (s := s) (by frame_go' [*]) hF1)
      (fun p hp => by simpa [Footprint.union] using hp) (fun p hp => by simpa [Footprint.union] using hp)
      (fun hj => by simpa [Footprint.union] using hj)
  js_until [] [hEa, hEb, hEc, hSa, hSb, hGd, hB1, hBlt1, hfw1, hGRE, hGREv, hREo, hREk, hRE1, hRElt1, e1, e2, e4, e5, Ne.symm e1, Ne.symm e2, hG, hGe, hGO, hGOv, hGOm, hGRT, hGRTv, hRTo, hRTk, hB, hBk, hBa, hBf, hBt, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  refine ⟨by js_norm [CallableC, hEa, hEb, hEc, hSa, hSb, hGd, hB1, hBlt1, hfw1, hGRE, hGREv, hREo, hREk, hRE1, hRElt1, e1, e2, e4, e5, Ne.symm e1, Ne.symm e2, hG, hGe, hGO, hGOv, hGOm, hGRT, hGRTv, hRTo, hRTk, hB, hBk, hBa, hBf, hBt, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner], ?_⟩
  refine wp_mono (hRE _ _ (by frame_go' [*]) (by js_norm [hEa, hEb, hEc, hSa, hSb, hGd, hB1, hBlt1, hfw1, hGRE, hGREv, hREo, hREk, hRE1, hRElt1, e1, e2, e4, e5, Ne.symm e1, Ne.symm e2, hG, hGe, hGO, hGOv, hGOm, hGRT, hGRTv, hRTo, hRTk, hB, hBk, hBa, hBf, hBt, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]; omega)) ?_
  rintro v2 w2 h2 ⟨hF2, hfu2, rfl⟩
  have hEa2 := envEntry_frame0 hF2 (e := s.envs.size) (by js_norm [hEa, hEb, hEc, hSa, hSb, hGd, hB1, hBlt1, hfw1, hGRE, hGREv, hREo, hREk, hRE1, hRElt1, e1, e2, e4, e5, Ne.symm e1, Ne.symm e2, hG, hGe, hGO, hGOv, hGOm, hGRT, hGRTv, hRTo, hRTk, hB, hBk, hBa, hBf, hBt, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner])
  have hEb2 := envEntry_frame0 hF2 (e := s.envs.size + 1) (by js_norm [hEa, hEb, hEc, hSa, hSb, hGd, hB1, hBlt1, hfw1, hGRE, hGREv, hREo, hREk, hRE1, hRElt1, e1, e2, e4, e5, Ne.symm e1, Ne.symm e2, hG, hGe, hGO, hGOv, hGOm, hGRT, hGRTv, hRTo, hRTk, hB, hBk, hBa, hBf, hBt, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner])
  have hEc2 := envEntry_frame0 hF2 (e := d.env) (by js_norm [hEa, hEb, hEc, hSa, hSb, hGd, hB1, hBlt1, hfw1, hGRE, hGREv, hREo, hREk, hRE1, hRElt1, e1, e2, e4, e5, Ne.symm e1, Ne.symm e2, hG, hGe, hGO, hGOv, hGOm, hGRT, hGRTv, hRTo, hRTk, hB, hBk, hBa, hBf, hBt, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner])
  have hSa2 : s.envs.size + 1 < w2.envs.size := Nat.lt_of_lt_of_le (by js_norm [hEa, hEb, hEc, hSa, hSb, hGd, hB1, hBlt1, hfw1, hGRE, hGREv, hREo, hREk, hRE1, hRElt1, e1, e2, e4, e5, Ne.symm e1, Ne.symm e2, hG, hGe, hGO, hGOv, hGOm, hGRT, hGRTv, hRTo, hRTk, hB, hBk, hBa, hBf, hBt, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]) hF2.envs_le
  have hSb2 : s.envs.size < w2.envs.size := by omega
  have hGd2 : d.env < w2.envs.size := Nat.lt_trans hG hSb2
  have hFs2 : Frame ⟨[(d.env, JSStr.ofString "offscreenDirectParentIsHidden")], [], false⟩ s w2 :=
    frame_mono (frame_trans (fp1 := ⟨[(d.env, JSStr.ofString "offscreenDirectParentIsHidden")], [], false⟩) (s := s)
      (by frame_go' [*]) hF2)
      (fun p hp => by simpa [Footprint.union] using hp) (fun p hp => by simpa [Footprint.union] using hp)
      (fun hj => by simpa [Footprint.union] using hj)
  have hB2 : w2.objEntry B = s.objEntry B := hFs2.obj_eq B hB (fun _ hh => by simp at hh)
  have hBlt2 : B < w2.heap.size := Nat.lt_of_lt_of_le hB hFs2.heap_le
  have hBc2 : w2.objEntry Bc = s.objEntry Bc := hFs2.obj_eq Bc hBc (fun _ hh => by simp at hh)
  have hBclt2 : Bc < w2.heap.size := Nat.lt_of_lt_of_le hBc hFs2.heap_le
  have hCH2 : w2.objEntry fCH = s.objEntry fCH := hFs2.obj_eq fCH hCHo (fun _ hh => by simp at hh)
  have hCHlt2 : fCH < w2.heap.size := Nat.lt_of_lt_of_le hCHo hFs2.heap_le
  have hfw2 : 3300 ≤ w2.fuel := by simp [bodyState, entryState] at hfu2; omega
  have hfr2 : w1.fuel ≤ w2.fuel + 60 := by simp [bodyState, entryState] at hfu2; omega
  js_until [] [hEa2, hEb2, hEc2, hSa2, hSb2, hGd2, hB2, hBlt2, hBc2, hBclt2, hCH2, hCHlt2, hfw2, h512, h32, h4, h1024, hBs, hBm, hBc, hBck, hBcm, hGCH, hGCHv, hCHo, hCHk, hEa, hEb, hEc, hSa, hSb, hGd, hB1, hBlt1, hfw1, hGRE, hGREv, hREo, hREk, hRE1, hRElt1, e1, e2, e4, e5, Ne.symm e1, Ne.symm e2, hG, hGe, hGO, hGOv, hGOm, hGRT, hGRTv, hRTo, hRTk, hB, hBk, hBa, hBf, hBt, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  refine wp_neNullObj' (by omega) ?_
  js_until [] [hEa2, hEb2, hEc2, hSa2, hSb2, hGd2, hB2, hBlt2, hBc2, hBclt2, hCH2, hCHlt2, hfw2, h512, h32, h4, h1024, hBs, hBm, hBc, hBck, hBcm, hGCH, hGCHv, hCHo, hCHk, hEa, hEb, hEc, hSa, hSb, hGd, hB1, hBlt1, hfw1, hGRE, hGREv, hREo, hREk, hRE1, hRElt1, e1, e2, e4, e5, Ne.symm e1, Ne.symm e2, hG, hGe, hGO, hGOv, hGOm, hGRT, hGRTv, hRTo, hRTk, hB, hBk, hBa, hBf, hBt, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  refine ⟨by js_norm [CallableC, hEa2, hEb2, hEc2, hSa2, hSb2, hGd2, hB2, hBlt2, hBc2, hBclt2, hCH2, hCHlt2, hfw2, h512, h32, h4, h1024, hBs, hBm, hBc, hBck, hBcm, hGCH, hGCHv, hCHo, hCHk, hEa, hEb, hEc, hSa, hSb, hGd, hB1, hBlt1, hfw1, hGRE, hGREv, hREo, hREk, hRE1, hRElt1, e1, e2, e4, e5, Ne.symm e1, Ne.symm e2, hG, hGe, hGO, hGOv, hGOm, hGRT, hGRTv, hRTo, hRTk, hB, hBk, hBa, hBf, hBt, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner], ?_⟩
  refine wp_mono (hCH _ _ (frame_setEnv_new hFs2 (Nat.le_refl _) _) (by simp only [State.setEnv_fuel]; omega)) ?_
  rintro v3 w3 h3 ⟨rfl, hfu3, hP3, hF3⟩
  have hEa3 := envEntry_frame hF3 (e := s.envs.size) (by simp; omega)
    (List.all_eq_true.mpr fun p hp => by simp [hfpH p hp, e1])
  have hEb3 := envEntry_frame hF3 (e := s.envs.size + 1) (by simp; omega)
    (List.all_eq_true.mpr fun p hp => by simp [hfpH p hp, e2])
  have hSa3 : s.envs.size + 1 < w3.envs.size := Nat.lt_of_lt_of_le (by simp; omega) hF3.envs_le
  have hSb3 : s.envs.size < w3.envs.size := by omega
  have hfw3 : 100 ≤ w3.fuel := by simp only [State.setEnv_fuel] at hfu3; omega
  have hfr3 : w2.fuel ≤ w3.fuel + 2110 := by simp only [State.setEnv_fuel] at hfu3; omega
  js_until [] [hEa3, hEb3, hSa3, hSb3, hfw3, hEa2, hEb2, hEc2, hSa2, hSb2, hGd2, hB2, hBlt2, hBc2, hBclt2, hCH2, hCHlt2, hfw2, h512, h32, h4, h1024, hBs, hBm, hBc, hBck, hBcm, hGCH, hGCHv, hCHo, hCHk, hEa, hEb, hEc, hSa, hSb, hGd, hB1, hBlt1, hfw1, hGRE, hGREv, hREo, hREk, hRE1, hRElt1, e1, e2, e4, e5, Ne.symm e1, Ne.symm e2, hG, hGe, hGO, hGOv, hGOm, hGRT, hGRTv, hRTo, hRTk, hB, hBk, hBa, hBf, hBt, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  exact ⟨by omega, hPHst _ _ _ hP3 rfl (fun _ _ => rfl),
    frame_restore (frame_trans (frame_setEnv_new hFs2 (Nat.le_refl _) _) hF3) s⟩

end

end ReactCommitButton
