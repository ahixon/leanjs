import JSProofs.CMESwitch
import JSProofs.Setter
import JSProofs.ReactHostContainer

/-!
# commitMutationEffectsOnFiber for the root (zippy docs/react-proofs.md)

The host root case (tag 3), not dehydrated, no form reset pending: `viewTransitionMutationContext` and `tagCaches`
cleared, `currentHoistableRoot` set to `getHoistableRoot(root.containerInfo)` around the children's traversal, the
reconciliation effects, `viewTransitionMutationContext` cleared again. The callees' contracts are premises, each at
any state framed from the entry state by the module bindings the case writes (`F0`).
-/

open ES ES.M HostRuns Logic
open Std (HashMap)

namespace ReactCommitRoot

/-- The module bindings the root case writes. -/
def F0 (g : EnvId) : Footprint :=
  ⟨[(g, JSStr.ofString "viewTransitionMutationContext"), (g, JSStr.ofString "tagCaches"),
    (g, JSStr.ofString "currentHoistableRoot")], [], false⟩

@[simp] theorem F0_props (g : EnvId) : (F0 g).props = [] := rfl
@[simp] theorem F0_jobs (g : EnvId) : (F0 g).jobs = false := rfl
@[simp] theorem F0_binds (g : EnvId) : (F0 g).binds = [(g, JSStr.ofString "viewTransitionMutationContext"),
    (g, JSStr.ofString "tagCaches"), (g, JSStr.ofString "currentHoistableRoot")] := rfl

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ}

theorem simple (d : FuncData) (hc : d.code = CMEGen.commitMutationEffectsOnFiber_func) : FDI.Simple d := by
  constructor <;> rw [hc] <;> try rfl
  simp [CMEGen.commitMutationEffectsOnFiber_func, Func.params, Func.info]

set_option maxRecDepth 40000 in
set_option maxHeartbeats 8000000 in
theorem cme_root {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t : Value} {s : State}
    {lv : Value} {R FR Cont : ObjId} {rcv : Value} {fl : F64} {KR : Nat}
    {aw ae ac fw fe fc tw te tc cw ce cc : Bool}
    {bG : HashMap JSStr Binding} {oG : Option EnvId} {bdV bdT bdH bdGH bdRT bdRE bdN : Binding} {vH0 : Value}
    {fGH fRT fRE : ObjId} {fpC : Footprint} {PC : State → σ → Prop}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : KR + 600 ≤ s.fuel)
    (hcode : d.code = CMEGen.commitMutationEffectsOnFiber_func) (hcls : d.isClassCtor = false)
    (hmode : d.thisMode = .strict)
    (hR : R < s.heap.size) (hRk : (s.objEntry R).kind.isPlain = true)
    (hRa : (s.objEntry R).props.get? (.str (JSStr.ofString "alternate")) = some (.data rcv aw ae ac))
    (hRf : (s.objEntry R).props.get? (.str (JSStr.ofString "flags")) = some (.data (.num fl) fw fe fc))
    (hRt : (s.objEntry R).props.get? (.str (JSStr.ofString "tag")) =
      some (.data (.num (F64.fin false 6755399441055744 (-51))) tw te tc))
    (h4 : numberBinOp .bitAnd fl (F64.fin false 4503599627370496 (-50)) = F64.fin false 0 (-1074))
    (hFR : FR < s.heap.size) (hFRk : (s.objEntry FR).kind.isPlain = true)
    (hFRc : (s.objEntry FR).props.get? (.str (JSStr.ofString "containerInfo")) = some (.data (.obj Cont) cw ce cc))
    (hG : d.env < s.envs.size) (hGe : Scope.declLike? (s.envEntry d.env) = some (bG, oG))
    (hGV : bG[JSStr.ofString "viewTransitionMutationContext"]? = some bdV) (hGVm : bdV.mutable = true)
    (hGVi : bdV.value.isSome = true)
    (hGT : bG[JSStr.ofString "tagCaches"]? = some bdT) (hGTm : bdT.mutable = true) (hGTi : bdT.value.isSome = true)
    (hGH : bG[JSStr.ofString "currentHoistableRoot"]? = some bdH) (hGHm : bdH.mutable = true)
    (hGHv : bdH.value = some vH0)
    (hGN : bG[JSStr.ofString "needsFormReset"]? = some bdN) (hGNv : bdN.value = some (.bool false))
    (hGGH : bG[JSStr.ofString "getHoistableRoot"]? = some bdGH) (hGGHv : bdGH.value = some (.obj fGH))
    (hGRT : bG[JSStr.ofString "recursivelyTraverseMutationEffects"]? = some bdRT) (hGRTv : bdRT.value = some (.obj fRT))
    (hGRE : bG[JSStr.ofString "commitReconciliationEffects"]? = some bdRE) (hGREv : bdRE.value = some (.obj fRE))
    (hGHo : fGH < s.heap.size) (hGHc : ∃ dd, (s.objEntry fGH).kind = .func dd)
    (hRTo : fRT < s.heap.size) (hRTc : ∃ dd, (s.objEntry fRT).kind = .func dd)
    (hREo : fRE < s.heap.size) (hREc : ∃ dd, (s.objEntry fRE).kind = .func dd)
    (hGHC : ∀ w h1, Frame (F0 d.env) s w → 300 ≤ w.fuel →
      WP eng answer (n + 1) h1 (callImpl eng (.obj fGH) .undefined #[.obj Cont]) w fun v w' h' =>
        Frame {} w w' ∧ w.fuel ≤ w'.fuel + 100)
    (hRT : ∀ w h1, Frame (F0 d.env) s w →
      (∀ bm o, Scope.declLike? (w.envEntry d.env) = some (bm, o) →
        ∃ bd, bm[JSStr.ofString "viewTransitionMutationContext"]? = some bd ∧ bd.mutable = true ∧
          bd.value.isSome = true) → KR + 200 ≤ w.fuel →
      WP eng answer (n + 1) h1 (callImpl eng (.obj fRT) .undefined #[.obj FR, .obj R, lv]) w fun v w' h' =>
        v = .undefined ∧ w.fuel ≤ w'.fuel + KR + 100 ∧ PC w' h' ∧ Frame fpC w w' ∧
        ∀ bm o, Scope.declLike? (w'.envEntry d.env) = some (bm, o) →
          ∃ bd, bm[JSStr.ofString "viewTransitionMutationContext"]? = some bd ∧ bd.mutable = true ∧
            bd.value.isSome = true)
    (hfpC : ∀ p, p ∈ fpC.binds → p.1 = d.env ∧ p.2 ≠ JSStr.ofString "currentHoistableRoot" ∧
      p.2 ≠ JSStr.ofString "commitReconciliationEffects" ∧ p.2 ≠ JSStr.ofString "needsFormReset")
    (hfpCp : ∀ p, p ∈ fpC.props → p.1 ≠ R ∧ p.1 ≠ fRE)
    (hRE : ∀ w h1, Frame ((F0 d.env).union fpC) s w → 100 ≤ w.fuel →
      WP eng answer (n + 1) h1 (callImpl eng (.obj fRE) .undefined #[.obj R]) w fun v w' h' =>
        Frame {} w w' ∧ w.fuel ≤ w'.fuel + 40 ∧ h' = h1 ∧ w'.heap = w.heap)
    (hPCst : ∀ w w' h', PC w h' → w'.heap = w.heap → (∀ e, e < s.envs.size → e ≠ d.env → w'.envEntry e = w.envEntry e) →
      PC w' h') :
    WP eng answer (n + 2) h (callImpl eng (.obj fo) t #[.obj R, .obj FR, lv]) s fun v w h' =>
      v = .undefined ∧ s.fuel ≤ w.fuel + KR + 500 ∧ PC w h' := by
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
  obtain ⟨dGH, hGHk⟩ := hGHc
  obtain ⟨dRT, hRTk⟩ := hRTc
  obtain ⟨dRE, hREk⟩ := hREc
  clear hcode
  simp only [CMEGen.commitMutationEffectsOnFiber]
  iterate 15 (first | js_go | js_norm [hR, hRk, hRa, hRf, hRt, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner] | js_split)
  refine wp_switchC CMESwitch.lex ?_
  js_until [] [h4, e1, e2, e4, e5, e1', e2', hG, hGe, hGV, hGVm, hGVi, hGT, hGTm, hGTi, hGH, hGHm, hGHv, hGGH, hGGHv, hGHo, hGHk, hFR, hFRk, hFRc, hR, hRk, hRa, hRf, hRt, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  refine ⟨by js_norm [CallableC, h4, e1, e2, e4, e5, e1', e2', hG, hGe, hGV, hGVm, hGVi, hGT, hGTm, hGTi, hGH, hGHm, hGHv, hGGH, hGGHv, hGHo, hGHk, hFR, hFRk, hFRc, hR, hRk, hRa, hRf, hRt, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner], ?_⟩
  refine wp_mono (hGHC _ _ (by unfold F0; frame_go' [*]) (by js_norm [h4, e1, e2, e4, e5, e1', e2', hG, hGe, hGV, hGVm, hGVi, hGT, hGTm, hGTi, hGH, hGHm, hGHv, hGGH, hGGHv, hGHo, hGHk, hFR, hFRk, hFRc, hR, hRk, hRa, hRf, hRt, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]; omega)) ?_
  rintro v1 w1 h1 ⟨hF1, hfu1⟩
  have hEa := envEntry_frame0 hF1 (e := s.envs.size) (by js_norm [h4, e1, e2, e4, e5, e1', e2', hG, hGe, hGV, hGVm, hGVi, hGT, hGTm, hGTi, hGH, hGHm, hGHv, hGGH, hGGHv, hGHo, hGHk, hFR, hFRk, hFRc, hR, hRk, hRa, hRf, hRt, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner])
  have hEb := envEntry_frame0 hF1 (e := s.envs.size + 1) (by js_norm [h4, e1, e2, e4, e5, e1', e2', hG, hGe, hGV, hGVm, hGVi, hGT, hGTm, hGTi, hGH, hGHm, hGHv, hGGH, hGGHv, hGHo, hGHk, hFR, hFRk, hFRc, hR, hRk, hRa, hRf, hRt, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner])
  have hEc := envEntry_frame0 hF1 (e := d.env) (by js_norm [h4, e1, e2, e4, e5, e1', e2', hG, hGe, hGV, hGVm, hGVi, hGT, hGTm, hGTi, hGH, hGHm, hGHv, hGGH, hGGHv, hGHo, hGHk, hFR, hFRk, hFRc, hR, hRk, hRa, hRf, hRt, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner])
  have hSa : s.envs.size + 1 < w1.envs.size := Nat.lt_of_lt_of_le (by js_norm [h4, e1, e2, e4, e5, e1', e2', hG, hGe, hGV, hGVm, hGVi, hGT, hGTm, hGTi, hGH, hGHm, hGHv, hGGH, hGGHv, hGHo, hGHk, hFR, hFRk, hFRc, hR, hRk, hRa, hRf, hRt, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]) hF1.envs_le
  have hSb : s.envs.size < w1.envs.size := by omega
  have hGd : d.env < w1.envs.size := Nat.lt_trans hG hSb
  have hfw1 : KR + 450 ≤ w1.fuel := by simp [bodyState, entryState] at hfu1; omega
  have hfr1 : s.fuel ≤ w1.fuel + 150 := by simp [bodyState, entryState] at hfu1; omega
  have hRT1 : w1.objEntry fRT = s.objEntry fRT := by
    rw [objEntry_frame0 hF1 (by js_norm [hRTo, hR])]; js_norm [hRTo, hR]
  have hRTlt1 : fRT < w1.heap.size := Nat.lt_of_lt_of_le (by js_norm [hRTo, hR]) hF1.heap_le
  have hFs1 : Frame (F0 d.env) s w1 := frame_mono (frame_trans (fp1 := F0 d.env) (s := s)
      (by unfold F0; frame_go' [*]) hF1)
    (fun p hp => by simpa [Footprint.union] using hp) (fun p hp => by simpa [Footprint.union] using hp)
    (fun hj => by simpa [Footprint.union] using hj)
  js_until [] [hRT1, hRTlt1, hEa, hEb, hEc, hSa, hSb, hGd, hfw1, hGRT, hGRTv, hRTo, hRTk, h4, e1, e2, e4, e5, e1', e2', hG, hGe, hGV, hGVm, hGVi, hGT, hGTm, hGTi, hGH, hGHm, hGHv, hGGH, hGGHv, hGHo, hGHk, hFR, hFRk, hFRc, hR, hRk, hRa, hRf, hRt, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  refine ⟨by js_norm [CallableC, hRT1, hRTlt1, hEa, hEb, hEc, hSa, hSb, hGd, hfw1, hGRT, hGRTv, hRTo, hRTk, h4, e1, e2, e4, e5, e1', e2', hG, hGe, hGV, hGVm, hGVi, hGT, hGTm, hGTi, hGH, hGHm, hGHv, hGGH, hGGHv, hGHo, hGHk, hFR, hFRk, hFRc, hR, hRk, hRa, hRf, hRt, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner], ?_⟩
  refine wp_mono (hRT _ _ (by unfold F0; frame_go' [*]) ?vt (by js_norm [hRT1, hRTlt1, hEa, hEb, hEc, hSa, hSb, hGd, hfw1, hGRT, hGRTv, hRTo, hRTk, h4, e1, e2, e4, e5, e1', e2', hG, hGe, hGV, hGVm, hGVi, hGT, hGTm, hGTi, hGH, hGHm, hGHv, hGGH, hGGHv, hGHo, hGHk, hFR, hFRk, hFRc, hR, hRk, hRa, hRf, hRt, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]; omega)) ?_
  case vt =>
    intro bm o hd
    rw [setEnv_envEntry, if_pos ⟨rfl, hGd⟩] at hd
    simp only [declLike_withBindings (declLike_withBindings (declLike_withBindings hGe _) _) _,
      Option.some.injEq, Prod.mk.injEq] at hd
    obtain ⟨rfl, rfl⟩ := hd
    simp [Std.HashMap.getElem?_modify, hGV, hGVm]
  rintro v2 w2 h2 ⟨rfl, hfu2, hP2, hF2, hVT2⟩
  have hEa2 := envEntry_frame hF2 (e := s.envs.size) (by js_norm [hRT1, hRTlt1, hEa, hEb, hEc, hSa, hSb, hGd, hfw1, hGRT, hGRTv, hRTo, hRTk, h4, e1, e2, e4, e5, e1', e2', hG, hGe, hGV, hGVm, hGVi, hGT, hGTm, hGTi, hGH, hGHm, hGHv, hGGH, hGGHv, hGHo, hGHk, hFR, hFRk, hFRc, hR, hRk, hRa, hRf, hRt, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner])
    (List.all_eq_true.mpr fun p hp => by simp [(hfpC p hp).1, e1])
  have hEb2 := envEntry_frame hF2 (e := s.envs.size + 1) (by js_norm [hRT1, hRTlt1, hEa, hEb, hEc, hSa, hSb, hGd, hfw1, hGRT, hGRTv, hRTo, hRTk, h4, e1, e2, e4, e5, e1', e2', hG, hGe, hGV, hGVm, hGVi, hGT, hGTm, hGTi, hGH, hGHm, hGHv, hGGH, hGGHv, hGHo, hGHk, hFR, hFRk, hFRc, hR, hRk, hRa, hRf, hRt, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner])
    (List.all_eq_true.mpr fun p hp => by simp [(hfpC p hp).1, e2])
  have hSa2 : s.envs.size + 1 < w2.envs.size := Nat.lt_of_lt_of_le (by js_norm [hRT1, hRTlt1, hEa, hEb, hEc, hSa, hSb, hGd, hfw1, hGRT, hGRTv, hRTo, hRTk, h4, e1, e2, e4, e5, e1', e2', hG, hGe, hGV, hGVm, hGVi, hGT, hGTm, hGTi, hGH, hGHm, hGHv, hGGH, hGGHv, hGHo, hGHk, hFR, hFRk, hFRc, hR, hRk, hRa, hRf, hRt, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]) hF2.envs_le
  have hSb2 : s.envs.size < w2.envs.size := by omega
  have hGd2 : d.env < w2.envs.size := Nat.lt_trans hG hSb2
  have hFs2 : Frame ((F0 d.env).union fpC) s w2 := frame_trans (by unfold F0; frame_go' [*]) hF2
  obtain ⟨bw, hd2, hbw⟩ := declLike_frame hF2 (e := d.env) (by js_norm [hRT1, hRTlt1, hEa, hEb, hEc, hSa, hSb, hGd, hfw1, hGRT, hGRTv, hRTo, hRTk, h4, e1, e2, e4, e5, e1', e2', hG, hGe, hGV, hGVm, hGVi, hGT, hGTm, hGTi, hGH, hGHm, hGHv, hGGH, hGGHv, hGHo, hGHk, hFR, hFRk, hFRc, hR, hRk, hRa, hRf, hRt, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]) (by js_norm [hRT1, hRTlt1, hEa, hEb, hEc, hSa, hSb, hGd, hfw1, hGRT, hGRTv, hRTo, hRTk, h4, e1, e2, e4, e5, e1', e2', hG, hGe, hGV, hGVm, hGVi, hGT, hGTm, hGTi, hGH, hGHm, hGHv, hGGH, hGGHv, hGHo, hGHk, hFR, hFRk, hFRc, hR, hRk, hRa, hRf, hRt, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]; rfl)
  have hbwH := hbw (JSStr.ofString "currentHoistableRoot") (fun hm => (hfpC _ hm).2.1 rfl)
  have hbwE := hbw (JSStr.ofString "commitReconciliationEffects") (fun hm => (hfpC _ hm).2.2.1 rfl)
  have hbwN := hbw (JSStr.ofString "needsFormReset") (fun hm => (hfpC _ hm).2.2.2 rfl)
  obtain ⟨bdV2, hbV2, hbV2m, hbV2i⟩ := hVT2 _ _ hd2
  have hR2 : w2.objEntry R = s.objEntry R := hFs2.obj_eq R hR (fun k hk => by
    simp [Footprint.union, F0] at hk; exact (hfpCp _ hk).1 rfl)
  have hRlt2 : R < w2.heap.size := Nat.lt_of_lt_of_le hR hFs2.heap_le
  have hRE2 : w2.objEntry fRE = s.objEntry fRE := hFs2.obj_eq fRE hREo (fun k hk => by
    simp [Footprint.union, F0] at hk; exact (hfpCp _ hk).2 rfl)
  have hRElt2 : fRE < w2.heap.size := Nat.lt_of_lt_of_le hREo hFs2.heap_le
  have hfw2 : 300 ≤ w2.fuel := by simp only [State.setEnv_fuel] at hfu2; omega
  have hfr2 : w1.fuel ≤ w2.fuel + KR + 100 := by simp only [State.setEnv_fuel] at hfu2; omega
  js_until [] [hd2, hbwH, hbwE, hbwN, hbV2, hbV2m, hbV2i, hR2, hRlt2, hRE2, hRElt2, hfw2, hEa2, hEb2, hSa2, hSb2, hGd2, hGRE, hGREv, hREo, hREk, hGN, hGNv, hRT1, hRTlt1, hEa, hEb, hEc, hSa, hSb, hGd, hfw1, hGRT, hGRTv, hRTo, hRTk, h4, e1, e2, e4, e5, e1', e2', hG, hGe, hGV, hGVm, hGVi, hGT, hGTm, hGTi, hGH, hGHm, hGHv, hGGH, hGGHv, hGHo, hGHk, hFR, hFRk, hFRc, hR, hRk, hRa, hRf, hRt, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  refine ⟨by js_norm [CallableC, hd2, hbwH, hbwE, hbwN, hbV2, hbV2m, hbV2i, hR2, hRlt2, hRE2, hRElt2, hfw2, hEa2, hEb2, hSa2, hSb2, hGd2, hGRE, hGREv, hREo, hREk, hGN, hGNv, hRT1, hRTlt1, hEa, hEb, hEc, hSa, hSb, hGd, hfw1, hGRT, hGRTv, hRTo, hRTk, h4, e1, e2, e4, e5, e1', e2', hG, hGe, hGV, hGVm, hGVi, hGT, hGTm, hGTi, hGH, hGHm, hGHv, hGGH, hGGHv, hGHo, hGHk, hFR, hFRk, hFRc, hR, hRk, hRa, hRf, hRt, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner], ?_⟩
  have hFs3 : Frame ((F0 d.env).union fpC) s (w2.setEnv d.env ((w2.envEntry d.env).withBindings fun x =>
      x.modify (JSStr.ofString "currentHoistableRoot") fun bd =>
        { value := some vH0, mutable := bd.mutable, strict := bd.strict, deletable := bd.deletable })) :=
    frame_setEnv_with_in hFs2 hG rfl (by rw [hd2]; rfl) (by simp [Footprint.union, F0]) _
  refine wp_mono (hRE _ _ hFs3 (by js_norm [hd2, hbwH, hbwE, hbwN, hbV2, hbV2m, hbV2i, hR2, hRlt2, hRE2, hRElt2, hfw2, hEa2, hEb2, hSa2, hSb2, hGd2, hGRE, hGREv, hREo, hREk, hGN, hGNv, hRT1, hRTlt1, hEa, hEb, hEc, hSa, hSb, hGd, hfw1, hGRT, hGRTv, hRTo, hRTk, h4, e1, e2, e4, e5, e1', e2', hG, hGe, hGV, hGVm, hGVi, hGT, hGTm, hGTi, hGH, hGHm, hGHv, hGGH, hGGHv, hGHo, hGHk, hFR, hFRk, hFRc, hR, hRk, hRa, hRf, hRt, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]; omega)) ?_
  rintro v3 w3 h3 ⟨hF3, hfu3, rfl, hH3⟩
  have hEa3 := envEntry_frame0 hF3 (e := s.envs.size) (by js_norm [hd2, hbwH, hbwE, hbwN, hbV2, hbV2m, hbV2i, hR2, hRlt2, hRE2, hRElt2, hfw2, hEa2, hEb2, hSa2, hSb2, hGd2, hGRE, hGREv, hREo, hREk, hGN, hGNv, hRT1, hRTlt1, hEa, hEb, hEc, hSa, hSb, hGd, hfw1, hGRT, hGRTv, hRTo, hRTk, h4, e1, e2, e4, e5, e1', e2', hG, hGe, hGV, hGVm, hGVi, hGT, hGTm, hGTi, hGH, hGHm, hGHv, hGGH, hGGHv, hGHo, hGHk, hFR, hFRk, hFRc, hR, hRk, hRa, hRf, hRt, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner])
  have hEb3 := envEntry_frame0 hF3 (e := s.envs.size + 1) (by js_norm [hd2, hbwH, hbwE, hbwN, hbV2, hbV2m, hbV2i, hR2, hRlt2, hRE2, hRElt2, hfw2, hEa2, hEb2, hSa2, hSb2, hGd2, hGRE, hGREv, hREo, hREk, hGN, hGNv, hRT1, hRTlt1, hEa, hEb, hEc, hSa, hSb, hGd, hfw1, hGRT, hGRTv, hRTo, hRTk, h4, e1, e2, e4, e5, e1', e2', hG, hGe, hGV, hGVm, hGVi, hGT, hGTm, hGTi, hGH, hGHm, hGHv, hGGH, hGGHv, hGHo, hGHk, hFR, hFRk, hFRc, hR, hRk, hRa, hRf, hRt, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner])
  have hEc3 := envEntry_frame0 hF3 (e := d.env) (by js_norm [hd2, hbwH, hbwE, hbwN, hbV2, hbV2m, hbV2i, hR2, hRlt2, hRE2, hRElt2, hfw2, hEa2, hEb2, hSa2, hSb2, hGd2, hGRE, hGREv, hREo, hREk, hGN, hGNv, hRT1, hRTlt1, hEa, hEb, hEc, hSa, hSb, hGd, hfw1, hGRT, hGRTv, hRTo, hRTk, h4, e1, e2, e4, e5, e1', e2', hG, hGe, hGV, hGVm, hGVi, hGT, hGTm, hGTi, hGH, hGHm, hGHv, hGGH, hGGHv, hGHo, hGHk, hFR, hFRk, hFRc, hR, hRk, hRa, hRf, hRt, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner])
  have hSa3 : s.envs.size + 1 < w3.envs.size := Nat.lt_of_lt_of_le (by js_norm [hd2, hbwH, hbwE, hbwN, hbV2, hbV2m, hbV2i, hR2, hRlt2, hRE2, hRElt2, hfw2, hEa2, hEb2, hSa2, hSb2, hGd2, hGRE, hGREv, hREo, hREk, hGN, hGNv, hRT1, hRTlt1, hEa, hEb, hEc, hSa, hSb, hGd, hfw1, hGRT, hGRTv, hRTo, hRTk, h4, e1, e2, e4, e5, e1', e2', hG, hGe, hGV, hGVm, hGVi, hGT, hGTm, hGTi, hGH, hGHm, hGHv, hGGH, hGGHv, hGHo, hGHk, hFR, hFRk, hFRc, hR, hRk, hRa, hRf, hRt, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]) hF3.envs_le
  have hSb3 : s.envs.size < w3.envs.size := by omega
  have hGd3 : d.env < w3.envs.size := Nat.lt_trans hG hSb3
  have hR3 : w3.objEntry R = s.objEntry R := by rw [objEntry_frame0 hF3 (by js_norm [hd2, hbwH, hbwE, hbwN, hbV2, hbV2m, hbV2i, hR2, hRlt2, hRE2, hRElt2, hfw2, hEa2, hEb2, hSa2, hSb2, hGd2, hGRE, hGREv, hREo, hREk, hGN, hGNv, hRT1, hRTlt1, hEa, hEb, hEc, hSa, hSb, hGd, hfw1, hGRT, hGRTv, hRTo, hRTk, h4, e1, e2, e4, e5, e1', e2', hG, hGe, hGV, hGVm, hGVi, hGT, hGTm, hGTi, hGH, hGHm, hGHv, hGGH, hGGHv, hGHo, hGHk, hFR, hFRk, hFRc, hR, hRk, hRa, hRf, hRt, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner])]; js_norm [hd2, hbwH, hbwE, hbwN, hbV2, hbV2m, hbV2i, hR2, hRlt2, hRE2, hRElt2, hfw2, hEa2, hEb2, hSa2, hSb2, hGd2, hGRE, hGREv, hREo, hREk, hGN, hGNv, hRT1, hRTlt1, hEa, hEb, hEc, hSa, hSb, hGd, hfw1, hGRT, hGRTv, hRTo, hRTk, h4, e1, e2, e4, e5, e1', e2', hG, hGe, hGV, hGVm, hGVi, hGT, hGTm, hGTi, hGH, hGHm, hGHv, hGGH, hGGHv, hGHo, hGHk, hFR, hFRk, hFRc, hR, hRk, hRa, hRf, hRt, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  have hfw3 : 100 ≤ w3.fuel := by simp only [State.setEnv_fuel] at hfu3; omega
  have hfr3 : w2.fuel ≤ w3.fuel + 40 := by simp only [State.setEnv_fuel] at hfu3; omega
  js_until [] [hEa3, hEb3, hEc3, hSa3, hSb3, hGd3, hR3, hfw3, hd2, hbwH, hbwE, hbwN, hbV2, hbV2m, hbV2i, hR2, hRlt2, hRE2, hRElt2, hfw2, hEa2, hEb2, hSa2, hSb2, hGd2, hGRE, hGREv, hREo, hREk, hGN, hGNv, hRT1, hRTlt1, hEa, hEb, hEc, hSa, hSb, hGd, hfw1, hGRT, hGRTv, hRTo, hRTk, h4, e1, e2, e4, e5, e1', e2', hG, hGe, hGV, hGVm, hGVi, hGT, hGTm, hGTi, hGH, hGHm, hGHv, hGGH, hGGHv, hGHo, hGHk, hFR, hFRk, hFRc, hR, hRk, hRa, hRf, hRt, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  refine ⟨by omega, hPCst w2 _ _ hP2 (by exact hH3) (fun e he hne => ?_)⟩
  exact (setEnv_envEntry_ne w3 d.env _ e (Ne.symm hne)).trans ((envEntry_frame0 hF3
    (by simpa using Nat.lt_trans he hSb2)).trans (setEnv_envEntry_ne w2 d.env _ e (Ne.symm hne)))

end

end ReactCommitRoot
