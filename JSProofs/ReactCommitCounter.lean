import JSProofs.CMESwitch
import JSProofs.Setter
import JSProofs.ReactHostContainer

/-!
# commitMutationEffectsOnFiber for the counter (zippy docs/react-proofs.md)

The function component case (tag 0) for a fiber without the Update flag: its children traversed
(`recursivelyTraverseMutationEffects`), then its reconciliation effects; the callees' contracts are premises.
-/

open ES ES.M HostRuns Logic
open Std (HashMap)

namespace ReactCommitCounter

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ} {HI : σ → Prop}

theorem simple (d : FuncData) (hc : d.code = CMEGen.commitMutationEffectsOnFiber_func) : FDI.Simple d := by
  constructor <;> rw [hc] <;> try rfl
  simp [CMEGen.commitMutationEffectsOnFiber_func, Func.params, Func.info]

set_option maxRecDepth 40000 in
set_option maxHeartbeats 8000000 in
theorem cme_counter {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t : Value} {s : State}
    {rv lv av : Value} {K : ObjId} {fl : F64} {KR : Nat}
    {aw ae ac fw fe fc tw te tc : Bool}
    {bG : HashMap JSStr Binding} {oG : Option EnvId} {bdRT bdRE : Binding}
    {fRT fRE : ObjId} {fpC : Footprint} {PC : State → σ → Prop}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : KR + 300 ≤ s.fuel)
    (hcode : d.code = CMEGen.commitMutationEffectsOnFiber_func) (hcls : d.isClassCtor = false)
    (hmode : d.thisMode = .strict)
    (hK : K < s.heap.size) (hKk : (s.objEntry K).kind.isPlain = true)
    (hKa : (s.objEntry K).props.get? (.str (JSStr.ofString "alternate")) = some (.data av aw ae ac))
    (hKf : (s.objEntry K).props.get? (.str (JSStr.ofString "flags")) = some (.data (.num fl) fw fe fc))
    (hKt : (s.objEntry K).props.get? (.str (JSStr.ofString "tag")) = some (.data (.num (F64.fin false 0 (-1074))) tw te tc))
    (h4 : numberBinOp .bitAnd fl (F64.fin false 4503599627370496 (-50)) = F64.fin false 0 (-1074))
    (hG : d.env < s.envs.size) (hGe : Scope.declLike? (s.envEntry d.env) = some (bG, oG))
    (hGRT : bG[JSStr.ofString "recursivelyTraverseMutationEffects"]? = some bdRT) (hGRTv : bdRT.value = some (.obj fRT))
    (hGRE : bG[JSStr.ofString "commitReconciliationEffects"]? = some bdRE) (hGREv : bdRE.value = some (.obj fRE))
    (hRTo : fRT < s.heap.size) (hRTc : ∃ dd, (s.objEntry fRT).kind = .func dd)
    (hREo : fRE < s.heap.size) (hREc : ∃ dd, (s.objEntry fRE).kind = .func dd)
    (hRT : ∀ w h1, Frame {} s w → HI h1 → KR + 200 ≤ w.fuel →
      WP eng answer (n + 1) h1 (callImpl eng (.obj fRT) .undefined #[rv, .obj K, lv]) w fun v w' h' =>
        v = .undefined ∧ w.fuel ≤ w'.fuel + KR + 100 ∧ PC w' h' ∧ Frame fpC w w')
    (hfpC : ∀ p, p ∈ fpC.binds → p.1 = d.env ∧ p.2 ≠ JSStr.ofString "commitReconciliationEffects")
    (hfpCp : ∀ p, p ∈ fpC.props → p.1 ≠ K ∧ p.1 ≠ fRE)
    (hRE : ∀ w h1, Frame fpC s w → 100 ≤ w.fuel →
      WP eng answer (n + 1) h1 (callImpl eng (.obj fRE) .undefined #[.obj K]) w fun v w' h' =>
        Frame {} w w' ∧ w.fuel ≤ w'.fuel + 40 ∧ h' = h1 ∧ w'.heap = w.heap)
    (hPCst : ∀ w w' h', PC w h' → w'.heap = w.heap → (∀ e, e < s.envs.size → w'.envEntry e = w.envEntry e) →
      PC w' h') (hHI : HI h) :
    WP eng answer (n + 2) h (callImpl eng (.obj fo) t #[.obj K, rv, lv]) s fun v w h' =>
      v = .undefined ∧ s.fuel ≤ w.fuel + KR + 200 ∧ PC w h' ∧ Frame fpC s w := by
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
  clear hcode
  simp only [CMEGen.commitMutationEffectsOnFiber]
  iterate 15 (first | js_go | js_norm [hK, hKk, hKa, hKf, hKt, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner] | js_split)
  refine wp_switchC CMESwitch.lex ?_
  js_until [] [h4, e1, e2, e4, e5, e1', e2', hG, hGe, hGRT, hGRTv, hRTo, hRTk, hK, hKk, hKa, hKf, hKt, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  refine ⟨by js_norm [CallableC, h4, e1, e2, e4, e5, e1', e2', hG, hGe, hGRT, hGRTv, hRTo, hRTk, hK, hKk, hKa, hKf, hKt, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner], ?_⟩
  refine wp_mono (hRT _ _ (by frame_go' [*]) hHI (by js_norm [h4, e1, e2, e4, e5, e1', e2', hG, hGe, hGRT, hGRTv, hRTo, hRTk, hK, hKk, hKa, hKf, hKt, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]; omega)) ?_
  rintro v1 w1 h1 ⟨rfl, hfu1, hP1, hF1⟩
  have hEa := envEntry_frame hF1 (e := s.envs.size) (by js_norm [h4, e1, e2, e4, e5, e1', e2', hG, hGe, hGRT, hGRTv, hRTo, hRTk, hK, hKk, hKa, hKf, hKt, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner])
    (List.all_eq_true.mpr fun p hp => by simp [(hfpC p hp).1, e1])
  have hEb := envEntry_frame hF1 (e := s.envs.size + 1) (by js_norm [h4, e1, e2, e4, e5, e1', e2', hG, hGe, hGRT, hGRTv, hRTo, hRTk, hK, hKk, hKa, hKf, hKt, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner])
    (List.all_eq_true.mpr fun p hp => by simp [(hfpC p hp).1, e2])
  have hSa : s.envs.size + 1 < w1.envs.size := Nat.lt_of_lt_of_le (by js_norm [h4, e1, e2, e4, e5, e1', e2', hG, hGe, hGRT, hGRTv, hRTo, hRTk, hK, hKk, hKa, hKf, hKt, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]) hF1.envs_le
  have hSb : s.envs.size < w1.envs.size := by omega
  have hFs1 : Frame fpC s w1 := frame_mono (frame_trans (fp1 := {}) (s := s) (by frame_go' [*]) hF1)
    (fun p hp => by simpa [Footprint.union] using hp) (fun p hp => by simpa [Footprint.union] using hp)
    (fun hj => by simpa [Footprint.union] using hj)
  have hK1 : w1.objEntry K = s.objEntry K := hFs1.obj_eq K hK (fun k hk => (hfpCp _ hk).1 rfl)
  have hKlt1 : K < w1.heap.size := Nat.lt_of_lt_of_le hK hFs1.heap_le
  have hRE1 : w1.objEntry fRE = s.objEntry fRE := hFs1.obj_eq fRE hREo (fun k hk => (hfpCp _ hk).2 rfl)
  obtain ⟨bw, hd1, hbw⟩ := declLike_frame hFs1 (e := d.env) (bs := bG) (o := oG) hG hGe
  have hRE1b : bw[JSStr.ofString "commitReconciliationEffects"]? = some bdRE := by
    have hx := hbw (JSStr.ofString "commitReconciliationEffects") (fun hm => (hfpC _ hm).2 rfl)
    rw [hx]; exact hGRE
  have hGd : d.env < w1.envs.size := Nat.lt_trans hG hSb
  have hRElt1 : fRE < w1.heap.size := Nat.lt_of_lt_of_le hREo hFs1.heap_le
  have hfw1 : 100 ≤ w1.fuel := by simp [bodyState, entryState] at hfu1; omega
  have hfr1 : s.fuel ≤ w1.fuel + KR + 110 := by simp [bodyState, entryState] at hfu1; omega
  js_until [] [hd1, hRE1b, hGd, hEa, hEb, hSa, hSb, hFs1, hK1, hKlt1, hRE1, hRElt1, hfw1, hGRE, hGREv, hREo, hREk, h4, e1, e2, e4, e5, e1', e2', hG, hGe, hGRT, hGRTv, hRTo, hRTk, hK, hKk, hKa, hKf, hKt, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  refine ⟨by js_norm [CallableC, hd1, hRE1b, hGd, hEa, hEb, hSa, hSb, hFs1, hK1, hKlt1, hRE1, hRElt1, hfw1, hGRE, hGREv, hREo, hREk, h4, e1, e2, e4, e5, e1', e2', hG, hGe, hGRT, hGRTv, hRTo, hRTk, hK, hKk, hKa, hKf, hKt, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner], ?_⟩
  refine wp_mono (hRE _ _ hFs1 (by omega)) ?_
  rintro v2 w2 h2 ⟨hF2, hfu2, rfl, hH2⟩
  have hP2 := hPCst w1 w2 _ hP1 hH2 (fun e he => envEntry_frame0 hF2 (Nat.lt_trans he hSb))
  have hEa2 := envEntry_frame0 hF2 (e := s.envs.size) hSb
  have hEb2 := envEntry_frame0 hF2 (e := s.envs.size + 1) hSa
  have hSa2 : s.envs.size + 1 < w2.envs.size := Nat.lt_of_lt_of_le hSa hF2.envs_le
  have hSb2 : s.envs.size < w2.envs.size := by omega
  have hfw2 : 40 ≤ w2.fuel := by omega
  js_until [] [hEa2, hEb2, hSa2, hSb2, hfw2, hd1, hRE1b, hGd, hEa, hEb, hSa, hSb, hFs1, hK1, hKlt1, hRE1, hRElt1, hfw1, hGRE, hGREv, hREo, hREk, h4, e1, e2, e4, e5, e1', e2', hG, hGe, hGRT, hGRTv, hRTo, hRTk, hK, hKk, hKa, hKf, hKt, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  refine ⟨by omega, hPCst w2 _ _ hP2 rfl (fun _ _ => rfl), frame_restore (frame_mono (frame_trans hFs1 hF2)
    (fun p hp => by simpa [Footprint.union] using hp) (fun p hp => by simpa [Footprint.union] using hp)
    (fun hj => by simpa [Footprint.union] using hj)) s⟩


end

end ReactCommitCounter
