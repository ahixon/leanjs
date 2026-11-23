import JSProofs.RTLGen
import JSProofs.Loops4
import JSProofs.ReactHostContainer
import JSProofs.Rebase

/-!
# recursivelyTraverseLayoutEffects (zippy docs/react-proofs.md)

`recursivelyTraverseLayoutEffects(root, parent)`: nothing when `parent.subtreeFlags & 8772` is zero (`rtl_none`);
otherwise `commitLayoutEffectOnFiber(root, child.alternate, child)` for the one child (its contract a premise, `hC`),
whose sibling is null (`rtl_one`).
-/

open ES ES.M HostRuns Logic
open Std (HashMap)

namespace ReactLayoutTraverse

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ}

theorem simple (d : FuncData) (hc : d.code = RTLGen.recursivelyTraverseLayoutEffects_func) : FDI.Simple d := by
  constructor <;> rw [hc] <;> try rfl
  simp [RTLGen.recursivelyTraverseLayoutEffects_func, Func.params, Func.info]

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
/-- **No subtree layout flags**: nothing changed. -/
theorem rtl_none {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t : Value} {s : State} {rv : Value} {P : ObjId}
    {sf : F64} {fw fe fc : Bool}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : 40 ≤ s.fuel)
    (hcode : d.code = RTLGen.recursivelyTraverseLayoutEffects_func) (hcls : d.isClassCtor = false)
    (hmode : d.thisMode = .strict)
    (hP : P < s.heap.size) (hPk : (s.objEntry P).kind.isPlain = true)
    (hPs : (s.objEntry P).props.get? (.str (JSStr.ofString "subtreeFlags")) = some (.data (.num sf) fw fe fc))
    (hsf : numberBinOp .bitAnd sf (F64.fin false 4822457999425536 (-39)) = F64.fin false 0 (-1074)) :
    WP eng answer (n + 1) h (callImpl eng (.obj fo) t #[rv, .obj P]) s fun v w h' =>
      v = .undefined ∧ Frame {} s w ∧ s.fuel ≤ w.fuel + 40 ∧ h' = h := by
  apply wp_callGen RTLGen.recursivelyTraverseLayoutEffects_eq (by decide) hlt hk (by omega) hcls hmode
    (by rw [hcode]; rfl) (by rw [hcode]; rfl) (simple d hcode) (by rw [hcode]; rfl) (by rw [hcode]; rfl)
  have hpn : d.code.info.fdi.paramNames = #[JSStr.ofString "root", JSStr.ofString "parentFiber"] := by rw [hcode]; rfl
  have hv : d.code.info.fdi.varNames = #[] := by rw [hcode]; rfl
  have hl : FDI.lexDecls d = #[] := by
    simp [FDI.lexDecls, hcode, RTLGen.recursivelyTraverseLayoutEffects_func, Func.info]
  have ha : d.code.isAsync = false := by rw [hcode]; rfl
  clear hcode
  simp only [RTLGen.recursivelyTraverseLayoutEffects]
  js [hP, hPk, hPs, hsf, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  exact ⟨by frame_go' [*], by omega⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 8000000 in
/-- **One child** `C` (sibling null): `commitLayoutEffectOnFiber(root, C.alternate, C)`, its contract `hC`. -/
theorem rtl_one {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t : Value} {s : State} {rv : Value} {P C : ObjId}
    {sf : F64} {fw fe fc cw ce cc aw ae ac : Bool} {av : Value}
    {bG : HashMap JSStr Binding} {oG : Option EnvId} {bdC : Binding} {fC : ObjId} {fpC : Footprint}
    {KC : Nat} {PC : State → σ → Prop}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : KC + 200 ≤ s.fuel)
    (hcode : d.code = RTLGen.recursivelyTraverseLayoutEffects_func) (hcls : d.isClassCtor = false)
    (hmode : d.thisMode = .strict)
    (hG : d.env < s.envs.size) (hGe : Scope.declLike? (s.envEntry d.env) = some (bG, oG))
    (hGC : bG[JSStr.ofString "commitLayoutEffectOnFiber"]? = some bdC) (hGCv : bdC.value = some (.obj fC))
    (hCo : fC < s.heap.size) (hCc : ∃ dC, (s.objEntry fC).kind = .func dC)
    (hP : P < s.heap.size) (hPk : (s.objEntry P).kind.isPlain = true)
    (hPs : (s.objEntry P).props.get? (.str (JSStr.ofString "subtreeFlags")) = some (.data (.num sf) fw fe fc))
    (hsf : (!((numberBinOp .bitAnd sf (F64.fin false 4822457999425536 (-39))).isZero ||
      numberBinOp .bitAnd sf (F64.fin false 4822457999425536 (-39)) == F64.nan)) = true)
    (hPc : (s.objEntry P).props.get? (.str (JSStr.ofString "child")) = some (.data (.obj C) cw ce cc))
    (hCx : C < s.heap.size) (hCxk : (s.objEntry C).kind.isPlain = true)
    (hCa : (s.objEntry C).props.get? (.str (JSStr.ofString "alternate")) = some (.data av aw ae ac))
    (hC : ∀ w h1, Frame {} s w → KC ≤ w.fuel →
      WP eng answer n h1 (callImpl eng (.obj fC) .undefined #[rv, av, .obj C]) w fun v w' h' =>
        Frame fpC w w' ∧ w.fuel ≤ w'.fuel + KC ∧ PC w' h' ∧ C < w'.heap.size ∧ (w'.objEntry C).kind.isPlain = true ∧
        ∃ sw se sc, (w'.objEntry C).props.get? (.str (JSStr.ofString "sibling")) = some (.data .null sw se sc))
    (hfpC : ∀ p, p ∈ fpC.binds → p.1 = d.env)
    (hPCst : ∀ w w' h', PC w h' → w'.heap = w.heap → (∀ e, e < s.envs.size → w'.envEntry e = w.envEntry e) →
      PC w' h') :
    WP eng answer (n + 1) h (callImpl eng (.obj fo) t #[rv, .obj P]) s fun v w h' =>
      v = .undefined ∧ s.fuel ≤ w.fuel + KC + 100 ∧ PC w h' ∧ Frame fpC s w := by
  apply wp_callGen RTLGen.recursivelyTraverseLayoutEffects_eq (by decide) hlt hk (by omega) hcls hmode
    (by rw [hcode]; rfl) (by rw [hcode]; rfl) (simple d hcode) (by rw [hcode]; rfl) (by rw [hcode]; rfl)
  have hpn : d.code.info.fdi.paramNames = #[JSStr.ofString "root", JSStr.ofString "parentFiber"] := by rw [hcode]; rfl
  have hv : d.code.info.fdi.varNames = #[] := by rw [hcode]; rfl
  have hl : FDI.lexDecls d = #[] := by
    simp [FDI.lexDecls, hcode, RTLGen.recursivelyTraverseLayoutEffects_func, Func.info]
  have ha : d.code.isAsync = false := by rw [hcode]; rfl
  have e1 : d.env ≠ s.envs.size := Nat.ne_of_lt hG
  have e4 : d.env < s.envs.size + 1 := Nat.lt_succ_of_lt hG
  clear hcode
  simp only [RTLGen.recursivelyTraverseLayoutEffects]
  js_until [] [hP, hPk, hPs, hsf, hPc, hCx, hCxk, hCa, e1, Ne.symm e1, e4, hG, hGe, hGC, hGCv, hCo, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  refine wp_forExpr ?_
  js_until [] [hP, hPk, hPs, hsf, hPc, hCx, hCxk, hCa, e1, Ne.symm e1, e4, hG, hGe, hGC, hGCv, hCo, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  js_until [] [hP, hPk, hPs, hsf, hPc, hCx, hCxk, hCa, e1, Ne.symm e1, e4, hG, hGe, hGC, hGCv, hCo, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  obtain ⟨dC, hCk⟩ := hCc
  refine ⟨by js_norm [CallableC, hCk, hP, hPk, hPs, hsf, hPc, hCx, hCxk, hCa, e1, Ne.symm e1, e4, hG, hGe, hGC, hGCv, hCo, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner], ?_⟩
  refine wp_mono (hC _ _ (by frame_go' [*]) (by js_norm [hP, hPk, hPs, hsf, hPc, hCx, hCxk, hCa, e1, Ne.symm e1, e4, hG, hGe, hGC, hGCv, hCo, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]; omega)) ?_
  rintro v1 w1 h1 ⟨hF1, hfu1, hP1, hClt1, hCk1, sw, se, sc, hCs1⟩
  have hE1 := envEntry_frame hF1 (e := s.envs.size) (by js_norm [hP, hPk, hPs, hsf, hPc, hCx, hCxk, hCa, e1, Ne.symm e1, e4, hG, hGe, hGC, hGCv, hCo, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner])
    (List.all_eq_true.mpr fun p hp => by simp [hfpC p hp, e1])
  have hS1 : s.envs.size < w1.envs.size := Nat.lt_of_lt_of_le (by js_norm [hP, hPk, hPs, hsf, hPc, hCx, hCxk, hCa, e1, Ne.symm e1, e4, hG, hGe, hGC, hGCv, hCo, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]) hF1.envs_le
  have hfw1 : 100 ≤ w1.fuel := by simp [State.withFuel, bodyState, entryState] at hfu1; omega
  have hfr1 : s.fuel ≤ w1.fuel + KC + 10 := by simp [State.withFuel, bodyState, entryState] at hfu1; omega
  js [hE1, hS1, hfw1, hClt1, hCk1, hCs1, hP, hPk, hPs, hsf, hPc, hCx, hCxk, hCa, e1, Ne.symm e1, e4, hG, hGe, hGC, hGCv, hCo, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  refine ⟨by omega, hPCst _ _ _ hP1 rfl (fun e he => ?_), ?_⟩
  · exact setEnv_envEntry_ne w1 s.envs.size _ e (Ne.symm (Nat.ne_of_lt he))
  · have hFs1 : Frame fpC s w1 := frame_mono (frame_trans (fp1 := {}) (s := s) (by frame_go' [*]) hF1)
      (fun p hp => by simpa [Footprint.union] using hp) (fun p hp => by simpa [Footprint.union] using hp)
      (fun hj => by simpa [Footprint.union] using hj)
    exact frame_restore (frame_withFuel (frame_setEnv_new hFs1 (Nat.le_refl _) _) _) s


set_option maxRecDepth 40000 in
set_option maxHeartbeats 8000000 in
/-- `rtl_one` for a child whose layout writes nothing and keeps the host state: **one child** `C` (sibling null): `commitLayoutEffectOnFiber(root, C.alternate, C)`, its contract `hC`. -/
theorem rtl_one_eq {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t : Value} {s : State} {rv : Value} {P C : ObjId}
    {sf : F64} {fw fe fc cw ce cc aw ae ac : Bool} {av : Value}
    {bG : HashMap JSStr Binding} {oG : Option EnvId} {bdC : Binding} {fC : ObjId}
    {KC : Nat}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : KC + 200 ≤ s.fuel)
    (hcode : d.code = RTLGen.recursivelyTraverseLayoutEffects_func) (hcls : d.isClassCtor = false)
    (hmode : d.thisMode = .strict)
    (hG : d.env < s.envs.size) (hGe : Scope.declLike? (s.envEntry d.env) = some (bG, oG))
    (hGC : bG[JSStr.ofString "commitLayoutEffectOnFiber"]? = some bdC) (hGCv : bdC.value = some (.obj fC))
    (hCo : fC < s.heap.size) (hCc : ∃ dC, (s.objEntry fC).kind = .func dC)
    (hP : P < s.heap.size) (hPk : (s.objEntry P).kind.isPlain = true)
    (hPs : (s.objEntry P).props.get? (.str (JSStr.ofString "subtreeFlags")) = some (.data (.num sf) fw fe fc))
    (hsf : (!((numberBinOp .bitAnd sf (F64.fin false 4822457999425536 (-39))).isZero ||
      numberBinOp .bitAnd sf (F64.fin false 4822457999425536 (-39)) == F64.nan)) = true)
    (hPc : (s.objEntry P).props.get? (.str (JSStr.ofString "child")) = some (.data (.obj C) cw ce cc))
    (hCx : C < s.heap.size) (hCxk : (s.objEntry C).kind.isPlain = true)
    (hCa : (s.objEntry C).props.get? (.str (JSStr.ofString "alternate")) = some (.data av aw ae ac))
    (hC : ∀ w h1, Frame {} s w → KC ≤ w.fuel →
      WP eng answer n h1 (callImpl eng (.obj fC) .undefined #[rv, av, .obj C]) w fun v w' h' =>
        Frame {} w w' ∧ w.fuel ≤ w'.fuel + KC ∧ h' = h1 ∧ C < w'.heap.size ∧ (w'.objEntry C).kind.isPlain = true ∧
        ∃ sw se sc, (w'.objEntry C).props.get? (.str (JSStr.ofString "sibling")) = some (.data .null sw se sc)):
    WP eng answer (n + 1) h (callImpl eng (.obj fo) t #[rv, .obj P]) s fun v w h' =>
      v = .undefined ∧ s.fuel ≤ w.fuel + KC + 100 ∧ h' = h ∧ Frame {} s w := by
  apply wp_callGen RTLGen.recursivelyTraverseLayoutEffects_eq (by decide) hlt hk (by omega) hcls hmode
    (by rw [hcode]; rfl) (by rw [hcode]; rfl) (simple d hcode) (by rw [hcode]; rfl) (by rw [hcode]; rfl)
  have hpn : d.code.info.fdi.paramNames = #[JSStr.ofString "root", JSStr.ofString "parentFiber"] := by rw [hcode]; rfl
  have hv : d.code.info.fdi.varNames = #[] := by rw [hcode]; rfl
  have hl : FDI.lexDecls d = #[] := by
    simp [FDI.lexDecls, hcode, RTLGen.recursivelyTraverseLayoutEffects_func, Func.info]
  have ha : d.code.isAsync = false := by rw [hcode]; rfl
  have e1 : d.env ≠ s.envs.size := Nat.ne_of_lt hG
  have e4 : d.env < s.envs.size + 1 := Nat.lt_succ_of_lt hG
  clear hcode
  simp only [RTLGen.recursivelyTraverseLayoutEffects]
  js_until [] [hP, hPk, hPs, hsf, hPc, hCx, hCxk, hCa, e1, Ne.symm e1, e4, hG, hGe, hGC, hGCv, hCo, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  refine wp_forExpr ?_
  js_until [] [hP, hPk, hPs, hsf, hPc, hCx, hCxk, hCa, e1, Ne.symm e1, e4, hG, hGe, hGC, hGCv, hCo, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  js_until [] [hP, hPk, hPs, hsf, hPc, hCx, hCxk, hCa, e1, Ne.symm e1, e4, hG, hGe, hGC, hGCv, hCo, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  obtain ⟨dC, hCk⟩ := hCc
  refine ⟨by js_norm [CallableC, hCk, hP, hPk, hPs, hsf, hPc, hCx, hCxk, hCa, e1, Ne.symm e1, e4, hG, hGe, hGC, hGCv, hCo, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner], ?_⟩
  refine wp_mono (hC _ _ (by frame_go' [*]) (by js_norm [hP, hPk, hPs, hsf, hPc, hCx, hCxk, hCa, e1, Ne.symm e1, e4, hG, hGe, hGC, hGCv, hCo, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]; omega)) ?_
  rintro v1 w1 h1 ⟨hF1, hfu1, rfl, hClt1, hCk1, sw, se, sc, hCs1⟩
  have hE1 := envEntry_frame hF1 (e := s.envs.size) (by js_norm [hP, hPk, hPs, hsf, hPc, hCx, hCxk, hCa, e1, Ne.symm e1, e4, hG, hGe, hGC, hGCv, hCo, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner])
    (List.all_eq_true.mpr fun p hp => by simp at hp)
  have hS1 : s.envs.size < w1.envs.size := Nat.lt_of_lt_of_le (by js_norm [hP, hPk, hPs, hsf, hPc, hCx, hCxk, hCa, e1, Ne.symm e1, e4, hG, hGe, hGC, hGCv, hCo, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]) hF1.envs_le
  have hfw1 : 100 ≤ w1.fuel := by simp [State.withFuel, bodyState, entryState] at hfu1; omega
  have hfr1 : s.fuel ≤ w1.fuel + KC + 10 := by simp [State.withFuel, bodyState, entryState] at hfu1; omega
  js [hE1, hS1, hfw1, hClt1, hCk1, hCs1, hP, hPk, hPs, hsf, hPc, hCx, hCxk, hCa, e1, Ne.symm e1, e4, hG, hGe, hGC, hGCv, hCo, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  have hFs1 : Frame {} s w1 := frame_then_empty (by frame_go' [hP]) hF1
  exact ⟨by omega, frame_restore (frame_withFuel (frame_setEnv_new hFs1 (Nat.le_refl _) _) _) s⟩



end

end ReactLayoutTraverse
