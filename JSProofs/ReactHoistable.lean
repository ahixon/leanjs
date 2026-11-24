import JSProofs.GHRGen
import JSProofs.Setter
import JSProofs.UPInfra
import JSProofs.ReactHostContainer

/-!
# getHoistableRoot for the root container (zippy docs/react-proofs.md)

`getHoistableRoot(container)`: `container.getRootNode` a builtin (found on its plain prototype chain), so `typeof` gives
"function"; its call (the DOM: a premise) returns the document, whose `nodeType` is 9 (a DOM read): the document.
-/

open ES ES.M HostRuns Logic
open Std (HashMap)

namespace ReactHoistable

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ} {HI : σ → Prop}

theorem typeOf_builtin {s : State} {o : ObjId} {bd : BuiltinData} (hlt : o < s.heap.size)
    (hk : (s.objEntry o).kind = .builtin bd) : typeOf (.obj o) s = .ok (JSStr.ofString "function") s := by
  simp [typeOf, isCallable, readObj_entry o _ s hlt, hk, M.bind_eq, M.bind_apply, Pure.pure, M.pure]

/-- **`typeof obj.k`**, `k` a data property on `obj`'s plain chain holding a builtin function: "function". -/
theorem wp_typeofMemberBuiltin {n : Nat} {h : σ} {obj : Sem.CExpr} {k : JSStr} {ctx : Ctx} {s : State}
    {Q : Value → State → σ → Prop}
    (hw : WP eng answer n h (obj ctx) s fun bv w h1 => GetsTo w bv k fun fv =>
      ∃ f bd, fv = .obj f ∧ f < w.heap.size ∧ (w.objEntry f).kind = .builtin bd ∧
        Q (.str (JSStr.ofString "function")) w h1) :
    WP eng answer n h (Sem.typeofRef (Sem.memberRef obj (.name k) false) ctx) s Q := by
  rw [wp_iff_wpr]
  simp only [Sem.typeofRef, Sem.memberRef, M.bind_eq, M.bind_apply]
  apply wpr_bind
  apply wpr_bind
  refine wp_mono hw fun bv w h1 q => ?_
  obtain ⟨o, m, hb, hc, hm, hna, f, bd, hfv, hflt, hfk, hq⟩ := q
  subst hb
  simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  refine wp_of_eq (a := Ref.prop (.obj o) (.str k) ctx.strict none) rfl ?_
  rw [wp_iff_wpr]
  simp only [M.bind_apply, getRefValue_prop, Obj'.get_chain w _ _ m o hc hm hna, M.bindRes_ok, hfv]
  show WPR eng answer n h1 (M.bindRes _ (typeOf (.obj f) w)) Q
  rw [typeOf_builtin hflt hfk, M.bindRes_ok]
  exact wpr_ok hq

theorem simple (d : FuncData) (hc : d.code = GHRGen.getHoistableRoot_func) : FDI.Simple d := by
  constructor <;> rw [hc] <;> try rfl
  simp [GHRGen.getHoistableRoot_func, Func.params, Func.info]

theorem getsTo_eq {s : State} {b : Value} {k : JSStr} {v : Value} {Q : Value → Prop}
    (h : GetsTo s b k fun x => x = v) (hq : Q v) : GetsTo s b k Q := by
  obtain ⟨o, m, hb, hc, hm, hna, hp⟩ := h
  exact ⟨o, m, hb, hc, hm, hna, hp ▸ hq⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
/-- **`getHoistableRoot(container)`**, `container.getRootNode()` the document `Doc` (`nodeType` 9): `Doc`. -/
theorem ghr_spec {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t : Value} {s : State} {Cont fRN Doc : ObjId}
    {bdRN : BuiltinData}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : 100 ≤ s.fuel)
    (hcode : d.code = GHRGen.getHoistableRoot_func) (hcls : d.isClassCtor = false) (hmode : d.thisMode = .strict)
    (hRN : ∀ w, Frame {} s w → GetsTo w (.obj Cont) (JSStr.ofString "getRootNode") fun v => v = .obj fRN)
    (hRNo : fRN < s.heap.size) (hRNk : (s.objEntry fRN).kind = .builtin bdRN)
    (hCall : ∀ w h1, Frame {} s w → HI h1 → 2 ≤ w.fuel → WP eng answer n h1 (callImpl eng (.obj fRN) (.obj Cont) #[]) w fun v w' h' =>
      v = .obj Doc ∧ Frame {} w w' ∧ w.fuel ≤ w'.fuel + 10 ∧ h' = h1)
    (hNT : ReactHostContainer.DomRead eng answer HI n s {} Doc "nodeType" (.num (F64.fin false 5066549580791808 (-49)))) (hHI : HI h) :
    WP eng answer (n + 1) h (callImpl eng (.obj fo) t #[.obj Cont]) s fun v w h' =>
      v = .obj Doc ∧ Frame {} s w ∧ s.fuel ≤ w.fuel + 100 ∧ h' = h := by
  apply wp_callGen GHRGen.getHoistableRoot_eq (by decide) hlt hk (by omega) hcls hmode
    (by rw [hcode]; rfl) (by rw [hcode]; rfl) (simple d hcode) (by rw [hcode]; rfl) (by rw [hcode]; rfl)
  have hpn : d.code.info.fdi.paramNames = #[JSStr.ofString "container"] := by rw [hcode]; rfl
  have hv : d.code.info.fdi.varNames = #[JSStr.ofString "rootNode"] := by rw [hcode]; rfl
  have hl : FDI.lexDecls d = #[] := by simp [FDI.lexDecls, hcode, GHRGen.getHoistableRoot_func, Func.info]
  have ha : d.code.isAsync = false := by rw [hcode]; rfl
  clear hcode
  have hw0 : Frame {} s (bodyState s fo d t #[.obj Cont]) := by frame_go' [*]
  simp only [GHRGen.getHoistableRoot]
  iterate 5 (first | js_go | js_norm [hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner] | js_split)
  refine wp_typeofMemberBuiltin ?_
  js_until [] [hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  refine getsTo_eq (hRN _ hw0) ⟨fRN, bdRN, rfl, by js_norm [hRNo], by js_norm [hRNk, hRNo], ?_⟩
  iterate 10 (first | js_go | js_norm [hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner] | js_split)
  refine wp_callMemberT ?_
  js_until [] [hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  refine getsTo_eq (hRN _ (by frame_go' [*])) ?_
  js_until [] [hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  refine ⟨by js_norm [CallableC, hRNk, hRNo, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner], wp_mono (hCall _ _ (by frame_go' [*]) hHI (by (try simp only [js_simp, State.pushEnv_fuel]); omega)) ?_⟩
  rintro v1 w1 h1 ⟨rfl, hF1, hfu1, rfl⟩
  have hE1 := envEntry_frame0 hF1 (e := s.envs.size) (by js_norm [hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner])
  have hS1 : s.envs.size < w1.envs.size := Nat.lt_of_lt_of_le (by js_norm [hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]) hF1.envs_le
  have hfw1 : 50 ≤ w1.fuel := by simp [bodyState, entryState] at hfu1; omega
  have hFs1 : Frame {} s w1 := frame_empty_trans (by frame_go' [*]) hF1
  js_until ["nodeType"] [hE1, hS1, hfw1, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  refine wp_getMemberAcc ?_
  js_until [] [hE1, hS1, hfw1, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  refine getsAcc_mono (hNT _ _ (by frame_go' [*]) hHI (by (try simp only [js_simp, State.pushEnv_fuel]); omega)) ?_
  intro v2 w2 h2 ⟨hv2, hh2, f_w2, hw2, hf_w2⟩
  subst hv2 hw2 hh2
  try simp only [js_simp, State.pushEnv_fuel] at hf_w2
  js [hE1, hS1, hfw1, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  refine ⟨frame_restore (frame_withFuel (frame_setEnv_new hFs1 (Nat.le_refl _) _) _) s, ?_⟩
  (try simp only [js_simp] at hf_w2 ⊢)
  (try simp [bodyState, entryState] at hfu1 ⊢)
  omega

end

end ReactHoistable
