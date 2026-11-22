import JSProofs.ReactPrerender
import JSProofs.ReactDSSI
import JSProofs.PWRGen

/-!
# React's `performWorkOnRoot` for a click's sync render (zippy docs/react-proofs.md)

`performWorkOnRoot(root, 2, true)` outside rendering: not prerendering (`checkIfRootIsPrerendering` by its theorem), so
`renderRootSync(root, 2, true)`; it completes (5), so the `do … while (1)` takes its switch's `case 5` and commits:
`completeRootWhenReady(root, root.current.alternate, …, 2, …, 5, null, -0, 0)`; then `ensureRootIsScheduled(root)`.
The render, the commit, and the rescheduling are hypotheses here.
-/

open ES ES.M HostRuns Logic
open Std (HashMap)

namespace ReactPerformWork

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ}

/-- After the render: the root's current fiber and its alternate (the finished work), the module's record with the
values `performWorkOnRoot` passes on to the commit. -/
structure RenderDone (w : State) (g : EnvId) (oG : Option EnvId) (R C : ObjId) (alt : Value)
    (bm : HashMap JSStr Binding) (x1 x2 x3 x4 x5 x6 x7 : Value) : Prop where
  record : Scope.declLike? (w.envEntry g) = some (bm, oG)
  v1 : ∃ bd, bm[JSStr.ofString "workInProgressRootRecoverableErrors"]? = some bd ∧ bd.value = some x1
  v2 : ∃ bd, bm[JSStr.ofString "workInProgressTransitions"]? = some bd ∧ bd.value = some x2
  v3 : ∃ bd, bm[JSStr.ofString "workInProgressRootDidIncludeRecursiveRenderUpdate"]? = some bd ∧ bd.value = some x3
  v4 : ∃ bd, bm[JSStr.ofString "workInProgressDeferredLane"]? = some bd ∧ bd.value = some x4
  v5 : ∃ bd, bm[JSStr.ofString "workInProgressRootInterleavedUpdatedLanes"]? = some bd ∧ bd.value = some x5
  v6 : ∃ bd, bm[JSStr.ofString "workInProgressSuspendedRetryLanes"]? = some bd ∧ bd.value = some x6
  v7 : ∃ bd, bm[JSStr.ofString "workInProgressRootDidSkipSuspendedSiblings"]? = some bd ∧ bd.value = some x7
  root : R < w.heap.size ∧ (w.objEntry R).kind.isPlain = true ∧
    ∃ a b c, (w.objEntry R).props.get? (.str "current") = some (.data (.obj C) a b c)
  cur : C < w.heap.size ∧ (w.objEntry C).kind.isPlain = true ∧
    ∃ a b c, (w.objEntry C).props.get? (.str "alternate") = some (.data alt a b c)

/-- The function's own locals (record `e`). -/
def fpOwn (e : EnvId) : Footprint :=
  ⟨[(e, "root$jscomp$0"), (e, "lanes"), (e, "forceSync"), (e, "shouldTimeSlice"), (e, "exitStatus"),
    (e, "renderWasConcurrent"), (e, "JSCompiler_inline_result"), (e, "root"), (e, "wasRootDehydrated")], [], false⟩

theorem simple (d : FuncData) (hc : d.code = PWRGen.performWorkOnRoot_func) : FDI.Simple d := by
  constructor <;> rw [hc] <;> try rfl
  simp [PWRGen.performWorkOnRoot_func, Func.params, Func.info]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
theorem call_spec {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t : Value} {s : State}
    {bG : HashMap JSStr Binding} {oG : Option EnvId}
    {bdX bdP bdRS : Binding} {R fP fRS : ObjId} {dP dRS : FuncData} {ec : F64}
    {lw le lc sw se sc pw pe pc : Bool} {Q : State → σ → Prop}
    {bdCR bdE : Binding} {fCR fE : ObjId} {dCR dE : FuncData} {fpR fpC fpE : Footprint} {kR kC kE : Nat}
    {PR PC : State → σ → Prop}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : kR + kC + kE + 300 ≤ s.fuel)
    (hcode : d.code = PWRGen.performWorkOnRoot_func) (hcls : d.isClassCtor = false) (hmode : d.thisMode = .strict)
    (hG : d.env < s.envs.size) (hGe : Scope.declLike? (s.envEntry d.env) = some (bG, oG))
    (hGX : bG[JSStr.ofString "executionContext"]? = some bdX) (hGXv : bdX.value = some (.num ec))
    (hec : isStrictlyEqual (.num (F64.fin false 0 (-1074)))
      (.num (numberBinOp .bitAnd ec (F64.fin false 6755399441055744 (-50)))) = true)
    (hGP : bG[JSStr.ofString "checkIfRootIsPrerendering"]? = some bdP) (hGPv : bdP.value = some (.obj fP))
    (hGRS : bG[JSStr.ofString "renderRootSync"]? = some bdRS) (hGRSv : bdRS.value = some (.obj fRS))
    (hPo : fP < s.heap.size) (hPk : (s.objEntry fP).kind = .func dP)
    (hPcode : dP.code = CPRGen.checkIfRootIsPrerendering_func) (hPcls : dP.isClassCtor = false)
    (hPmode : dP.thisMode = .strict)
    (hRSo : fRS < s.heap.size) (hRSk : (s.objEntry fRS).kind = .func dRS)
    (hR : R < s.heap.size) (hRk : (s.objEntry R).kind.isPlain = true)
    (hRp : (s.objEntry R).props.get? (.str "pendingLanes") =
      some (.data (.num (F64.fin false 4503599627370496 (-51))) lw le lc))
    (hRs : (s.objEntry R).props.get? (.str "suspendedLanes") = some (.data (.num (F64.fin false 0 (-1074))) sw se sc))
    (hRi : (s.objEntry R).props.get? (.str "pingedLanes") = some (.data (.num (F64.fin false 0 (-1074))) pw pe pc))
    (hGCR : bG[JSStr.ofString "completeRootWhenReady"]? = some bdCR) (hGCRv : bdCR.value = some (.obj fCR))
    (hGE : bG[JSStr.ofString "ensureRootIsScheduled"]? = some bdE) (hGEv : bdE.value = some (.obj fE))
    (hCRo : fCR < s.heap.size) (hCRk : (s.objEntry fCR).kind = .func dCR)
    (hEo : fE < s.heap.size) (hEk : (s.objEntry fE).kind = .func dE)
    -- (`renderRootSync(root, 2, true)`: completed, 5)
    (hRender : ∀ w h1, Frame {} s w → s.fuel ≤ w.fuel + 40 →
      WP eng answer n h1 (callImpl eng (.obj fRS) .undefined
          #[.obj R, .num (F64.fin false 4503599627370496 (-51)), .bool true]) w fun v w' h' =>
        v = .num (F64.fin false 5629499534213120 (-50)) ∧ Frame fpR w w' ∧ w.fuel ≤ w'.fuel + kR ∧
        (∃ C alt bm x1 x2 x3 x4 x5 x6 x7, RenderDone w' d.env oG R C alt bm x1 x2 x3 x4 x5 x6 x7) ∧ PR w' h')
    (hfpRE : fpR.binds.all (fun q => q.1 != s.envs.size) = true)
    (hfpRC : (d.env, JSStr.ofString "completeRootWhenReady") ∉ fpR.binds)
    (hfpRS : (d.env, JSStr.ofString "ensureRootIsScheduled") ∉ fpR.binds)
    (hfpRO : fpR.props.all (fun q => q.1 != fCR && q.1 != fE) = true)
    -- (`completeRootWhenReady(root, finishedWork, …, lanes, …, 5, null, -0, 0)`: the commit)
    (hComplete : ∀ w2 w h1 C alt bm x1 x2 x3 x4 x5 x6 x7, RenderDone w2 d.env oG R C alt bm x1 x2 x3 x4 x5 x6 x7 →
      PR w2 h1 → Frame (fpOwn s.envs.size) w2 w → s.fuel ≤ w.fuel + kR + 80 →
      WP eng answer n h1 (callImpl eng (.obj fCR) .undefined #[.obj R, alt, x1, x2, x3,
          .num (F64.fin false 4503599627370496 (-51)), x4, x5, x6, x7, .num (F64.fin false 5629499534213120 (-50)),
          .null, .num (F64.fin false 0 (-1074)).neg, .num (F64.fin false 0 (-1074))]) w fun _ w' h' =>
        Frame fpC w w' ∧ w.fuel ≤ w'.fuel + kC ∧ PC w' h')
    (hfpCE : fpC.binds.all (fun q => q.1 != s.envs.size) = true)
    (hfpCS : (d.env, JSStr.ofString "ensureRootIsScheduled") ∉ fpC.binds)
    (hfpCO : fpC.props.all (fun q => q.1 != fE) = true)
    -- (`ensureRootIsScheduled(root)`)
    (hEnsure : ∀ w3 w h1, PC w3 h1 → Frame (fpOwn s.envs.size) w3 w → 20 ≤ w.fuel →
      WP eng answer n h1 (callImpl eng (.obj fE) .undefined #[.obj R]) w fun _ w' h' =>
        Frame fpE w w' ∧ w.fuel ≤ w'.fuel + kE ∧ Q (w'.restore s) h')
    (hfpEB : fpE.binds.all (fun q => decide (q.1 < s.envs.size)) = true) :
    WP eng answer (n + 1) h (callImpl eng (.obj fo) t #[.obj R, .num (F64.fin false 4503599627370496 (-51)), .bool true]) s
      fun v w h' => v = .undefined ∧ Frame ⟨fpR.binds ++ fpC.binds ++ fpE.binds, fpR.props ++ fpC.props ++ fpE.props,
        fpR.jobs || fpC.jobs || fpE.jobs⟩ s w ∧ s.fuel ≤ w.fuel + kR + kC + kE + 300 ∧ Q w h' := by
  replace hRender := ReactDSSI.Hold.mk hRender
  replace hComplete := ReactDSSI.Hold.mk hComplete
  replace hEnsure := ReactDSSI.Hold.mk hEnsure
  apply wp_callGen PWRGen.performWorkOnRoot_eq (by decide) hlt hk (by omega) hcls hmode
    (by rw [hcode]; rfl) (by rw [hcode]; rfl) (simple d hcode) (by rw [hcode]; rfl) (by rw [hcode]; rfl)
  have hpn : d.code.info.fdi.paramNames = #[JSStr.ofString "root$jscomp$0", JSStr.ofString "lanes",
      JSStr.ofString "forceSync"] := by rw [hcode]; rfl
  have hv : d.code.info.fdi.varNames = #[JSStr.ofString "shouldTimeSlice", JSStr.ofString "exitStatus",
      JSStr.ofString "renderWasConcurrent", JSStr.ofString "JSCompiler_inline_result", JSStr.ofString "root",
      JSStr.ofString "wasRootDehydrated"] := by rw [hcode]; rfl
  have hl : FDI.lexDecls d = #[] := by simp [FDI.lexDecls, hcode, PWRGen.performWorkOnRoot_func, Func.info]
  have ha : d.code.isAsync = false := by rw [hcode]; rfl
  have hne : s.envs.size ≠ d.env := Nat.ne_of_gt hG
  have hG1 : d.env < s.envs.size + 1 := Nat.lt_succ_of_lt hG
  clear hcode
  simp only [PWRGen.performWorkOnRoot]
  js [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGX, hGXv, hec, hGP, hGPv, hPo, hPk, FDI.fdiCtx, Sem.inner]
  refine ⟨by js_norm [CallableC, *], ?_⟩
  refine wp_mono (ReactPrerender.call_spec (by simpa using hPo) (by simpa using hPk) (by simp; omega) hPcode hPcls
    hPmode (by simpa using hR) (by simpa using hRk) (by simpa using hRp) (by simpa using hRs) (by simpa using hRi)) ?p1
  case p1 =>
  intro r w1 h1 ⟨hr, hF1, hfu1⟩
  subst hr
  try simp only [js_simp] at hfu1
  have hE1s : s.envs.size < w1.envs.size := envs_frame hF1 (by simp)
  have hG1s : d.env < w1.envs.size := envs_frame hF1 (by simp; omega)
  js [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGRS, hGRSv, hRSo, hRSk, hE1s, hG1s, envEntry_frame0 hF1,
    objEntry_frame0 hF1, heap_frame hF1, envs_frame hF1, FDI.fdiCtx, Sem.inner]
  -- (`renderRootSync(root, 2, true)`)
  refine ⟨by js_norm [CallableC, *, objEntry_frame0 hF1, heap_frame hF1], ?_⟩
  refine wp_mono ((ReactDSSI.Hold.get hRender) _ h1 ?fr2 ?fu2) ?post2
  case fr2 => frame_go' [*, hne, Ne.symm hne, hG1]
  case fu2 => simp at hfu1 ⊢; omega
  case post2 =>
  intro r w2 h2 ⟨hr, hF2, hfu2, ⟨C, alt, bm, x1, x2, x3, x4, x5, x6, x7, hRD⟩, hPR⟩
  subst hr
  have hRD' := hRD
  obtain ⟨hW, ⟨bd1, hb1, hv1⟩, ⟨bd2, hb2, hv2⟩, ⟨bd3, hb3, hv3⟩, ⟨bd4, hb4, hv4⟩, ⟨bd5, hb5, hv5⟩, ⟨bd6, hb6, hv6⟩,
    ⟨bd7, hb7, hv7⟩, ⟨hR2, hRk2, a1, a2, a3, hRc2⟩, ⟨hC2, hCk2, c1, c2, c3, hCa2⟩⟩ := hRD
  have hE2 := envEntry_frame hF2 (e := s.envs.size) (by simp only [js_simp]; exact hE1s) hfpRE
  have hE2s : s.envs.size < w2.envs.size := envs_frame hF2 (by simp only [js_simp]; exact hE1s)
  have hG2s : d.env < w2.envs.size := envs_frame hF2 (by simp only [js_simp]; exact hG1s)
  try simp only [js_simp] at hfu2
  obtain ⟨bW2, hW2, hW2x⟩ := declLike_frame hF2 (e := d.env) (o := oG) (by simp only [js_simp]; exact hG1s)
    (by js_norm [*, Ne.symm hne, envEntry_frame0 hF1]; rfl)
  have hbm : bm = bW2 := by rw [hW] at hW2; simp only [Option.some.injEq, Prod.mk.injEq] at hW2; exact hW2.1
  subst hbm
  have hWCR := hW2x _ hfpRC
  have hWE := hW2x _ hfpRS
  have hCR2 : fCR < w2.heap.size := heap_frame hF2 (by simp only [js_simp]; exact heap_frame hF1 (by simpa using hCRo))
  have hCRk2 : (w2.objEntry fCR).kind = .func dCR := by
    rw [objEntry_frame hF2 (by simp only [js_simp]; exact heap_frame hF1 (by simpa using hCRo))
      (by simp only [List.all_eq_true, bne_iff_ne, ne_eq] at hfpRO ⊢; intro q hq; exact fun h => by simpa [h] using hfpRO q hq)]
    simp only [js_simp]; rw [objEntry_frame0 hF1 (by simpa using hCRo)]; simpa using hCRk
  have hE2a : s.envs.size < w2.envs.size + 1 := Nat.lt_succ_of_lt hE2s
  have hE2b : s.envs.size ≠ w2.envs.size := Nat.ne_of_lt hE2s
  have hG2a : d.env < w2.envs.size + 1 := Nat.lt_succ_of_lt hG2s
  have hG2b : d.env ≠ w2.envs.size := Nat.ne_of_lt hG2s
  js [hpn, hv, hl, ha, hG, hne, Ne.symm hne, hE2, hE2s, hG2s, hE2a, hE2b, hG2a, hG2b, Ne.symm hE2b, Ne.symm hG2b, hW, hR2, hRk2, hRc2, hC2, hCk2, hCa2,
    hb1, hv1, hb2, hv2, hb3, hv3, hb4, hv4, hb5, hv5, hb6, hv6, hb7, hv7, hWCR, hWE, hGCR, hGCRv, hGE, hGEv,
    hCR2, hCRk2, FDI.fdiCtx, Sem.inner]
  -- (`completeRootWhenReady(…)`: the commit)
  refine ⟨by js_norm [CallableC, *], ?_⟩
  refine wp_mono ((ReactDSSI.Hold.get hComplete) w2 _ h2 C alt bm x1 x2 x3 x4 x5 x6 x7 hRD' hPR ?fr3 ?fu3) ?post3
  case fr3 => simp only [fpOwn]; frame_go' [*, hne, Ne.symm hne]
  case fu3 => simp only [js_simp] at hfu1 hfu2 ⊢; omega
  case post3 =>
  intro r w3 h3 ⟨hF3, hfu3, hPC⟩
  try simp only [js_simp] at hfu3
  have hsz : ∀ {x : Nat}, x < w2.envs.size → x < w3.envs.size := fun hx =>
    envs_frame hF3 (by simp only [js_simp]; first | exact Nat.lt_succ_of_lt hx | exact hx | omega)
  have hE3 := envEntry_frame hF3 (e := s.envs.size) (by simp only [js_simp]; first | exact hE2a | exact hE2s | omega) hfpCE
  have hE3s : s.envs.size < w3.envs.size := hsz hE2s
  have hG3s : d.env < w3.envs.size := hsz hG2s
  obtain ⟨bW3, hW3, hW3x⟩ := declLike_frame hF3 (e := d.env) (o := oG)
    (by simp only [js_simp]; first | exact hG2a | exact hG2s | omega) (by js_norm [*, Ne.symm hne, Ne.symm hG2b]; rfl)
  have hWE3 := hW3x _ hfpCS
  have hE1o : fE < w1.heap.size := heap_frame hF1 (by simpa using hEo)
  have hE1k : (w1.objEntry fE).kind = .func dE := by rw [objEntry_frame0 hF1 (by simpa using hEo)]; simpa using hEk
  have hE2o : fE < w2.heap.size := heap_frame hF2 (by simp only [js_simp]; exact hE1o)
  have hE2k : (w2.objEntry fE).kind = .func dE := by
    rw [objEntry_frame hF2 (by simp only [js_simp]; exact hE1o)
      (by simp only [List.all_eq_true, bne_iff_ne, ne_eq] at hfpRO ⊢; intro q hq; exact fun h => by simpa [h] using hfpRO q hq)]
    simp only [js_simp]; exact hE1k
  have hE3o : fE < w3.heap.size := heap_frame hF3 (by simp only [js_simp]; exact hE2o)
  have hEk3 : (w3.objEntry fE).kind = .func dE := by
    rw [objEntry_frame hF3 (by simp only [js_simp]; exact hE2o) hfpCO]; simp only [js_simp]; exact hE2k
  have hE3a : s.envs.size < w3.envs.size + 1 := Nat.lt_succ_of_lt hE3s
  have hE3b : s.envs.size ≠ w3.envs.size := Nat.ne_of_lt hE3s
  have hG3a : d.env < w3.envs.size + 1 := Nat.lt_succ_of_lt hG3s
  have hG3b : d.env ≠ w3.envs.size := Nat.ne_of_lt hG3s
  js [hpn, hv, hl, ha, hG, hne, Ne.symm hne, hE3, hE3s, hG3s, hE3a, hE3b, hG3a, hG3b, Ne.symm hE3b, Ne.symm hG3b,
    hW3, hWE3, hWE, hGE, hGEv, hE3o, hEk3, FDI.fdiCtx, Sem.inner]
  -- (`ensureRootIsScheduled(root)`)
  refine ⟨by js_norm [CallableC, *], ?_⟩
  refine wp_mono ((ReactDSSI.Hold.get hEnsure) w3 _ h3 hPC ?fr4 ?fu4) ?post4
  case fr4 => simp only [fpOwn]; frame_go' [*, hne, Ne.symm hne]
  case fu4 => first | omega | (simp only [js_simp] at hfu3; omega)
  case post4 =>
  intro r w4 h4 ⟨hF4, hfu4, hQ⟩
  have hE4 := envEntry_frame hF4 (e := s.envs.size) (by first | exact hE3s | (simp only [js_simp]; exact hE3s) | (simp only [js_simp]; omega))
    (binds_avoid hfpEB (Nat.le_refl _))
  js [FDI.fdiCtx, Sem.inner, hQ, hE4]
  all_goals (try apply And.intro)
  all_goals (try apply And.intro)
  all_goals (try apply And.intro)
  all_goals first | rfl | exact hQ | omega | (simp only [js_simp] at *; omega) | skip
  frame_go' [*, hne, Ne.symm hne, hG1]

end

end ReactPerformWork
