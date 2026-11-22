import JSProofs.ReactEnqueueHook
import JSProofs.ReactIRPUAuto
import JSProofs.ReactBSR
import JSProofs.DSSIGen

/-!
# React's `dispatchSetStateInternal` for a click (zippy docs/react-proofs.md)

`setN(v)` with a primitive `v` different from the current state, in the counter's steady state (both fibers' lanes
0, outside rendering): an update object is made; it is not a render-phase update (`isRenderPhaseUpdate`); the eager
state is computed with the queue's reducer (`basicStateReducer`: `v`) and differs from the current state
(`Object.is`); the update is queued and the root found (`enqueueConcurrentHookUpdate`); `scheduleUpdateOnFiber` and
`entangleTransitionUpdate` are called with the root (their specs are hypotheses here: each from any state framed from
the start, with an abstract footprint that leaves this function's record and the names it reads alone); `true` is
returned. Every callee's theorem is used at its call; the reads after each call go through that call's frame.
-/

open ES ES.M HostRuns Logic
open Std (HashMap)

namespace ReactDSSI

/-- A hypothesis kept out of `simp`'s way (the tactic passes every hypothesis to `simp`; callee specs are
`∀`-statements about `WP`s it would try at every call). -/
@[irreducible] def Hold (p : Prop) : Prop := p
theorem Hold.mk {p : Prop} (h : p) : Hold p := by unfold Hold; exact h
theorem Hold.get {p : Prop} (h : Hold p) : p := by unfold Hold at h; exact h

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ}

theorem simple (d : FuncData) (hc : d.code = DSSIGen.dispatchSetStateInternal_func) : FDI.Simple d := by
  constructor <;> rw [hc] <;> try rfl
  simp [DSSIGen.dispatchSetStateInternal_func, Func.params, Func.info]

/-- `basicStateReducer`'s theorem in the value/frame/fuel shape. -/
theorem bsr_frame {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t st a : Value} {s : State}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : 4 ≤ s.fuel)
    (hcode : d.code = BSRGen.basicStateReducer_func) (hcls : d.isClassCtor = false) (hmode : d.thisMode = .strict)
    (ha : ∀ o, a ≠ .obj o) :
    WP eng answer n h (callImpl eng (.obj fo) t #[st, a]) s fun v w _ =>
      v = a ∧ Frame {} s w ∧ s.fuel ≤ w.fuel + 1 := by
  refine wp_mono (ReactBSR.call_prim hlt hk hf hcode hcls hmode ha) fun v w _ ⟨hv, hw⟩ => ⟨hv, ?_, ?_⟩
  · rw [hw]; exact frame_restore (frame_bodyState (frame_refl {} s) _ _ _ _) _
  · rw [hw]; simp [State.restore]; omega

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
theorem call_spec {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t : Value} {s : State}
    {bG : HashMap JSStr Binding} {oG : Option EnvId} {F Q : ObjId} {p : F64} {a : Value}
    {bdRP bdC : Binding} {fI : ObjId} {dI : FuncData} {Alt : ObjId} {aw ae ac : Bool}
    {fe fc xe xc rw re rc sw se sc : Bool} {fB : ObjId} {dB : FuncData} {cur : F64}
    {bdO : Binding} {fO : ObjId} {bdOb : BuiltinData}
    {fH fEU fGR fS fT : ObjId} {dH dEU dGR : FuncData} {bdH bdA bdI bdL bdN bdEU bdGR bdS bdT : Binding}
    {A R Root : ObjId} {L c : F64} {lw le lc ow oe oc rw' re' rc' tw te tc nw ne nc : Bool} {v0 v1 v2 v3 : Value}
    {e0 e1 e2 e3 c0 c1 c2 c3 : Bool} {fpS : Footprint} {dS dT : FuncData} {P : State → σ → Prop} {Rs : State → σ → Prop}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : 200 ≤ s.fuel)
    (hcode : d.code = DSSIGen.dispatchSetStateInternal_func) (hcls : d.isClassCtor = false)
    (hmode : d.thisMode = .strict)
    (hG : d.env < s.envs.size) (hGe : Scope.declLike? (s.envEntry d.env) = some (bG, oG))
    (hGI : bG[JSStr.ofString "isRenderPhaseUpdate"]? = some bdRP) (hGIv : bdRP.value = some (.obj fI))
    (hI : fI < s.heap.size) (hIk : (s.objEntry fI).kind = .func dI)
    (hIcode : dI.code = IRPUGen.isRenderPhaseUpdate_func) (hIcls : dI.isClassCtor = false)
    (hImode : dI.thisMode = .strict) (hIenv : dI.env = d.env)
    (hGC : bG[JSStr.ofString "currentlyRenderingFiber"]? = some bdC) (hGCv : bdC.value = some .null)
    (hF : F < s.heap.size) (hFk : (s.objEntry F).kind.isPlain = true)
    (hFa : (s.objEntry F).props.get? (.str "alternate") = some (.data (.obj Alt) aw ae ac))
    -- (the steady state: both fibers' lanes 0; the queue's reducer and current state)
    (hFl : (s.objEntry F).props.get? (.str "lanes") = some (.data (.num (F64.fin false 0 (-1074))) true fe fc))
    (hX : Alt < s.heap.size) (hXk : (s.objEntry Alt).kind.isPlain = true)
    (hXl : (s.objEntry Alt).props.get? (.str "lanes") = some (.data (.num (F64.fin false 0 (-1074))) true xe xc))
    (hQ : Q < s.heap.size) (hQk : (s.objEntry Q).kind.isPlain = true)
    (hQr : (s.objEntry Q).props.get? (.str "lastRenderedReducer") = some (.data (.obj fB) rw re rc))
    (hQs : (s.objEntry Q).props.get? (.str "lastRenderedState") = some (.data (.num cur) sw se sc))
    (hB : fB < s.heap.size) (hBk : (s.objEntry fB).kind = .func dB)
    (hBcode : dB.code = BSRGen.basicStateReducer_func) (hBcls : dB.isClassCtor = false)
    (hBmode : dB.thisMode = .strict) (hA : ∀ o, a ≠ .obj o)
    -- (`objectIs` is the built-in `Object.is`; the new state differs from the current one)
    (hGO : bG[JSStr.ofString "objectIs"]? = some bdO) (hGOv : bdO.value = some (.obj fO))
    (hO : fO < s.heap.size) (hOk : (s.objEntry fO).kind = .builtin bdOb)
    (hOtab : eng.builtins[bdOb.id]? = some objectIs) (hneq : sameValue a (.num cur) = false)
    -- (`enqueueConcurrentHookUpdate` and what it reads: `ReactEnqueueHook.call_spec`'s premises)
    (hGH : bG[JSStr.ofString "enqueueConcurrentHookUpdate"]? = some bdH) (hGHv : bdH.value = some (.obj fH))
    (hH : fH < s.heap.size) (hHk : (s.objEntry fH).kind = .func dH)
    (hHcode : dH.code = ECHUGen.enqueueConcurrentHookUpdate_func) (hHcls : dH.isClassCtor = false)
    (hHmode : dH.thisMode = .strict) (hHenv : dH.env = d.env)
    (hGEU : bG[JSStr.ofString "enqueueUpdate$1"]? = some bdEU) (hGEUv : bdEU.value = some (.obj fEU))
    (hGGR : bG[JSStr.ofString "getRootForUpdatedFiber"]? = some bdGR) (hGGRv : bdGR.value = some (.obj fGR))
    (hEU : fEU < s.heap.size) (hEUk : (s.objEntry fEU).kind = .func dEU)
    (hEUcode : dEU.code = EUGen.fn0_func) (hEUcls : dEU.isClassCtor = false) (hEUmode : dEU.thisMode = .strict)
    (hEUenv : dEU.env = d.env)
    (hGA : bG[JSStr.ofString "concurrentQueues"]? = some bdA) (hGAv : bdA.value = some (.obj A))
    (hGQI : bG[JSStr.ofString "concurrentQueuesIndex"]? = some bdI)
    (hGQIv : bdI.value = some (.num (F64.fin false 0 (-1074)))) (hGQIm : bdI.mutable = true)
    (hGL : bG[JSStr.ofString "concurrentlyUpdatedLanes"]? = some bdL) (hGLv : bdL.value = some (.num c))
    (hGLm : bdL.mutable = true)
    (hA' : A < s.heap.size) (hAk : (s.objEntry A).kind = .array)
    (hA0 : (s.objEntry A).props.get? (.str "0") = some (.data v0 true e0 c0))
    (hA1 : (s.objEntry A).props.get? (.str "1") = some (.data v1 true e1 c1))
    (hA2 : (s.objEntry A).props.get? (.str "2") = some (.data v2 true e2 c2))
    (hA3 : (s.objEntry A).props.get? (.str "3") = some (.data v3 true e3 c3))
    (hAL : (s.objEntry A).props.get? (.str "length") = some (.data (.num L) lw le lc))
    (hL4 : 4 ≤ (Conv.toNat? L).getD 0) (hFA : F ≠ A) (hXA : Alt ≠ A) (hXF : Alt ≠ F)
    (hGRo : fGR < s.heap.size) (hGRk : (s.objEntry fGR).kind = .func dGR)
    (hGRcode : dGR.code = GRFGen.getRootForUpdatedFiber_func) (hGRcls : dGR.isClassCtor = false)
    (hGRmode : dGR.thisMode = .strict) (hGRenv : dGR.env = d.env) (hGRA : fGR ≠ A) (hGRF : fGR ≠ F)
    (hGRX : fGR ≠ Alt)
    (hGN : bG[JSStr.ofString "nestedUpdateCount"]? = some bdN)
    (hGNv : bdN.value = some (.num (F64.fin false 0 (-1074))))
    (hFr : (s.objEntry F).props.get? (.str "return") = some (.data (.obj R) ow oe oc))
    (hR : R < s.heap.size) (hRk : (s.objEntry R).kind.isPlain = true) (hRA : R ≠ A) (hRF : R ≠ F) (hRX : R ≠ Alt)
    (hRr : (s.objEntry R).props.get? (.str "return") = some (.data .null rw' re' rc'))
    (hRt : (s.objEntry R).props.get? (.str "tag") = some (.data (.num (F64.fin false 6755399441055744 (-51))) tw te tc))
    (hRs : (s.objEntry R).props.get? (.str "stateNode") = some (.data (.obj Root) nw ne nc))
    -- (`scheduleUpdateOnFiber` and `entangleTransitionUpdate`: hypotheses, from any state framed from the start;
    -- the first leaves this function's record and the module's `entangleTransitionUpdate` alone)
    (hGS : bG[JSStr.ofString "scheduleUpdateOnFiber"]? = some bdS) (hGSv : bdS.value = some (.obj fS))
    (hGT : bG[JSStr.ofString "entangleTransitionUpdate"]? = some bdT) (hGTv : bdT.value = some (.obj fT))
    (hSo : fS < s.heap.size) (hSk : (s.objEntry fS).kind = .func dS) (hTo : fT < s.heap.size)
    (hTk : (s.objEntry fT).kind = .func dT)
    (hSA : fS ≠ A) (hSF : fS ≠ F) (hSX : fS ≠ Alt) (hTA : fT ≠ A) (hTF : fT ≠ F) (hTX : fT ≠ Alt)
    (hSpec : ∀ w h1, Frame ⟨[(d.env, "concurrentQueuesIndex"), (d.env, "concurrentlyUpdatedLanes")],
        [(A, .str "0"), (A, .str "1"), (A, .str "2"), (A, .str "3"), (F, .str "lanes"), (Alt, .str "lanes")]⟩ s w →
      s.fuel ≤ w.fuel + 60 →
      WP eng answer (n + 2) h1 (callImpl eng (.obj fS) .undefined #[.obj Root, .obj F, .num p]) w fun _ w' h' =>
        Frame fpS w w' ∧ w.fuel ≤ w'.fuel + 30 ∧ P w' h')
    (hSfpE : fpS.binds.all (fun q => q.1 != s.envs.size) = true)
    (hSfpG : (d.env, JSStr.ofString "entangleTransitionUpdate") ∉ fpS.binds)
    (hSfpT : fpS.props.all (fun q => q.1 != fT) = true)
    (hTspec : ∀ w h1, P w h1 → 10 ≤ w.fuel →
      WP eng answer (n + 2) h1 (callImpl eng (.obj fT) .undefined #[.obj Root, .obj Q, .num p]) w fun _ w' h' =>
        Rs (w'.restore s) h') :
    WP eng answer (n + 3) h (callImpl eng (.obj fo) t #[.obj F, .obj Q, a, .num p]) s fun v w h' =>
      v = .bool true ∧ Rs w h' := by
  apply wp_callGen DSSIGen.dispatchSetStateInternal_eq (by decide) hlt hk (by omega) hcls hmode
    (by rw [hcode]; rfl) (by rw [hcode]; rfl) (simple d hcode) (by rw [hcode]; rfl) (by rw [hcode]; rfl)
  have hpn : d.code.info.fdi.paramNames = #[JSStr.ofString "fiber", JSStr.ofString "queue",
      JSStr.ofString "action", JSStr.ofString "lane"] := by rw [hcode]; rfl
  have hv : d.code.info.fdi.varNames = #[JSStr.ofString "update", JSStr.ofString "alternate",
      JSStr.ofString "currentState", JSStr.ofString "eagerState"] := by rw [hcode]; rfl
  have hl : FDI.lexDecls d = #[] := by simp [FDI.lexDecls, hcode, DSSIGen.dispatchSetStateInternal_func, Func.info]
  have ha : d.code.isAsync = false := by rw [hcode]; rfl
  have hne : s.envs.size ≠ d.env := Nat.ne_of_gt hG
  have hG1 : d.env < s.envs.size + 1 := Nat.lt_succ_of_lt hG
  clear hcode
  replace hSpec := Hold.mk hSpec
  replace hTspec := Hold.mk hTspec
  simp only [DSSIGen.dispatchSetStateInternal]
  have hIs : s.heap.size ≠ fI := Nat.ne_of_gt hI
  have hFs : s.heap.size ≠ F := Nat.ne_of_gt hF
  have hI1 : fI < s.heap.size + 1 := Nat.lt_succ_of_lt hI
  have hF1 : F < s.heap.size + 1 := Nat.lt_succ_of_lt hF
  have hXs : s.heap.size ≠ Alt := Nat.ne_of_gt hX
  have hX1 : Alt < s.heap.size + 1 := Nat.lt_succ_of_lt hX
  have hQs' : s.heap.size ≠ Q := Nat.ne_of_gt hQ
  have hQ1 : Q < s.heap.size + 1 := Nat.lt_succ_of_lt hQ
  have hBs : s.heap.size ≠ fB := Nat.ne_of_gt hB
  have hB1 : fB < s.heap.size + 1 := Nat.lt_succ_of_lt hB
  have hOs : s.heap.size ≠ fO := Nat.ne_of_gt hO
  have hO1 : fO < s.heap.size + 1 := Nat.lt_succ_of_lt hO
  have hfHs : s.heap.size ≠ fH := Nat.ne_of_gt (by assumption)
  have hfHs' := Ne.symm hfHs
  have hfH1 : fH < s.heap.size + 1 := Nat.lt_succ_of_lt (by assumption)
  have hfEUs : s.heap.size ≠ fEU := Nat.ne_of_gt (by assumption)
  have hfEUs' := Ne.symm hfEUs
  have hfEU1 : fEU < s.heap.size + 1 := Nat.lt_succ_of_lt (by assumption)
  have hfGRs : s.heap.size ≠ fGR := Nat.ne_of_gt (by assumption)
  have hfGRs' := Ne.symm hfGRs
  have hfGR1 : fGR < s.heap.size + 1 := Nat.lt_succ_of_lt (by assumption)
  have hAs : s.heap.size ≠ A := Nat.ne_of_gt (by assumption)
  have hAs' := Ne.symm hAs
  have hA1 : A < s.heap.size + 1 := Nat.lt_succ_of_lt (by assumption)
  have hRs : s.heap.size ≠ R := Nat.ne_of_gt (by assumption)
  have hRs' := Ne.symm hRs
  have hR1 : R < s.heap.size + 1 := Nat.lt_succ_of_lt (by assumption)
  have hfSs : s.heap.size ≠ fS := Nat.ne_of_gt (by assumption)
  have hfSs' := Ne.symm hfSs
  have hfS1 : fS < s.heap.size + 1 := Nat.lt_succ_of_lt (by assumption)
  have hfTs : s.heap.size ≠ fT := Nat.ne_of_gt (by assumption)
  have hfTs' := Ne.symm hfTs
  have hfT1 : fT < s.heap.size + 1 := Nat.lt_succ_of_lt (by assumption)
  have hne' := Ne.symm hne
  have hIs' := Ne.symm hIs
  have hFs'' := Ne.symm hFs
  have hXs' := Ne.symm hXs
  have hQs'' := Ne.symm hQs'
  have hBs' := Ne.symm hBs
  have hOs' := Ne.symm hOs
  js [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGI, hGIv, hI, hIk, hIs, Ne.symm hIs, hF, hFs, Ne.symm hFs,
    FDI.fdiCtx, Sem.inner]
  -- (`isRenderPhaseUpdate(fiber)`: false outside rendering)
  refine ⟨by js_norm [CallableC, hI, hI1, hIk, hIs, Ne.symm hIs], ?_⟩
  refine wp_mono (ReactIRPUAuto.call_spec (alt := .obj Alt) (cur := .null) (bG := bG) (oG := oG) (bdG := bdC)
    (wa := aw) (ea := ae) (ca := ac) ?_ ?_ ?_ hIcode hIcls hImode ?_ ?_ hGC hGCv
    ?_ ?_ ?_) ?_
  all_goals first
    | (js_norm [*, hIenv, hG, hG1, hne, Ne.symm hne, hGe, hI, hIk, hIs, Ne.symm hIs, hF, hFk, hFa, hFs, Ne.symm hFs, hI1, hF1]; done)
    | js_side
    | skip
  intro b w2 h2 ⟨hb, hFr2, hfu2⟩
  subst hb
  simp only [js_simp] at hfu2
  have hE2 : s.envs.size < w2.envs.size := envs_frame hFr2 (by simp)
  have hG2 : d.env < w2.envs.size := envs_frame hFr2 (by simp; omega)
  js [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hI, hIk, hIs, Ne.symm hIs, hF, hFs, Ne.symm hFs, hI1, hF1,
    envEntry_frame0 hFr2, objEntry_frame0 hFr2, envs_frame hFr2, heap_frame hFr2, hFl, hX, hXk, hXl, hXs, Ne.symm hXs,
    hX1, hQ, hQk, hQr, hQs, hQs', Ne.symm hQs', hQ1, hB, hBk, hBs, Ne.symm hBs, hB1, hFk, hFa, FDI.fdiCtx, Sem.inner]
  -- (`alternate(currentState, action)`: the reducer, `basicStateReducer`)
  refine ⟨by js_norm [CallableC, *, envEntry_frame0 hFr2, objEntry_frame0 hFr2, envs_frame hFr2, heap_frame hFr2, hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hI, hIk, hIs, Ne.symm hIs, hF, hFs, Ne.symm hFs, hI1, hF1,
    hFl, hX, hXk, hXl, hXs, Ne.symm hXs, hX1, hQ, hQk, hQr, hQs, hQs', Ne.symm hQs', hQ1, hB, hBk, hBs, Ne.symm hBs,
    hB1, hFk, hFa], ?_⟩
  refine wp_mono (bsr_frame (st := .num cur) (a := a) ?_ ?_ ?_ hBcode hBcls hBmode hA) ?post
  all_goals first
    | (js_norm [*, envEntry_frame0 hFr2, objEntry_frame0 hFr2, envs_frame hFr2, heap_frame hFr2, hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hI, hIk, hIs, Ne.symm hIs, hF, hFs, Ne.symm hFs, hI1, hF1,
    hFl, hX, hXk, hXl, hXs, Ne.symm hXs, hX1, hQ, hQk, hQr, hQs, hQs', Ne.symm hQs', hQ1, hB, hBk, hBs, Ne.symm hBs,
    hB1, hFk, hFa]; done)
    | js_side
    | skip
  case post =>
  intro b w3 h3 ⟨hb, hFr3, hfu3⟩
  subst hb
  simp only [js_simp] at hfu3
  have hE3 : s.envs.size < w3.envs.size := envs_frame hFr3 (by simpa using hE2)
  have hG3 : d.env < w3.envs.size := envs_frame hFr3 (by simpa using hG2)
  have hU2 : s.heap.size < w2.heap.size := heap_frame hFr2 (by simp)
  have hU2e := objEntry_frame0 hFr2 (o := s.heap.size) (by simp [js_simp])
  have hE2e := envEntry_frame0 hFr2 (e := s.envs.size) (by simp [js_simp])
  have hG2e := envEntry_frame0 hFr2 (e := d.env) (by simp [js_simp]; omega)
  have hF2e := objEntry_frame0 hFr2 (o := F) (by simpa using hF1)
  have hF2h : F < w2.heap.size := heap_frame hFr2 (by simpa using hF1)
  have hAlt2e := objEntry_frame0 hFr2 (o := Alt) (by simpa using hX1)
  have hAlt2h : Alt < w2.heap.size := heap_frame hFr2 (by simpa using hX1)
  have hQ2e := objEntry_frame0 hFr2 (o := Q) (by simpa using hQ1)
  have hQ2h : Q < w2.heap.size := heap_frame hFr2 (by simpa using hQ1)
  have hfB2e := objEntry_frame0 hFr2 (o := fB) (by simpa using hB1)
  have hfB2h : fB < w2.heap.size := heap_frame hFr2 (by simpa using hB1)
  have hfO2e := objEntry_frame0 hFr2 (o := fO) (by simpa using hO1)
  have hfO2h : fO < w2.heap.size := heap_frame hFr2 (by simpa using hO1)
  have hfI2e := objEntry_frame0 hFr2 (o := fI) (by simpa using hI1)
  have hfI2h : fI < w2.heap.size := heap_frame hFr2 (by simpa using hI1)
  have hfH2e := objEntry_frame0 hFr2 (o := fH) (by simpa using hfH1)
  have hfH2h : fH < w2.heap.size := heap_frame hFr2 (by simpa using hfH1)
  have hfEU2e := objEntry_frame0 hFr2 (o := fEU) (by simpa using hfEU1)
  have hfEU2h : fEU < w2.heap.size := heap_frame hFr2 (by simpa using hfEU1)
  have hfGR2e := objEntry_frame0 hFr2 (o := fGR) (by simpa using hfGR1)
  have hfGR2h : fGR < w2.heap.size := heap_frame hFr2 (by simpa using hfGR1)
  have hA2e := objEntry_frame0 hFr2 (o := A) (by simpa using hA1)
  have hA2h : A < w2.heap.size := heap_frame hFr2 (by simpa using hA1)
  have hR2e := objEntry_frame0 hFr2 (o := R) (by simpa using hR1)
  have hR2h : R < w2.heap.size := heap_frame hFr2 (by simpa using hR1)
  have hfS2e := objEntry_frame0 hFr2 (o := fS) (by simpa using hfS1)
  have hfS2h : fS < w2.heap.size := heap_frame hFr2 (by simpa using hfS1)
  have hfT2e := objEntry_frame0 hFr2 (o := fT) (by simpa using hfT1)
  have hfT2h : fT < w2.heap.size := heap_frame hFr2 (by simpa using hfT1)
  have hU3 : s.heap.size < w3.heap.size := heap_frame hFr3 (by simpa using hU2)
  have hU3e := objEntry_frame0 hFr3 (o := s.heap.size) (by simpa using hU2)
  have hE3e := envEntry_frame0 hFr3 (e := s.envs.size) (by simpa using hE2)
  have hG3e := envEntry_frame0 hFr3 (e := d.env) (by simpa using hG2)
  have hF3e := objEntry_frame0 hFr3 (o := F) (by simpa using hF2h)
  have hF3h : F < w3.heap.size := heap_frame hFr3 (by simpa using hF2h)
  have hAlt3e := objEntry_frame0 hFr3 (o := Alt) (by simpa using hAlt2h)
  have hAlt3h : Alt < w3.heap.size := heap_frame hFr3 (by simpa using hAlt2h)
  have hQ3e := objEntry_frame0 hFr3 (o := Q) (by simpa using hQ2h)
  have hQ3h : Q < w3.heap.size := heap_frame hFr3 (by simpa using hQ2h)
  have hfB3e := objEntry_frame0 hFr3 (o := fB) (by simpa using hfB2h)
  have hfB3h : fB < w3.heap.size := heap_frame hFr3 (by simpa using hfB2h)
  have hfO3e := objEntry_frame0 hFr3 (o := fO) (by simpa using hfO2h)
  have hfO3h : fO < w3.heap.size := heap_frame hFr3 (by simpa using hfO2h)
  have hfI3e := objEntry_frame0 hFr3 (o := fI) (by simpa using hfI2h)
  have hfI3h : fI < w3.heap.size := heap_frame hFr3 (by simpa using hfI2h)
  have hfH3e := objEntry_frame0 hFr3 (o := fH) (by simpa using hfH2h)
  have hfH3h : fH < w3.heap.size := heap_frame hFr3 (by simpa using hfH2h)
  have hfEU3e := objEntry_frame0 hFr3 (o := fEU) (by simpa using hfEU2h)
  have hfEU3h : fEU < w3.heap.size := heap_frame hFr3 (by simpa using hfEU2h)
  have hfGR3e := objEntry_frame0 hFr3 (o := fGR) (by simpa using hfGR2h)
  have hfGR3h : fGR < w3.heap.size := heap_frame hFr3 (by simpa using hfGR2h)
  have hA3e := objEntry_frame0 hFr3 (o := A) (by simpa using hA2h)
  have hA3h : A < w3.heap.size := heap_frame hFr3 (by simpa using hA2h)
  have hR3e := objEntry_frame0 hFr3 (o := R) (by simpa using hR2h)
  have hR3h : R < w3.heap.size := heap_frame hFr3 (by simpa using hR2h)
  have hfS3e := objEntry_frame0 hFr3 (o := fS) (by simpa using hfS2h)
  have hfS3h : fS < w3.heap.size := heap_frame hFr3 (by simpa using hfS2h)
  have hfT3e := objEntry_frame0 hFr3 (o := fT) (by simpa using hfT2h)
  have hfT3h : fT < w3.heap.size := heap_frame hFr3 (by simpa using hfT2h)
  js [*, hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hI, hIk, hIs, Ne.symm hIs, hF, hFs, Ne.symm hFs, hI1, hF1,
    hFl, hX, hXk, hXl, hXs, Ne.symm hXs, hX1, hQ, hQk, hQr, hQs, hQs', Ne.symm hQs', hQ1, hB, hBk, hBs, Ne.symm hBs,
    hB1, hFk, hFa,
    envEntry_frame0 hFr3, objEntry_frame0 hFr3, envs_frame hFr3, heap_frame hFr3, FDI.fdiCtx, Sem.inner]
  -- (`objectIs(eagerState, currentState)`: the built-in `Object.is`, false)
  refine ⟨by js_norm [CallableC, *], ?_⟩
  refine wp_mono (objectIs_spec ?_ ?_ hOtab ?_) ?post
  all_goals first
    | (js_norm [*]; done)
    | js_side
    | skip
  case post =>
  intro b w4 h4 ⟨hb, hFr4, hfu4⟩
  subst hb
  simp only [js_simp] at hfu4
  have hE4 : s.envs.size < w4.envs.size := envs_frame hFr4 (by simp [js_simp]; omega)
  have hG4 : d.env < w4.envs.size := envs_frame hFr4 (by simp [js_simp]; omega)
  have hU4 : s.heap.size < w4.heap.size := heap_frame hFr4 (by simp [js_simp]; omega)
  have hU4e := objEntry_frame0 hFr4 (o := s.heap.size) (by simp [js_simp]; omega)
  have hE4e := envEntry_frame0 hFr4 (e := s.envs.size) (by simp [js_simp]; omega)
  have hG4e := envEntry_frame0 hFr4 (e := d.env) (by simp [js_simp]; omega)
  have hF4e := objEntry_frame0 hFr4 (o := F) (by simpa using hF3h)
  have hF4h : F < w4.heap.size := heap_frame hFr4 (by simpa using hF3h)
  have hAlt4e := objEntry_frame0 hFr4 (o := Alt) (by simpa using hAlt3h)
  have hAlt4h : Alt < w4.heap.size := heap_frame hFr4 (by simpa using hAlt3h)
  have hQ4e := objEntry_frame0 hFr4 (o := Q) (by simpa using hQ3h)
  have hQ4h : Q < w4.heap.size := heap_frame hFr4 (by simpa using hQ3h)
  have hfB4e := objEntry_frame0 hFr4 (o := fB) (by simpa using hfB3h)
  have hfB4h : fB < w4.heap.size := heap_frame hFr4 (by simpa using hfB3h)
  have hfO4e := objEntry_frame0 hFr4 (o := fO) (by simpa using hfO3h)
  have hfO4h : fO < w4.heap.size := heap_frame hFr4 (by simpa using hfO3h)
  have hfI4e := objEntry_frame0 hFr4 (o := fI) (by simpa using hfI3h)
  have hfI4h : fI < w4.heap.size := heap_frame hFr4 (by simpa using hfI3h)
  have hfH4e := objEntry_frame0 hFr4 (o := fH) (by simpa using hfH3h)
  have hfH4h : fH < w4.heap.size := heap_frame hFr4 (by simpa using hfH3h)
  have hfEU4e := objEntry_frame0 hFr4 (o := fEU) (by simpa using hfEU3h)
  have hfEU4h : fEU < w4.heap.size := heap_frame hFr4 (by simpa using hfEU3h)
  have hfGR4e := objEntry_frame0 hFr4 (o := fGR) (by simpa using hfGR3h)
  have hfGR4h : fGR < w4.heap.size := heap_frame hFr4 (by simpa using hfGR3h)
  have hA4e := objEntry_frame0 hFr4 (o := A) (by simpa using hA3h)
  have hA4h : A < w4.heap.size := heap_frame hFr4 (by simpa using hA3h)
  have hR4e := objEntry_frame0 hFr4 (o := R) (by simpa using hR3h)
  have hR4h : R < w4.heap.size := heap_frame hFr4 (by simpa using hR3h)
  have hfS4e := objEntry_frame0 hFr4 (o := fS) (by simpa using hfS3h)
  have hfS4h : fS < w4.heap.size := heap_frame hFr4 (by simpa using hfS3h)
  have hfT4e := objEntry_frame0 hFr4 (o := fT) (by simpa using hfT3h)
  have hfT4h : fT < w4.heap.size := heap_frame hFr4 (by simpa using hfT3h)
  rw [hneq] at *
  js [*, FDI.fdiCtx, Sem.inner]
  -- (`enqueueConcurrentHookUpdate(fiber, queue, update, lane)`: its theorem)
  refine ⟨by js_norm [CallableC, *], ?_⟩
  refine wp_mono (ReactEnqueueHook.call_spec (d := dH) (fEU := fEU) (fGR := fGR) (dEU := dEU) (dGR := dGR) (A := A) (R := R)
    (Root := Root) (L := L) (c := c) (fl := F64.fin false 0 (-1074)) (al := F64.fin false 0 (-1074)) (Alt := Alt)
    (bG := bG) (oG := oG) (bdA := bdA) (bdI := bdI) (bdL := bdL)
    (bdN := bdN) (bdEU := bdEU) (bdGR := bdGR) (sw := ow) (se := oe) (sc := oc) (rw := rw') (re := re') (rc := rc')
    (tw := tw) (te := te) (tc := tc) (nw := nw) (ne := ne) (nc := nc) (aw := aw) (ae := ae) (ac := ac)
    (fe := fe) (fc := fc) (xe := xe) (xc := xc) (lw := lw) (le := le) (lc := lc) (v0 := v0) (v1 := v1) (v2 := v2)
    (v3 := v3) (e0 := e0) (e1 := e1) (e2 := e2) (e3 := e3) (c0 := c0) (c1 := c1) (c2 := c2) (c3 := c3)
    ?_ ?_ ?_ hHcode hHcls hHmode ?_ ?_ hGEU hGEUv hGGR hGGRv ?_ ?_ hEUcode hEUcls hEUmode (hEUenv.trans hHenv.symm) hGA hGAv hGQI hGQIv hGQIm hGL hGLv hGLm ?_ ?_ ?_ ?_ ?_ ?_ ?_ hL4 ?_ ?_ hFA ?_ ?_ ?_ ?_ hXA hXF ?_ ?_ ?_ hGRcode hGRcls hGRmode (hGRenv.trans hHenv.symm) hGRA hGRF hGRX hGN hGNv ?_ ?_ ?_ hRA hRF hRX ?_ ?_ ?_) ?post
  all_goals first
    | (js_norm [*]; done)
    | js_side
    | skip
  case post =>
  intro b w5 h5 ⟨hb, hFrH, hlanes5, hfu5⟩
  subst hb
  rw [hHenv] at hFrH
  -- (what `enqueueConcurrentHookUpdate` left: this function's record exactly; the module's lookups outside its
  -- footprint; the callees' function objects)
  have hE5 : s.envs.size < w5.envs.size := envs_frame hFrH (by simpa using hE4)
  have hE5e := envEntry_frame hFrH (e := s.envs.size) (by simpa using hE4) (by simp [hne'])
  obtain ⟨bW, hW, hWx⟩ := declLike_frame hFrH (e := d.env) (bs := bG) (o := oG) (by simpa using hG4) (by js_norm [*])
  have hG5 : d.env < w5.envs.size := envs_frame hFrH (by simpa using hG4)
  have hWS : bW[JSStr.ofString "scheduleUpdateOnFiber"]? = some bdS := by rw [hWx _ (by simp)]; exact hGS
  have hWT : bW[JSStr.ofString "entangleTransitionUpdate"]? = some bdT := by rw [hWx _ (by simp)]; exact hGT
  have hfS5e := objEntry_frame hFrH (o := fS) (by simpa using hfS4h) (by simp [hSA, hSF, hSX, Ne.symm hSA, Ne.symm hSF, Ne.symm hSX])
  have hfS5h : fS < w5.heap.size := heap_frame hFrH (by simpa using hfS4h)
  have hfT5e := objEntry_frame hFrH (o := fT) (by simpa using hfT4h) (by simp [hTA, hTF, hTX, Ne.symm hTA, Ne.symm hTF, Ne.symm hTX])
  have hfT5h : fT < w5.heap.size := heap_frame hFrH (by simpa using hfT4h)
  try simp only [js_simp] at hfu5
  js [*, FDI.fdiCtx, Sem.inner]
  -- (`scheduleUpdateOnFiber(root, fiber, lane)`: the hypothesis, from the state framed from the start)
  refine ⟨by js_norm [CallableC, *], ?_⟩
  refine wp_mono ((Hold.get hSpec) _ h5 ?fr ?fu) ?post2
  case fr =>
    frame_go' [*, hne, hne', hHenv]
  case fu => js_side
  case post2 =>
  intro b w7 h7 ⟨hFrS, hfuS, hP⟩
  -- (after `scheduleUpdateOnFiber`: this function's record, the module's `entangleTransitionUpdate`, its object)
  have hE7e := envEntry_frame hFrS (e := s.envs.size) (by simpa using hE5) hSfpE
  have hE7 : s.envs.size < w7.envs.size := envs_frame hFrS (by simpa using hE5)
  obtain ⟨bW7, hW7, hW7x⟩ := declLike_frame hFrS (e := d.env) (bs := bW) (o := oG) (by simpa using hG5)
    (by js_norm [*])
  have hG7 : d.env < w7.envs.size := envs_frame hFrS (by simpa using hG5)
  have hW7T : bW7[JSStr.ofString "entangleTransitionUpdate"]? = some bdT := by rw [hW7x _ hSfpG]; exact hWT
  have hfT7e := objEntry_frame hFrS (o := fT) (by simpa using hfT5h) hSfpT
  have hfT7h : fT < w7.heap.size := heap_frame hFrS (by simpa using hfT5h)
  try simp only [js_simp] at hfuS
  js [*, FDI.fdiCtx, Sem.inner]
  -- (`entangleTransitionUpdate(root, queue, lane)`: the hypothesis)
  refine ⟨by js_norm [CallableC, *], ?_⟩
  refine wp_mono ((Hold.get hTspec) _ h7 hP ?fu2) ?post3
  case fu2 => js_side
  case post3 =>
  intro b w8 h8 hRs
  js [*, FDI.fdiCtx, Sem.inner]
  all_goals first | rfl | decide

end

end ReactDSSI
