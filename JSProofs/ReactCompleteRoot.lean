import JSProofs.ReactCompleteButton
import JSProofs.ReactRootPops

/-!
# completeWork for the root fiber (zippy docs/react-proofs.md)

`completeWork(current, workInProgress, lanes)` for the host root in the click's render: `popTreeContext`; tag 3:
the cache unchanged (no flag), `popProvider(CacheContext)` and `popHostContainer()` (what the root's `beginWork`
pushed: stack index 3 back to -1), no pending context, the current root has a child (no hydration step),
`bubbleProperties` over its one child, the new counter fiber (`bubble_one`); `null`.
-/

open ES ES.M HostRuns Logic
open Std (HashMap)

namespace ReactCompleteRoot

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ}

/-- What it writes: the stack (index, slots 3..0, the value and host-context cursors), the cache context's current
value, the root fiber's subtree flags and child lanes, the counter fiber's `return`. -/
def fpRC (g : EnvId) (VS Cu Cx CS CF RI R C : ObjId) : Footprint :=
  ⟨[(g, "index")], [(Cx, .str "_currentValue"), (VS, .str "3"), (Cu, .str "current"),
    (VS, .str "2"), (CS, .str "current"), (VS, .str "1"), (CF, .str "current"), (VS, .str "0"), (RI, .str "current"),
    (R, .str "subtreeFlags"), (R, .str "childLanes"), (C, .str "return")], false⟩

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
/-- **`completeWork(current, workInProgress, lanes)`** for the host root. -/
theorem root_spec {n : Nat} {h : σ} {fW : ObjId} {dW : FuncData} {tW : Value} {s : State}
    {bG : HashMap JSStr Binding} {g : EnvId} {H R FR MS0 MS1 CA C Y : ObjId} {ln pp rv cl : Value}
    {bdPT bdPP bdPHC bdBP bdTF bdTC bdCC bdI bdV bdVC bdCS bdCF bdRI bdO : Binding}
    {fPT fPP fPHC fBP fO : ObjId} {dPT dPP dPHC dBP dO : FuncData} {VS Cu Cx CS CF RI : ObjId}
    {L a b c e f : F64} {o0 o1 o2 o3 vu cxv vr vf vc : Value}
    {ppw ppe ppc tgw tge tgc snw sne snc m0w m0e m0c m1w m1e m1c caw cae cac cbw cbe cbc pcw pce pcc hcw hce hcc
      aw ae ac cw ce cc yw ye yc xlw xle xlc xcw xce xcc xsw xse xsc xfw xfe xfc rwe rwc sbw sbe sbc se sc le lc
      e0 c0 e1 c1 e2 c2 e3 c3 lw lle llc ue uc xe xc re rc fe fc vce vcc : Bool}
    {oG : Option EnvId}
    (hW : fW < s.heap.size) (hWk : (s.objEntry fW).kind = .func dW) (hf : 200 ≤ s.fuel)
    (hWcode : dW.code = CWGen.completeWork_func) (hWcls : dW.isClassCtor = false) (hWmode : dW.thisMode = .strict)
    (hWenv : dW.env = g)
    -- (react-dom's module record: the functions, the stack, the cursors, the cache context)
    (hG : g < s.envs.size) (hGe : Scope.declLike? (s.envEntry g) = some (bG, oG))
    (hGPT : bG[JSStr.ofString "popTreeContext"]? = some bdPT) (hGPTv : bdPT.value = some (.obj fPT))
    (hGPP : bG[JSStr.ofString "popProvider"]? = some bdPP) (hGPPv : bdPP.value = some (.obj fPP))
    (hGPHC : bG[JSStr.ofString "popHostContainer"]? = some bdPHC) (hGPHCv : bdPHC.value = some (.obj fPHC))
    (hGBP : bG[JSStr.ofString "bubbleProperties"]? = some bdBP) (hGBPv : bdBP.value = some (.obj fBP))
    (hGTF : bG[JSStr.ofString "treeForkProvider"]? = some bdTF) (hGTFv : bdTF.value = some .null)
    (hGTC : bG[JSStr.ofString "treeContextProvider"]? = some bdTC) (hGTCv : bdTC.value = some .null)
    (hGCC : bG[JSStr.ofString "CacheContext"]? = some bdCC) (hGCCv : bdCC.value = some (.obj Cx))
    (hGI : bG[JSStr.ofString "index"]? = some bdI) (hGIm : bdI.mutable = true)
    (hGIv : bdI.value = some (.num (F64.fin false 6755399441055744 (-51))))
    (hGV : bG[JSStr.ofString "valueStack"]? = some bdV) (hGVv : bdV.value = some (.obj VS))
    (hGVC : bG[JSStr.ofString "valueCursor"]? = some bdVC) (hGVCv : bdVC.value = some (.obj Cu))
    (hGCS : bG[JSStr.ofString "contextStackCursor"]? = some bdCS) (hGCSv : bdCS.value = some (.obj CS))
    (hGCF : bG[JSStr.ofString "contextFiberStackCursor"]? = some bdCF) (hGCFv : bdCF.value = some (.obj CF))
    (hGRI : bG[JSStr.ofString "rootInstanceStackCursor"]? = some bdRI) (hGRIv : bdRI.value = some (.obj RI))
    (hGO : bG[JSStr.ofString "pop"]? = some bdO) (hGOv : bdO.value = some (.obj fO))
    (hPT : fPT < s.heap.size) (hPTk : (s.objEntry fPT).kind = .func dPT)
    (hPTcode : dPT.code = PTCGen.popTreeContext_func) (hPTcls : dPT.isClassCtor = false)
    (hPTmode : dPT.thisMode = .strict) (hPTenv : dPT.env = g)
    (hPP : fPP < s.heap.size) (hPPk : (s.objEntry fPP).kind = .func dPP)
    (hPPcode : dPP.code = PopProvGen.popProvider_func) (hPPcls : dPP.isClassCtor = false)
    (hPPmode : dPP.thisMode = .strict) (hPPenv : dPP.env = g)
    (hPHC : fPHC < s.heap.size) (hPHCk : (s.objEntry fPHC).kind = .func dPHC)
    (hPHCcode : dPHC.code = PoHCGen.popHostContainer_func) (hPHCcls : dPHC.isClassCtor = false)
    (hPHCmode : dPHC.thisMode = .strict) (hPHCenv : dPHC.env = g)
    (hBP : fBP < s.heap.size) (hBPk : (s.objEntry fBP).kind = .func dBP)
    (hBPcode : dBP.code = BPGen.bubbleProperties_func) (hBPcls : dBP.isClassCtor = false)
    (hBPmode : dBP.thisMode = .strict)
    (hOo : fO < s.heap.size) (hOk : (s.objEntry fO).kind = .func dO) (hOcode : dO.code = PopGen.pop_func)
    (hOcls : dO.isClassCtor = false) (hOmode : dO.thisMode = .strict) (hOenv : dO.env = g)
    -- (the stack: four entries, the cache provider's on top of the host container's three)
    (hVS : VS < s.heap.size) (hVSk : (s.objEntry VS).kind = .array)
    (hV0 : (s.objEntry VS).props.get? (.str "0") = some (.data o0 true e0 c0))
    (hV1 : (s.objEntry VS).props.get? (.str "1") = some (.data o1 true e1 c1))
    (hV2 : (s.objEntry VS).props.get? (.str "2") = some (.data o2 true e2 c2))
    (hV3 : (s.objEntry VS).props.get? (.str "3") = some (.data o3 true e3 c3))
    (hVL : (s.objEntry VS).props.get? (.str "length") = some (.data (.num L) lw lle llc))
    (hL4 : 4 ≤ (Conv.toNat? L).getD 0)
    (hCu : Cu < s.heap.size) (hCuk : (s.objEntry Cu).kind.isPlain = true)
    (hCuc : (s.objEntry Cu).props.get? (.str "current") = some (.data vu true ue uc))
    (hCx : Cx < s.heap.size) (hCxk : (s.objEntry Cx).kind.isPlain = true)
    (hCxv : (s.objEntry Cx).props.get? (.str "_currentValue") = some (.data cxv true xe xc))
    (hRI : RI < s.heap.size) (hRIk : (s.objEntry RI).kind.isPlain = true)
    (hRIc : (s.objEntry RI).props.get? (.str "current") = some (.data vr true re rc))
    (hCF : CF < s.heap.size) (hCFk : (s.objEntry CF).kind.isPlain = true)
    (hCFc : (s.objEntry CF).props.get? (.str "current") = some (.data vf true fe fc))
    (hCS : CS < s.heap.size) (hCSk : (s.objEntry CS).kind.isPlain = true)
    (hCSc : (s.objEntry CS).props.get? (.str "current") = some (.data vc true vce vcc))
    (dS1 : VS ≠ Cu) (dS2 : VS ≠ Cx) (dS3 : Cu ≠ Cx) (dS4 : VS ≠ RI) (dS5 : VS ≠ CF) (dS6 : VS ≠ CS)
    (dS7 : RI ≠ CF) (dS8 : RI ≠ CS) (dS9 : CF ≠ CS)
    (dU1 : Cu ≠ CS) (dU2 : Cu ≠ CF) (dU3 : Cu ≠ RI) (dX1 : Cx ≠ CS) (dX2 : Cx ≠ CF) (dX3 : Cx ≠ RI)
    (dO1 : fO ≠ VS) (dO2 : fO ≠ Cu) (dO3 : fO ≠ Cx) (dO4 : fO ≠ RI) (dO5 : fO ≠ CF) (dO6 : fO ≠ CS)
    -- (the current root and the work in progress: the root (tag 3) of the fiber root `FR` (no pending context),
    -- the same cache, the current root's child the old counter fiber, the new root's the new counter fiber)
    (hH : H < s.heap.size) (hHk : (s.objEntry H).kind.isPlain = true)
    (hHms : (s.objEntry H).props.get? (.str "memoizedState") = some (.data (.obj MS0) m0w m0e m0c))
    (hHc : (s.objEntry H).props.get? (.str "child") = some (.data (.obj Y) hcw hce hcc))
    (hMS0 : MS0 < s.heap.size) (hMS0k : (s.objEntry MS0).kind.isPlain = true)
    (hMS0c : (s.objEntry MS0).props.get? (.str "cache") = some (.data (.obj CA) caw cae cac))
    (hR : R < s.heap.size) (hRk : (s.objEntry R).kind.isPlain = true)
    (hRpp : (s.objEntry R).props.get? (.str "pendingProps") = some (.data pp ppw ppe ppc))
    (hRtag : (s.objEntry R).props.get? (.str "tag") = some (.data (.num (F64.fin false 6755399441055744 (-51))) tgw tge tgc))
    (hRsn : (s.objEntry R).props.get? (.str "stateNode") = some (.data (.obj FR) snw sne snc))
    (hRms : (s.objEntry R).props.get? (.str "memoizedState") = some (.data (.obj MS1) m1w m1e m1c))
    (hMS1 : MS1 < s.heap.size) (hMS1k : (s.objEntry MS1).kind.isPlain = true)
    (hMS1c : (s.objEntry MS1).props.get? (.str "cache") = some (.data (.obj CA) cbw cbe cbc))
    (hFR : FR < s.heap.size) (hFRk : (s.objEntry FR).kind.isPlain = true)
    (hFRp : (s.objEntry FR).props.get? (.str "pendingContext") = some (.data .null pcw pce pcc))
    (hRa : (s.objEntry R).props.get? (.str "alternate") = some (.data (.obj H) aw ae ac))
    (hRc : (s.objEntry R).props.get? (.str "child") = some (.data (.obj C) cw ce cc))
    (hRs : (s.objEntry R).props.get? (.str "subtreeFlags") = some (.data (.num e) true se sc))
    (hRl : (s.objEntry R).props.get? (.str "childLanes") = some (.data cl true le lc))
    (hYC : Y ≠ C)
    (hC : C < s.heap.size) (hCk : (s.objEntry C).kind.isPlain = true) (hRC : R ≠ C)
    (hCl : (s.objEntry C).props.get? (.str "lanes") = some (.data (.num a) xlw xle xlc))
    (hCcl : (s.objEntry C).props.get? (.str "childLanes") = some (.data (.num b) xcw xce xcc))
    (hCs : (s.objEntry C).props.get? (.str "subtreeFlags") = some (.data (.num c) xsw xse xsc))
    (hCf : (s.objEntry C).props.get? (.str "flags") = some (.data (.num f) xfw xfe xfc))
    (hCr : (s.objEntry C).props.get? (.str "return") = some (.data rv true rwe rwc))
    (hCsb : (s.objEntry C).props.get? (.str "sibling") = some (.data .null sbw sbe sbc))
    (hdF : ∀ Y₁ ∈ [FR, H, R, C, fBP, fPHC, MS0, MS1], Y₁ ∉ [VS, Cu, Cx, CS, CF, RI]) :
    WP eng answer (n + 2) h (callImpl eng (.obj fW) tW #[.obj H, .obj R, ln]) s fun v w h' =>
      v = .null ∧ Frame (fpRC g VS Cu Cx CS CF RI R C) s w ∧ s.fuel ≤ w.fuel + 200 ∧ h' = h ∧ w.realm = s.realm ∧
      (w.objEntry R).props.get? (.str "subtreeFlags") = some (.data (.num (numberBinOp .bitOr e
        (numberBinOp .bitOr (numberBinOp .bitOr (F64.fin false 0 (-1074)) c) f))) true se sc) ∧
      (w.objEntry R).props.get? (.str "childLanes") = some (.data (.num (numberBinOp .bitOr (F64.fin false 0 (-1074))
        (numberBinOp .bitOr a b))) true le lc) ∧
      (w.objEntry C).props.get? (.str "return") = some (.data (.obj R) true rwe rwc) := by
  apply wp_callGen CWGen.completeWork_eq (by decide) hW hWk (by omega) hWcls hWmode
    (by rw [hWcode]; rfl) (by rw [hWcode]; rfl) (ReactCompleteButton.simpleW dW hWcode) (by rw [hWcode]; rfl)
    (by rw [hWcode]; rfl)
  have hpn : dW.code.info.fdi.paramNames = #[JSStr.ofString "current", JSStr.ofString "workInProgress",
      JSStr.ofString "renderLanes"] := by rw [hWcode]; rfl
  have hv : dW.code.info.fdi.varNames = #[JSStr.ofString "newProps", JSStr.ofString "type",
    JSStr.ofString "nextResource", JSStr.ofString "ownerDocument"] := by rw [hWcode]; rfl
  have hl : FDI.lexDecls dW = #[] := by simp [FDI.lexDecls, hWcode, CWGen.completeWork_func, Func.info]
  have ha : dW.code.isAsync = false := by rw [hWcode]; rfl
  have hne : s.envs.size ≠ g := Nat.ne_of_gt hG
  have hG1 : g < s.envs.size + 1 := Nat.lt_succ_of_lt hG
  clear hWcode
  simp only [CWGen.completeWork]
  js [hpn, hv, hl, ha, hWenv, hG, hG1, hne, Ne.symm hne, hGe, hR, hRk, hRpp, hGPT, hGPTv, hPT, hPTk, FDI.fdiCtx, Sem.inner]
  refine ⟨by js_norm [CallableC, hpn, hv, hl, ha, hWenv, hG, hG1, hne, Ne.symm hne, hGe, hR, hRk, hRpp, hGPT, hGPTv, hPT, hPTk, FDI.fdiCtx, Sem.inner], ?_⟩
  refine wp_mono (ReactCompleteHelpers.ptc_none (bG := bG) (oG := oG) (X := R) (by js_norm [hPT]) (by js_norm [hPTk])
    (by simp only [js_simp]; omega) hPTcode hPTcls hPTmode (by rw [hPTenv]; js_norm [hG1])
    (by rw [hPTenv]; js_norm [hG, hG1, hne, Ne.symm hne, hGe]) hGTF hGTFv hGTC hGTCv) ?_
  intro v1 w1 h1 ⟨hv1, hF1, hfu1, hh1, hr1⟩
  subst hv1 hh1
  have hw1K := envEntry_frame0 hF1 (e := s.envs.size) (by js_norm)
  have hw1G := envEntry_frame0 hF1 (e := g) (by js_norm [hG1])
  simp only [js_simp, ↓reduceIte, hG, hG1, hne, Ne.symm hne] at hw1K hw1G
  have hw1o : ∀ o, o < s.heap.size → w1.objEntry o = s.objEntry o := fun o ho =>
    (objEntry_frame0 hF1 (o := o) (by js_norm [ho])).trans (by js_norm)
  have hw1E : s.envs.size + 1 ≤ w1.envs.size := by have := hF1.envs_le; simp only [js_simp] at this; exact this
  have hw1z : s.heap.size ≤ w1.heap.size := by have := hF1.heap_le; simp only [js_simp] at this; exact this
  simp only [js_simp] at hfu1
  have hw1f : 175 ≤ w1.fuel := by omega
  have hK1 : s.envs.size < w1.envs.size := Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hw1E
  have hG1' : g < w1.envs.size := Nat.lt_of_lt_of_le hG1 hw1E
  have hnK1 : w1.envs.size ≠ s.envs.size := Nat.ne_of_gt hK1
  have hnG1 : w1.envs.size ≠ g := Nat.ne_of_gt hG1'
  have hK2 : s.envs.size < w1.envs.size + 1 := Nat.lt_succ_of_lt hK1
  have hG2 : g < w1.envs.size + 1 := Nat.lt_succ_of_lt hG1'
  have hcaq : isStrictlyEqual (.obj CA) (.obj CA) = true := by simp [isStrictlyEqual, sameValue]
  iterate 1 (first | js_go | js_norm [hw1K, hw1G, hw1o, hR, hRk, hRtag, hK1, hG1', hnK1, hnG1, Ne.symm hnK1, Ne.symm hnG1, hK2, hG2, Nat.lt_of_lt_of_le hR hw1z, hpn, hv, hl, ha, hGe, hne, Ne.symm hne, FDI.fdiCtx, Sem.inner] | js_split)
  refine wp_switchC CWSwitch.lex ?_
  js [hcaq, hw1K, hw1G, hw1o, hR, hRk, hRtag, hRsn, hRms, hH, hHk, hHms, hMS0, hMS0k, hMS0c, hMS1, hMS1k, hMS1c, hK1, hG1', hnK1, hnG1, Ne.symm hnK1, Ne.symm hnG1, hK2, hG2, Nat.lt_of_lt_of_le hR hw1z, Nat.lt_of_lt_of_le hH hw1z, Nat.lt_of_lt_of_le hMS0 hw1z, Nat.lt_of_lt_of_le hMS1 hw1z, Nat.lt_of_lt_of_le hPP hw1z, hPP, hPPk, hGPP, hGPPv, hGCC, hGCCv, hpn, hv, hl, ha, hGe, hne, Ne.symm hne, FDI.fdiCtx, Sem.inner]
  have n3 : numberToJSStr (F64.fin false 6755399441055744 (-51)) = JSStr.ofString "3" := by decide
  have s32 : Conv.subF (F64.fin false 6755399441055744 (-51)) F64.one = F64.fin false 4503599627370496 (-51) := by decide
  refine ⟨by js_norm [CallableC, hw1o fPP hPP, hw1o fO hOo, hw1o VS hVS, hw1o Cu hCu, hw1o Cx hCx, hw1o, hK1, hG1', hnK1, hnG1, Ne.symm hnK1, Ne.symm hnG1, hK2, hG2, hw1G, hGe, hne, Ne.symm hne, Nat.lt_of_lt_of_le hPP hw1z, hPP, hPPk], ?_⟩
  refine wp_mono (ReactRootPops.pop_provider (bG := bG) (oG := oG) (bdI := bdI) (bdV := bdV) (bdC := bdVC) (bdO := bdO)
    (VS := VS) (Cu := Cu) (Cx := Cx) (fO := fO) (dO := dO) (iv := F64.fin false 6755399441055744 (-51)) (L := L)
    (cur := vu) (saved := o3) (cv := cxv) (ce := ue) (cc := uc) (oe := e3) (oc := c3) (lw := lw) (le := lle) (lc := llc)
    (xe := xe) (xc := xc) (i := 3)
    (hlt := by js_norm [hw1o fPP hPP, hw1o fO hOo, hw1o VS hVS, hw1o Cu hCu, hw1o Cx hCx, hw1o, hK1, hG1', hnK1, hnG1, Ne.symm hnK1, Ne.symm hnG1, hK2, hG2, hw1G, hGe, hne, Ne.symm hne, Nat.lt_of_lt_of_le hPP hw1z]) (hk := by js_norm [hw1o fPP hPP, hw1o fO hOo, hw1o VS hVS, hw1o Cu hCu, hw1o Cx hCx, hw1o, hK1, hG1', hnK1, hnG1, Ne.symm hnK1, Ne.symm hnG1, hK2, hG2, hw1G, hGe, hne, Ne.symm hne, hPPk]) (hf := by simp only [js_simp]; omega)
    (hcode := hPPcode) (hcls := hPPcls) (hmode := hPPmode) (hG := by rw [hPPenv]; js_norm [hw1o fPP hPP, hw1o fO hOo, hw1o VS hVS, hw1o Cu hCu, hw1o Cx hCx, hw1o, hK1, hG1', hnK1, hnG1, Ne.symm hnK1, Ne.symm hnG1, hK2, hG2, hw1G, hGe, hne, Ne.symm hne])
    (hGe := by rw [hPPenv]; js_norm [hw1o fPP hPP, hw1o fO hOo, hw1o VS hVS, hw1o Cu hCu, hw1o Cx hCx, hw1o, hK1, hG1', hnK1, hnG1, Ne.symm hnK1, Ne.symm hnG1, hK2, hG2, hw1G, hGe, hne, Ne.symm hne]) (hGI := hGI) (hGIm := hGIm) (hGIv := hGIv) (hGV := hGV) (hGVv := hGVv)
    (hGC := hGVC) (hGCv := hGVCv) (hGO := hGO) (hGOv := hGOv) (hOo := by js_norm [hw1o fPP hPP, hw1o fO hOo, hw1o VS hVS, hw1o Cu hCu, hw1o Cx hCx, hw1o, hK1, hG1', hnK1, hnG1, Ne.symm hnK1, Ne.symm hnG1, hK2, hG2, hw1G, hGe, hne, Ne.symm hne, Nat.lt_of_lt_of_le hOo hw1z])
    (hOk := by js_norm [hw1o fPP hPP, hw1o fO hOo, hw1o VS hVS, hw1o Cu hCu, hw1o Cx hCx, hw1o, hK1, hG1', hnK1, hnG1, Ne.symm hnK1, Ne.symm hnG1, hK2, hG2, hw1G, hGe, hne, Ne.symm hne, hOk]) (hOcode := hOcode) (hOcls := hOcls) (hOmode := hOmode)
    (hOenv := by rw [hOenv, hPPenv]) (hVS := by js_norm [hw1o fPP hPP, hw1o fO hOo, hw1o VS hVS, hw1o Cu hCu, hw1o Cx hCx, hw1o, hK1, hG1', hnK1, hnG1, Ne.symm hnK1, Ne.symm hnG1, hK2, hG2, hw1G, hGe, hne, Ne.symm hne, Nat.lt_of_lt_of_le hVS hw1z]) (hVSk := by js_norm [hw1o fPP hPP, hw1o fO hOo, hw1o VS hVS, hw1o Cu hCu, hw1o Cx hCx, hw1o, hK1, hG1', hnK1, hnG1, Ne.symm hnK1, Ne.symm hnG1, hK2, hG2, hw1G, hGe, hne, Ne.symm hne, hVSk])
    (hCu := by js_norm [hw1o fPP hPP, hw1o fO hOo, hw1o VS hVS, hw1o Cu hCu, hw1o Cx hCx, hw1o, hK1, hG1', hnK1, hnG1, Ne.symm hnK1, Ne.symm hnG1, hK2, hG2, hw1G, hGe, hne, Ne.symm hne, Nat.lt_of_lt_of_le hCu hw1z]) (hCuk := by js_norm [hw1o fPP hPP, hw1o fO hOo, hw1o VS hVS, hw1o Cu hCu, hw1o Cx hCx, hw1o, hK1, hG1', hnK1, hnG1, Ne.symm hnK1, Ne.symm hnG1, hK2, hG2, hw1G, hGe, hne, Ne.symm hne, hCuk]) (hCx := by js_norm [hw1o fPP hPP, hw1o fO hOo, hw1o VS hVS, hw1o Cu hCu, hw1o Cx hCx, hw1o, hK1, hG1', hnK1, hnG1, Ne.symm hnK1, Ne.symm hnG1, hK2, hG2, hw1G, hGe, hne, Ne.symm hne, Nat.lt_of_lt_of_le hCx hw1z])
    (hCxk := by js_norm [hw1o fPP hPP, hw1o fO hOo, hw1o VS hVS, hw1o Cu hCu, hw1o Cx hCx, hw1o, hK1, hG1', hnK1, hnG1, Ne.symm hnK1, Ne.symm hnG1, hK2, hG2, hw1G, hGe, hne, Ne.symm hne, hCxk]) (d1 := dS1) (d2 := dS2) (d3 := dS3) (d4 := dO1) (d5 := dO2) (d6 := dO3)
    (hCc := by js_norm [hw1o fPP hPP, hw1o fO hOo, hw1o VS hVS, hw1o Cu hCu, hw1o Cx hCx, hw1o, hK1, hG1', hnK1, hnG1, Ne.symm hnK1, Ne.symm hnG1, hK2, hG2, hw1G, hGe, hne, Ne.symm hne, hCuc]) (hCxv := by js_norm [hw1o fPP hPP, hw1o fO hOo, hw1o VS hVS, hw1o Cu hCu, hw1o Cx hCx, hw1o, hK1, hG1', hnK1, hnG1, Ne.symm hnK1, Ne.symm hnG1, hK2, hG2, hw1G, hGe, hne, Ne.symm hne, hCxv]) (hslot := by rw [n3]; js_norm [hw1o fPP hPP, hw1o fO hOo, hw1o VS hVS, hw1o Cu hCu, hw1o Cx hCx, hw1o, hK1, hG1', hnK1, hnG1, Ne.symm hnK1, Ne.symm hnG1, hK2, hG2, hw1G, hGe, hne, Ne.symm hne, hV3])
    (hidx := by rw [n3]; js_norm) (hlen := by js_norm [hw1o fPP hPP, hw1o fO hOo, hw1o VS hVS, hw1o Cu hCu, hw1o Cx hCx, hw1o, hK1, hG1', hnK1, hnG1, Ne.symm hnK1, Ne.symm hnG1, hK2, hG2, hw1G, hGe, hne, Ne.symm hne, hVL]) (hiL := by omega) (hnl := by rw [n3]; decide)
    (hpos := by decide)) ?_
  intro v2 w2 h2 ⟨hv2, hF2, hfu2, hh2, hr2, hI2, hS2, hC2, hX2⟩
  subst hv2 hh2
  rw [hPPenv, n3] at hF2
  rw [hPPenv, s32] at hI2
  rw [n3] at hS2
  have fp2 : ∀ o k, (o, k) ∉ [(Cx, PropKey.str (JSStr.ofString "_currentValue")), (VS, PropKey.str (JSStr.ofString "3")),
      (Cu, PropKey.str (JSStr.ofString "current"))] → o < s.heap.size →
      (w2.objEntry o).props.get? k = (s.objEntry o).props.get? k := fun o k hk ho => by
    rw [props_frame hF2 (by js_norm [Nat.lt_of_lt_of_le ho hw1z]) (by simpa [ReactRootPops.fpPP] using hk)]
    js_norm [hw1o o ho]
  have kd2 : ∀ o, o < s.heap.size → (w2.objEntry o).kind = (s.objEntry o).kind := fun o ho => by
    rw [kind_frame hF2 (by js_norm [Nat.lt_of_lt_of_le ho hw1z])]; js_norm [hw1o o ho]
  have ob2 : ∀ o, o < s.heap.size → o ∉ [VS, Cu, Cx] → w2.objEntry o = s.objEntry o := fun o ho hn => by
    simp at hn
    rw [objEntry_frame hF2 (by js_norm [Nat.lt_of_lt_of_le ho hw1z]) (by simp [ReactRootPops.fpPP, hn, Ne.symm hn.1,
      Ne.symm hn.2.1, Ne.symm hn.2.2])]
    js_norm [hw1o o ho]
  have z2 : s.heap.size ≤ w2.heap.size := Nat.le_trans hw1z (by have := hF2.heap_le; simp only [js_simp] at this; exact this)
  have E2 : w1.envs.size + 1 ≤ w2.envs.size := by have := hF2.envs_le; simp only [js_simp] at this; exact this
  simp only [js_simp] at hfu2
  have fPHCn : fPHC ∉ [VS, Cu, Cx, CS, CF, RI] := hdF fPHC (by simp)
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at fPHCn
  have gK2 := envEntry_frame hF2 (e := s.envs.size) (by js_norm [hK2]) (by simp [ReactRootPops.fpPP, hne, Ne.symm hne])
  have gB2 := envEntry_frame hF2 (e := w1.envs.size) (by js_norm) (by simp [ReactRootPops.fpPP, hnG1, Ne.symm hnG1])
  simp only [js_simp, ↓reduceIte, hK1, hK2, hnK1, Ne.symm hnK1] at gK2 gB2
  js [gK2, gB2, hI2, ob2 fPHC hPHC (by simp [fPHCn.1, fPHCn.2.1, fPHCn.2.2.1]), hPHCk, Nat.lt_of_lt_of_le hPHC z2,
    ReactRootPops.other_modify, hGPHC, hGPHCv, Nat.lt_of_lt_of_le (Nat.lt_succ_self _) E2,
    Nat.lt_of_lt_of_le hK2 E2, Nat.lt_of_lt_of_le hG2 E2, Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) E2),
    Nat.ne_of_gt (Nat.lt_of_lt_of_le hK2 E2), Nat.ne_of_gt (Nat.lt_of_lt_of_le hG2 E2), hnK1, hnG1, Ne.symm hnK1,
    Ne.symm hnG1, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  have hO2 := ob2 fO hOo (by simp [dO1, dO2, dO3])
  refine ⟨by js_norm [CallableC, ob2 fPHC hPHC (by simp [fPHCn.1, fPHCn.2.1, fPHCn.2.2.1]), hPHCk, Nat.lt_of_lt_of_le hPHC z2], ?_⟩
  refine wp_mono (ReactRootPops.pop_host_container
    (bG := bG.modify (JSStr.ofString "index") (fun bd => { bd with value := some (.num (F64.fin false 4503599627370496 (-51))) })) (oG := oG)
    (bdI := { bdI with value := some (.num (F64.fin false 4503599627370496 (-51))) }) (bdV := bdV) (bdCS := bdCS) (bdCF := bdCF) (bdRI := bdRI)
    (bdO := bdO) (VS := VS) (CS := CS) (CF := CF) (RI := RI) (fO := fO) (dO := dO) (L := L) (o0 := o0) (o1 := o1)
    (o2 := o2) (vr := vr) (vf := vf) (vc := vc) (e0 := e0) (c0 := c0) (e1 := e1) (c1 := c1) (e2 := e2) (c2 := c2)
    (lw := lw) (le := lle) (lc := llc) (re := re) (rc := rc) (fe := fe) (fc := fc) (ce := vce) (cc := vcc)
    (hlt := Nat.lt_of_lt_of_le hPHC z2) (hk := by rw [ob2 fPHC hPHC (by simp [fPHCn.1, fPHCn.2.1, fPHCn.2.2.1])]; exact hPHCk)
    (hf := by omega) (hcode := hPHCcode) (hcls := hPHCcls) (hmode := hPHCmode)
    (hG := by rw [hPHCenv]; exact Nat.lt_of_lt_of_le hG2 E2) (hGe := by rw [hPHCenv]; exact hI2)
    (hGI := ReactRootPops.idx_modify hGI _) (hGIm := hGIm) (hGIv := rfl)
    (hGV := by rw [ReactRootPops.other_modify _ (by decide)]; exact hGV) (hGVv := hGVv)
    (hGCS := by rw [ReactRootPops.other_modify _ (by decide)]; exact hGCS) (hGCSv := hGCSv)
    (hGCF := by rw [ReactRootPops.other_modify _ (by decide)]; exact hGCF) (hGCFv := hGCFv)
    (hGRI := by rw [ReactRootPops.other_modify _ (by decide)]; exact hGRI) (hGRIv := hGRIv)
    (hGO := by rw [ReactRootPops.other_modify _ (by decide)]; exact hGO) (hGOv := hGOv)
    (hOo := Nat.lt_of_lt_of_le hOo z2) (hOk := by rw [hO2]; exact hOk) (hOcode := hOcode) (hOcls := hOcls)
    (hOmode := hOmode) (hOenv := by rw [hOenv, hPHCenv]) (hVS := Nat.lt_of_lt_of_le hVS z2)
    (hVSk := by rw [kd2 VS hVS]; exact hVSk)
    (hV0 := by rw [fp2 VS _ (by simp [dS1, dS2, dS3, dS4, dS5, dS6, dS7, dS8, dS9, dU1, dU2, dU3, dX1, dX2, dX3, Ne.symm dS1, Ne.symm dS2, Ne.symm dS3, Ne.symm dS4, Ne.symm dS5, Ne.symm dS6, Ne.symm dS7, Ne.symm dS8, Ne.symm dS9, Ne.symm dU1, Ne.symm dU2, Ne.symm dU3, Ne.symm dX1, Ne.symm dX2, Ne.symm dX3] <;> decide) hVS]; exact hV0)
    (hV1 := by rw [fp2 VS _ (by simp [dS1, dS2, dS3, dS4, dS5, dS6, dS7, dS8, dS9, dU1, dU2, dU3, dX1, dX2, dX3, Ne.symm dS1, Ne.symm dS2, Ne.symm dS3, Ne.symm dS4, Ne.symm dS5, Ne.symm dS6, Ne.symm dS7, Ne.symm dS8, Ne.symm dS9, Ne.symm dU1, Ne.symm dU2, Ne.symm dU3, Ne.symm dX1, Ne.symm dX2, Ne.symm dX3] <;> decide) hVS]; exact hV1)
    (hV2 := by rw [fp2 VS _ (by simp [dS1, dS2, dS3, dS4, dS5, dS6, dS7, dS8, dS9, dU1, dU2, dU3, dX1, dX2, dX3, Ne.symm dS1, Ne.symm dS2, Ne.symm dS3, Ne.symm dS4, Ne.symm dS5, Ne.symm dS6, Ne.symm dS7, Ne.symm dS8, Ne.symm dS9, Ne.symm dU1, Ne.symm dU2, Ne.symm dU3, Ne.symm dX1, Ne.symm dX2, Ne.symm dX3] <;> decide) hVS]; exact hV2)
    (hVL := by rw [fp2 VS _ (by simp [dS1, dS2, dS3, dS4, dS5, dS6, dS7, dS8, dS9, dU1, dU2, dU3, dX1, dX2, dX3, Ne.symm dS1, Ne.symm dS2, Ne.symm dS3, Ne.symm dS4, Ne.symm dS5, Ne.symm dS6, Ne.symm dS7, Ne.symm dS8, Ne.symm dS9, Ne.symm dU1, Ne.symm dU2, Ne.symm dU3, Ne.symm dX1, Ne.symm dX2, Ne.symm dX3] <;> decide) hVS]; exact hVL) (hL3 := by omega)
    (hRI := Nat.lt_of_lt_of_le hRI z2) (hRIk := by rw [kd2 RI hRI]; exact hRIk)
    (hRIc := by rw [fp2 RI _ (by simp [dS1, dS2, dS3, dS4, dS5, dS6, dS7, dS8, dS9, dU1, dU2, dU3, dX1, dX2, dX3, Ne.symm dS1, Ne.symm dS2, Ne.symm dS3, Ne.symm dS4, Ne.symm dS5, Ne.symm dS6, Ne.symm dS7, Ne.symm dS8, Ne.symm dS9, Ne.symm dU1, Ne.symm dU2, Ne.symm dU3, Ne.symm dX1, Ne.symm dX2, Ne.symm dX3]) hRI]; exact hRIc)
    (hCF := Nat.lt_of_lt_of_le hCF z2) (hCFk := by rw [kd2 CF hCF]; exact hCFk)
    (hCFc := by rw [fp2 CF _ (by simp [dS1, dS2, dS3, dS4, dS5, dS6, dS7, dS8, dS9, dU1, dU2, dU3, dX1, dX2, dX3, Ne.symm dS1, Ne.symm dS2, Ne.symm dS3, Ne.symm dS4, Ne.symm dS5, Ne.symm dS6, Ne.symm dS7, Ne.symm dS8, Ne.symm dS9, Ne.symm dU1, Ne.symm dU2, Ne.symm dU3, Ne.symm dX1, Ne.symm dX2, Ne.symm dX3]) hCF]; exact hCFc)
    (hCS := Nat.lt_of_lt_of_le hCS z2) (hCSk := by rw [kd2 CS hCS]; exact hCSk)
    (hCSc := by rw [fp2 CS _ (by simp [dS1, dS2, dS3, dS4, dS5, dS6, dS7, dS8, dS9, dU1, dU2, dU3, dX1, dX2, dX3, Ne.symm dS1, Ne.symm dS2, Ne.symm dS3, Ne.symm dS4, Ne.symm dS5, Ne.symm dS6, Ne.symm dS7, Ne.symm dS8, Ne.symm dS9, Ne.symm dU1, Ne.symm dU2, Ne.symm dU3, Ne.symm dX1, Ne.symm dX2, Ne.symm dX3]) hCS]; exact hCSc)
    (d1 := dS4) (d2 := dS5) (d3 := dS6) (d4 := dS7) (d5 := dS8) (d6 := dS9) (dO1 := dO1) (dO2 := dO4) (dO3 := dO5)
    (dO4 := dO6)) ?_
  intro v3 w3 h3 ⟨hv3, hF3, hfu3, hh3, hr3, hI3, hW0, hW1, hW2, hW3, hW4, hW5⟩
  subst hv3 hh3
  rw [hPHCenv] at hF3 hI3
  have z3 : s.heap.size ≤ w3.heap.size := Nat.le_trans z2 hF3.heap_le
  have E3 : w1.envs.size + 1 ≤ w3.envs.size := Nat.le_trans E2 hF3.envs_le
  have ob3 : ∀ o, o < s.heap.size → o ∉ [VS, Cu, Cx, CS, CF, RI] → w3.objEntry o = s.objEntry o := fun o ho hn => by
    have hn' := hn
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn'
    rw [objEntry_frame hF3 (Nat.lt_of_lt_of_le ho z2) (by simp [ReactRootPops.fpHC, hn'.1, hn'.2.1, hn'.2.2.1, hn'.2.2.2.1,
      hn'.2.2.2.2.1, hn'.2.2.2.2.2, Ne.symm hn'.1, Ne.symm hn'.2.2.2.1, Ne.symm hn'.2.2.2.2.1, Ne.symm hn'.2.2.2.2.2]),
      ob2 o ho (by simp [hn'.1, hn'.2.1, hn'.2.2.1])]
  have gK3 := (envEntry_frame hF3 (e := s.envs.size) (Nat.lt_of_lt_of_le hK2 E2) (by simp [ReactRootPops.fpHC, hne, Ne.symm hne])).trans gK2
  have gB3 := (envEntry_frame hF3 (e := w1.envs.size) (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) E2)
    (by simp [ReactRootPops.fpHC, hnG1, Ne.symm hnG1])).trans gB2
  obtain ⟨bm3, hbm3, -, hbm3o⟩ := hI3
  have hbBP : bm3[JSStr.ofString "bubbleProperties"]? = some bdBP := by
    rw [hbm3o _ (by decide), ReactRootPops.other_modify _ (by decide)]; exact hGBP
  have hFR3 := ob3 FR hFR (hdF FR (by simp))
  have hH3 := ob3 H hH (hdF H (by simp))
  have hR3 := ob3 R hR (hdF R (by simp))
  have hBP3 := ob3 fBP hBP (hdF fBP (by simp))
  js [gK3, gB3, hFR3, hH3, hR3, hBP3, hFR, hFRk, hFRp, hH, hHk, hHc, hR, hRk, hBP, hBPk, Nat.lt_of_lt_of_le hFR z3,
    Nat.lt_of_lt_of_le hH z3, Nat.lt_of_lt_of_le hR z3, Nat.lt_of_lt_of_le hBP z3, hbm3, hbBP, hGBPv, Nat.lt_of_lt_of_le (Nat.lt_succ_self _) E3, Nat.lt_of_lt_of_le hK2 E3, Nat.lt_of_lt_of_le hG2 E3,
    Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) E3), Nat.ne_of_gt (Nat.lt_of_lt_of_le hK2 E3),
    Nat.ne_of_gt (Nat.lt_of_lt_of_le hG2 E3), hnK1, hnG1, Ne.symm hnK1, Ne.symm hnG1, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  have hC3 := ob3 C hC (hdF C (by simp))
  refine ⟨by js_norm [CallableC, hBP3, hBPk, Nat.lt_of_lt_of_le hBP z3], ?_⟩
  refine wp_mono (ReactCompleteHelpers.bubble_one (C := R) (A := H) (X := C) (Y := Y) (a := a) (b := b) (c := c)
    (e := e) (f := f) (rv := rv) (cl := cl) (aw := aw) (ae := ae) (ac := ac) (cw := cw) (ce := ce) (cc := cc) (yw := hcw)
    (ye := hce) (yc := hcc) (xlw := xlw) (xle := xle) (xlc := xlc) (xcw := xcw) (xce := xce) (xcc := xcc) (xsw := xsw)
    (xse := xse) (xsc := xsc) (xfw := xfw) (xfe := xfe) (xfc := xfc) (rwe := rwe) (rwc := rwc) (sbw := sbw) (sbe := sbe)
    (sbc := sbc) (se := se) (sc := sc) (le := le) (lc := lc)
    (Nat.lt_of_lt_of_le hBP z3) (by rw [hBP3]; exact hBPk) (by omega) hBPcode hBPcls hBPmode
    (Nat.lt_of_lt_of_le hR z3) (by rw [hR3]; exact hRk) (by rw [hR3]; exact hRa) (by rw [hR3]; exact hRc)
    (by rw [hR3]; exact hRs) (by rw [hR3]; exact hRl) (Nat.lt_of_lt_of_le hH z3) (by rw [hH3]; exact hHk)
    (by rw [hH3]; exact hHc) hYC (Nat.lt_of_lt_of_le hC z3) (by rw [hC3]; exact hCk) hRC (by rw [hC3]; exact hCl)
    (by rw [hC3]; exact hCcl) (by rw [hC3]; exact hCs) (by rw [hC3]; exact hCf) (by rw [hC3]; exact hCr)
    (by rw [hC3]; exact hCsb)) ?_
  intro v4 w4 h4 ⟨hv4, hF4, hfu4, hh4, hr4, hRs4, hRl4, hCr4⟩
  subst hv4 hh4
  have gK4 := (envEntry_frame hF4 (e := s.envs.size) (Nat.lt_of_lt_of_le hK2 E3) (by simp)).trans gK3
  have gB4 := (envEntry_frame hF4 (e := w1.envs.size) (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) E3) (by simp)).trans gB3
  have E4 : w1.envs.size + 1 ≤ w4.envs.size := Nat.le_trans E3 hF4.envs_le
  (try simp only [js_simp] at hfu3); (try simp only [js_simp] at hfu4)
  js [gK4, gB4, Nat.lt_of_lt_of_le (Nat.lt_succ_self _) E4, Nat.lt_of_lt_of_le hK2 E4,
    Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) E4), Nat.ne_of_gt (Nat.lt_of_lt_of_le hK2 E4), hnK1,
    Ne.symm hnK1, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  have gB : Frame (fpRC g VS Cu Cx CS CF RI R C) s (bodyState s fW dW tW #[.obj H, .obj R, ln]) :=
    frame_mono (frame_bodyState (frame_refl ({} : Footprint) s) fW dW tW _) (by simp) (by simp) (fun _ => rfl)
  have FW1 := frame_extend' (frame_setEnv_new gB (Nat.le_refl _) _) hF1 (fun q hq _ => by simp at hq)
    (fun q hq _ => by simp at hq) (fun _ => rfl)
  have FW2 := frame_extend' (frame_setEnv_new (frame_pushEnv FW1 _) (Nat.le_refl _) _) hF2
    (fun q hq _ => by simp [ReactRootPops.fpPP] at hq; simp [fpRC, hq])
    (fun q hq _ => by simp [ReactRootPops.fpPP] at hq; rcases hq with hq | hq | hq <;> simp [fpRC, hq]) (fun _ => rfl)
  have FW3 := frame_extend' FW2 hF3 (fun q hq _ => by simp [ReactRootPops.fpHC] at hq; simp [fpRC, hq])
    (fun q hq _ => by simp [ReactRootPops.fpHC] at hq; rcases hq with hq | hq | hq | hq | hq | hq <;> simp [fpRC, hq])
    (fun _ => rfl)
  have FW4 := frame_extend' FW3 hF4 (fun q hq _ => by simp at hq)
    (fun q hq _ => by simp at hq; rcases hq with hq | hq | hq <;> simp [fpRC, hq]) (fun _ => rfl)
  all_goals (repeat' apply And.intro)
  all_goals first | rfl | omega | exact frame_restore FW4 s | assumption

end

end ReactCompleteRoot
