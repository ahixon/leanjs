import JSProofs.ReactCompleteHelpers
import JSProofs.CWSwitch
import JSProofs.FrameExt
import JSProofs.ReactBeginButton

/-!
# completeWork for the counter's button (zippy docs/react-proofs.md)

`completeWork(current, workInProgress, 2)` for the button's host-component fiber in the click's render:
`popTreeContext` (nothing), tag 5: `popHostContext` (nothing), the DOM element exists and the props are a new object,
so `markUpdate` (flags `|= 4`: the commit will update its properties, the text content among them);
`bubbleProperties` (a leaf: child lanes 0), the subtree flags `&= -33554433`, `preloadInstanceAndSuspendIfNeeded`
(flags `&= -16777217`); `null`.
-/

open ES ES.M HostRuns Logic
open Std (HashMap)

namespace ReactCompleteButton

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ}

/-- What it writes: the work in progress's flags, subtree flags and child lanes. -/
def fpCW (X : ObjId) : Footprint := ⟨[], [(X, .str "flags"), (X, .str "subtreeFlags"), (X, .str "childLanes")], false⟩

theorem simpleW (d : FuncData) (hc : d.code = CWGen.completeWork_func) : FDI.Simple d := by
  constructor <;> rw [hc] <;> try rfl
  simp [CWGen.completeWork_func, Func.params, Func.info]

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
/-- **`completeWork(current, workInProgress, lanes)`** for the button. -/
theorem button_spec {n : Nat} {h : σ} {fW : ObjId} {dW : FuncData} {tW : Value} {s : State}
    {bG : HashMap JSStr Binding} {g : EnvId} {H X P0 P1 D CF HT R : ObjId} {ln : Value}
    {bdPT bdPH bdMU bdBP bdPI bdTF bdTC bdCF bdHT : Binding}
    {fPT fPH fMU fBP fPI : ObjId} {dPT dPH dMU dBP dPI : FuncData} {fl sf m : F64} {cl : Value}
    {mpw mpe mpc ppw ppe ppc tgw tge tgc tyw tye tyc snw sne snc aw ae ac cw ce cc hcw hce hcc fe fc se sc le lc me mc
      cfw cfe cfc htw hte htc : Bool}
    (hW : fW < s.heap.size) (hWk : (s.objEntry fW).kind = .func dW) (hf : 120 ≤ s.fuel)
    (hWcode : dW.code = CWGen.completeWork_func) (hWcls : dW.isClassCtor = false) (hWmode : dW.thisMode = .strict)
    (hWenv : dW.env = g)
    -- (react-dom's module record)
    (hG : g < s.envs.size) (hGe : Scope.declLike? (s.envEntry g) = some (bG, none))
    (hGPT : bG[JSStr.ofString "popTreeContext"]? = some bdPT) (hGPTv : bdPT.value = some (.obj fPT))
    (hGPH : bG[JSStr.ofString "popHostContext"]? = some bdPH) (hGPHv : bdPH.value = some (.obj fPH))
    (hGMU : bG[JSStr.ofString "markUpdate"]? = some bdMU) (hGMUv : bdMU.value = some (.obj fMU))
    (hGBP : bG[JSStr.ofString "bubbleProperties"]? = some bdBP) (hGBPv : bdBP.value = some (.obj fBP))
    (hGPI : bG[JSStr.ofString "preloadInstanceAndSuspendIfNeeded"]? = some bdPI) (hGPIv : bdPI.value = some (.obj fPI))
    (hGTF : bG[JSStr.ofString "treeForkProvider"]? = some bdTF) (hGTFv : bdTF.value = some .null)
    (hGTC : bG[JSStr.ofString "treeContextProvider"]? = some bdTC) (hGTCv : bdTC.value = some .null)
    (hGCF : bG[JSStr.ofString "contextFiberStackCursor"]? = some bdCF) (hGCFv : bdCF.value = some (.obj CF))
    (hGHT : bG[JSStr.ofString "hostTransitionProviderCursor"]? = some bdHT) (hGHTv : bdHT.value = some (.obj HT))
    -- (the module's functions)
    (hPT : fPT < s.heap.size) (hPTk : (s.objEntry fPT).kind = .func dPT)
    (hPTcode : dPT.code = PTCGen.popTreeContext_func) (hPTcls : dPT.isClassCtor = false)
    (hPTmode : dPT.thisMode = .strict) (hPTenv : dPT.env = g)
    (hPH : fPH < s.heap.size) (hPHk : (s.objEntry fPH).kind = .func dPH)
    (hPHcode : dPH.code = PopHCGen.popHostContext_func) (hPHcls : dPH.isClassCtor = false)
    (hPHmode : dPH.thisMode = .strict) (hPHenv : dPH.env = g)
    (hMU : fMU < s.heap.size) (hMUk : (s.objEntry fMU).kind = .func dMU)
    (hMUcode : dMU.code = MUGen.markUpdate_func) (hMUcls : dMU.isClassCtor = false) (hMUmode : dMU.thisMode = .strict)
    (hBP : fBP < s.heap.size) (hBPk : (s.objEntry fBP).kind = .func dBP)
    (hBPcode : dBP.code = BPGen.bubbleProperties_func) (hBPcls : dBP.isClassCtor = false)
    (hBPmode : dBP.thisMode = .strict)
    (hPI : fPI < s.heap.size) (hPIk : (s.objEntry fPI).kind = .func dPI)
    (hPIcode : dPI.code = PISGen.preloadInstanceAndSuspendIfNeeded_func) (hPIcls : dPI.isClassCtor = false)
    (hPImode : dPI.thisMode = .strict)
    -- (the host context cursors: another fiber's context, no host transition provider)
    (hCF : CF < s.heap.size) (hCFk : (s.objEntry CF).kind.isPlain = true)
    (hCFc : (s.objEntry CF).props.get? (.str "current") = some (.data (.obj R) cfw cfe cfc)) (hRX : R ≠ X)
    (hHT : HT < s.heap.size) (hHTk : (s.objEntry HT).kind.isPlain = true)
    (hHTc : (s.objEntry HT).props.get? (.str "current") = some (.data .null htw hte htc))
    -- (the current button fiber: its old props, no child)
    (hH : H < s.heap.size) (hHk : (s.objEntry H).kind.isPlain = true)
    (hHmp : (s.objEntry H).props.get? (.str "memoizedProps") = some (.data (.obj P0) mpw mpe mpc))
    (hHc : (s.objEntry H).props.get? (.str "child") = some (.data .null hcw hce hcc))
    -- (the work in progress: a host component (tag 5) `button` with its DOM element, its new props, no child)
    (hX : X < s.heap.size) (hXk : (s.objEntry X).kind.isPlain = true) (hHX : H ≠ X)
    (hXpp : (s.objEntry X).props.get? (.str "pendingProps") = some (.data (.obj P1) ppw ppe ppc))
    (hXtag : (s.objEntry X).props.get? (.str "tag") = some (.data (.num (F64.fin false 5629499534213120 (-50))) tgw tge tgc))
    (hXty : (s.objEntry X).props.get? (.str "type") = some (.data (.str (JSStr.ofString "button")) tyw tye tyc))
    (hXsn : (s.objEntry X).props.get? (.str "stateNode") = some (.data (.obj D) snw sne snc))
    (hXa : (s.objEntry X).props.get? (.str "alternate") = some (.data (.obj H) aw ae ac))
    (hXc : (s.objEntry X).props.get? (.str "child") = some (.data .null cw ce cc))
    (hXf : (s.objEntry X).props.get? (.str "flags") = some (.data (.num fl) true fe fc))
    (hXs : (s.objEntry X).props.get? (.str "subtreeFlags") = some (.data (.num sf) true se sc))
    (hXl : (s.objEntry X).props.get? (.str "childLanes") = some (.data cl true le lc))
    (hXm : (s.objEntry X).props.get? (.str "mode") = some (.data (.num m) true me mc))
    (hm : numberBinOp .bitAnd m (F64.fin false 4503599627370496 (-47)) = F64.fin false 0 (-1074))
    (hP01 : P0 ≠ P1)
    (hdX : ∀ Y ∈ [fPT, fPH, fMU, fBP, fPI, CF, HT, fW], Y ≠ X) :
    WP eng answer (n + 1) h (callImpl eng (.obj fW) tW #[.obj H, .obj X, ln]) s fun v w h' =>
      v = .null ∧ Frame (fpCW X) s w ∧ s.fuel ≤ w.fuel + 120 ∧ h' = h ∧ w.realm = s.realm ∧
      (w.objEntry X).props.get? (.str "flags") = some (.data (.num (numberBinOp .bitAnd
        (numberBinOp .bitOr fl (F64.fin false 4503599627370496 (-50))) (F64.fin true 4503599895805952 (-28)))) true fe fc) ∧
      (w.objEntry X).props.get? (.str "subtreeFlags") = some (.data (.num (numberBinOp .bitAnd
        (numberBinOp .bitOr sf (F64.fin false 0 (-1074))) (F64.fin true 4503599761588224 (-27)))) true se sc) ∧
      (w.objEntry X).props.get? (.str "childLanes") = some (.data (.num (F64.fin false 0 (-1074))) true le lc) := by
  apply wp_callGen CWGen.completeWork_eq (by decide) hW hWk (by omega) hWcls hWmode
    (by rw [hWcode]; rfl) (by rw [hWcode]; rfl) (simpleW dW hWcode) (by rw [hWcode]; rfl) (by rw [hWcode]; rfl)
  have hpn : dW.code.info.fdi.paramNames = #[JSStr.ofString "current", JSStr.ofString "workInProgress",
      JSStr.ofString "renderLanes"] := by rw [hWcode]; rfl
  have hv : dW.code.info.fdi.varNames = #[JSStr.ofString "newProps", JSStr.ofString "type",
    JSStr.ofString "nextResource", JSStr.ofString "ownerDocument"] := by rw [hWcode]; rfl
  have hl : FDI.lexDecls dW = #[] := by simp [FDI.lexDecls, hWcode, CWGen.completeWork_func, Func.info]
  have ha : dW.code.isAsync = false := by rw [hWcode]; rfl
  have hne : s.envs.size ≠ g := Nat.ne_of_gt hG
  have hG1 : g < s.envs.size + 1 := Nat.lt_succ_of_lt hG
  have x1 := hdX fPT (by simp); have x2 := hdX fPH (by simp); have x3 := hdX fMU (by simp)
  have x4 := hdX fBP (by simp); have x5 := hdX fPI (by simp); have x6 := hdX CF (by simp)
  have x7 := hdX HT (by simp); have x8 := hdX fW (by simp)
  have hPs : isStrictlyEqual (.obj P0) (.obj P1) = false := by simp [isStrictlyEqual, sameValue, hP01]
  clear hWcode
  simp only [CWGen.completeWork]
  js [hpn, hv, hl, ha, hWenv, hG, hG1, hne, Ne.symm hne, hGe, hX, hXk, hXpp, hGPT, hGPTv, hPT, hPTk, FDI.fdiCtx, Sem.inner]
  refine ⟨by js_norm [CallableC, hpn, hv, hl, ha, hWenv, hG, hG1, hne, Ne.symm hne, hGe, hX, hXk, hXpp, hGPT, hGPTv, hPT, hPTk, FDI.fdiCtx, Sem.inner], ?_⟩
  refine wp_mono (ReactCompleteHelpers.ptc_none (bG := bG) (X := X) (by js_norm [hpn, hv, hl, ha, hWenv, hG, hG1, hne, Ne.symm hne, hGe, hX, hXk, hXpp, hGPT, hGPTv, hPT, hPTk, FDI.fdiCtx, Sem.inner]) (by js_norm [hpn, hv, hl, ha, hWenv, hG, hG1, hne, Ne.symm hne, hGe, hX, hXk, hXpp, hGPT, hGPTv, hPT, hPTk, FDI.fdiCtx, Sem.inner])
    (by simp only [js_simp]; omega) hPTcode hPTcls hPTmode (by rw [hPTenv]; js_norm [hpn, hv, hl, ha, hWenv, hG, hG1, hne, Ne.symm hne, hGe, hX, hXk, hXpp, hGPT, hGPTv, hPT, hPTk, FDI.fdiCtx, Sem.inner])
    (by rw [hPTenv]; js_norm [hpn, hv, hl, ha, hWenv, hG, hG1, hne, Ne.symm hne, hGe, hX, hXk, hXpp, hGPT, hGPTv, hPT, hPTk, FDI.fdiCtx, Sem.inner]) hGTF hGTFv hGTC hGTCv) ?_
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
  have hw1f : 95 ≤ w1.fuel := by omega
  have hK1 : s.envs.size < w1.envs.size := Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hw1E
  have hG1' : g < w1.envs.size := Nat.lt_of_lt_of_le hG1 hw1E
  have hnK1 : w1.envs.size ≠ s.envs.size := Nat.ne_of_gt hK1
  have hnG1 : w1.envs.size ≠ g := Nat.ne_of_gt hG1'
  have hK2 : s.envs.size < w1.envs.size + 1 := Nat.lt_succ_of_lt hK1
  have hG2 : g < w1.envs.size + 1 := Nat.lt_succ_of_lt hG1'
  iterate 1 (first | js_go | js_norm [hw1K, hw1G, hw1o, hX, hXk, hXtag, hK1, hG1', hnK1, hnG1, Ne.symm hnK1, Ne.symm hnG1, hK2, hG2, Nat.lt_of_lt_of_le hX hw1z, hpn, hv, hl, ha, hGe, hne, Ne.symm hne, FDI.fdiCtx, Sem.inner] | js_split)
  refine wp_switchC CWSwitch.lex ?_
  js [hw1K, hw1G, hw1o, hX, hXk, hXtag, hK1, hG1', hnK1, hnG1, Ne.symm hnK1, Ne.symm hnG1, hK2, hG2, Nat.lt_of_lt_of_le hX hw1z, hpn, hv, hl, ha, hGe, hne, Ne.symm hne, FDI.fdiCtx, Sem.inner, hXpp, hXty, hXsn, hH, hHk, hHmp, hP01, Ne.symm hP01, hHX, Ne.symm hHX, hGPH, hGPHv, hPH, hPHk, hPHenv]
  refine ⟨by js_norm [CallableC, hw1K, hw1G, hw1o, hX, hXk, hXtag, hK1, hG1', hnK1, hnG1, Ne.symm hnK1, Ne.symm hnG1, hK2, hG2, Nat.lt_of_lt_of_le hX hw1z, hpn, hv, hl, ha, hGe, hne, Ne.symm hne, FDI.fdiCtx, Sem.inner, hXpp, hXty, hXsn, hH, hHk, hHmp, hP01, Ne.symm hP01, hHX, Ne.symm hHX, hGPH, hGPHv, hPH, hPHk, hPHenv, hGCF, hGCFv, hGHT, hGHTv, hCF, hCFk, hCFc, hHT, hHTk, hHTc, Nat.lt_of_lt_of_le hCF hw1z, Nat.lt_of_lt_of_le hHT hw1z, Nat.lt_of_lt_of_le hPH hw1z], ?_⟩
  refine wp_mono (ReactCompleteHelpers.phc_none (bG := bG) (X := X) (R := R) (CF := CF) (HT := HT) (fw := cfw)
    (fe := cfe) (fc := cfc) (tw := htw) (te := hte) (tc := htc)
    (by js_norm [hw1K, hw1G, hw1o, hX, hXk, hXtag, hK1, hG1', hnK1, hnG1, Ne.symm hnK1, Ne.symm hnG1, hK2, hG2, Nat.lt_of_lt_of_le hX hw1z, hpn, hv, hl, ha, hGe, hne, Ne.symm hne, FDI.fdiCtx, Sem.inner, hXpp, hXty, hXsn, hH, hHk, hHmp, hP01, Ne.symm hP01, hHX, Ne.symm hHX, hGPH, hGPHv, hPH, hPHk, hPHenv, hGCF, hGCFv, hGHT, hGHTv, hCF, hCFk, hCFc, hHT, hHTk, hHTc, Nat.lt_of_lt_of_le hCF hw1z, Nat.lt_of_lt_of_le hHT hw1z, Nat.lt_of_lt_of_le hPH hw1z]) (by js_norm [hw1K, hw1G, hw1o, hX, hXk, hXtag, hK1, hG1', hnK1, hnG1, Ne.symm hnK1, Ne.symm hnG1, hK2, hG2, Nat.lt_of_lt_of_le hX hw1z, hpn, hv, hl, ha, hGe, hne, Ne.symm hne, FDI.fdiCtx, Sem.inner, hXpp, hXty, hXsn, hH, hHk, hHmp, hP01, Ne.symm hP01, hHX, Ne.symm hHX, hGPH, hGPHv, hPH, hPHk, hPHenv, hGCF, hGCFv, hGHT, hGHTv, hCF, hCFk, hCFc, hHT, hHTk, hHTc, Nat.lt_of_lt_of_le hCF hw1z, Nat.lt_of_lt_of_le hHT hw1z, Nat.lt_of_lt_of_le hPH hw1z]) (by simp only [js_simp]; omega) hPHcode hPHcls hPHmode
    (by rw [hPHenv]; js_norm [hw1K, hw1G, hw1o, hX, hXk, hXtag, hK1, hG1', hnK1, hnG1, Ne.symm hnK1, Ne.symm hnG1, hK2, hG2, Nat.lt_of_lt_of_le hX hw1z, hpn, hv, hl, ha, hGe, hne, Ne.symm hne, FDI.fdiCtx, Sem.inner, hXpp, hXty, hXsn, hH, hHk, hHmp, hP01, Ne.symm hP01, hHX, Ne.symm hHX, hGPH, hGPHv, hPH, hPHk, hPHenv, hGCF, hGCFv, hGHT, hGHTv, hCF, hCFk, hCFc, hHT, hHTk, hHTc, Nat.lt_of_lt_of_le hCF hw1z, Nat.lt_of_lt_of_le hHT hw1z, Nat.lt_of_lt_of_le hPH hw1z]) (by rw [hPHenv]; js_norm [hw1K, hw1G, hw1o, hX, hXk, hXtag, hK1, hG1', hnK1, hnG1, Ne.symm hnK1, Ne.symm hnG1, hK2, hG2, Nat.lt_of_lt_of_le hX hw1z, hpn, hv, hl, ha, hGe, hne, Ne.symm hne, FDI.fdiCtx, Sem.inner, hXpp, hXty, hXsn, hH, hHk, hHmp, hP01, Ne.symm hP01, hHX, Ne.symm hHX, hGPH, hGPHv, hPH, hPHk, hPHenv, hGCF, hGCFv, hGHT, hGHTv, hCF, hCFk, hCFc, hHT, hHTk, hHTc, Nat.lt_of_lt_of_le hCF hw1z, Nat.lt_of_lt_of_le hHT hw1z, Nat.lt_of_lt_of_le hPH hw1z]) hGCF hGCFv hGHT hGHTv
    (by js_norm [hw1K, hw1G, hw1o, hX, hXk, hXtag, hK1, hG1', hnK1, hnG1, Ne.symm hnK1, Ne.symm hnG1, hK2, hG2, Nat.lt_of_lt_of_le hX hw1z, hpn, hv, hl, ha, hGe, hne, Ne.symm hne, FDI.fdiCtx, Sem.inner, hXpp, hXty, hXsn, hH, hHk, hHmp, hP01, Ne.symm hP01, hHX, Ne.symm hHX, hGPH, hGPHv, hPH, hPHk, hPHenv, hGCF, hGCFv, hGHT, hGHTv, hCF, hCFk, hCFc, hHT, hHTk, hHTc, Nat.lt_of_lt_of_le hCF hw1z, Nat.lt_of_lt_of_le hHT hw1z, Nat.lt_of_lt_of_le hPH hw1z]) (by js_norm [hw1K, hw1G, hw1o, hX, hXk, hXtag, hK1, hG1', hnK1, hnG1, Ne.symm hnK1, Ne.symm hnG1, hK2, hG2, Nat.lt_of_lt_of_le hX hw1z, hpn, hv, hl, ha, hGe, hne, Ne.symm hne, FDI.fdiCtx, Sem.inner, hXpp, hXty, hXsn, hH, hHk, hHmp, hP01, Ne.symm hP01, hHX, Ne.symm hHX, hGPH, hGPHv, hPH, hPHk, hPHenv, hGCF, hGCFv, hGHT, hGHTv, hCF, hCFk, hCFc, hHT, hHTk, hHTc, Nat.lt_of_lt_of_le hCF hw1z, Nat.lt_of_lt_of_le hHT hw1z, Nat.lt_of_lt_of_le hPH hw1z]) (by js_norm [hw1K, hw1G, hw1o, hX, hXk, hXtag, hK1, hG1', hnK1, hnG1, Ne.symm hnK1, Ne.symm hnG1, hK2, hG2, Nat.lt_of_lt_of_le hX hw1z, hpn, hv, hl, ha, hGe, hne, Ne.symm hne, FDI.fdiCtx, Sem.inner, hXpp, hXty, hXsn, hH, hHk, hHmp, hP01, Ne.symm hP01, hHX, Ne.symm hHX, hGPH, hGPHv, hPH, hPHk, hPHenv, hGCF, hGCFv, hGHT, hGHTv, hCF, hCFk, hCFc, hHT, hHTk, hHTc, Nat.lt_of_lt_of_le hCF hw1z, Nat.lt_of_lt_of_le hHT hw1z, Nat.lt_of_lt_of_le hPH hw1z]) hRX (by js_norm [hw1K, hw1G, hw1o, hX, hXk, hXtag, hK1, hG1', hnK1, hnG1, Ne.symm hnK1, Ne.symm hnG1, hK2, hG2, Nat.lt_of_lt_of_le hX hw1z, hpn, hv, hl, ha, hGe, hne, Ne.symm hne, FDI.fdiCtx, Sem.inner, hXpp, hXty, hXsn, hH, hHk, hHmp, hP01, Ne.symm hP01, hHX, Ne.symm hHX, hGPH, hGPHv, hPH, hPHk, hPHenv, hGCF, hGCFv, hGHT, hGHTv, hCF, hCFk, hCFc, hHT, hHTk, hHTc, Nat.lt_of_lt_of_le hCF hw1z, Nat.lt_of_lt_of_le hHT hw1z, Nat.lt_of_lt_of_le hPH hw1z]) (by js_norm [hw1K, hw1G, hw1o, hX, hXk, hXtag, hK1, hG1', hnK1, hnG1, Ne.symm hnK1, Ne.symm hnG1, hK2, hG2, Nat.lt_of_lt_of_le hX hw1z, hpn, hv, hl, ha, hGe, hne, Ne.symm hne, FDI.fdiCtx, Sem.inner, hXpp, hXty, hXsn, hH, hHk, hHmp, hP01, Ne.symm hP01, hHX, Ne.symm hHX, hGPH, hGPHv, hPH, hPHk, hPHenv, hGCF, hGCFv, hGHT, hGHTv, hCF, hCFk, hCFc, hHT, hHTk, hHTc, Nat.lt_of_lt_of_le hCF hw1z, Nat.lt_of_lt_of_le hHT hw1z, Nat.lt_of_lt_of_le hPH hw1z])
    (by js_norm [hw1K, hw1G, hw1o, hX, hXk, hXtag, hK1, hG1', hnK1, hnG1, Ne.symm hnK1, Ne.symm hnG1, hK2, hG2, Nat.lt_of_lt_of_le hX hw1z, hpn, hv, hl, ha, hGe, hne, Ne.symm hne, FDI.fdiCtx, Sem.inner, hXpp, hXty, hXsn, hH, hHk, hHmp, hP01, Ne.symm hP01, hHX, Ne.symm hHX, hGPH, hGPHv, hPH, hPHk, hPHenv, hGCF, hGCFv, hGHT, hGHTv, hCF, hCFk, hCFc, hHT, hHTk, hHTc, Nat.lt_of_lt_of_le hCF hw1z, Nat.lt_of_lt_of_le hHT hw1z, Nat.lt_of_lt_of_le hPH hw1z])) ?_
  intro v2 w2 h2 ⟨hv2, hF2, hfu2, hh2, hr2⟩
  subst hv2 hh2
  have hw2K := envEntry_frame0 hF2 (e := s.envs.size) (by js_norm [hK2])
  have hw2B := envEntry_frame0 hF2 (e := w1.envs.size) (by js_norm)
  have hw2G := envEntry_frame0 hF2 (e := g) (by js_norm [hG2])
  simp only [js_simp, ↓reduceIte, hK1, hG1', hnK1, hnG1, Ne.symm hnK1, Ne.symm hnG1] at hw2K hw2G hw2B
  rw [hw1K] at hw2K
  rw [hw1G] at hw2G
  have hw2o : ∀ o, o < s.heap.size → w2.objEntry o = s.objEntry o := fun o ho =>
    ((objEntry_frame0 hF2 (o := o) (by js_norm [Nat.lt_of_lt_of_le ho hw1z])).trans (by js_norm)).trans (hw1o o ho)
  have hw2E : w1.envs.size + 1 ≤ w2.envs.size := by have := hF2.envs_le; simp only [js_simp] at this; exact this
  have hw2z : s.heap.size ≤ w2.heap.size := by
    have := hF2.heap_le; simp only [js_simp] at this; exact Nat.le_trans hw1z this
  simp only [js_simp] at hfu2
  have hw2f : 70 ≤ w2.fuel := by omega
  have hK3 : s.envs.size < w2.envs.size := Nat.lt_of_lt_of_le hK2 hw2E
  have hB3 : w1.envs.size < w2.envs.size := Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hw2E
  have hG3 : g < w2.envs.size := Nat.lt_of_lt_of_le hG2 hw2E
  have hBK : w1.envs.size ≠ s.envs.size := hnK1
  have hBG : w1.envs.size ≠ g := hnG1
  js [hPs, hw2K, hw2B, hw2G, hw2o, hK3, hB3, hG3, Nat.ne_of_gt hK3, Nat.ne_of_gt hB3, Nat.ne_of_gt hG3, Ne.symm (Nat.ne_of_gt hK3), Ne.symm (Nat.ne_of_gt hB3), Ne.symm (Nat.ne_of_gt hG3), hBK, hBG, Ne.symm hBK, Ne.symm hBG, Nat.lt_of_lt_of_le hX hw2z, Nat.lt_of_lt_of_le hH hw2z, Nat.lt_of_lt_of_le hMU hw2z, hX, hXk, hXty, hXsn, hXpp, hH, hHk, hHmp, hMU, hMUk, hGMU, hGMUv, hGe, hne, Ne.symm hne, hpn, hv, hl, ha, hWenv, FDI.fdiCtx, Sem.inner]
  refine wp_neNullObj (by simp only [js_simp]; omega) ?_
  js [hPs, hw2K, hw2B, hw2G, hw2o, hK3, hB3, hG3, Nat.ne_of_gt hK3, Nat.ne_of_gt hB3, Nat.ne_of_gt hG3, Ne.symm (Nat.ne_of_gt hK3), Ne.symm (Nat.ne_of_gt hB3), Ne.symm (Nat.ne_of_gt hG3), hBK, hBG, Ne.symm hBK, Ne.symm hBG, Nat.lt_of_lt_of_le hX hw2z, Nat.lt_of_lt_of_le hH hw2z, Nat.lt_of_lt_of_le hMU hw2z, hX, hXk, hXty, hXsn, hXpp, hH, hHk, hHmp, hMU, hMUk, hGMU, hGMUv, hGe, hne, Ne.symm hne, hpn, hv, hl, ha, hWenv, FDI.fdiCtx, Sem.inner]
  refine ⟨by js_norm [CallableC, hPs, hw2K, hw2B, hw2G, hw2o, hK3, hB3, hG3, Nat.ne_of_gt hK3, Nat.ne_of_gt hB3, Nat.ne_of_gt hG3, Ne.symm (Nat.ne_of_gt hK3), Ne.symm (Nat.ne_of_gt hB3), Ne.symm (Nat.ne_of_gt hG3), hBK, hBG, Ne.symm hBK, Ne.symm hBG, Nat.lt_of_lt_of_le hX hw2z, Nat.lt_of_lt_of_le hH hw2z, Nat.lt_of_lt_of_le hMU hw2z, hX, hXk, hXty, hXsn, hXpp, hH, hHk, hHmp, hMU, hMUk, hGMU, hGMUv, hGe, hne, Ne.symm hne, hpn, hv, hl, ha, hWenv, FDI.fdiCtx, Sem.inner, hXf, hMU, hMUk], ?_⟩
  refine wp_mono (ReactCompleteHelpers.mark_update (X := X) (fl := fl) (fe := fe) (fc := fc)
    (by js_norm [hPs, hw2K, hw2B, hw2G, hw2o, hK3, hB3, hG3, Nat.ne_of_gt hK3, Nat.ne_of_gt hB3, Nat.ne_of_gt hG3, Ne.symm (Nat.ne_of_gt hK3), Ne.symm (Nat.ne_of_gt hB3), Ne.symm (Nat.ne_of_gt hG3), hBK, hBG, Ne.symm hBK, Ne.symm hBG, Nat.lt_of_lt_of_le hX hw2z, Nat.lt_of_lt_of_le hH hw2z, Nat.lt_of_lt_of_le hMU hw2z, hX, hXk, hXty, hXsn, hXpp, hH, hHk, hHmp, hMU, hMUk, hGMU, hGMUv, hGe, hne, Ne.symm hne, hpn, hv, hl, ha, hWenv, FDI.fdiCtx, Sem.inner, hXf, hMU, hMUk]) (by js_norm [hPs, hw2K, hw2B, hw2G, hw2o, hK3, hB3, hG3, Nat.ne_of_gt hK3, Nat.ne_of_gt hB3, Nat.ne_of_gt hG3, Ne.symm (Nat.ne_of_gt hK3), Ne.symm (Nat.ne_of_gt hB3), Ne.symm (Nat.ne_of_gt hG3), hBK, hBG, Ne.symm hBK, Ne.symm hBG, Nat.lt_of_lt_of_le hX hw2z, Nat.lt_of_lt_of_le hH hw2z, Nat.lt_of_lt_of_le hMU hw2z, hX, hXk, hXty, hXsn, hXpp, hH, hHk, hHmp, hMU, hMUk, hGMU, hGMUv, hGe, hne, Ne.symm hne, hpn, hv, hl, ha, hWenv, FDI.fdiCtx, Sem.inner, hXf, hMU, hMUk]) (by simp only [js_simp]; omega) hMUcode hMUcls hMUmode
    (by js_norm [hPs, hw2K, hw2B, hw2G, hw2o, hK3, hB3, hG3, Nat.ne_of_gt hK3, Nat.ne_of_gt hB3, Nat.ne_of_gt hG3, Ne.symm (Nat.ne_of_gt hK3), Ne.symm (Nat.ne_of_gt hB3), Ne.symm (Nat.ne_of_gt hG3), hBK, hBG, Ne.symm hBK, Ne.symm hBG, Nat.lt_of_lt_of_le hX hw2z, Nat.lt_of_lt_of_le hH hw2z, Nat.lt_of_lt_of_le hMU hw2z, hX, hXk, hXty, hXsn, hXpp, hH, hHk, hHmp, hMU, hMUk, hGMU, hGMUv, hGe, hne, Ne.symm hne, hpn, hv, hl, ha, hWenv, FDI.fdiCtx, Sem.inner, hXf, hMU, hMUk]) (by js_norm [hPs, hw2K, hw2B, hw2G, hw2o, hK3, hB3, hG3, Nat.ne_of_gt hK3, Nat.ne_of_gt hB3, Nat.ne_of_gt hG3, Ne.symm (Nat.ne_of_gt hK3), Ne.symm (Nat.ne_of_gt hB3), Ne.symm (Nat.ne_of_gt hG3), hBK, hBG, Ne.symm hBK, Ne.symm hBG, Nat.lt_of_lt_of_le hX hw2z, Nat.lt_of_lt_of_le hH hw2z, Nat.lt_of_lt_of_le hMU hw2z, hX, hXk, hXty, hXsn, hXpp, hH, hHk, hHmp, hMU, hMUk, hGMU, hGMUv, hGe, hne, Ne.symm hne, hpn, hv, hl, ha, hWenv, FDI.fdiCtx, Sem.inner, hXf, hMU, hMUk]) (by js_norm [hPs, hw2K, hw2B, hw2G, hw2o, hK3, hB3, hG3, Nat.ne_of_gt hK3, Nat.ne_of_gt hB3, Nat.ne_of_gt hG3, Ne.symm (Nat.ne_of_gt hK3), Ne.symm (Nat.ne_of_gt hB3), Ne.symm (Nat.ne_of_gt hG3), hBK, hBG, Ne.symm hBK, Ne.symm hBG, Nat.lt_of_lt_of_le hX hw2z, Nat.lt_of_lt_of_le hH hw2z, Nat.lt_of_lt_of_le hMU hw2z, hX, hXk, hXty, hXsn, hXpp, hH, hHk, hHmp, hMU, hMUk, hGMU, hGMUv, hGe, hne, Ne.symm hne, hpn, hv, hl, ha, hWenv, FDI.fdiCtx, Sem.inner, hXf, hMU, hMUk])) ?_
  intro v3 w3 h3 ⟨hv3, hF3, hfu3, hh3, hr3, hXf3⟩
  subst hv3 hh3
  have hz2 : s.heap.size ≤ w2.heap.size := hw2z
  have hw3K : w3.envEntry s.envs.size = _ := envEntry_frame hF3 (by js_norm [hK3]) (by simp)
  have hw3B : w3.envEntry w1.envs.size = _ := envEntry_frame hF3 (by js_norm [hB3]) (by simp)
  have hw3G : w3.envEntry g = _ := envEntry_frame hF3 (by js_norm [hG3]) (by simp)
  simp only [js_simp, ↓reduceIte, hK3, hB3, hG3, Nat.ne_of_gt hK3, Nat.ne_of_gt hB3, Nat.ne_of_gt hG3, hBK, hBG, Ne.symm hBK,
    Ne.symm hBG, hw2B, hw2G] at hw3K hw3B hw3G
  have hO3 : ∀ o, o < s.heap.size → o ≠ X → w3.objEntry o = s.objEntry o := fun o ho hoX => by
    rw [objEntry_frame hF3 (by js_norm [Nat.lt_of_lt_of_le ho hz2]) (by simp [Ne.symm hoX, hoX])]
    js_norm [hw2o o ho]
  have hX3k : (w3.objEntry X).kind = (s.objEntry X).kind := by
    rw [kind_frame hF3 (by js_norm [Nat.lt_of_lt_of_le hX hz2])]; js_norm [hw2o X hX]
  have hX3p : ∀ k, k ≠ PropKey.str (JSStr.ofString "flags") → (w3.objEntry X).props.get? k = (s.objEntry X).props.get? k :=
    fun k hk => by
      rw [props_frame hF3 (by js_norm [Nat.lt_of_lt_of_le hX hz2]) (by simp [Ne.symm hk, hk])]; js_norm [hw2o X hX]
  have hw3E : w2.envs.size ≤ w3.envs.size := by have := hF3.envs_le; simp only [js_simp] at this; exact this
  have hw3z : s.heap.size ≤ w3.heap.size := by
    have := hF3.heap_le; simp only [js_simp] at this; exact Nat.le_trans hz2 this
  simp only [js_simp] at hfu3
  have hw3f : 55 ≤ w3.fuel := by omega
  have hK4 : s.envs.size < w3.envs.size := Nat.lt_of_lt_of_le hK3 hw3E
  have hB4 : w1.envs.size < w3.envs.size := Nat.lt_of_lt_of_le hB3 hw3E
  have hG4 : g < w3.envs.size := Nat.lt_of_lt_of_le hG3 hw3E
  have hX3a := (hX3p _ (by decide)).trans hXa
  have hX3c := (hX3p _ (by decide)).trans hXc
  have hX3s := (hX3p _ (by decide)).trans hXs
  have hX3l := (hX3p _ (by decide)).trans hXl
  have hBPo := hO3 fBP hBP x4
  have hH3 := hO3 H hH hHX
  js [hw3K, hw3B, hw3G, hX3k, hBPo, hK4, hB4, hG4, Nat.ne_of_gt hK4, Nat.ne_of_gt hB4, Nat.ne_of_gt hG4,
    Ne.symm (Nat.ne_of_gt hK4), Ne.symm (Nat.ne_of_gt hB4), Ne.symm (Nat.ne_of_gt hG4), hBK, hBG, Ne.symm hBK, Ne.symm hBG,
    Nat.lt_of_lt_of_le hX hw3z, Nat.lt_of_lt_of_le hBP hw3z, hX, hXk, hBP, hBPk, hGBP, hGBPv, hGe, hne, Ne.symm hne, hpn,
    hv, hl, ha, hWenv, FDI.fdiCtx, Sem.inner]
  refine ⟨by js_norm [CallableC, hBPo, hBPk, Nat.lt_of_lt_of_le hBP hw3z], ?_⟩
  refine wp_mono (ReactCompleteHelpers.bubble_leaf (X := X) (H := H) (sf := sf) (cl := cl) (aw := aw) (ae := ae)
    (ac := ac) (cw := cw) (ce := ce) (cc := cc) (hw := hcw) (he := hce) (hc := hcc) (se := se) (sc := sc) (le := le)
    (lc := lc) (Nat.lt_of_lt_of_le hBP hw3z) (by rw [hBPo]; exact hBPk) (by omega) hBPcode hBPcls hBPmode
    (Nat.lt_of_lt_of_le hX hw3z) (by rw [hX3k]; exact hXk) hX3a hX3c hX3s hX3l (Nat.lt_of_lt_of_le hH hw3z)
    (by rw [hH3]; exact hHk) (by rw [hH3]; exact hHc)) ?_
  intro v4 w4 h4 ⟨hv4, hF4, hfu4, hh4, hr4, hXs4, hXl4⟩
  subst hv4 hh4
  have hw4K : w4.envEntry s.envs.size = _ := (envEntry_frame hF4 hK4 (by simp)).trans hw3K
  have hw4B : w4.envEntry w1.envs.size = _ := (envEntry_frame hF4 hB4 (by simp)).trans hw3B
  have hw4G : w4.envEntry g = _ := (envEntry_frame hF4 hG4 (by simp)).trans hw3G
  have hO4 : ∀ o, o < s.heap.size → o ≠ X → w4.objEntry o = s.objEntry o := fun o ho hoX => by
    rw [objEntry_frame hF4 (Nat.lt_of_lt_of_le ho hw3z) (by simp [Ne.symm hoX, hoX]), hO3 o ho hoX]
  have hX4k : (w4.objEntry X).kind = (s.objEntry X).kind := by
    rw [kind_frame hF4 (Nat.lt_of_lt_of_le hX hw3z), hX3k]
  have hX4p : ∀ k, k ≠ PropKey.str (JSStr.ofString "subtreeFlags") → k ≠ PropKey.str (JSStr.ofString "childLanes") →
      (w4.objEntry X).props.get? k = (w3.objEntry X).props.get? k := fun k hk1 hk2 => by
    rw [props_frame hF4 (Nat.lt_of_lt_of_le hX hw3z) (by simp [Ne.symm hk1, hk1, Ne.symm hk2, hk2])]
  have hXf4 := (hX4p _ (by decide) (by decide)).trans hXf3
  have hX4m := ((hX4p _ (by decide) (by decide)).trans (hX3p _ (by decide))).trans hXm
  have hX4ty := ((hX4p _ (by decide) (by decide)).trans (hX3p _ (by decide))).trans hXty
  have hX4pp := ((hX4p _ (by decide) (by decide)).trans (hX3p _ (by decide))).trans hXpp
  have hw4E : w3.envs.size ≤ w4.envs.size := hF4.envs_le
  have hw4z : s.heap.size ≤ w4.heap.size := Nat.le_trans hw3z hF4.heap_le
  have hw4f : 35 ≤ w4.fuel := by omega
  have hK5 : s.envs.size < w4.envs.size := Nat.lt_of_lt_of_le hK4 hw4E
  have hB5 : w1.envs.size < w4.envs.size := Nat.lt_of_lt_of_le hB4 hw4E
  have hG5 : g < w4.envs.size := Nat.lt_of_lt_of_le hG4 hw4E
  have hPIo := hO4 fPI hPI x5
  have hH4 := hO4 H hH hHX
  js [hHX, Ne.symm hHX, x5, Ne.symm x5, x1, x2, x3, x4, Ne.symm x1, Ne.symm x2, Ne.symm x3, Ne.symm x4, hw4K, hw4B, hw4G, hX4k, hXs4, hXl4, hXf4, hX4m, hX4ty, hX4pp, hPIo, hH4, hHmp, hHk, hK5, hB5, hG5, Nat.ne_of_gt hK5,
    Nat.ne_of_gt hB5, Nat.ne_of_gt hG5, Ne.symm (Nat.ne_of_gt hK5), Ne.symm (Nat.ne_of_gt hB5), Ne.symm (Nat.ne_of_gt hG5),
    hBK, hBG, Ne.symm hBK, Ne.symm hBG, Nat.lt_of_lt_of_le hX hw4z, Nat.lt_of_lt_of_le hPI hw4z, Nat.lt_of_lt_of_le hH hw4z,
    hX, hXk, hPI, hPIk, hGPI, hGPIv, hGe, hne, Ne.symm hne, hpn, hv, hl, ha, hWenv, FDI.fdiCtx, Sem.inner]
  have hneg : (F64.fin false 4503599761588224 (-27)).neg = F64.fin true 4503599761588224 (-27) := rfl
  refine ⟨by js_norm [CallableC, hHX, Ne.symm hHX, x5, Ne.symm x5, x1, x2, x3, x4, Ne.symm x1, Ne.symm x2, Ne.symm x3, Ne.symm x4, hw4K, hw4B, hw4G, hX4k, hXs4, hXl4, hXf4, hX4m, hX4ty, hX4pp, hPIo, hH4, hHmp, hHk, hK5, hB5, hG5, Nat.ne_of_gt hK5, Nat.ne_of_gt hB5, Nat.ne_of_gt hG5, Ne.symm (Nat.ne_of_gt hK5), Ne.symm (Nat.ne_of_gt hB5), Ne.symm (Nat.ne_of_gt hG5), hBK, hBG, Ne.symm hBK, Ne.symm hBG, Nat.lt_of_lt_of_le hX hw4z, Nat.lt_of_lt_of_le hPI hw4z, Nat.lt_of_lt_of_le hH hw4z, hX, hXk, hPI, hPIk, hGPI, hGPIv, hGe, hne, Ne.symm hne, hpn, hv, hl, ha, hWenv, FDI.fdiCtx, Sem.inner], ?_⟩
  refine wp_mono (ReactCompleteHelpers.preload_none (X := X) (fl := numberBinOp .bitOr fl (F64.fin false 4503599627370496 (-50)))
    (m := m) (me := me) (mc := mc) (fe := fe) (fc := fc)
    (by js_norm [hHX, Ne.symm hHX, x5, Ne.symm x5, x1, x2, x3, x4, Ne.symm x1, Ne.symm x2, Ne.symm x3, Ne.symm x4, hw4K, hw4B, hw4G, hX4k, hXs4, hXl4, hXf4, hX4m, hX4ty, hX4pp, hPIo, hH4, hHmp, hHk, hK5, hB5, hG5, Nat.ne_of_gt hK5, Nat.ne_of_gt hB5, Nat.ne_of_gt hG5, Ne.symm (Nat.ne_of_gt hK5), Ne.symm (Nat.ne_of_gt hB5), Ne.symm (Nat.ne_of_gt hG5), hBK, hBG, Ne.symm hBK, Ne.symm hBG, Nat.lt_of_lt_of_le hX hw4z, Nat.lt_of_lt_of_le hPI hw4z, Nat.lt_of_lt_of_le hH hw4z, hX, hXk, hPI, hPIk, hGPI, hGPIv, hGe, hne, Ne.symm hne, hpn, hv, hl, ha, hWenv, FDI.fdiCtx, Sem.inner]) (by js_norm [hHX, Ne.symm hHX, x5, Ne.symm x5, x1, x2, x3, x4, Ne.symm x1, Ne.symm x2, Ne.symm x3, Ne.symm x4, hw4K, hw4B, hw4G, hX4k, hXs4, hXl4, hXf4, hX4m, hX4ty, hX4pp, hPIo, hH4, hHmp, hHk, hK5, hB5, hG5, Nat.ne_of_gt hK5, Nat.ne_of_gt hB5, Nat.ne_of_gt hG5, Ne.symm (Nat.ne_of_gt hK5), Ne.symm (Nat.ne_of_gt hB5), Ne.symm (Nat.ne_of_gt hG5), hBK, hBG, Ne.symm hBK, Ne.symm hBG, Nat.lt_of_lt_of_le hX hw4z, Nat.lt_of_lt_of_le hPI hw4z, Nat.lt_of_lt_of_le hH hw4z, hX, hXk, hPI, hPIk, hGPI, hGPIv, hGe, hne, Ne.symm hne, hpn, hv, hl, ha, hWenv, FDI.fdiCtx, Sem.inner]) (by simp only [js_simp]; omega) hPIcode hPIcls hPImode
    (by js_norm [hHX, Ne.symm hHX, x5, Ne.symm x5, x1, x2, x3, x4, Ne.symm x1, Ne.symm x2, Ne.symm x3, Ne.symm x4, hw4K, hw4B, hw4G, hX4k, hXs4, hXl4, hXf4, hX4m, hX4ty, hX4pp, hPIo, hH4, hHmp, hHk, hK5, hB5, hG5, Nat.ne_of_gt hK5, Nat.ne_of_gt hB5, Nat.ne_of_gt hG5, Ne.symm (Nat.ne_of_gt hK5), Ne.symm (Nat.ne_of_gt hB5), Ne.symm (Nat.ne_of_gt hG5), hBK, hBG, Ne.symm hBK, Ne.symm hBG, Nat.lt_of_lt_of_le hX hw4z, Nat.lt_of_lt_of_le hPI hw4z, Nat.lt_of_lt_of_le hH hw4z, hX, hXk, hPI, hPIk, hGPI, hGPIv, hGe, hne, Ne.symm hne, hpn, hv, hl, ha, hWenv, FDI.fdiCtx, Sem.inner]) (by js_norm [hHX, Ne.symm hHX, x5, Ne.symm x5, x1, x2, x3, x4, Ne.symm x1, Ne.symm x2, Ne.symm x3, Ne.symm x4, hw4K, hw4B, hw4G, hX4k, hXs4, hXl4, hXf4, hX4m, hX4ty, hX4pp, hPIo, hH4, hHmp, hHk, hK5, hB5, hG5, Nat.ne_of_gt hK5, Nat.ne_of_gt hB5, Nat.ne_of_gt hG5, Ne.symm (Nat.ne_of_gt hK5), Ne.symm (Nat.ne_of_gt hB5), Ne.symm (Nat.ne_of_gt hG5), hBK, hBG, Ne.symm hBK, Ne.symm hBG, Nat.lt_of_lt_of_le hX hw4z, Nat.lt_of_lt_of_le hPI hw4z, Nat.lt_of_lt_of_le hH hw4z, hX, hXk, hPI, hPIk, hGPI, hGPIv, hGe, hne, Ne.symm hne, hpn, hv, hl, ha, hWenv, FDI.fdiCtx, Sem.inner]) (by js_norm [hHX, Ne.symm hHX, x5, Ne.symm x5, x1, x2, x3, x4, Ne.symm x1, Ne.symm x2, Ne.symm x3, Ne.symm x4, hw4K, hw4B, hw4G, hX4k, hXs4, hXl4, hXf4, hX4m, hX4ty, hX4pp, hPIo, hH4, hHmp, hHk, hK5, hB5, hG5, Nat.ne_of_gt hK5, Nat.ne_of_gt hB5, Nat.ne_of_gt hG5, Ne.symm (Nat.ne_of_gt hK5), Ne.symm (Nat.ne_of_gt hB5), Ne.symm (Nat.ne_of_gt hG5), hBK, hBG, Ne.symm hBK, Ne.symm hBG, Nat.lt_of_lt_of_le hX hw4z, Nat.lt_of_lt_of_le hPI hw4z, Nat.lt_of_lt_of_le hH hw4z, hX, hXk, hPI, hPIk, hGPI, hGPIv, hGe, hne, Ne.symm hne, hpn, hv, hl, ha, hWenv, FDI.fdiCtx, Sem.inner]) hm (by js_norm [hHX, Ne.symm hHX, x5, Ne.symm x5, x1, x2, x3, x4, Ne.symm x1, Ne.symm x2, Ne.symm x3, Ne.symm x4, hw4K, hw4B, hw4G, hX4k, hXs4, hXl4, hXf4, hX4m, hX4ty, hX4pp, hPIo, hH4, hHmp, hHk, hK5, hB5, hG5, Nat.ne_of_gt hK5, Nat.ne_of_gt hB5, Nat.ne_of_gt hG5, Ne.symm (Nat.ne_of_gt hK5), Ne.symm (Nat.ne_of_gt hB5), Ne.symm (Nat.ne_of_gt hG5), hBK, hBG, Ne.symm hBK, Ne.symm hBG, Nat.lt_of_lt_of_le hX hw4z, Nat.lt_of_lt_of_le hPI hw4z, Nat.lt_of_lt_of_le hH hw4z, hX, hXk, hPI, hPIk, hGPI, hGPIv, hGe, hne, Ne.symm hne, hpn, hv, hl, ha, hWenv, FDI.fdiCtx, Sem.inner])) ?_
  intro v5 w5 h5 ⟨hv5, hF5, hfu5, hh5, hr5, hXf5⟩
  subst hv5 hh5
  have hz4 : X < w4.heap.size := Nat.lt_of_lt_of_le hX hw4z
  have hw5K : w5.envEntry s.envs.size = _ := envEntry_frame hF5 (by js_norm [hK5]) (by simp)
  have hw5B : w5.envEntry w1.envs.size = _ := envEntry_frame hF5 (by js_norm [hB5]) (by simp)
  simp only [js_simp, ↓reduceIte, hK5, hB5, hw4K, hw4B] at hw5K hw5B
  have hw5E : w4.envs.size ≤ w5.envs.size := by have := hF5.envs_le; simp only [js_simp] at this; exact this
  have hw5f : 25 ≤ w5.fuel := by simp only [js_simp] at hfu5; omega
  js [hw5K, hw5B, hw5f, Nat.lt_of_lt_of_le hK5 hw5E, Nat.lt_of_lt_of_le hB5 hw5E, Nat.ne_of_gt (Nat.lt_of_lt_of_le hK5 hw5E),
    Nat.ne_of_gt (Nat.lt_of_lt_of_le hB5 hw5E), Ne.symm (Nat.ne_of_gt (Nat.lt_of_lt_of_le hK5 hw5E)),
    Ne.symm (Nat.ne_of_gt (Nat.lt_of_lt_of_le hB5 hw5E)), hBK, Ne.symm hBK, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  have gB : Frame (fpCW X) s (bodyState s fW dW tW #[.obj H, .obj X, ln]) :=
    frame_mono (frame_bodyState (frame_refl ({} : Footprint) s) fW dW tW _) (by simp) (by simp) (fun _ => rfl)
  have FW1 := frame_extend' (frame_setEnv_new gB (Nat.le_refl _) _) hF1 (fun q hq _ => by simp at hq)
    (fun q hq _ => by simp at hq) (fun _ => rfl)
  have FW2 := frame_extend' (frame_pushEnv FW1 _) hF2 (fun q hq _ => by simp at hq) (fun q hq _ => by simp at hq)
    (fun _ => rfl)
  have FW3 := frame_extend' (frame_setEnv_new FW2 (Nat.le_refl _) _) hF3 (fun q hq _ => by simp at hq)
    (fun q hq _ => by simp at hq; simp [fpCW, hq]) (fun _ => rfl)
  have FW4 := frame_extend' FW3 hF4 (fun q hq _ => by simp at hq)
    (fun q hq _ => by simp at hq; rcases hq with hq | hq <;> simp [fpCW, hq]) (fun _ => rfl)
  have FW4' := frame_mono (fp' := fpCW X) (frame_setProp_prop FW4 hX (.str (JSStr.ofString "subtreeFlags"))
    (.data (.num (numberBinOp .bitAnd (numberBinOp .bitOr sf (F64.fin false 0 (-1074)))
      (F64.fin false 4503599761588224 (-27)).neg)) true se sc))
    (fun p hp => hp) (fun p hp => by simp only [List.mem_cons] at hp; rcases hp with rfl | hp; simp [fpCW]; exact hp)
    (fun h => h)
  have FW5 := frame_extend' FW4' hF5 (fun q hq _ => by simp at hq) (fun q hq _ => by simp at hq; simp [fpCW, hq])
    (fun _ => rfl)
  have hs5 : (w5.objEntry X).props.get? (.str "subtreeFlags") = some (.data (.num (numberBinOp .bitAnd
      (numberBinOp .bitOr sf (F64.fin false 0 (-1074))) (F64.fin true 4503599761588224 (-27)))) true se sc) := by
    rw [props_frame hF5 (by js_norm [hz4]) (by simp)]; js_norm [hz4, hneg]
  have hl5 : (w5.objEntry X).props.get? (.str "childLanes") = some (.data (.num (F64.fin false 0 (-1074))) true le lc) := by
    rw [props_frame hF5 (by js_norm [hz4]) (by simp)]; js_norm [hz4, hXl4]
  simp only [js_simp] at hfu1 hfu2 hfu3 hfu4 hfu5
  exact ⟨frame_restore FW5 s, by omega, rfl, hs5, hl5⟩

end

end ReactCompleteButton
