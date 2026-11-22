import JSProofs.Rules7
import JSProofs.Loops2
import JSProofs.Loops5
import JSProofs.PTCGen
import JSProofs.PopHCGen
import JSProofs.MUGen
import JSProofs.BPGen
import JSProofs.PISGen

/-!
# The button's completeWork helpers (zippy docs/react-proofs.md)

`popTreeContext(fiber)` outside any tree fork or id context (nothing), `popHostContext(fiber)` for a fiber that pushed
nothing (nothing), `markUpdate(fiber)` (flags `|= 4`), `bubbleProperties(fiber)` for a fiber without children whose
alternate has none either (a bailout: child lanes 0, subtree flags unchanged in value), and
`preloadInstanceAndSuspendIfNeeded` for a fiber not in the suspensey-images mode (flags `&= ~16777216`).
-/

open ES ES.M HostRuns Logic
open Std (HashMap)

namespace ReactCompleteHelpers

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ}

theorem simplePT (d : FuncData) (hc : d.code = PTCGen.popTreeContext_func) : FDI.Simple d := by
  constructor <;> rw [hc] <;> try rfl
  simp [PTCGen.popTreeContext_func, Func.params, Func.info]

set_option maxRecDepth 40000 in
/-- **`popTreeContext(fiber)`** when the fiber is neither the tree fork provider nor the id provider: nothing. -/
theorem ptc_none {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t : Value} {s : State} {X : ObjId} {bG : HashMap JSStr Binding} {bdF bdC : Binding}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : 20 ≤ s.fuel)
    (hcode : d.code = PTCGen.popTreeContext_func) (hcls : d.isClassCtor = false) (hmode : d.thisMode = .strict)
    (hG : d.env < s.envs.size) (hGe : Scope.declLike? (s.envEntry d.env) = some (bG, none))
    (hGF : bG[JSStr.ofString "treeForkProvider"]? = some bdF) (hGFv : bdF.value = some .null)
    (hGC : bG[JSStr.ofString "treeContextProvider"]? = some bdC) (hGCv : bdC.value = some .null) :
    WP eng answer n h (callImpl eng (.obj fo) t #[.obj X]) s fun v w h' =>
      v = .undefined ∧ Frame {} s w ∧ s.fuel ≤ w.fuel + 20 ∧ h' = h ∧ w.realm = s.realm := by
  apply wp_callGen PTCGen.popTreeContext_eq (by decide) hlt hk (by omega) hcls hmode
    (by rw [hcode]; rfl) (by rw [hcode]; rfl) (simplePT d hcode) (by rw [hcode]; rfl) (by rw [hcode]; rfl)
  have hpn : d.code.info.fdi.paramNames = #[JSStr.ofString "workInProgress"] := by rw [hcode]; rfl
  have hv : d.code.info.fdi.varNames = #[] := by rw [hcode]; rfl
  have hl : FDI.lexDecls d = #[] := by simp [FDI.lexDecls, hcode, PTCGen.popTreeContext_func, Func.info]
  have ha : d.code.isAsync = false := by rw [hcode]; rfl
  have hne : s.envs.size ≠ d.env := Nat.ne_of_gt hG
  have hG1 : d.env < s.envs.size + 1 := Nat.lt_succ_of_lt hG
  clear hcode
  simp only [PTCGen.popTreeContext]
  repeat (first | (refine wp_forVar ?_) | (refine wp_forNone ?_) | js_go | js_norm [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGF, hGFv, hGC, hGCv, FDI.fdiCtx, Sem.inner] | js_split)
  all_goals (repeat' apply And.intro)
  all_goals first | rfl | omega | (simp only [js_simp]; omega) | frame_go' [*] | (js_norm [*]; done)

theorem simplePH (d : FuncData) (hc : d.code = PopHCGen.popHostContext_func) : FDI.Simple d := by
  constructor <;> rw [hc] <;> try rfl
  simp [PopHCGen.popHostContext_func, Func.params, Func.info]

set_option maxRecDepth 40000 in
/-- **`popHostContext(fiber)`** for a fiber that pushed no host context (another fiber's on the cursor) and provides
no host transition: nothing. -/
theorem phc_none {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t : Value} {s : State} {X R CF HT : ObjId} {bG : HashMap JSStr Binding} {bdCF bdHT : Binding}
    {fw fe fc tw te tc : Bool}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : 20 ≤ s.fuel)
    (hcode : d.code = PopHCGen.popHostContext_func) (hcls : d.isClassCtor = false) (hmode : d.thisMode = .strict)
    (hG : d.env < s.envs.size) (hGe : Scope.declLike? (s.envEntry d.env) = some (bG, none))
    (hGCF : bG[JSStr.ofString "contextFiberStackCursor"]? = some bdCF) (hGCFv : bdCF.value = some (.obj CF))
    (hGHT : bG[JSStr.ofString "hostTransitionProviderCursor"]? = some bdHT) (hGHTv : bdHT.value = some (.obj HT))
    (hCF : CF < s.heap.size) (hCFk : (s.objEntry CF).kind.isPlain = true)
    (hCFc : (s.objEntry CF).props.get? (.str "current") = some (.data (.obj R) fw fe fc)) (hRX : R ≠ X)
    (hHT : HT < s.heap.size) (hHTk : (s.objEntry HT).kind.isPlain = true)
    (hHTc : (s.objEntry HT).props.get? (.str "current") = some (.data .null tw te tc)) :
    WP eng answer n h (callImpl eng (.obj fo) t #[.obj X]) s fun v w h' =>
      v = .undefined ∧ Frame {} s w ∧ s.fuel ≤ w.fuel + 20 ∧ h' = h ∧ w.realm = s.realm := by
  apply wp_callGen PopHCGen.popHostContext_eq (by decide) hlt hk (by omega) hcls hmode
    (by rw [hcode]; rfl) (by rw [hcode]; rfl) (simplePH d hcode) (by rw [hcode]; rfl) (by rw [hcode]; rfl)
  have hpn : d.code.info.fdi.paramNames = #[JSStr.ofString "fiber"] := by rw [hcode]; rfl
  have hv : d.code.info.fdi.varNames = #[] := by rw [hcode]; rfl
  have hl : FDI.lexDecls d = #[] := by simp [FDI.lexDecls, hcode, PopHCGen.popHostContext_func, Func.info]
  have ha : d.code.isAsync = false := by rw [hcode]; rfl
  have hne : s.envs.size ≠ d.env := Nat.ne_of_gt hG
  have hG1 : d.env < s.envs.size + 1 := Nat.lt_succ_of_lt hG
  have hRX' : isStrictlyEqual (.obj R) (.obj X) = false := by simp [isStrictlyEqual, sameValue, hRX]
  clear hcode
  simp only [PopHCGen.popHostContext]
  repeat (first | (refine wp_forVar ?_) | (refine wp_forNone ?_) | js_go | js_norm [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGCF, hGCFv, hGHT, hGHTv, hCF, hCFk, hCFc, hHT, hHTk, hHTc, hRX', FDI.fdiCtx, Sem.inner] | js_split)
  all_goals (repeat' apply And.intro)
  all_goals first | rfl | omega | (simp only [js_simp]; omega) | frame_go' [*] | (js_norm [*]; done)

theorem simpleMU (d : FuncData) (hc : d.code = MUGen.markUpdate_func) : FDI.Simple d := by
  constructor <;> rw [hc] <;> try rfl
  simp [MUGen.markUpdate_func, Func.params, Func.info]

set_option maxRecDepth 40000 in
/-- **`markUpdate(fiber)`**: `fiber.flags |= 4`. -/
theorem mark_update {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t : Value} {s : State} {X : ObjId} {fl : F64} {fe fc : Bool}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : 10 ≤ s.fuel)
    (hcode : d.code = MUGen.markUpdate_func) (hcls : d.isClassCtor = false) (hmode : d.thisMode = .strict)
    (hX : X < s.heap.size) (hXk : (s.objEntry X).kind.isPlain = true)
    (hXf : (s.objEntry X).props.get? (.str "flags") = some (.data (.num fl) true fe fc)) :
    WP eng answer n h (callImpl eng (.obj fo) t #[.obj X]) s fun v w h' =>
      v = .undefined ∧ Frame ⟨[], [(X, .str "flags")], false⟩ s w ∧ s.fuel ≤ w.fuel + 10 ∧ h' = h ∧
      w.realm = s.realm ∧
      (w.objEntry X).props.get? (.str "flags") =
        some (.data (.num (numberBinOp .bitOr fl (F64.fin false 4503599627370496 (-50)))) true fe fc) := by
  apply wp_callGen MUGen.markUpdate_eq (by decide) hlt hk (by omega) hcls hmode
    (by rw [hcode]; rfl) (by rw [hcode]; rfl) (simpleMU d hcode) (by rw [hcode]; rfl) (by rw [hcode]; rfl)
  have hpn : d.code.info.fdi.paramNames = #[JSStr.ofString "workInProgress"] := by rw [hcode]; rfl
  have hv : d.code.info.fdi.varNames = #[] := by rw [hcode]; rfl
  have hl : FDI.lexDecls d = #[] := by simp [FDI.lexDecls, hcode, MUGen.markUpdate_func, Func.info]
  have ha : d.code.isAsync = false := by rw [hcode]; rfl
  clear hcode
  simp only [MUGen.markUpdate]
  repeat (first | (refine wp_forVar ?_) | (refine wp_forNone ?_) | js_go | js_norm [hpn, hv, hl, ha, hX, hXk, hXf, FDI.fdiCtx, Sem.inner] | js_split)
  all_goals (repeat' apply And.intro)
  all_goals first | rfl | omega | (simp only [js_simp]; omega) | frame_go' [*] | (js_norm [*]; done)

theorem simpleBP (d : FuncData) (hc : d.code = BPGen.bubbleProperties_func) : FDI.Simple d := by
  constructor <;> rw [hc] <;> try rfl
  simp [BPGen.bubbleProperties_func, Func.params, Func.info]

set_option maxRecDepth 40000 in
/-- **`bubbleProperties(fiber)`** for a fiber without a child whose alternate has none either: a bailout (`true`);
no child lanes, the subtree flags or-ed with 0. -/
theorem bubble_leaf {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t : Value} {s : State} {X H : ObjId} {sf : F64} {cl : Value} {aw ae ac cw ce cc hw he hc se sc le lc : Bool}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : 20 ≤ s.fuel)
    (hcode : d.code = BPGen.bubbleProperties_func) (hcls : d.isClassCtor = false) (hmode : d.thisMode = .strict)
    (hX : X < s.heap.size) (hXk : (s.objEntry X).kind.isPlain = true)
    (hXa : (s.objEntry X).props.get? (.str "alternate") = some (.data (.obj H) aw ae ac))
    (hXc : (s.objEntry X).props.get? (.str "child") = some (.data .null cw ce cc))
    (hXs : (s.objEntry X).props.get? (.str "subtreeFlags") = some (.data (.num sf) true se sc))
    (hXl : (s.objEntry X).props.get? (.str "childLanes") = some (.data cl true le lc))
    (hH : H < s.heap.size) (hHk : (s.objEntry H).kind.isPlain = true)
    (hHc : (s.objEntry H).props.get? (.str "child") = some (.data .null hw he hc)) :
    WP eng answer n h (callImpl eng (.obj fo) t #[.obj X]) s fun v w h' =>
      v = .bool true ∧ Frame ⟨[], [(X, .str "subtreeFlags"), (X, .str "childLanes")], false⟩ s w ∧
      s.fuel ≤ w.fuel + 20 ∧ h' = h ∧ w.realm = s.realm ∧
      (w.objEntry X).props.get? (.str "subtreeFlags") =
        some (.data (.num (numberBinOp .bitOr sf (F64.fin false 0 (-1074)))) true se sc) ∧
      (w.objEntry X).props.get? (.str "childLanes") = some (.data (.num (F64.fin false 0 (-1074))) true le lc) := by
  apply wp_callGen BPGen.bubbleProperties_eq (by decide) hlt hk (by omega) hcls hmode
    (by rw [hcode]; rfl) (by rw [hcode]; rfl) (simpleBP d hcode) (by rw [hcode]; rfl) (by rw [hcode]; rfl)
  have hpn : d.code.info.fdi.paramNames = #[JSStr.ofString "completedWork"] := by rw [hcode]; rfl
  have hv : d.code.info.fdi.varNames = #[JSStr.ofString "didBailout", JSStr.ofString "newChildLanes", JSStr.ofString "subtreeFlags", JSStr.ofString "child$113"] := by rw [hcode]; rfl
  have hl : FDI.lexDecls d = #[] := by simp [FDI.lexDecls, hcode, BPGen.bubbleProperties_func, Func.info]
  have ha : d.code.isAsync = false := by rw [hcode]; rfl
  clear hcode
  simp only [BPGen.bubbleProperties]
  repeat (first | (refine wp_forVar ?_) | (refine wp_forNone ?_) | js_go | js_norm [hpn, hv, hl, ha, hX, hXk, hXa, hXc, hXs, hXl, hH, hHk, hHc, FDI.fdiCtx, Sem.inner] | js_split)
  all_goals (repeat' apply And.intro)
  all_goals first | rfl | omega | (simp only [js_simp]; omega) | frame_go' [*] | (js_norm [*]; done)

theorem simplePI (d : FuncData) (hc : d.code = PISGen.preloadInstanceAndSuspendIfNeeded_func) : FDI.Simple d := by
  constructor <;> rw [hc] <;> try rfl
  simp [PISGen.preloadInstanceAndSuspendIfNeeded_func, Func.params, Func.info]

set_option maxRecDepth 40000 in
/-- **`preloadInstanceAndSuspendIfNeeded(fiber, …)`** for a fiber not in the suspensey-images mode (bit 32):
`fiber.flags &= ~16777216`. -/
theorem preload_none {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t : Value} {s : State} {X : ObjId} {fl m : F64} {ty ov nv ln : Value} {me mc fe fc : Bool}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : 10 ≤ s.fuel)
    (hcode : d.code = PISGen.preloadInstanceAndSuspendIfNeeded_func) (hcls : d.isClassCtor = false)
    (hmode : d.thisMode = .strict)
    (hX : X < s.heap.size) (hXk : (s.objEntry X).kind.isPlain = true)
    (hXm : (s.objEntry X).props.get? (.str "mode") = some (.data (.num m) true me mc))
    (hm : numberBinOp .bitAnd m (F64.fin false 4503599627370496 (-47)) = F64.fin false 0 (-1074))
    (hXf : (s.objEntry X).props.get? (.str "flags") = some (.data (.num fl) true fe fc)) :
    WP eng answer n h (callImpl eng (.obj fo) t #[.obj X, ty, ov, nv, ln]) s fun v w h' =>
      v = .undefined ∧ Frame ⟨[], [(X, .str "flags")], false⟩ s w ∧ s.fuel ≤ w.fuel + 10 ∧ h' = h ∧
      w.realm = s.realm ∧
      (w.objEntry X).props.get? (.str "flags") =
        some (.data (.num (numberBinOp .bitAnd fl (F64.fin true 4503599895805952 (-28)))) true fe fc) := by
  apply wp_callGen PISGen.preloadInstanceAndSuspendIfNeeded_eq (by decide) hlt hk (by omega) hcls hmode
    (by rw [hcode]; rfl) (by rw [hcode]; rfl) (simplePI d hcode) (by rw [hcode]; rfl) (by rw [hcode]; rfl)
  have hpn : d.code.info.fdi.paramNames = #[JSStr.ofString "workInProgress", JSStr.ofString "type", JSStr.ofString "oldProps", JSStr.ofString "newProps", JSStr.ofString "renderLanes"] := by rw [hcode]; rfl
  have hv : d.code.info.fdi.varNames = #[JSStr.ofString "JSCompiler_temp"] := by rw [hcode]; rfl
  have hl : FDI.lexDecls d = #[] := by simp [FDI.lexDecls, hcode, PISGen.preloadInstanceAndSuspendIfNeeded_func, Func.info]
  have ha : d.code.isAsync = false := by rw [hcode]; rfl
  have hz : isStrictlyEqual (.num (F64.fin false 0 (-1074))) (.num (F64.fin false 0 (-1074))) = true := by decide
  clear hcode
  simp only [PISGen.preloadInstanceAndSuspendIfNeeded]
  repeat (first | (refine wp_forVar ?_) | (refine wp_forNone ?_) | js_go | js_norm [hpn, hv, hl, ha, hX, hXk, hXm, hm, hXf, hz, FDI.fdiCtx, Sem.inner] | js_split)
  all_goals (repeat' apply And.intro)
  all_goals first | rfl | omega | (simp only [js_simp]; omega) | frame_go' [*] | (js_norm [*]; done)

end

end ReactCompleteHelpers
