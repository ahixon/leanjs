import JSProofs.Rules5
import JSProofs.Loops5
import JSProofs.CCRGen
import JSProofs.CRGen

/-!
# The child reconciler's helpers on the click's path (zippy docs/react-proofs.md)

`deleteRemainingChildren(returnFiber, null)` (nothing left to delete), `placeSingleChild(X)` for a reused fiber
(it has its alternate: no placement flag), and `coerceRef(X, element)` for an element whose props have no `ref`.
-/

open ES ES.M HostRuns Logic
open Std (HashMap)

namespace ReactReconcileHelpers

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ}

theorem simpleD (d : FuncData) (hc : d.code = CCRGen.deleteRemainingChildren_func) : FDI.Simple d := by
  constructor <;> rw [hc] <;> try rfl
  simp [CCRGen.deleteRemainingChildren_func, Func.params, Func.info]

theorem simpleP (d : FuncData) (hc : d.code = CCRGen.placeSingleChild_func) : FDI.Simple d := by
  constructor <;> rw [hc] <;> try rfl
  simp [CCRGen.placeSingleChild_func, Func.params, Func.info]

theorem simpleC (d : FuncData) (hc : d.code = CRGen.coerceRef_func) : FDI.Simple d := by
  constructor <;> rw [hc] <;> try rfl
  simp [CRGen.coerceRef_func, Func.params, Func.info]

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
set_option maxRecDepth 20000 in
/-- **`deleteRemainingChildren(returnFiber, null)`** in the reconciler that tracks side effects: `null`. -/
theorem delete_none {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t rf : Value} {s : State}
    {bR : HashMap JSStr Binding} {oR : Option EnvId} {bdT : Binding}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : 10 ≤ s.fuel)
    (hcode : d.code = CCRGen.deleteRemainingChildren_func) (hcls : d.isClassCtor = false)
    (hmode : d.thisMode = .strict)
    (hE : d.env < s.envs.size) (hEe : Scope.declLike? (s.envEntry d.env) = some (bR, oR))
    (hET : bR[JSStr.ofString "shouldTrackSideEffects"]? = some bdT) (hETv : bdT.value = some (.bool true)) :
    WP eng answer n h (callImpl eng (.obj fo) t #[rf, .null]) s fun v w h' =>
      v = .null ∧ Frame {} s w ∧ s.fuel ≤ w.fuel + 10 ∧ h' = h ∧ w.realm = s.realm := by
  apply wp_callGen CCRGen.deleteRemainingChildren_eq (by decide) hlt hk (by omega) hcls hmode
    (by rw [hcode]; rfl) (by rw [hcode]; rfl) (simpleD d hcode) (by rw [hcode]; rfl) (by rw [hcode]; rfl)
  have hpn : d.code.info.fdi.paramNames = #[JSStr.ofString "returnFiber", JSStr.ofString "currentFirstChild"] := by
    rw [hcode]; rfl
  have hv : d.code.info.fdi.varNames = #[] := by rw [hcode]; rfl
  have hl : FDI.lexDecls d = #[] := by simp [FDI.lexDecls, hcode, CCRGen.deleteRemainingChildren_func, Func.info]
  have ha : d.code.isAsync = false := by rw [hcode]; rfl
  have hne : s.envs.size ≠ d.env := Nat.ne_of_gt hE
  have hE1 : d.env < s.envs.size + 1 := Nat.lt_succ_of_lt hE
  clear hcode
  simp only [CCRGen.deleteRemainingChildren]
  js [hpn, hv, hl, ha, hE, hE1, hne, Ne.symm hne, hEe, hET, hETv, FDI.fdiCtx, Sem.inner]
  refine wp_forNone ?_
  js [hpn, hv, hl, ha, hE, hE1, hne, Ne.symm hne, hEe, hET, hETv, FDI.fdiCtx, Sem.inner]
  all_goals (repeat' apply And.intro)
  all_goals first
    | rfl | omega | (simp only [js_simp]; omega) | (frame_go' [*, hne, Ne.symm hne, hE1]; done)
    | (js_norm [*]; done) | skip

/-- **`placeSingleChild(X)`** for a fiber with its alternate: `X`, unchanged. -/
theorem place_reused {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t : Value} {s : State}
    {bR : HashMap JSStr Binding} {oR : Option EnvId} {bdT : Binding} {X A : ObjId} {aw ae ac : Bool}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : 10 ≤ s.fuel)
    (hcode : d.code = CCRGen.placeSingleChild_func) (hcls : d.isClassCtor = false)
    (hmode : d.thisMode = .strict)
    (hE : d.env < s.envs.size) (hEe : Scope.declLike? (s.envEntry d.env) = some (bR, oR))
    (hET : bR[JSStr.ofString "shouldTrackSideEffects"]? = some bdT) (hETv : bdT.value = some (.bool true))
    (hX : X < s.heap.size) (hXk : (s.objEntry X).kind.isPlain = true)
    (hXa : (s.objEntry X).props.get? (.str "alternate") = some (.data (.obj A) aw ae ac)) :
    WP eng answer n h (callImpl eng (.obj fo) t #[.obj X]) s fun v w h' =>
      v = .obj X ∧ Frame {} s w ∧ s.fuel ≤ w.fuel + 10 ∧ h' = h ∧ w.realm = s.realm := by
  apply wp_callGen CCRGen.placeSingleChild_eq (by decide) hlt hk (by omega) hcls hmode
    (by rw [hcode]; rfl) (by rw [hcode]; rfl) (simpleP d hcode) (by rw [hcode]; rfl) (by rw [hcode]; rfl)
  have hpn : d.code.info.fdi.paramNames = #[JSStr.ofString "newFiber"] := by rw [hcode]; rfl
  have hv : d.code.info.fdi.varNames = #[] := by rw [hcode]; rfl
  have hl : FDI.lexDecls d = #[] := by simp [FDI.lexDecls, hcode, CCRGen.placeSingleChild_func, Func.info]
  have ha : d.code.isAsync = false := by rw [hcode]; rfl
  have hne : s.envs.size ≠ d.env := Nat.ne_of_gt hE
  have hE1 : d.env < s.envs.size + 1 := Nat.lt_succ_of_lt hE
  clear hcode
  simp only [CCRGen.placeSingleChild]
  js [hpn, hv, hl, ha, hE, hE1, hne, Ne.symm hne, hEe, hET, hETv, hX, hXk, hXa, FDI.fdiCtx, Sem.inner]
  all_goals (repeat' apply And.intro)
  all_goals first
    | rfl | omega | (simp only [js_simp]; omega) | (frame_go' [*, hne, Ne.symm hne, hE1]; done)
    | (js_norm [*]; done) | skip

/-- **`coerceRef(X, element)`** for an element whose props (and their prototype) have no `ref`: `X.ref = null`. -/
theorem coerce_none {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t : Value} {s : State}
    {X El C OP : ObjId} {pw pe pc rv re rc : Bool} {r0 : Value}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : 10 ≤ s.fuel)
    (hcode : d.code = CRGen.coerceRef_func) (hcls : d.isClassCtor = false) (hmode : d.thisMode = .strict)
    (hX : X < s.heap.size) (hXk : (s.objEntry X).kind.isPlain = true)
    (hXr : (s.objEntry X).props.get? (.str "ref") = some (.data r0 true re rc))
    (hEl : El < s.heap.size) (hElk : (s.objEntry El).kind.isPlain = true)
    (hElp : (s.objEntry El).props.get? (.str "props") = some (.data (.obj C) pw pe pc))
    (hC : C < s.heap.size) (hCk : (s.objEntry C).kind.isPlain = true) (hCp : (s.objEntry C).proto = .obj OP)
    (hCr : (s.objEntry C).props.get? (.str "ref") = none)
    (hOP : OP < s.heap.size) (hOPk : (s.objEntry OP).kind.isPlain = true) (hOPp : (s.objEntry OP).proto = .null)
    (hOPr : (s.objEntry OP).props.get? (.str "ref") = none) :
    WP eng answer n h (callImpl eng (.obj fo) t #[.obj X, .obj El]) s fun v w h' =>
      v = .undefined ∧ Frame ⟨[], [(X, .str "ref")], false⟩ s w ∧ s.fuel ≤ w.fuel + 10 ∧ h' = h ∧
      w.realm = s.realm ∧ (w.objEntry X).props.get? (.str "ref") = some (.data .null true re rc) := by
  apply wp_callGen CRGen.coerceRef_eq (by decide) hlt hk (by omega) hcls hmode
    (by rw [hcode]; rfl) (by rw [hcode]; rfl) (simpleC d hcode) (by rw [hcode]; rfl) (by rw [hcode]; rfl)
  have hpn : d.code.info.fdi.paramNames = #[JSStr.ofString "workInProgress", JSStr.ofString "element"] := by
    rw [hcode]; rfl
  have hv : d.code.info.fdi.varNames = #[] := by rw [hcode]; rfl
  have hl : FDI.lexDecls d = #[] := by simp [FDI.lexDecls, hcode, CRGen.coerceRef_func, Func.info]
  have ha : d.code.isAsync = false := by rw [hcode]; rfl
  clear hcode
  simp only [CRGen.coerceRef]
  iterate 5 (first | js_go | js_norm [hpn, hv, hl, ha, hX, hXk, hXr, hEl, hElk, hElp, FDI.fdiCtx, Sem.inner] | js_split)
  refine wp_getMemberAbsent2 ?_
  js [hpn, hv, hl, ha, hX, hXk, hXr, hEl, hElk, hElp, hC, hCk, hCp, hCr, hOP, hOPk, hOPp, hOPr, FDI.fdiCtx, Sem.inner]
  refine ⟨C, OP, rfl, by js_norm [hpn, hv, hl, ha, hX, hXk, hXr, hEl, hElk, hElp, hC, hCk, hCp, hCr, hOP, hOPk, hOPp, hOPr, FDI.fdiCtx, Sem.inner], by js_norm [hpn, hv, hl, ha, hX, hXk, hXr, hEl, hElk, hElp, hC, hCk, hCp, hCr, hOP, hOPk, hOPp, hOPr, FDI.fdiCtx, Sem.inner], by js_norm [hpn, hv, hl, ha, hX, hXk, hXr, hEl, hElk, hElp, hC, hCk, hCp, hCr, hOP, hOPk, hOPp, hOPr, FDI.fdiCtx, Sem.inner], by js_norm [hpn, hv, hl, ha, hX, hXk, hXr, hEl, hElk, hElp, hC, hCk, hCp, hCr, hOP, hOPk, hOPp, hOPr, FDI.fdiCtx, Sem.inner], by js_norm [hpn, hv, hl, ha, hX, hXk, hXr, hEl, hElk, hElp, hC, hCk, hCp, hCr, hOP, hOPk, hOPp, hOPr, FDI.fdiCtx, Sem.inner],
    by js_norm [hpn, hv, hl, ha, hX, hXk, hXr, hEl, hElk, hElp, hC, hCk, hCp, hCr, hOP, hOPk, hOPp, hOPr, FDI.fdiCtx, Sem.inner], by js_norm [hpn, hv, hl, ha, hX, hXk, hXr, hEl, hElk, hElp, hC, hCk, hCp, hCr, hOP, hOPk, hOPp, hOPr, FDI.fdiCtx, Sem.inner], by js_norm [hpn, hv, hl, ha, hX, hXk, hXr, hEl, hElk, hElp, hC, hCk, hCp, hCr, hOP, hOPk, hOPp, hOPr, FDI.fdiCtx, Sem.inner], ?_⟩
  js [hpn, hv, hl, ha, hX, hXk, hXr, hEl, hElk, hElp, hC, hCk, hCp, hCr, hOP, hOPk, hOPp, hOPr, FDI.fdiCtx, Sem.inner]
  refine wp_void ?_
  js [hpn, hv, hl, ha, hX, hXk, hXr, hEl, hElk, hElp, hC, hCk, hCp, hCr, hOP, hOPk, hOPp, hOPr, FDI.fdiCtx, Sem.inner]
  all_goals (repeat' apply And.intro)
  all_goals first
    | rfl | omega | (simp only [js_simp]; omega) | (frame_go' [*]; done)
    | (js_norm [*]; done) | skip

end

end ReactReconcileHelpers
