import JSProofs.Auto
import JSProofs.ReactIRPU

open ES ES.M HostRuns Logic
open Std (HashMap)

/-!
# React's `isRenderPhaseUpdate` by the `js` tactic (zippy docs/react-proofs.md)

The same theorem as `ReactIRPU.call_spec`, proved by `js`: after the call rule and the function's static facts, one
tactic follows the code (the `var`, the property read, the scope-chain reads, the case splits on `===`).
-/

namespace ReactIRPUAuto
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ}

/-- **`isRenderPhaseUpdate(fiber)`** (as `ReactIRPU.call_spec`, the module's record a declarative one). -/
theorem call_spec {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t : Value} {s : State} {F : ObjId}
    {alt cur : Value} {wa ea ca : Bool} {bG : HashMap JSStr Binding} {oG : Option EnvId} {bdG : Binding}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : 20 ≤ s.fuel)
    (hcode : d.code = IRPUGen.isRenderPhaseUpdate_func) (hcls : d.isClassCtor = false)
    (hmode : d.thisMode = .strict)
    (hG : d.env < s.envs.size) (hGe : s.envEntry d.env = .decl bG oG)
    (hGb : bG[JSStr.ofString "currentlyRenderingFiber"]? = some bdG) (hGv : bdG.value = some cur)
    (hF : F < s.heap.size) (hFk : (s.objEntry F).kind.isPlain = true)
    (hFp : (s.objEntry F).props.get? (.str "alternate") = some (.data alt wa ea ca)) :
    WP eng answer n h (callImpl eng (.obj fo) t #[.obj F]) s fun v _ _ =>
      v = .bool (isStrictlyEqual (.obj F) cur || (!isStrictlyEqual .null alt && isStrictlyEqual alt cur)) := by
  apply wp_call_simple hlt hk (by omega) hcls hmode (by rw [hcode]; rfl) (by rw [hcode]; rfl)
    (ReactIRPU.simple d hcode) (by rw [hcode]; rfl) (by rw [hcode]; rfl)
  change WP eng answer n h (evalStmts (999964 + 35) _ IRPUGen.isRenderPhaseUpdate_stmts) _ _
  rw [← congrFun (IRPUGen.isRenderPhaseUpdate_eq 999964) _]
  have hp : d.code.info.fdi.paramNames = #[JSStr.ofString "fiber"] := by rw [hcode]; rfl
  have hv : d.code.info.fdi.varNames = #[JSStr.ofString "alternate"] := by rw [hcode]; rfl
  have hl : FDI.lexDecls d = #[] := by simp [FDI.lexDecls, hcode, IRPUGen.isRenderPhaseUpdate_func, Func.info]
  have hne : s.envs.size ≠ d.env := Nat.ne_of_gt hG
  have ha : d.code.isAsync = false := by rw [hcode]; rfl
  clear hcode
  simp only [IRPUGen.isRenderPhaseUpdate]
  have hG1 : d.env < s.envs.size + 1 := Nat.lt_succ_of_lt hG
  js [hp, hv, hl, hG, hG1, hne, Ne.symm hne, hGe, hGb, hGv, hF, hFk, hFp, FDI.fdiCtx, Sem.inner]

end ReactIRPUAuto
