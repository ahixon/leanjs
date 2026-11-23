import JSProofs.CREGen
import JSProofs.ReactHostContainer

/-!
# commitReconciliationEffects for a fiber that is neither placed nor hydrated (zippy docs/react-proofs.md)

`commitReconciliationEffects(F)`, `F.flags` without Placement (2) and Hydrating (4096): nothing happens.
-/

open ES ES.M HostRuns Logic
open Std (HashMap)

namespace ReactCommitRec

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ}

theorem simple (d : FuncData) (hc : d.code = CREGen.commitReconciliationEffects_func) : FDI.Simple d := by
  constructor <;> rw [hc] <;> try rfl
  simp [CREGen.commitReconciliationEffects_func, Func.params, Func.info]

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
/-- **`commitReconciliationEffects(F)`**, `F.flags & 2` and `F.flags & 4096` zero: nothing changed. -/
theorem cre_spec {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t : Value} {s : State} {F : ObjId} {fl : F64}
    {fw fe fc : Bool}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : 40 ≤ s.fuel)
    (hcode : d.code = CREGen.commitReconciliationEffects_func) (hcls : d.isClassCtor = false)
    (hmode : d.thisMode = .strict)
    (hF : F < s.heap.size) (hFk : (s.objEntry F).kind.isPlain = true)
    (hFf : (s.objEntry F).props.get? (.str (JSStr.ofString "flags")) = some (.data (.num fl) fw fe fc))
    (h2 : numberBinOp .bitAnd fl (F64.fin false 4503599627370496 (-51)) = F64.fin false 0 (-1074))
    (h4096 : numberBinOp .bitAnd fl (F64.fin false 4503599627370496 (-40)) = F64.fin false 0 (-1074)) :
    WP eng answer (n + 1) h (callImpl eng (.obj fo) t #[.obj F]) s fun v w h' =>
      v = .undefined ∧ Frame {} s w ∧ s.fuel ≤ w.fuel + 40 ∧ h' = h := by
  apply wp_callGen CREGen.commitReconciliationEffects_eq (by decide) hlt hk (by omega) hcls hmode
    (by rw [hcode]; rfl) (by rw [hcode]; rfl) (simple d hcode) (by rw [hcode]; rfl) (by rw [hcode]; rfl)
  have hpn : d.code.info.fdi.paramNames = #[JSStr.ofString "finishedWork"] := by rw [hcode]; rfl
  have hv : d.code.info.fdi.varNames = #[JSStr.ofString "flags", JSStr.ofString "hostParentFiber",
    JSStr.ofString "parentFiber", JSStr.ofString "parent", JSStr.ofString "fragmentInstance",
    JSStr.ofString "JSCompiler_inline_result", JSStr.ofString "parent$jscomp$0", JSStr.ofString "before",
    JSStr.ofString "parent$149", JSStr.ofString "before$150", JSStr.ofString "parent$151",
    JSStr.ofString "before$152"] := by rw [hcode]; rfl
  have hl : FDI.lexDecls d = #[] := by simp [FDI.lexDecls, hcode, CREGen.commitReconciliationEffects_func, Func.info]
  have ha : d.code.isAsync = false := by rw [hcode]; rfl
  clear hcode
  simp only [CREGen.commitReconciliationEffects]
  js [hF, hFk, hFf, h2, h4096, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  refine ⟨by frame_go' [*], ?_⟩
  omega

end

end ReactCommitRec
