import JSProofs.JsTactic
import JSProofs.CPRGen

/-!
# React's `checkIfRootIsPrerendering` for a click's root (zippy docs/react-proofs.md)

```js
function checkIfRootIsPrerendering(root, renderLanes) {
  return 0 === (root.pendingLanes & ~(root.suspendedLanes & ~root.pingedLanes) & renderLanes);
}
```
The root after a click (pending lanes 2, nothing suspended or pinged), rendering the sync lane: not prerendering.
Reads only.
-/

open ES ES.M HostRuns Logic
open Std (HashMap)

namespace ReactPrerender

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ}

theorem simple (d : FuncData) (hc : d.code = CPRGen.checkIfRootIsPrerendering_func) : FDI.Simple d := by
  constructor <;> rw [hc] <;> try rfl
  simp [CPRGen.checkIfRootIsPrerendering_func, Func.params, Func.info]

set_option maxRecDepth 10000 in
theorem call_spec {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t : Value} {s : State} {R : ObjId}
    {lw le lc sw se sc pw pe pc : Bool}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : 10 ≤ s.fuel)
    (hcode : d.code = CPRGen.checkIfRootIsPrerendering_func) (hcls : d.isClassCtor = false)
    (hmode : d.thisMode = .strict)
    (hR : R < s.heap.size) (hRk : (s.objEntry R).kind.isPlain = true)
    (hRp : (s.objEntry R).props.get? (.str "pendingLanes") =
      some (.data (.num (F64.fin false 4503599627370496 (-51))) lw le lc))
    (hRs : (s.objEntry R).props.get? (.str "suspendedLanes") = some (.data (.num (F64.fin false 0 (-1074))) sw se sc))
    (hRi : (s.objEntry R).props.get? (.str "pingedLanes") = some (.data (.num (F64.fin false 0 (-1074))) pw pe pc)) :
    WP eng answer n h (callImpl eng (.obj fo) t #[.obj R, .num (F64.fin false 4503599627370496 (-51))]) s
      fun v w _ => v = .bool false ∧ Frame {} s w ∧ s.fuel ≤ w.fuel + 10 := by
  apply wp_callGen CPRGen.checkIfRootIsPrerendering_eq (by decide) hlt hk (by omega) hcls hmode
    (by rw [hcode]; rfl) (by rw [hcode]; rfl) (simple d hcode) (by rw [hcode]; rfl) (by rw [hcode]; rfl)
  have hpn : d.code.info.fdi.paramNames = #[JSStr.ofString "root", JSStr.ofString "renderLanes"] := by rw [hcode]; rfl
  have hv : d.code.info.fdi.varNames = #[] := by rw [hcode]; rfl
  have hl : FDI.lexDecls d = #[] := by simp [FDI.lexDecls, hcode, CPRGen.checkIfRootIsPrerendering_func, Func.info]
  have ha : d.code.isAsync = false := by rw [hcode]; rfl
  clear hcode
  simp only [CPRGen.checkIfRootIsPrerendering]
  js [hpn, hv, hl, ha, hR, hRk, hRp, hRs, hRi, FDI.fdiCtx, Sem.inner]
  all_goals (try apply And.intro)
  all_goals first | rfl | omega | frame_go' [*]

end

end ReactPrerender
