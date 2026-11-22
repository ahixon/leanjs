import JSProofs.JsTactic
import JSProofs.RWSGen
import JSProofs.GELGen

/-!
# `prepareFreshStack`'s small callees for a click's render (zippy docs/react-proofs.md)

`resetWorkInProgressStack()` after a commit (`workInProgress` is null: nothing to unwind) and
`getEntangledLanes(root, 2)` with no entangled lanes (returns 2).
-/

open ES ES.M HostRuns Logic
open Std (HashMap)

namespace ReactPrepCallees

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ}

theorem simpleR (d : FuncData) (hc : d.code = RWSGen.resetWorkInProgressStack_func) : FDI.Simple d := by
  constructor <;> rw [hc] <;> try rfl
  simp [RWSGen.resetWorkInProgressStack_func, Func.params, Func.info]

theorem simpleE (d : FuncData) (hc : d.code = GELGen.getEntangledLanes_func) : FDI.Simple d := by
  constructor <;> rw [hc] <;> try rfl
  simp [GELGen.getEntangledLanes_func, Func.params, Func.info]

set_option maxRecDepth 10000 in
/-- **`resetWorkInProgressStack()`** with no work in progress: nothing changes. -/
theorem reset_spec {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t : Value} {s : State}
    {bG : HashMap JSStr Binding} {oG : Option EnvId} {bdW : Binding}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : 10 ≤ s.fuel)
    (hcode : d.code = RWSGen.resetWorkInProgressStack_func) (hcls : d.isClassCtor = false)
    (hmode : d.thisMode = .strict)
    (hG : d.env < s.envs.size) (hGe : Scope.declLike? (s.envEntry d.env) = some (bG, oG))
    (hGW : bG[JSStr.ofString "workInProgress"]? = some bdW) (hGWv : bdW.value = some .null) :
    WP eng answer n h (callImpl eng (.obj fo) t #[]) s fun v w h' =>
      v = .undefined ∧ Frame {} s w ∧ s.fuel ≤ w.fuel + 10 ∧ h' = h := by
  apply wp_callGen RWSGen.resetWorkInProgressStack_eq (by decide) hlt hk (by omega) hcls hmode
    (by rw [hcode]; rfl) (by rw [hcode]; rfl) (simpleR d hcode) (by rw [hcode]; rfl) (by rw [hcode]; rfl)
  have hpn : d.code.info.fdi.paramNames = #[] := by rw [hcode]; rfl
  have hv : d.code.info.fdi.varNames = #[JSStr.ofString "interruptedWork"] := by rw [hcode]; rfl
  have hl : FDI.lexDecls d = #[] := by simp [FDI.lexDecls, hcode, RWSGen.resetWorkInProgressStack_func, Func.info]
  have ha : d.code.isAsync = false := by rw [hcode]; rfl
  have hne : s.envs.size ≠ d.env := Nat.ne_of_gt hG
  have hG1 : d.env < s.envs.size + 1 := Nat.lt_succ_of_lt hG
  clear hcode
  simp only [RWSGen.resetWorkInProgressStack]
  js [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGW, hGWv, FDI.fdiCtx, Sem.inner]
  all_goals (try apply And.intro)
  all_goals (try apply And.intro)
  all_goals (try apply And.intro)
  all_goals first | rfl | omega | frame_go' [*, hne, Ne.symm hne, hG1]

set_option maxRecDepth 10000 in
/-- **`getEntangledLanes(root, 2)`** with `root.entangledLanes` 0: returns 2, changes nothing. -/
theorem entangled_spec {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t : Value} {s : State}
    {R : ObjId} {ew ee ec : Bool}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : 10 ≤ s.fuel)
    (hcode : d.code = GELGen.getEntangledLanes_func) (hcls : d.isClassCtor = false)
    (hmode : d.thisMode = .strict)
    (hR : R < s.heap.size) (hRk : (s.objEntry R).kind.isPlain = true)
    (hRe : (s.objEntry R).props.get? (.str "entangledLanes") = some (.data (.num (F64.fin false 0 (-1074))) ew ee ec)) :
    WP eng answer n h (callImpl eng (.obj fo) t #[.obj R, .num (F64.fin false 4503599627370496 (-51))]) s
      fun v w h' => v = .num (F64.fin false 4503599627370496 (-51)) ∧ Frame {} s w ∧ s.fuel ≤ w.fuel + 10 ∧ h' = h := by
  apply wp_callGen GELGen.getEntangledLanes_eq (by decide) hlt hk (by omega) hcls hmode
    (by rw [hcode]; rfl) (by rw [hcode]; rfl) (simpleE d hcode) (by rw [hcode]; rfl) (by rw [hcode]; rfl)
  have hpn : d.code.info.fdi.paramNames = #[JSStr.ofString "root", JSStr.ofString "renderLanes"] := by rw [hcode]; rfl
  have hv : d.code.info.fdi.varNames = #[JSStr.ofString "allEntangledLanes", JSStr.ofString "index$4",
    JSStr.ofString "lane"] := by rw [hcode]; rfl
  have hl : FDI.lexDecls d = #[] := by simp [FDI.lexDecls, hcode, GELGen.getEntangledLanes_func, Func.info]
  have ha : d.code.isAsync = false := by rw [hcode]; rfl
  clear hcode
  simp only [GELGen.getEntangledLanes]
  js [hpn, hv, hl, ha, hR, hRk, hRe, FDI.fdiCtx, Sem.inner]
  all_goals (try apply And.intro)
  all_goals (try apply And.intro)
  all_goals (try apply And.intro)
  all_goals first | rfl | omega | frame_go' [*]

end

end ReactPrepCallees
