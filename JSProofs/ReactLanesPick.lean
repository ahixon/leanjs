import JSProofs.JsTactic
import JSProofs.GHPGen
import JSProofs.GNLGen

/-!
# React's `getHighestPriorityLanes` and `getNextLanes` for a click's root (zippy docs/react-proofs.md)

`getHighestPriorityLanes(2)`: the sync lanes among them (`2 & 42`), 2. `getNextLanes(root, 0, false)`: for the root
after a click (pending lanes 2, nothing suspended, pinged or warm) the sync lane, 2; after the commit (no pending
lanes) 0. Both read only.
-/

open ES ES.M HostRuns Logic
open Std (HashMap)

namespace ReactLanesPick

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ}

theorem simpleH (d : FuncData) (hc : d.code = GHPGen.getHighestPriorityLanes_func) : FDI.Simple d := by
  constructor <;> rw [hc] <;> try rfl
  simp [GHPGen.getHighestPriorityLanes_func, Func.params, Func.info]

set_option maxRecDepth 10000 in
theorem highest_spec {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t : Value} {s : State}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : 10 ≤ s.fuel)
    (hcode : d.code = GHPGen.getHighestPriorityLanes_func) (hcls : d.isClassCtor = false)
    (hmode : d.thisMode = .strict) :
    WP eng answer n h (callImpl eng (.obj fo) t #[.num (F64.fin false 4503599627370496 (-51))]) s
      fun v w _ => v = .num (F64.fin false 4503599627370496 (-51)) ∧ Frame {} s w ∧ s.fuel ≤ w.fuel + 10 := by
  apply wp_callGen GHPGen.getHighestPriorityLanes_eq (by decide) hlt hk (by omega) hcls hmode
    (by rw [hcode]; rfl) (by rw [hcode]; rfl) (simpleH d hcode) (by rw [hcode]; rfl) (by rw [hcode]; rfl)
  have hpn : d.code.info.fdi.paramNames = #[JSStr.ofString "lanes"] := by rw [hcode]; rfl
  have hv : d.code.info.fdi.varNames = #[JSStr.ofString "pendingSyncLanes"] := by rw [hcode]; rfl
  have hl : FDI.lexDecls d = #[] := by simp [FDI.lexDecls, hcode, GHPGen.getHighestPriorityLanes_func, Func.info]
  have ha : d.code.isAsync = false := by rw [hcode]; rfl
  clear hcode
  simp only [GHPGen.getHighestPriorityLanes]
  js [hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  all_goals (try apply And.intro)
  all_goals (try apply And.intro)
  all_goals first | rfl | omega | frame_go' [*]

theorem simpleN (d : FuncData) (hc : d.code = GNLGen.getNextLanes_func) : FDI.Simple d := by
  constructor <;> rw [hc] <;> try rfl
  simp [GNLGen.getNextLanes_func, Func.params, Func.info]

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
/-- **`getNextLanes(root, 0, false)` after a click**: the sync lane. -/
theorem next_click {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t : Value} {s : State}
    {bG : HashMap JSStr Binding} {oG : Option EnvId} {bdH : Binding} {R fH : ObjId} {dH : FuncData}
    {wv : Value} {lw le lc sw se sc pw pe pc ww we wc : Bool}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : 40 ≤ s.fuel)
    (hcode : d.code = GNLGen.getNextLanes_func) (hcls : d.isClassCtor = false) (hmode : d.thisMode = .strict)
    (hG : d.env < s.envs.size) (hGe : Scope.declLike? (s.envEntry d.env) = some (bG, oG))
    (hGH : bG[JSStr.ofString "getHighestPriorityLanes"]? = some bdH) (hGHv : bdH.value = some (.obj fH))
    (hHo : fH < s.heap.size) (hHk : (s.objEntry fH).kind = .func dH)
    (hHcode : dH.code = GHPGen.getHighestPriorityLanes_func) (hHcls : dH.isClassCtor = false)
    (hHmode : dH.thisMode = .strict)
    (hR : R < s.heap.size) (hRk : (s.objEntry R).kind.isPlain = true)
    (hRp : (s.objEntry R).props.get? (.str "pendingLanes") =
      some (.data (.num (F64.fin false 4503599627370496 (-51))) lw le lc))
    (hRs : (s.objEntry R).props.get? (.str "suspendedLanes") = some (.data (.num (F64.fin false 0 (-1074))) sw se sc))
    (hRi : (s.objEntry R).props.get? (.str "pingedLanes") = some (.data (.num (F64.fin false 0 (-1074))) pw pe pc))
    (hRw : (s.objEntry R).props.get? (.str "warmLanes") = some (.data wv ww we wc)) :
    WP eng answer (n + 1) h (callImpl eng (.obj fo) t #[.obj R, .num (F64.fin false 0 (-1074)), .bool false]) s
      fun v w _ => v = .num (F64.fin false 4503599627370496 (-51)) ∧ Frame {} s w ∧ s.fuel ≤ w.fuel + 20 := by
  apply wp_callGen GNLGen.getNextLanes_eq (by decide) hlt hk (by omega) hcls hmode
    (by rw [hcode]; rfl) (by rw [hcode]; rfl) (simpleN d hcode) (by rw [hcode]; rfl) (by rw [hcode]; rfl)
  have hpn : d.code.info.fdi.paramNames = #[JSStr.ofString "root", JSStr.ofString "wipLanes",
      JSStr.ofString "rootHasPendingCommit"] := by rw [hcode]; rfl
  have hv : d.code.info.fdi.varNames = #[JSStr.ofString "pendingLanes", JSStr.ofString "nextLanes", JSStr.ofString "suspendedLanes", JSStr.ofString "pingedLanes", JSStr.ofString "nonIdlePendingLanes"] := by rw [hcode]; rfl
  have hl : FDI.lexDecls d = #[] := by simp [FDI.lexDecls, hcode, GNLGen.getNextLanes_func, Func.info]
  have ha : d.code.isAsync = false := by rw [hcode]; rfl
  have hne : s.envs.size ≠ d.env := Nat.ne_of_gt hG
  have hG1 : d.env < s.envs.size + 1 := Nat.lt_succ_of_lt hG
  clear hcode
  simp only [GNLGen.getNextLanes]
  js [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGH, hGHv, hHo, hHk, hR, hRk, hRp, hRs, hRi, hRw,
    FDI.fdiCtx, Sem.inner]
  refine ⟨by js_norm [CallableC, *], ?_⟩
  refine wp_mono (highest_spec (by simpa using hHo) (by simpa using hHk) (by simp; omega) hHcode hHcls hHmode) ?post
  case post =>
  intro r w1 h1 ⟨hr, hF1, hfu1⟩
  subst hr
  try simp only [js_simp] at hfu1
  js [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hR, hRk, hRp, hRs, hRi, hRw, envEntry_frame0 hF1,
    objEntry_frame0 hF1, heap_frame hF1, envs_frame hF1, FDI.fdiCtx, Sem.inner]
  all_goals (try apply And.intro)
  all_goals (try apply And.intro)
  all_goals first | rfl | omega | frame_go' [*, hne, Ne.symm hne, hG1]

set_option maxRecDepth 10000 in
/-- **`getNextLanes` of a root with no pending lanes**: 0. -/
theorem next_none {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t a b : Value} {s : State} {R : ObjId}
    {lw le lc : Bool}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : 10 ≤ s.fuel)
    (hcode : d.code = GNLGen.getNextLanes_func) (hcls : d.isClassCtor = false) (hmode : d.thisMode = .strict)
    (hR : R < s.heap.size) (hRk : (s.objEntry R).kind.isPlain = true)
    (hRp : (s.objEntry R).props.get? (.str "pendingLanes") = some (.data (.num (F64.fin false 0 (-1074))) lw le lc)) :
    WP eng answer n h (callImpl eng (.obj fo) t #[.obj R, a, b]) s
      fun v w _ => v = .num (F64.fin false 0 (-1074)) ∧ Frame {} s w ∧ s.fuel ≤ w.fuel + 10 := by
  apply wp_callGen GNLGen.getNextLanes_eq (by decide) hlt hk (by omega) hcls hmode
    (by rw [hcode]; rfl) (by rw [hcode]; rfl) (simpleN d hcode) (by rw [hcode]; rfl) (by rw [hcode]; rfl)
  have hpn : d.code.info.fdi.paramNames = #[JSStr.ofString "root", JSStr.ofString "wipLanes",
      JSStr.ofString "rootHasPendingCommit"] := by rw [hcode]; rfl
  have hv : d.code.info.fdi.varNames = #[JSStr.ofString "pendingLanes", JSStr.ofString "nextLanes", JSStr.ofString "suspendedLanes", JSStr.ofString "pingedLanes", JSStr.ofString "nonIdlePendingLanes"] := by rw [hcode]; rfl
  have hl : FDI.lexDecls d = #[] := by simp [FDI.lexDecls, hcode, GNLGen.getNextLanes_func, Func.info]
  have ha : d.code.isAsync = false := by rw [hcode]; rfl
  clear hcode
  simp only [GNLGen.getNextLanes]
  js [hpn, hv, hl, ha, hR, hRk, hRp, FDI.fdiCtx, Sem.inner]
  all_goals (try apply And.intro)
  all_goals (try apply And.intro)
  all_goals first | rfl | omega | frame_go' [*]

end

end ReactLanesPick
