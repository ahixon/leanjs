import JSProofs.JsTactic
import JSProofs.MRUGen

/-!
# React's `markRootUpdated$1` for a click's lane (zippy docs/react-proofs.md)

```js
function markRootUpdated$1(root, updateLane) {
  root.pendingLanes |= updateLane;
  268435456 !== updateLane &&
    ((root.suspendedLanes = 0), (root.pingedLanes = 0), (root.warmLanes = 0));
}
```
The root records the lane as pending; for any lane but the idle lane, nothing on it is suspended, pinged, or warm any
more. Footprint: those four properties of the root.
-/

open ES ES.M HostRuns Logic
open Std (HashMap)

namespace ReactMarkRoot

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ}

theorem simple (d : FuncData) (hc : d.code = MRUGen.fn0_func) : FDI.Simple d := by
  constructor <;> rw [hc] <;> try rfl
  simp [MRUGen.fn0_func, Func.params, Func.info]

theorem call_spec {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t : Value} {s : State} {p pl : F64} {R : ObjId}
    {pe pc ue uc ie ic we wc : Bool} {u i wv : Value}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : 10 ≤ s.fuel)
    (hcode : d.code = MRUGen.fn0_func) (hcls : d.isClassCtor = false) (hmode : d.thisMode = .strict)
    (hp : isStrictlyEqual (.num (F64.fin false 4503599627370496 (-24))) (.num p) = false)
    (hR : R < s.heap.size) (hRk : (s.objEntry R).kind.isPlain = true)
    (hRp : (s.objEntry R).props.get? (.str "pendingLanes") = some (.data (.num pl) true pe pc))
    (hRs : (s.objEntry R).props.get? (.str "suspendedLanes") = some (.data u true ue uc))
    (hRi : (s.objEntry R).props.get? (.str "pingedLanes") = some (.data i true ie ic))
    (hRw : (s.objEntry R).props.get? (.str "warmLanes") = some (.data wv true we wc)) :
    WP eng answer n h (callImpl eng (.obj fo) t #[.obj R, .num p]) s fun v w _ =>
      v = .undefined ∧
      Frame ⟨[], [(R, .str "pendingLanes"), (R, .str "suspendedLanes"), (R, .str "pingedLanes"),
        (R, .str "warmLanes")], false⟩ s w ∧
      s.fuel ≤ w.fuel + 1 ∧
      (w.objEntry R).props.get? (.str "pendingLanes") = some (.data (.num (numberBinOp .bitOr pl p)) true pe pc) ∧
      (w.objEntry R).props.get? (.str "suspendedLanes") = some (.data (.num (F64.fin false 0 (-1074))) true ue uc) ∧
      (w.objEntry R).props.get? (.str "pingedLanes") = some (.data (.num (F64.fin false 0 (-1074))) true ie ic) ∧
      (w.objEntry R).props.get? (.str "warmLanes") = some (.data (.num (F64.fin false 0 (-1074))) true we wc) := by
  apply wp_callGen MRUGen.fn0_eq (by decide) hlt hk (by omega) hcls hmode
    (by rw [hcode]; rfl) (by rw [hcode]; rfl) (simple d hcode) (by rw [hcode]; rfl) (by rw [hcode]; rfl)
  have hpn : d.code.info.fdi.paramNames = #[JSStr.ofString "root", JSStr.ofString "updateLane"] := by rw [hcode]; rfl
  have hv : d.code.info.fdi.varNames = #[] := by rw [hcode]; rfl
  have hl : FDI.lexDecls d = #[] := by simp [FDI.lexDecls, hcode, MRUGen.fn0_func, Func.info]
  have ha : d.code.isAsync = false := by rw [hcode]; rfl
  clear hcode
  simp only [MRUGen.fn0]
  js [hpn, hv, hl, ha, hp, hR, hRk, hRp, hRs, hRi, hRw, FDI.fdiCtx, Sem.inner]
  all_goals (try apply And.intro)
  all_goals (try apply And.intro)
  all_goals first | rfl | omega | frame_go' [*]

end

/-- The premise holds for a click's lane (`SyncLane` = 2; the idle lane is 268435456). -/
example : isStrictlyEqual (.num (F64.fin false 4503599627370496 (-24))) (.num (F64.fin false 4503599627370496 (-51))) =
    false := by decide

end ReactMarkRoot
