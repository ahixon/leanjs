import JSProofs.Builtins
import JSProofs.Object
import JSProofs.Loops2

/-!
# `Object.prototype.hasOwnProperty` (zippy docs/react-proofs.md)

`o.hasOwnProperty(k)` for a plain object and a string key: whether `o` has an own property `k`, nothing changed.
React's `updateProperties` asks it of the old and new props for each key.
-/

open ES ES.M HostRuns
open Std (HashMap)

namespace Logic

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ}

/-- **`o.hasOwnProperty(k)`**, `o` plain, `k` a string: whether `o`'s properties have `k`; nothing changed, one step
of fuel. -/
theorem hasOwn_spec {n : Nat} {h : σ} {fo : ObjId} {bd : BuiltinData} {o : ObjId} {k : JSStr} {s : State}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .builtin bd)
    (hfn : eng.builtins[bd.id]? = some objProtoHasOwnProperty) (hf : s.fuel ≠ 0)
    (ho : o < s.heap.size) (hok : (s.objEntry o).kind.isPlain = true) :
    WP eng answer n h (callImpl eng (.obj fo) (.obj o) #[.str k]) s fun v w h' =>
      v = .bool ((s.objEntry o).props.get? (.str k)).isSome ∧ Frame {} s w ∧ s.fuel ≤ w.fuel + 1 ∧
        w = s.withFuel (s.fuel - 1) ∧ h' = h := by
  rw [wp_iff_wpr, callImpl_builtin eng fo bd objProtoHasOwnProperty (.obj o) _ s hlt hk hfn hf, ← wp_iff_wpr]
  apply wp_inCallee
  refine wp_of_eq (a := ?a) (w := ?w) ?eq ?post
  case eq =>
    simp [objProtoHasOwnProperty, arg, hasOwnProperty, toPropertyKey, toObject, toObj, M.bind_apply, Pure.pure, M.pure]
    rw [Obj'.getOwnProperty_entry o (.str k) _ (by exact ho) (by exact hok)]
    rfl
  case post => exact ⟨rfl, frame_same rfl rfl rfl rfl, by first | omega | (simp; omega) | simp, rfl, rfl⟩

end

end Logic
