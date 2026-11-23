import JSProofs.Frame
import JSProofs.Object

/-!
# The props object a render creates (zippy docs/react-proofs.md)

The counter's render makes its button's new props, `{ onClick, children }`. The commit reads it whole (its keys, in
order, for `diffProperties`), so its facts travel up the render's specs together, as `NewProps`, carried through
each later frame whose footprint has none of its properties (`NewProps.frame`).
-/

open ES Logic

namespace ReactNewProps

/-- `C` is the props object `{ onClick: F, children: t }`, made from an object literal with prototype `OP`. -/
def NewProps (w : State) (C F OP : ObjId) (t : JSStr) : Prop :=
  C < w.heap.size ∧ (w.objEntry C).kind = .ordinary ∧ (w.objEntry C).proto = .obj OP ∧
  (w.objEntry C).props.keys = #[.str (JSStr.ofString "onClick"), .str (JSStr.ofString "children")] ∧
  (w.objEntry C).props.get? (.str (JSStr.ofString "onClick")) = some (.data (.obj F) true true true) ∧
  (w.objEntry C).props.get? (.str (JSStr.ofString "children")) = some (.data (.str t) true true true) ∧
  (w.objEntry C).props.get? (.str (JSStr.ofString "hasOwnProperty")) = none ∧
  (w.objEntry C).props.get? (.str (JSStr.ofString "ref")) = none ∧ C < F

theorem NewProps.frame {fp : Footprint} {s w : State} {C F OP : ObjId} {t : JSStr} (hF : Frame fp s w)
    (h : NewProps s C F OP t) (hn : ∀ k, (C, k) ∉ fp.props) : NewProps w C F OP t := by
  have he := hF.obj_eq C h.1 hn
  unfold NewProps; rw [he]; exact ⟨Nat.lt_of_lt_of_le h.1 hF.heap_le, h.2⟩

/-- The keys of an object literal with two (different) properties, in order. -/
theorem keys_two (k1 k2 : PropKey) (p1 p2 : Property) (h : k1 ≠ k2) :
    ((({} : PropMap).insert k1 p1).insert k2 p2).keys = #[k1, k2] := by
  have h1 : ({} : PropMap).map.get? k1 = none := by simp
  have h2 : (({} : PropMap).insert k1 p1).map.get? k2 = none := by
    simp [PropMap.insert, h]
  simp only [PropMap.keys, PropMap.insert, h1, h2]
  simp [Std.HashMap.size_insert, h]

end ReactNewProps
