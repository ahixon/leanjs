import Lean

/-! The simp set of the `js` tactic (`JSProofs/Auto.lean`): files add the lemmas that compute their rules' premises
with `attribute [js_simp]`. -/

register_simp_attr js_simp
