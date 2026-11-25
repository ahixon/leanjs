/-!
# A proposition hidden from `simp` (zippy docs/react-proofs.md, "Composition in Lean")

A spec's callee contracts are stated as `Hide (∀ w …, Frame … → WP …)` and applied as `hc.get …`. Its proof's
`js_norm [*, …]` steps then see the contract as an opaque fact: unwrapped, simp tries every contract as a rewrite rule
at every step, and a proof with several contracts in scope ran past its heartbeats. `facts_compose` unwraps it.
-/

namespace Logic

/-- `P`, which `simp [*]` does not use. -/
structure Hide (P : Prop) : Prop where
  get : P

end Logic
