import JSProofs.FactsCompose
import JSProofs.ReactFlushLayout
import JSProofs.ReactLayoutFull

/-! flushLayoutEffects with the click's layout pass, composed in Lean: `commitLayoutEffectOnFiber(root, …)` by `ReactLayoutFull.lay_root`. -/

facts_form ReactFlushLayout.fle_spec
facts_form ReactLayoutFull.lay_root

namespace ReactFlushLayout
open ES Logic

facts_compose fle_comp := fle_spec (n := n + 8) (KC := 1840)
  | hC => ReactLayoutFull.lay_root (oG := oG) with u_d.env = d.env by
      rintro v w' h' ⟨-, hfu, hF, rfl⟩
      exact ⟨hF, by omega, rfl⟩

end ReactFlushLayout
