import JSProofs.FactsComposeRoot
import JSProofs.ReactFlushMutation

/-! flushMutationEffects with the click's mutation pass, composed in Lean: `commitMutationEffectsOnFiber(root, …)` by the root's commit, `cme_root_comp`. -/

facts_form ReactFlushMutation.fme_spec

namespace ReactFlushMutation
open ES Logic

facts_compose fme_comp {dom : ObjId} {kP : JSStr} {R1 R2 : State → σ → Prop} := fme_spec
    (n := n + 8) (KC := 5000)
    (fpC := (ReactCommitRoot.F0 d.env).union (Footprint.union
      ⟨[(d.env, JSStr.ofString "offscreenDirectParentIsHidden")], [], false⟩
      ⟨[(d.env, JSStr.ofString "viewTransitionMutationContext")], [(dom, .str kP)], false⟩))
    (PC := fun _ h => (∃ w0 h0, R1 w0 h0) ∧ (∃ w0, R2 w0 h) ∧ HI h)
  | hC => ReactCommitRoot.cme_root_comp (dom := dom) (kP := kP) (R1 := R1) (R2 := R2) with u_d.env = d.env by
      have he := hob.get.2
      rintro v w' h' ⟨rfl, hfu, hP, hF⟩
      rw [he] at hF
      exact ⟨rfl, by omega, hP, hP.2.2, hF⟩

end ReactFlushMutation
