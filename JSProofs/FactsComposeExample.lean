import JSProofs.FactsCompose
import JSProofs.FactsFormExample

/-! `facts_compose` on commitBeforeMutationEffects: its hasSelectionCapabilities contract by `hsc_spec`, its walk's
completion by `cbmc_root`. -/

namespace ReactBeforeMutation

open Logic in
facts_compose cbm_comp := cbm_spec
  | hHSC => ReactSelection.hsc_spec
  | hCCC => cbmc_root with u_d.env = d.env by
      have he := hob.get.2
      rintro v w' h' ⟨rfl, hfu, rfl, hF, bm, hd', ⟨bd', hb', hv'⟩, -⟩
      rw [he] at hF hd'
      refine ⟨rfl, hfu, rfl, hF, frame_then_sub ‹Frame (FB _) _ _› hF (fun p hp => by simp at hp; simp [hp, FB]) rfl rfl, ?_⟩
      intro bm' o' hd''
      rw [hd'] at hd''
      cases hd''
      exact ⟨bd', hb', hv'⟩

#check @cbm_comp

end ReactBeforeMutation
