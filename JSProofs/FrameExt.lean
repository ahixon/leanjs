import JSProofs.Frame

/-!
# Extending a frame by one whose footprint mentions new objects (zippy docs/react-proofs.md)

A frame from `s` to `u`, then one from `u` to `w` whose footprint may mention records and objects that `s` did not
have (a callee's writes to what an earlier callee allocated): a frame from `s` to `w` if the second footprint's
entries about `s`'s records and objects are in the first's.
-/

open ES

namespace Logic

theorem frame_extend' {fp fp2 : Footprint} {s u w : State} (h1 : Frame fp s u) (h2 : Frame fp2 u w)
    (hb : ∀ q ∈ fp2.binds, q.1 < s.envs.size → q ∈ fp.binds)
    (hp : ∀ q ∈ fp2.props, q.1 < s.heap.size → q ∈ fp.props) (hj : fp.jobs = false → fp2.jobs = false) :
    Frame fp s w where
  envs_le := Nat.le_trans h1.envs_le h2.envs_le
  heap_le := Nat.le_trans h1.heap_le h2.heap_le
  env_agree e he := envAgree_mono (envAgree_trans (h1.env_agree e he)
      (h2.env_agree e (Nat.lt_of_lt_of_le he h1.envs_le)))
    fun x hx => by
      rcases hx with hx | hx
      · exact hx
      · exact hb (e, x) hx he
  obj_agree o ho :=
    have h := objAgree_trans (h1.obj_agree o ho) (h2.obj_agree o (Nat.lt_of_lt_of_le ho h1.heap_le))
    ⟨h.1, h.2.1, h.2.2.1, fun k hk => h.2.2.2 k (fun hx => by
      rcases hx with hx | hx
      · exact hk hx
      · exact hk (hp (o, k) hx ho))⟩
  env_eq e he hn := by
    rw [h2.env_eq e (Nat.lt_of_lt_of_le he h1.envs_le) (fun x hx => hn x (hb (e, x) hx he)),
      h1.env_eq e he hn]
  obj_eq o ho hn := by
    rw [h2.obj_eq o (Nat.lt_of_lt_of_le ho h1.heap_le) (fun k hk => hn k (hp (o, k) hk ho)), h1.obj_eq o ho hn]
  realms_eq := h2.realms_eq.trans h1.realms_eq
  jobs_prefix := by
    obtain ⟨j1, e1⟩ := h1.jobs_prefix
    obtain ⟨j2, e2⟩ := h2.jobs_prefix
    exact ⟨j1 ++ j2, by rw [e2, e1, Array.append_assoc]⟩
  jobs_eq hj' := by rw [h2.jobs_eq (hj hj'), h1.jobs_eq hj']

end Logic
