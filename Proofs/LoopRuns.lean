import Proofs.Nested

/-!
# The loop rule for loops whose iterations make calls

`loop_runs`: as `M.loop_inv`, but each iteration only *runs* (`Nested.Runs`) to its result, its call requests
answered by the driver one level deeper.
-/

open ES

namespace Nested

theorem runs_loopRes_inl (eng : Engine) {σ α : Type} (next : σ → State → Res α) :
    ∀ (n : Nat) (r : Res (σ ⊕ α)) (st : σ) (w1 : State), Runs eng n r (.inl st) w1 →
      ∀ (a : α) (w2 : State), Runs eng n (next st w1) a w2 → Runs eng n (M.loopRes next r) a w2 := by
  intro n r st w1 h
  generalize hb : (Sum.inl st : σ ⊕ α) = b at h
  induction h with
  | ok n b w => intro a w2 hk; subst hb; exact hk
  | call n f t args w K x w1 b w' h hk ih =>
    intro a w2 hk2; exact .call n f t args w _ x w1 a w2 h (ih hb a w2 hk2)
  | callErr n f t args w K e w1 b w' h hk ih =>
    intro a w2 hk2; exact .callErr n f t args w _ e w1 a w2 h (ih hb a w2 hk2)

theorem runs_loopRes_inr (eng : Engine) {σ α : Type} (next : σ → State → Res α) :
    ∀ (n : Nat) (r : Res (σ ⊕ α)) (a : α) (w : State), Runs eng n r (.inr a) w → Runs eng n (M.loopRes next r) a w := by
  intro n r a w h
  generalize hb : (Sum.inr a : σ ⊕ α) = b at h
  induction h with
  | ok n b w => subst hb; exact .ok n a w
  | call n f t args w K x w1 b w' h hk ih => exact .call n f t args w _ x w1 a w' h (ih hb)
  | callErr n f t args w K e w1 b w' h hk ih => exact .callErr n f t args w _ e w1 a w' h (ih hb)

/-- **The loop rule, with calls.** An invariant `I` holds before each iteration; each iteration runs either to
`inl` (the invariant again, the measure `V` smaller) or to `inr` with a result satisfying `Q`. -/
theorem loop_runs (eng : Engine) (d : Nat) {α σ : Type} (body : σ → M (σ ⊕ α)) (I : σ → State → Prop)
    (Q : α → State → Prop) (V : σ → State → Nat)
    (hstep : ∀ st s, I st s →
      (∃ st' s', Runs eng d (body st s) (.inl st') s' ∧ I st' s' ∧ V st' s' < V st s) ∨
      (∃ a s', Runs eng d (body st s) (.inr a) s' ∧ Q a s')) :
    ∀ (n : Nat) (st : σ) (s : State), I st s → V st s < n →
      ∃ a s', Runs eng d (M.loop body n st s) a s' ∧ Q a s' := by
  intro n
  induction n with
  | zero => intro st s _ h; omega
  | succ n ih =>
    intro st s hI hV
    rcases hstep st s hI with ⟨st', s', hb, hI', hV'⟩ | ⟨a, s', hb, hQ⟩
    · obtain ⟨a, s'', hl, hQ⟩ := ih st' s' hI' (by omega)
      exact ⟨a, s'', runs_loopRes_inl eng _ d _ st' s' hb a s'' hl, hQ⟩
    · exact ⟨a, s', runs_loopRes_inr eng _ d _ a s' hb, hQ⟩

/-- **Three statements**: the first completes normally, the second runs (its calls answered) to a normal
completion, the third returns `v`: the list runs to that return. -/
theorem stmts3_runs (eng : Engine) (d : Nat) (a b c : Sem.CStmt) (ctx : Ctx) (w w1 w2 w3 : State)
    (ra rb : Option Value) (v : Value) (ha : a ctx w = .ok (.normal ra) w1)
    (hb : Runs eng d (b ctx w1) (.normal rb) w2) (hc : c ctx w2 = .ok (.ret v) w3) (hf : 4 ≤ w.fuel) :
    Runs eng d (Sem.stmts #[a, b, c] ctx w) (.ret v) w3 := by
  obtain ⟨j, hj⟩ : ∃ j, w.fuel = j + 4 := ⟨w.fuel - 4, by omega⟩
  simp only [Sem.stmts, M.repeatFrom, hj, M.loop]
  simp only [List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.zero_lt_succ,
    ↓reduceDIte, List.getElem_toArray, List.getElem_cons_zero, M.bind_eq, M.bind_apply, ha, M.bindRes_ok, pure,
    M.pure, M.loopRes_inl, M.loop]
  refine runs_loopRes_inl eng _ d _ (2, rb <|> (ra <|> none)) w2 ?_ _ _ ?_
  · refine runs_bind eng _ d _ _ w2 hb _ w2 ?_
    exact .ok _ _ _
  · simp [M.loop, M.bind_eq, M.bind_apply, hc, pure, M.pure, M.loopRes_inr]
    exact .ok _ _ _

end Nested
