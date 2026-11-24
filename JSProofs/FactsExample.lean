import JSProofs.FactsForm

/-! Facts through a frame: those whose places the footprint misses, decided by `facts_apart`. -/

open ES Logic

-- Premises over objects R, X and a record g; a callee's footprint writes X.child and g's "n".
example (R X F : ObjId) (g : EnvId) (v c : Value) (s w : State) (oG : Option EnvId) (hRX : R ≠ X)
    (hF : Frame ⟨[(g, JSStr.ofString "n")], [(X, .str (JSStr.ofString "child"))], false⟩ s w)
    (h : Facts.holds
      [.prop R (.str (JSStr.ofString "current")) (some (.data (.obj X) true false false)),
       .prop X (.str (JSStr.ofString "memoizedState")) (some (.data v true true true)),
       .kindP F (· = .ordinary),
       .bind g oG (JSStr.ofString "m") (fun b => ∃ bd, b = some bd ∧ bd.value = some c)] s) :
    (w.objEntry R).props.get? (.str (JSStr.ofString "current")) = some (.data (.obj X) true false false) ∧
    (w.objEntry X).props.get? (.str (JSStr.ofString "memoizedState")) = some (.data v true true true) := by
  have h' := Facts.frame hF (by facts_apart; exact ⟨by simp [hRX], by simp⟩) h
  exact ⟨(Facts.get h' 0 (by simp)).2, (Facts.get h' 1 (by simp)).2⟩
