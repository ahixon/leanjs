import JSProofs.FactsForm

/-! Facts through a frame: those whose places the footprint misses, decided by `facts_apart_wf`. -/

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
  have h' := Facts.frame hF (by facts_apart_wf; exact ⟨by simp [hRX], by simp⟩) h
  exact ⟨(Facts.get h' 0 (by simp)).2, (Facts.get h' 1 (by simp)).2⟩

-- `facts_apart` asks only for the distinctness it needs: here none (no key is shared) …
example (R X : ObjId) (g : EnvId) (v c : Value) (s w : State) (oG : Option EnvId)
    (hF : Frame ⟨[(g, JSStr.ofString "n")], [(X, .str (JSStr.ofString "child"))], false⟩ s w)
    (h : Facts.holds
      [.prop R (.str (JSStr.ofString "current")) (some (.data (.obj X) true false false)),
       .prop X (.str (JSStr.ofString "memoizedState")) (some (.data v true true true)),
       .bind g oG (JSStr.ofString "m") (fun b => ∃ bd, b = some bd ∧ bd.value = some c)] s) :
    (w.objEntry X).props.get? (.str (JSStr.ofString "memoizedState")) = some (.data v true true true) :=
  (Facts.get (Facts.frame hF (by facts_apart) h) 1 (by simp)).2

-- … and here `R ≠ X` (both have a "current"), from the context.
example (R X : ObjId) (s w : State) (hRX : R ≠ X)
    (hF : Frame ⟨[], [(X, .str (JSStr.ofString "current"))], false⟩ s w)
    (h : Facts.holds [.prop R (.str (JSStr.ofString "current")) (some (.data (.obj X) true false false))] s) :
    Facts.holds [.prop R (.str (JSStr.ofString "current")) (some (.data (.obj X) true false false))] w :=
  Facts.frame hF (by facts_apart) h

-- `facts_frame` keeps what a frame misses: here R's "current" (with `R ≠ X`) and g's "m", not X's "child".
example (R X : ObjId) (g : EnvId) (c : Value) (s w : State) (oG : Option EnvId) (hRX : R ≠ X)
    (hF : Frame ⟨[(g, JSStr.ofString "n")], [(X, .str (JSStr.ofString "child")), (X, .str (JSStr.ofString "current"))], false⟩ s w)
    (h : Facts.holds
      [.prop R (.str (JSStr.ofString "current")) (some (.data (.obj X) true false false)),
       .prop X (.str (JSStr.ofString "child")) (some (.data .null true true true)),
       .bind g oG (JSStr.ofString "m") (fun b => ∃ bd, b = some bd ∧ bd.value = some c)] s) :
    (w.objEntry R).props.get? (.str (JSStr.ofString "current")) = some (.data (.obj X) true false false) := by
  facts_frame h hF as h'
  exact (Facts.get h' 0 (by simp)).2
