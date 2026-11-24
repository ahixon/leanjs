import JSProofs.Facts

/-! Facts through a frame, and a written fact not kept: the checks `rfl`. -/
open ES Logic

-- A spec's premises over three objects R, X, F and a record g, and a callee footprint writing X.child and g's "n".
example (R X F : ObjId) (g : EnvId) (v c : Value) (s w : State) (oG : Option EnvId)
    (hd : [R, X, F].Nodup)
    (hF : Frame (SFoot.eval ⟨[R, X, F], [g]⟩ ⟨[(0, JSStr.ofString "n")], [(1, .str (JSStr.ofString "child"))], false⟩) s w)
    (h : Facts.holds (a := ⟨[R, X, F], [g]⟩)
      [.prop 0 (.str (JSStr.ofString "current")) (some (.data (.obj X) true false false)),
       .prop 1 (.str (JSStr.ofString "memoizedState")) (some (.data v true true true)),
       .kind 2 .ordinary,
       .bind 0 oG (JSStr.ofString "m") (fun b => ∃ bd, b = some bd ∧ bd.value = some c)] s) :
    (w.objEntry R).props.get? (.str (JSStr.ofString "current")) = some (.data (.obj X) true false false) ∧
    (w.objEntry X).props.get? (.str (JSStr.ofString "memoizedState")) = some (.data v true true true) := by
  have h' := Facts.frame ⟨hd, by simp⟩ hF rfl h
  exact ⟨(Facts.get h' 0 (by simp)).2, (Facts.get h' 1 (by simp)).2⟩

-- A fact the footprint writes is not kept.
example (R X F : ObjId) (g : EnvId) :
    Facts.apart (a := ⟨[R, X, F], [g]⟩) ⟨[], [(1, .str (JSStr.ofString "child"))], false⟩
      [.prop 1 (.str (JSStr.ofString "child")) none] = false := rfl
