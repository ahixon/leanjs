import Proofs.State

/-!
# Loops as folds

`M.foldArr` (a bounded loop, constant stack) is `M.foldList` over the array's list: proofs unroll
the fold on literal arrays with `foldList_cons`.
-/

namespace ES.M

variable {α β σ γ : Type}

/-- Folding a list in the monad, element by element. -/
def foldList : List α → β → (β → α → M β) → M β
  | [], b, _ => M.pure b
  | a :: l, b, f => fun s => bindRes (fun b' => foldList l b' f) (f b a s)

@[simp] theorem foldList_nil (b : β) (f : β → α → M β) (s : State) :
    foldList [] b f s = .ok b s := Eq.trans rfl rfl

@[simp] theorem foldList_cons (a : α) (l : List α) (b : β) (f : β → α → M β) (s : State) :
    foldList (a :: l) b f s = bindRes (fun b' => foldList l b' f) (f b a s) := Eq.trans rfl rfl

/-- Continuing a loop after a step that returns `inl (g b)` is binding the step's result. -/
theorem loopRes_bindRes (next : σ → State → Res γ) (g : β → σ) (r : Res β) :
    loopRes next (bindRes (fun b s => .ok (.inl (g b)) s) r) = bindRes (fun b s => next (g b) s) r := by
  induction r with
  | ok a s => rfl
  | err e s => rfl
  | halt m s => rfl
  | req r s k ih =>
    simp only [bindRes, loopRes]
    congr 1
    funext o s'
    exact ih o s'

/-- `loopRes_bindRes` for foldArr's step (the next index paired with the accumulator). -/
theorem loopRes_bindRes_pair (next : Nat × β → State → Res γ) (j : Nat) (r : Res β) :
    loopRes next (bindRes (fun b s => .ok (.inl (j, b)) s) r) = bindRes (fun b s => next (j, b) s) r :=
  loopRes_bindRes next (fun b => (j, b)) r

theorem bindRes_congr (f g : β → M γ) (r : Res β) (h : ∀ b s, f b s = g b s) :
    bindRes f r = bindRes g r := by
  have : f = g := funext fun b => funext fun s => h b s
  rw [this]

/-- foldArr's loop body. -/
def foldBody (xs : Array α) (f : β → α → M β) (st : Nat × β) : M (Nat × β ⊕ β) :=
  if h : st.1 < xs.size then
    fun s => bindRes (fun acc' s => .ok (.inl (st.1 + 1, acc')) s) (f st.2 xs[st.1] s)
  else M.pure (.inr st.2)

theorem foldArr_eq_loop (xs : Array α) (init : β) (f : β → α → M β) (s : State) :
    foldArr xs init f s = loop (foldBody xs f) (xs.size + 1) (0, init) s := rfl

theorem foldBody_lt (xs : Array α) (f : β → α → M β) (i : Nat) (acc : β) (s : State) (h : i < xs.size) :
    foldBody xs f (i, acc) s = bindRes (fun acc' s => .ok (.inl (i + 1, acc')) s) (f acc xs[i] s) := by
  simp [foldBody, h]

theorem foldBody_ge (xs : Array α) (f : β → α → M β) (i : Nat) (acc : β) (s : State) (h : ¬ i < xs.size) :
    foldBody xs f (i, acc) s = .ok (.inr acc) s := by
  simp [foldBody, h, M.pure]

/-- foldArr's loop from index `i` (with enough bound) is the fold of the rest of the list. -/
theorem foldArr_loop (xs : Array α) (f : β → α → M β) :
    ∀ (m i : Nat) (acc : β) (s : State) (n : Nat), xs.size - i = m → i ≤ xs.size → n ≥ m + 1 →
    loop (foldBody xs f) n (i, acc) s = foldList (xs.toList.drop i) acc f s := by
  intro m
  induction m with
  | zero =>
    intro i acc s n hm hi hn
    have hi' : i = xs.size := by omega
    subst hi'
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    have hd : xs.toList.drop xs.size = [] := by simp
    simp only [loop]
    rw [foldBody_ge xs f _ acc s (by omega), hd]
    rfl
  | succ m ih =>
    intro i acc s n hm hi hn
    have hlt : i < xs.size := by omega
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    have hdrop : xs.toList.drop i = xs[i] :: xs.toList.drop (i + 1) := by
      rw [List.drop_eq_getElem_cons (by simpa using hlt)]
      simp
    simp only [loop]
    rw [foldBody_lt xs f i acc s hlt, loopRes_bindRes_pair, hdrop, foldList_cons]
    apply bindRes_congr
    intro b s'
    exact ih (i + 1) b s' n' (by omega) (by omega) (by omega)

/-- `foldArr` is `foldList` over the array's elements. -/
theorem foldArr_eq (xs : Array α) (init : β) (f : β → α → M β) :
    foldArr xs init f = foldList xs.toList init f := by
  funext s
  rw [foldArr_eq_loop]
  exact foldArr_loop xs f xs.size 0 init s (xs.size + 1) (by omega) (by omega) (by omega)

/-- On a literal array: unrolled by `foldList_cons`. -/
@[simp] theorem foldArr_toArray (l : List α) (init : β) (f : β → α → M β) :
    foldArr l.toArray init f = foldList l init f := by
  rw [foldArr_eq]

@[simp] theorem forArr_def (xs : Array α) (f : α → M Unit) :
    forArr xs f = foldArr xs () (fun _ x => f x) := Eq.trans rfl rfl

end ES.M
