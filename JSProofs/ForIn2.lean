import JSProofs.ForIn
import JSProofs.Object

/-!
# More for-in rules (zippy docs/react-proofs.md)

A plain object's own keys (`ownPropertyKeys_plain`), a key visited before (`forIn_visited`), and a run of keys none
of which the loop visits (`forIn_hidden`: each visited before, missing, or not enumerable; e.g. all of
`Object.prototype`'s).
-/

open ES ES.M HostRuns
open Std (HashMap HashSet)

namespace Logic

theorem ownPropertyKeys_plain (o : ObjId) (s : State) (h : o < s.heap.size)
    (hk : (s.objEntry o).kind.isPlain = true) :
    Obj'.ownPropertyKeys o s = .ok (orderedKeys (s.objEntry o).props.keys) s := by
  unfold Obj'.ownPropertyKeys; rw [maxDepth_eq]
  rw [ES.ownPropertyKeys]
  simp only [M.bind_eq, M.bind_apply, objKind, readObj_entry' _ _ _ h, M.bindRes_ok]
  cases hkd : (s.objEntry o).kind <;> simp [hkd, Kind.isPlain] at hk ⊢ <;> first | rfl | exact readObj_entry' _ _ _ h

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ}

/-- **A key visited before**: skipped. -/
theorem forIn_visited {N n : Nat} {ctx : Ctx} {lhs : ForLhs} {body : Stmt} {labels : Array JSStr} {b : Nat}
    {co : ObjId} {visited : HashSet PropKey} {keys : Array PropKey} {i : Nat} {v : Value}
    {h : σ} {s : State} {Q : Compl → State → σ → Prop} (hb : 1 ≤ b) (hf : 1 ≤ s.fuel) (hi : i < keys.size)
    (hvis : visited.contains keys[i] = true)
    (hw : ForInWP eng answer N n ctx lhs body labels (b - 1) (.obj co, visited, keys, i + 1, true, v) h
      (s.withFuel (s.fuel - 1)) Q) :
    ForInWP eng answer N n ctx lhs body labels b (.obj co, visited, keys, i, true, v) h s Q := by
  refine forIn_step' hb hf ?_
  simp only [forInStep', Bool.not_true, Bool.false_eq_true, ↓reduceIte, hi, ↓reduceDIte, hvis]
  exact wp_pure hw

/-- **Keys the loop does not visit**: from key `i` to the end, each visited before, or a missing or non-enumerable
property of `co` (a plain object): the loop reaches the end of the keys, `keys.size - i` steps (and fuel) later. -/
theorem forIn_hidden {N n : Nat} {ctx : Ctx} {lhs : ForLhs} {body : Stmt} {labels : Array JSStr}
    {co : ObjId} {keys : Array PropKey} {v : Value} {h : σ} {Q : Compl → State → σ → Prop} :
    ∀ (m i b : Nat) (visited : HashSet PropKey) (s : State), keys.size = i + m → m ≤ b → m ≤ s.fuel →
      co < s.heap.size → (s.objEntry co).kind.isPlain = true →
      (∀ j (hj : j < keys.size), i ≤ j → ∀ p, (s.objEntry co).props.get? keys[j] = some p → p.enumerable = false) →
      (∀ vis', ForInWP eng answer N n ctx lhs body labels (b - m) (.obj co, vis', keys, keys.size, true, v) h
        (s.withFuel (s.fuel - m)) Q) →
      ForInWP eng answer N n ctx lhs body labels b (.obj co, visited, keys, i, true, v) h s Q := by
  intro m
  induction m with
  | zero =>
    intro i b visited s hm _ _ _ _ _ hw
    have hi : i = keys.size := by omega
    subst hi
    have := hw visited
    simpa [State.withFuel] using this
  | succ m ih =>
    intro i b visited s hm hb hf hco hk hne hw
    have hi : i < keys.size := by omega
    have hfs : (s.withFuel (s.fuel - 1)).objEntry co = s.objEntry co := rfl
    have hco' : co < (s.withFuel (s.fuel - 1)).heap.size := hco
    have hw' : ∀ vis', ForInWP eng answer N n ctx lhs body labels (b - 1 - m) (.obj co, vis', keys, keys.size, true, v)
        h ((s.withFuel (s.fuel - 1)).withFuel ((s.withFuel (s.fuel - 1)).fuel - m)) Q := by
      intro vis'
      have := hw vis'
      have e1 : b - 1 - m = b - (m + 1) := by omega
      have e2 : (s.withFuel (s.fuel - 1)).withFuel ((s.withFuel (s.fuel - 1)).fuel - m) = s.withFuel (s.fuel - (m + 1)) := by
        simp [State.withFuel]; omega
      rw [e1, e2]; exact this
    cases hv : visited.contains keys[i] with
    | true =>
      refine forIn_visited (by omega) (by omega) hi hv ?_
      exact ih (i + 1) (b - 1) visited _ (by omega) (by omega) (by simp [State.withFuel]; omega) hco' (by rw [hfs]; exact hk)
        (fun j hj hij p hp => hne j hj (by omega) p (by rw [← hfs]; exact hp)) hw'
    | false =>
      refine forIn_skip (by omega) (by omega) hi hv ?_
      refine wp_of_eq (Obj'.getOwnProperty_entry co keys[i] _ hco' (by rw [hfs]; exact hk)) ?_
      rw [hfs]
      cases hp : (s.objEntry co).props.get? keys[i] with
      | none =>
        exact ih (i + 1) (b - 1) visited _ (by omega) (by omega) (by simp [State.withFuel]; omega) hco'
          (by rw [hfs]; exact hk) (fun j hj hij p hp => hne j hj (by omega) p (by rw [← hfs]; exact hp)) hw'
      | some p =>
        refine ⟨hne i hi (Nat.le_refl _) p hp, ?_⟩
        exact ih (i + 1) (b - 1) _ _ (by omega) (by omega) (by simp [State.withFuel]; omega) hco'
          (by rw [hfs]; exact hk) (fun j hj hij p hp => hne j hj (by omega) p (by rw [← hfs]; exact hp)) hw'

end

end Logic
