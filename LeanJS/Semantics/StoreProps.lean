/-
  Properties of the mutable store (heap).
  Pure lemmas about Store.alloc, Store.read, and Store.write.
-/
import LeanJS.Semantics.Value

namespace LeanJS.Semantics

open LeanJS.IR

private theorem Array.getElem!_of_lt {α : Type} [Inhabited α] (a : Array α) (i : Nat)
    (h : i < a.size) : a[i]! = a[i] := by
  simp only [getElem!, decidableGetElem?, dif_pos h]

private theorem Array.getElem!_push_lt {α : Type} [Inhabited α] (a : Array α) (v : α) (i : Nat)
    (h : i < a.size) : (a.push v)[i]! = a[i]! := by
  have hlt : i < (a.push v).size := by simp [Array.size_push]; omega
  simp only [getElem!_of_lt _ _ hlt, getElem!_of_lt _ _ h]
  exact Array.getElem_push_lt a v i h

private theorem Array.getElem!_push_eq {α : Type} [Inhabited α] (a : Array α) (v : α) :
    (a.push v)[a.size]! = v := by
  have hlt : a.size < (a.push v).size := by simp [Array.size_push]
  simp only [getElem!_of_lt _ _ hlt]
  exact Array.getElem_push_eq a v

theorem Store.alloc_read (store : Store) (v : IRValue) :
    let (s', loc) := store.alloc v
    s'.read loc = some v := by
  unfold Store.alloc Store.read
  simp [Array.size_push, Array.getElem!_push_eq]

theorem Store.alloc_preserves (store : Store) (v : IRValue) (loc : Loc)
    (h : loc.n < store.cells.size) :
    let (s', _) := store.alloc v
    s'.read loc = store.read loc := by
  unfold Store.alloc Store.read
  have hlt : loc.n < store.cells.size + 1 := by omega
  simp [Array.size_push, hlt, h, Array.getElem!_push_lt _ _ _ h]

theorem Store.alloc_increases_size (store : Store) (v : IRValue) :
    let (s', _) := store.alloc v
    s'.cells.size = store.cells.size + 1 := by
  unfold Store.alloc
  simp [Array.size_push]

theorem Store.alloc_loc (store : Store) (v : IRValue) :
    (store.alloc v).2 = Loc.mk store.cells.size := by
  unfold Store.alloc
  rfl

/-- A store extends another if every existing cell is preserved -/
def StoreExtends (s1 s2 : Store) : Prop :=
  s1.cells.size ≤ s2.cells.size ∧
  ∀ (loc : Loc), loc.n < s1.cells.size → s2.read loc = s1.read loc

theorem StoreExtends.refl (s : Store) : StoreExtends s s :=
  ⟨Nat.le_refl _, fun _ _ => rfl⟩

theorem StoreExtends.trans {s1 s2 s3 : Store}
    (h1 : StoreExtends s1 s2) (h2 : StoreExtends s2 s3) : StoreExtends s1 s3 :=
  ⟨Nat.le_trans h1.1 h2.1, fun loc hloc => by
    rw [h2.2 loc (Nat.lt_of_lt_of_le hloc h1.1)]; exact h1.2 loc hloc⟩

/-- Allocation extends the store -/
theorem StoreExtends.alloc (s : Store) (v : IRValue) : StoreExtends s (s.alloc v).1 :=
  ⟨by have := Store.alloc_increases_size s v; simp_all,
   fun loc hloc => Store.alloc_preserves s v loc hloc⟩

end LeanJS.Semantics
