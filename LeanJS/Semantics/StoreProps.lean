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

end LeanJS.Semantics
