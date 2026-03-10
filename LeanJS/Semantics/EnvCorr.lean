/-
  Environment correspondence predicates for forward simulation.

  Defines how JS/Lean environments correspond to IR environments + store,
  handling the key difference: JS mutable variables ↔ IR refs.
-/
import LeanJS.Semantics.Value

set_option autoImplicit true

namespace LeanJS.Semantics

open LeanJS.IR

/-! ## JS ↔ IR Environment Correspondence -/

/-- JS environment is just an alias for Env (same structure, different semantics) -/
abbrev JSEnv := Env

/-- Correspondence between a JS env (mutable vars stored directly) and an
    IR env + store (mutable vars stored via refs in the store).

    - `pure`: immutable variable — same value in both envs
    - `mut`: mutable variable — JS has value directly, IR has ref to store cell -/
inductive EnvCorr : JSEnv → Env → Store → Prop where
  | nil : EnvCorr .nil .nil store
  | pure : EnvCorr jenv ienv store →
           EnvCorr (jenv.extend x v) (ienv.extend x v) store
  | «mut» : EnvCorr jenv ienv store →
            store.read loc = some v →
            EnvCorr (jenv.extend x v) (ienv.extend x (.ref loc)) store

/-- Result correspondence: accounts for unit/undefined gap and store evolution -/
inductive ResultCorr : EvalResult → EvalResult → Prop where
  | val : ResultCorr (.val v s1) (.val v s2)
  | val_unit_undefined : ResultCorr (.val .unit s1) (.val .undefined s2)
  | val_undefined_unit : ResultCorr (.val .undefined s1) (.val .unit s2)
  | return_ : ResultCorr (.return_ v s1) (.return_ v s2)
  | break_ : ResultCorr (.break_ s1) (.break_ s2)
  | continue_ : ResultCorr (.continue_ s1) (.continue_ s2)
  | throw_ : ResultCorr (.throw_ v s1) (.throw_ v s2)
  | error : ResultCorr (.error msg) (.error msg)

/-! ## EnvCorr Lemmas -/

/-- Extending both envs with the same pure binding preserves correspondence -/
theorem EnvCorr.extend_pure_thm {jenv ienv : Env} {store : Store}
    (hcorr : EnvCorr jenv ienv store) (x : String) (v : IRValue) :
    EnvCorr (jenv.extend x v) (ienv.extend x v) store :=
  .pure hcorr

/-- Extending JS env with value and IR env with ref preserves correspondence -/
theorem EnvCorr.extend_mut_thm {jenv ienv : Env} {store : Store}
    (hcorr : EnvCorr jenv ienv store) (x : String) (v : IRValue) (loc : Loc)
    (hread : store.read loc = some v) :
    EnvCorr (jenv.extend x v) (ienv.extend x (.ref loc)) store :=
  .«mut» hcorr hread

/-- Empty envs correspond under any store -/
theorem EnvCorr.empty (store : Store) : EnvCorr .nil .nil store := .nil

/-! ## Lean ↔ IR Environment Correspondence -/

/-- Correspondence between Lean env and IR env + store.
    Lean mutable (do-block `let mut`) variables correspond to IR refs,
    similar to JS EnvCorr. -/
inductive LeanEnvCorr : Env → Env → Store → Prop where
  | nil : LeanEnvCorr .nil .nil store
  | pure : LeanEnvCorr lenv ienv store →
           LeanEnvCorr (lenv.extend x v) (ienv.extend x v) store
  | «mut» : LeanEnvCorr lenv ienv store →
            store.read loc = some v →
            LeanEnvCorr (lenv.extend x v) (ienv.extend x (.ref loc)) store

/-- Extending both envs with same pure binding preserves Lean correspondence -/
theorem LeanEnvCorr.extend_pure_thm {lenv ienv : Env} {store : Store}
    (hcorr : LeanEnvCorr lenv ienv store) (x : String) (v : IRValue) :
    LeanEnvCorr (lenv.extend x v) (ienv.extend x v) store :=
  .pure hcorr

/-- Extending Lean env with value and IR env with ref preserves correspondence -/
theorem LeanEnvCorr.extend_mut_thm {lenv ienv : Env} {store : Store}
    (hcorr : LeanEnvCorr lenv ienv store) (x : String) (v : IRValue) (loc : Loc)
    (hread : store.read loc = some v) :
    LeanEnvCorr (lenv.extend x v) (ienv.extend x (.ref loc)) store :=
  .«mut» hcorr hread

/-- Empty Lean envs correspond under any store -/
theorem LeanEnvCorr.empty (store : Store) : LeanEnvCorr .nil .nil store := .nil

/-! ## Store Monotonicity -/

/-- A store is an extension of another if all existing cells are preserved -/
def StoreExtends (s1 s2 : Store) : Prop :=
  s1.cells.size ≤ s2.cells.size ∧
  ∀ (loc : Loc), loc.n < s1.cells.size → s2.read loc = s1.read loc

/-- Store extension is reflexive -/
theorem StoreExtends.refl (s : Store) : StoreExtends s s :=
  ⟨Nat.le_refl _, fun _ _ => rfl⟩

/-- Store extension is transitive -/
theorem StoreExtends.trans' {s1 s2 s3 : Store}
    (h1 : StoreExtends s1 s2) (h2 : StoreExtends s2 s3) :
    StoreExtends s1 s3 := by
  constructor
  · exact Nat.le_trans h1.1 h2.1
  · intro loc hloc
    rw [h2.2 loc (Nat.lt_of_lt_of_le hloc h1.1)]
    exact h1.2 loc hloc

/-- Allocating preserves store extension -/
theorem StoreExtends.alloc (s : Store) (v : IRValue) :
    StoreExtends s (s.alloc v).1 := by
  constructor
  · unfold Store.alloc; simp [Array.size_push]
  · intro loc hloc
    sorry  -- Follows from Array.getElem_push_lt

/-- EnvCorr is preserved when the store is extended -/
theorem EnvCorr.store_mono' {jenv : JSEnv} {ienv : Env} {store store' : Store}
    (hcorr : EnvCorr jenv ienv store)
    (hpres : ∀ (loc : Loc) (v : IRValue), store.read loc = some v → store'.read loc = some v) :
    EnvCorr jenv ienv store' := by
  induction hcorr with
  | nil => exact .nil
  | pure _ ih => exact .pure (ih hpres)
  | «mut» _ hread ih =>
    exact .«mut» (ih hpres) (hpres _ _ hread)

end LeanJS.Semantics
