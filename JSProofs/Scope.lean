import JSProofs.FDI

/-!
# Identifier lookup through a scope chain, as a function on the state (zippy docs/react-proofs.md)

`lookup s k e n` walks declarative and function records from `e` outwards (at most `k` of them) and returns the
first binding of `n`'s value. Where it finds an initialized binding, `identValue` (what reading an identifier does)
returns that value and changes nothing (`identValue_of_lookup`): so a proof reads a closure's variable — React's
module-level `executionContext`, `workInProgressRoot`, … — by computing `lookup` on the state's records, not by a
lemma per lookup. `resolve` is the same walk for ResolveBinding (references: calls, assignments, `typeof`).
-/

open ES ES.M
open Std (HashMap)

namespace Scope

/-- The value of `n` in the first declarative or function record of the chain from `e` that binds it (`none`: not
found within `k` records, another kind of record reached first, or uninitialized). -/
def lookup (s : State) : Nat → EnvId → JSStr → Option Value
  | 0, _, _ => none
  | k + 1, e, n =>
    if e < s.envs.size then
      match s.envEntry e with
      | .decl b o | .func b o .. =>
        match b[n]? with
        | some bd => bd.value
        | none => match o with
          | some o => lookup s k o n
          | none => none
      | _ => none
    else none

/-- One step of `identValue`'s walk (its loop body). -/
def identBody (n : JSStr) (strict : Bool) (e : EnvId) : M (EnvId ⊕ Value) := do
  let r ← readEnv e fun ev => match ev with
    | .decl b o | .func b o .. => match b.get? n with
      | some bd => Sum.inr (Sum.inl bd.value)
      | none => match o with
        | some o => Sum.inl o
        | none => Sum.inr (Sum.inr ())
    | _ => Sum.inr (Sum.inr ())
  match r with
  | .inl o => return .inl o
  | .inr (.inl (some v)) => return .inr v
  | .inr (.inl none) => tdzError n
  | .inr (.inr ()) => return .inr (← getRefValue (← resolveBinding e n strict))

theorem identValue_eq (e : EnvId) (n : JSStr) (strict : Bool) :
    identValue e n strict = M.repeatFrom e (identBody n strict) := rfl

/-- The bindings and outer record of a declarative or function record. -/
def declLike? : Env → Option (HashMap JSStr Binding × Option EnvId)
  | .decl b o | .func b o .. => some (b, o)
  | _ => none

theorem identBody_entry (n : JSStr) (strict : Bool) (e : EnvId) (s : State) (he : e < s.envs.size)
    (bm : HashMap JSStr Binding) (o : Option EnvId) (hd : declLike? (s.envEntry e) = some (bm, o)) :
    identBody n strict e s = (match (match bm.get? n with
        | some bd => Sum.inr (Sum.inl bd.value)
        | none => match o with
          | some o => Sum.inl o
          | none => Sum.inr (Sum.inr ())) with
      | .inl o => return .inl o
      | .inr (.inl (some v)) => return .inr v
      | .inr (.inl none) => tdzError n
      | .inr (.inr ()) => return .inr (← getRefValue (← resolveBinding e n strict)) : M (EnvId ⊕ Value)) s := by
  simp only [identBody, M.bind_eq, M.bind_apply, readEnv_entry e _ s he, M.bindRes_ok]
  cases hen : s.envEntry e <;> rw [hen] at hd <;> simp [declLike?] at hd <;> obtain ⟨rfl, rfl⟩ := hd <;> rfl

/-- The record binds `n`, initialized: the walk ends with its value. -/
theorem identBody_found (n : JSStr) (strict : Bool) (e : EnvId) (s : State) (he : e < s.envs.size)
    (bm : HashMap JSStr Binding) (o : Option EnvId) (hd : declLike? (s.envEntry e) = some (bm, o))
    (bd : Binding) (v : Value) (hb : bm[n]? = some bd) (hv : bd.value = some v) :
    identBody n strict e s = .ok (.inr v) s := by
  rw [identBody_entry n strict e s he bm o hd]
  simp [HashMap.get?_eq_getElem?, hb, hv]; rfl

/-- The record does not bind `n`: on to its outer record. -/
theorem identBody_outer (n : JSStr) (strict : Bool) (e : EnvId) (s : State) (he : e < s.envs.size)
    (bm : HashMap JSStr Binding) (o : EnvId) (hd : declLike? (s.envEntry e) = some (bm, some o))
    (hb : bm[n]? = none) :
    identBody n strict e s = .ok (.inl o) s := by
  rw [identBody_entry n strict e s he bm (some o) hd]
  simp [HashMap.get?_eq_getElem?, hb]; rfl

theorem lookup_succ (s : State) (k : Nat) (e : EnvId) (n : JSStr) :
    lookup s (k + 1) e n = if e < s.envs.size then
      (match declLike? (s.envEntry e) with
        | some (bm, o) => match bm[n]? with
          | some bd => bd.value
          | none => match o with
            | some o => lookup s k o n
            | none => none
        | none => none) else none := by
  simp only [lookup]
  split <;> try rfl
  cases s.envEntry e <;> rfl

/-- **Reading an identifier** that `lookup` finds within the loop's bound: its value, nothing changed. -/
theorem loop_identBody (s : State) (n : JSStr) (strict : Bool) (v : Value) :
    ∀ (k : Nat) (e : EnvId) (b : Nat), lookup s k e n = some v → k ≤ b →
      M.loop (identBody n strict) b e s = .ok v s := by
  intro k
  induction k with
  | zero => intro e b h; simp [lookup] at h
  | succ k ih =>
    intro e b h hb
    obtain ⟨b, rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
    rw [lookup_succ] at h
    by_cases he : e < s.envs.size
    · simp only [he, ↓reduceIte] at h
      cases hd : declLike? (s.envEntry e) with
      | none => rw [hd] at h; simp at h
      | some p =>
        obtain ⟨bm, o⟩ := p
        rw [hd] at h
        simp only at h
        cases hbn : bm[n]? with
        | some bd =>
          rw [hbn] at h
          simp only at h
          simp only [M.loop, identBody_found n strict e s he bm o hd bd v hbn h, M.loopRes_inr]
        | none =>
          rw [hbn] at h
          cases o with
          | none => simp at h
          | some o =>
            simp only at h
            simp only [M.loop, identBody_outer n strict e s he bm o hd hbn, M.loopRes_inl]
            exact ih o b h (by omega)
    · simp [he] at h

/-- **`identValue`** of a name `lookup` finds (with no more records walked than the fuel). -/
theorem identValue_of_lookup (s : State) (k : Nat) (e : EnvId) (n : JSStr) (strict : Bool) (v : Value)
    (h : lookup s k e n = some v) (hk : k ≤ s.fuel) : identValue e n strict s = .ok v s := by
  rw [identValue_eq]
  exact loop_identBody s n strict v k e s.fuel h hk

/-! ## ResolveBinding -/

/-- The first declarative or function record of the chain from `e` that binds `n`. -/
def resolve (s : State) : Nat → EnvId → JSStr → Option EnvId
  | 0, _, _ => none
  | k + 1, e, n =>
    if e < s.envs.size then
      match declLike? (s.envEntry e) with
      | some (bm, o) =>
        if bm.contains n then some e
        else match o with
          | some o => resolve s k o n
          | none => none
      | none => none
    else none

/-- One step of ResolveBinding's walk. -/
def resolveBody (n : JSStr) (strict : Bool) (e : Option EnvId) : M (Option EnvId ⊕ Ref) := do
  match e with
  | none => return .inr (.env none n strict)
  | some e =>
    if ← hasBinding e n then return .inr (.env (some e) n strict)
    return .inl (← readEnv e Env.outer)

theorem resolveBinding_eq (e : EnvId) (n : JSStr) (strict : Bool) :
    resolveBinding e n strict = M.repeatFrom (some e) (resolveBody n strict) := rfl

theorem declLike_isDeclLike {ev : Env} {bm : HashMap JSStr Binding} {o : Option EnvId}
    (h : declLike? ev = some (bm, o)) : ev.isDeclLike = true ∧ ev.bindingsMap = bm ∧ ev.outer = o := by
  cases ev <;> simp [declLike?] at h <;> obtain ⟨rfl, rfl⟩ := h <;> simp [Env.isDeclLike, Env.bindingsMap, Env.outer]

theorem loop_resolveBody (s : State) (n : JSStr) (strict : Bool) (e' : EnvId) :
    ∀ (k : Nat) (e : EnvId) (b : Nat), resolve s k e n = some e' → k ≤ b →
      M.loop (resolveBody n strict) b (some e) s = .ok (.env (some e') n strict) s := by
  intro k
  induction k with
  | zero => intro e b h; simp [resolve] at h
  | succ k ih =>
    intro e b h hb
    obtain ⟨b, rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
    simp only [resolve] at h
    by_cases he : e < s.envs.size
    · simp only [he, ↓reduceIte] at h
      cases hd : declLike? (s.envEntry e) with
      | none => rw [hd] at h; simp at h
      | some p =>
        obtain ⟨bm, o⟩ := p
        rw [hd] at h
        obtain ⟨hdl, hbm, ho⟩ := declLike_isDeclLike hd
        have hhas := hasBinding_declLike e n s he hdl
        rw [hbm] at hhas
        simp only at h
        by_cases hc : bm.contains n = true
        · simp only [hc, ↓reduceIte, Option.some.injEq] at h
          subst h
          simp [M.loop, resolveBody, M.bind_eq, M.bind_apply, hhas, hc]; rfl
        · simp only [hc, Bool.false_eq_true, ↓reduceIte] at h
          cases o with
          | none => simp at h
          | some o =>
            simp only at h
            have hout : readEnv e Env.outer s = .ok (some o) s := by
              rw [readEnv_entry e _ s he, ho]
            simp only [M.loop, resolveBody, M.bind_eq, M.bind_apply, hhas, hc, M.bindRes_ok]
            simp only [Bool.false_eq_true, ↓reduceIte, M.bind_apply, hout, M.bindRes_ok, FDI.pure_app,
              M.loopRes_inl]
            exact ih o b h (by omega)
    · simp [he] at h

/-- **ResolveBinding** of a name `resolve` finds: an environment reference to that record, nothing changed. -/
theorem resolveBinding_of_resolve (s : State) (k : Nat) (e : EnvId) (n : JSStr) (strict : Bool) (e' : EnvId)
    (h : resolve s k e n = some e') (hk : k ≤ s.fuel) :
    resolveBinding e n strict s = .ok (.env (some e') n strict) s := by
  rw [resolveBinding_eq]
  exact loop_resolveBody s n strict e' k e s.fuel h hk

/-- GetValue of a reference to an initialized binding of a declarative or function record. -/
theorem getRefValue_env (s : State) (e : EnvId) (n : JSStr) (strict : Bool) (he : e < s.envs.size)
    (bm : HashMap JSStr Binding) (o : Option EnvId) (hd : declLike? (s.envEntry e) = some (bm, o))
    (bd : Binding) (v : Value) (hb : bm[n]? = some bd) (hv : bd.value = some v) :
    getRefValue (.env (some e) n strict) s = .ok v s := by
  simp only [getRefValue, getBindingValue, M.bind_eq, M.bind_apply, readEnv_entry e _ s he, M.bindRes_ok, id]
  cases hen : s.envEntry e <;> rw [hen] at hd <;> simp [declLike?] at hd <;> obtain ⟨rfl, rfl⟩ := hd <;>
    obtain ⟨bv, bm', bs, bdl⟩ := bd <;> simp at hv <;> subst hv <;>
    simp [HashMap.get?_eq_getElem?, hb] <;> rfl

/- The walks are computed by rewriting (`lookup_succ`, `resolve`'s equations), never by `whnf`: evaluating them
symbolically through a function body's nested states is what made goals with a pending lookup expensive to look at
(any tactic that inspects such a goal reduces it). -/
attribute [irreducible] lookup resolve

end Scope
