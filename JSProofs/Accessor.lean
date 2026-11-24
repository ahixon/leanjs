import JSProofs.ObjRules

/-!
# Reading an accessor property (zippy docs/react-proofs.md)

`o.k` where the lookup through a chain of plain objects finds an accessor with a getter: [[Get]] calls the getter
with `o` as `this` (ECMA-262 OrdinaryGet steps 4-6). The DOM's attributes on the Lean engine are such accessors on the
interfaces' prototypes, their getters built-ins answered by the host (React reads `container.nodeType`).
-/

open ES ES.M HostRuns
open Std (HashMap)

namespace Logic

/-- [[Get]] of a property the lookup finds as an accessor with getter `g`: the call of `g`. -/
theorem get_chain_accessor (s : State) (k : PropKey) (r : Value) {g sv : Value} {e c : Bool}
    (hg : g.isUndefined = false) :
    ∀ (n : Nat) (o : ObjId) (m : Nat), PlainChain s n o k → 2 * n + 1 ≤ m →
      ordLookup s n o k = some (.accessor g sv e c) →
      ES.get m o k r s = ES.call g r #[] s := by
  intro n
  induction n with
  | zero => intro o m h; simp [PlainChain] at h
  | succ n ih =>
    intro o m ⟨hlt, hk, hrest⟩ hm hl
    obtain ⟨j, rfl⟩ : ∃ j, m = j + 3 := ⟨m - 3, by omega⟩
    rw [ES.get]
    simp only [M.bind_eq, M.bind_apply, objKind, readObj_entry' _ _ _ hlt, M.bindRes_ok]
    cases hkd : (s.objEntry o).kind <;> simp [hkd, Kind.isPlain] at hk <;>
    · rw [ES.ordinaryGet]
      simp only [M.bind_eq, M.bind_apply, getOwnProperty_entry _ o k s hlt (by simp [hkd]), M.bindRes_ok]
      cases hp : (s.objEntry o).props.get? k with
      | some p =>
        simp only [ordLookup, hp, Option.some.injEq] at hl
        subst hl
        simp [hg]
      | none =>
        have hr := hrest hp
        simp only [M.bind_apply, getPrototypeOf_plain _ o s hlt (by simp [hkd]), M.bindRes_ok]
        cases hpr : (s.objEntry o).proto with
        | obj p =>
          rw [hpr] at hr
          simp only [hpr]
          have hl' : ordLookup s n p k = some (.accessor g sv e c) := by simpa [ordLookup, hp, hpr] using hl
          exact ih p (j + 1) hr (by omega) hl'
        | _ => simp [ordLookup, hp, hpr] at hl

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ}

/-- `o.k` finds an accessor whose getter is called next (one level down); or, for an object whose [[Get]] is not an
ordinary lookup (a proxy: a legacy platform object's wrapper), its [[Get]] itself. -/
def GetsAcc (eng : Engine) (answer : HostAnswer σ) (n : Nat) (h : σ) (s : State) (base : Value) (k : JSStr)
    (Q : Value → State → σ → Prop) : Prop :=
  (∃ o m g sv e c, base = .obj o ∧ PlainChain s m o (.str k) ∧ m ≤ 9999 ∧
    ordLookup s m o (.str k) = some (.accessor g sv e c) ∧ g.isUndefined = false ∧
    WP eng answer n h (callImpl eng g (.obj o) #[]) s Q) ∨
  (∃ o, base = .obj o ∧ WP eng answer (n + 1) h (Obj'.get o (.str k) (.obj o)) s Q)

theorem getsAcc_mono {n : Nat} {h : σ} {s : State} {b : Value} {k : JSStr} {P Q : Value → State → σ → Prop}
    (hg : GetsAcc eng answer n h s b k P) (hpq : ∀ v w h', P v w h' → Q v w h') : GetsAcc eng answer n h s b k Q := by
  rcases hg with ⟨o, m, g, sv, e, c, hb, hc, hm, hl, hgu, q⟩ | ⟨o, hb, q⟩
  · exact .inl ⟨o, m, g, sv, e, c, hb, hc, hm, hl, hgu, wp_mono q hpq⟩
  · exact .inr ⟨o, hb, wp_mono q hpq⟩

/-- **`obj.k`, an accessor**: the getter's call with `obj` as `this`. -/
theorem wp_getMemberAcc {n : Nat} {h : σ} {obj : Sem.CExpr} {k : JSStr} {ctx : Ctx} {s : State}
    {Q : Value → State → σ → Prop}
    (hw : WP eng answer (n + 1) h (obj ctx) s fun bv w h1 => GetsAcc eng answer n h1 w bv k Q) :
    WP eng answer (n + 1) h (Sem.getValue (Sem.memberRef obj (.name k) false) ctx) s Q := by
  rw [wp_iff_wpr]
  simp only [Sem.getValue, Sem.memberRef, M.bind_eq, M.bind_apply]
  apply wpr_bind
  apply wpr_bind
  refine wp_mono hw fun bv w h1 hga => ?_
  rcases hga with ⟨o, m, g, sv, e, c, hb, hc, hm, hl, hg, q⟩ | ⟨o, hb, q⟩
  rotate_left
  · subst hb
    simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    refine wp_of_eq (a := Ref.prop (.obj o) (.str k) ctx.strict none) rfl ?_
    rw [show getRefValue (Ref.prop (.obj o) (.str k) ctx.strict none) = Obj'.get o (.str k) (.obj o) from
      funext (getRefValue_prop o k ctx.strict)]
    exact q
  subst hb
  simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  refine wp_of_eq (a := Ref.prop (.obj o) (.str k) ctx.strict none) rfl ?_
  rw [wp_iff_wpr]
  rw [show getRefValue (Ref.prop (.obj o) (.str k) ctx.strict none) w = ES.call g (.obj o) #[] w from by
    rw [getRefValue_prop]; unfold Obj'.get
    exact get_chain_accessor w _ _ hg m o maxDepth hc (by rw [show maxDepth = 20000 from rfl]; omega) hl]
  exact wp_call q

end

end Logic
