import JSProofs.Rules5
import JSProofs.Loops5

/-!
# `typeof x` and labeled statements (zippy docs/react-proofs.md)

React's child reconciler: `"object" === typeof newChild` and `a: { for (…) { … break a; } … }`.
-/

open ES ES.M HostRuns
open Std (HashMap)

namespace Logic

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ}

@[js_simp] theorem isStrictlyEqual_str_sym (a : JSStr) (i : Nat) : isStrictlyEqual (.str a) (.sym i) = false := rfl
@[js_simp] theorem isStrictlyEqual_sym_str (a : JSStr) (i : Nat) : isStrictlyEqual (.sym i) (.str a) = false := rfl
@[js_simp] theorem isStrictlyEqual_sym_sym (i j : Nat) : isStrictlyEqual (.sym i) (.sym j) = (i == j) := by
  simp [isStrictlyEqual, sameValue]
@[js_simp] theorem isStrictlyEqual_null_obj (o : ObjId) : isStrictlyEqual .null (.obj o) = false := rfl
@[js_simp] theorem isStrictlyEqual_obj_null (o : ObjId) : isStrictlyEqual (.obj o) .null = false := rfl
@[js_simp] theorem isStrictlyEqual_undef_obj (o : ObjId) : isStrictlyEqual .undefined (.obj o) = false := rfl

/-- `typeof v` as a condition: what it is, for the values `typeof` sees without calls. -/
def TypeofC (s : State) (v : Value) (P : JSStr → Prop) : Prop :=
  match v with
  | .obj o => o < s.heap.size ∧ (s.objEntry o).kind = .ordinary ∧ P "object"
  | .null => P "object"
  | .undefined => P "undefined"
  | .str _ => P "string"
  | .num _ => P "number"
  | .bool _ => P "boolean"
  | .sym _ => P "symbol"
  | _ => False

theorem typeOf_of {s : State} {v : Value} {P : JSStr → Prop} (h : TypeofC s v P) :
    ∃ t, typeOf v s = .ok t s ∧ P t := by
  cases v with
  | obj o =>
    obtain ⟨hlt, hk, hp⟩ := h
    refine ⟨"object", ?_, hp⟩
    simp [typeOf, isCallable, readObj_entry o _ s hlt, hk, M.bind_eq, M.bind_apply, Pure.pure, M.pure]
  | bigint _ => exact h.elim
  | _ => exact ⟨_, rfl, h⟩

/-- **`typeof x`** of a variable. -/
theorem wp_typeofIdentC {n : Nat} {h : σ} {x : JSStr} {ctx : Ctx} {s : State} {Q : Value → State → σ → Prop}
    (hk : depth ≤ s.fuel)
    (hw : match Scope.resolve s depth ctx.lex x, Scope.lookup s depth ctx.lex x with
      | some _, some v => TypeofC s v fun t => Q (.str t) s h
      | _, _ => False) :
    WP eng answer n h (Sem.typeofRef (Sem.identRef x) ctx) s Q := by
  cases hr : Scope.resolve s depth ctx.lex x with
  | none => rw [hr] at hw; exact hw.elim
  | some e =>
    cases hl : Scope.lookup s depth ctx.lex x with
    | none => rw [hr, hl] at hw; exact hw.elim
    | some v =>
      rw [hr, hl] at hw
      obtain ⟨bm, o, bd, he, hd, hb, hv⟩ := resolve_lookup s x v depth ctx.lex e hr hl
      have h1 : Sem.identRef x ctx s = .ok (.env (some e) x ctx.strict) s :=
        Scope.resolveBinding_of_resolve s depth ctx.lex x ctx.strict e hr hk
      have h2 := Scope.getRefValue_env s e x ctx.strict he bm o hd bd v hb hv
      obtain ⟨t, ht, hq⟩ := typeOf_of hw
      refine wp_of_eq ?_ hq
      simp only [Sem.typeofRef, M.bind_eq, M.bind_apply, h1, M.bindRes_ok]
      simp only [h2, M.bindRes_ok, M.bind_eq, M.bind_apply, ht]
      rfl

end

end Logic
