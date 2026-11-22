import JSProofs.Rules3
import JSProofs.Loops2

/-!
# More rules for the `js` tactic (zippy docs/react-proofs.md)

`a > b` on Numbers, `x--` on a variable, destructuring declarators (`const [a, b] = e`: the compiled initializer,
then the interpreter's pattern binding), and the lemmas that reduce a `switch`'s default case on a literal case list.
-/

open ES ES.M HostRuns
open Std (HashMap)

namespace Logic

attribute [js_simp] List.findIdx?_toArray List.findIdx?_cons List.findIdx?_nil Option.isNone_some Option.isNone_none

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ}

theorem binaryOp_gt_num (a b : F64) (s : State) :
    Sem.binaryOp .gt (.num a) (.num b) s = .ok (.bool (ltNum b a)) s := by
  simp only [Sem.binaryOp, isLessThan, M.bind_eq, M.bind_apply, ↓reduceIte, Logic.toPrim_num, M.bindRes_ok, Bool.false_eq_true,
    FDI.pure_app, Logic.toNumeric_num, ltNum]

/-- **`a > b`** of two Numbers. -/
theorem wp_gtNum {n : Nat} {h : σ} {a b : F64} {s : State} {Q : Value → State → σ → Prop}
    (hq : Q (.bool (ltNum b a)) s h) : WP eng answer n h (Sem.binaryOp .gt (.num a) (.num b)) s Q :=
  wp_of_eq (binaryOp_gt_num a b s) hq

/-- **`x--`** of a variable holding a Number: the old value; the variable decremented. -/
theorem wp_postDecIdentC {n : Nat} {h : σ} {x : JSStr} {ctx : Ctx} {s : State} {Q : Value → State → σ → Prop}
    (hk : depth ≤ s.fuel)
    (hw : match Scope.resolve s depth ctx.lex x, Scope.lookup s depth ctx.lex x with
      | some e, some (.num a) => SetsC s e x (.num (Conv.subF a F64.one)) fun w' => Q (.num a) w' h
      | _, _ => False) :
    WP eng answer n h (Sem.update false false (Sem.identRef x) ctx) s Q := by
  cases hr : Scope.resolve s depth ctx.lex x with
  | none => rw [hr] at hw; exact hw.elim
  | some e =>
    cases hl : Scope.lookup s depth ctx.lex x with
    | none => rw [hr, hl] at hw; exact hw.elim
    | some v =>
      rw [hr, hl] at hw
      cases v with
      | num a =>
        simp only at hw
        obtain ⟨bm, o, bd, he, hd, hb, hv⟩ := resolve_lookup s x (.num a) depth ctx.lex e hr hl
        obtain ⟨bm', o', bd', he', hd', hb', hv', hm', q⟩ := setsC_setsVar hw
        have h1 : Sem.identRef x ctx s = .ok (.env (some e) x ctx.strict) s :=
          Scope.resolveBinding_of_resolve s depth ctx.lex x ctx.strict e hr hk
        have h2 := Scope.getRefValue_env s e x ctx.strict he bm o hd bd (.num a) hb hv
        have h3 := setMutableBinding_declLike e x (.num (Conv.subF a F64.one)) ctx.strict s he' hd' hb' hv' hm'
        apply wp_of_eq _ q
        simp only [Sem.update, M.bind_eq, M.bind_apply, h1, M.bindRes_ok, getRefValueOnce, h2, FDI.pure_app,
          Logic.toNumeric_num, putRefValue, ite_true, if_true, Bool.false_eq_true, ↓reduceIte]
        rw [h3]
        rfl
      | _ => exact hw.elim

/-- **A destructuring declarator** (`const [a, b] = e`): the initializer, then the pattern bound to its value. -/
theorem wp_declPat {n : Nat} {h : σ} {rhs : Sem.CExpr} {bind : Ctx → Value → M Unit} {ctx : Ctx} {s : State}
    {Q : Unit → State → σ → Prop}
    (hw : WP eng answer n h (rhs ctx) s fun v w h1 => WP eng answer n h1 (bind ctx v) w Q) :
    WP eng answer n h (Sem.declPat rhs bind ctx) s Q := wp_bind hw

end

end Logic
