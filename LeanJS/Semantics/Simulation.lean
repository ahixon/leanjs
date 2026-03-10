/-
  IR-level semantic equivalence lemmas.

  These prove that certain IR transformations preserve semantics,
  validating patterns used by the transpiler.
-/
import LeanJS.Semantics.Relation
import LeanJS.Semantics.Determinism

set_option autoImplicit true

namespace LeanJS.Semantics

open LeanJS.IR

/-- `if c t e` and `ternary c t e` evaluate identically -/
theorem if_ternary_equiv (env : Env) (store : Store) (fuel : Nat)
    (c t e : IRExpr) (r : EvalResult) :
    Eval env store fuel (.«if» c t e) r ↔ Eval env store fuel (.ternary c t e) r := by
  constructor
  · intro h
    cases h with
    | fuel_zero => exact .fuel_zero
    | if_true hc ht hb => exact .ternary_true hc ht hb
    | if_false hc ht hb => exact .ternary_false hc ht hb
    | if_signal hc hs => exact .ternary_signal hc hs
  · intro h
    cases h with
    | fuel_zero => exact .fuel_zero
    | ternary_true hc ht hb => exact .if_true hc ht hb
    | ternary_false hc ht hb => exact .if_false hc ht hb
    | ternary_signal hc hs => exact .if_signal hc hs

/-- `seq [lit unit, e]` evaluates the same as `e` when e evaluates to a value -/
theorem seq_unit_skip (env : Env) (store : Store) (fuel : Nat)
    (e : IRExpr) (v : IRValue) (s : Store) :
    Eval env store (fuel+1) e (.val v s) →
    Eval env store (fuel+1+1) (.seq [.lit .unit, e]) (.val v s) := by
  intro he
  exact .seq (.cons_ok (.lit (fuel := fuel)) (.singleton he) (List.cons_ne_nil _ _))

/-- `break` produces a break signal -/
theorem break_is_signal (env : Env) (store : Store) (fuel : Nat) :
    Eval env store (fuel+1) .«break» (.break_ store) :=
  .«break»

/-- `continue` produces a continue signal -/
theorem continue_is_signal (env : Env) (store : Store) (fuel : Nat) :
    Eval env store (fuel+1) .«continue» (.continue_ store) :=
  .«continue»

/-- A let binding where the value is a literal evaluates the body with the literal bound -/
theorem let_lit_eval (env : Env) (store : Store) (fuel : Nat)
    (name : String) (lit : IRLit) (body : IRExpr) (result : EvalResult) :
    Eval (env.extend name (irLitToValue lit)) store (fuel+1) body result →
    Eval env store (fuel+1+1) (.«let» name .any (.lit lit) body) result :=
  fun hbody => .let_ok (.lit (fuel := fuel)) hbody

/-- Variable lookup succeeds when the variable is in the environment -/
theorem var_lookup (env : Env) (name : String) (v : IRValue) (store : Store) (fuel : Nat)
    (h : env.lookup name = some v) :
    Eval env store (fuel+1) (.var name) (.val v store) :=
  .var_ok h

/-- Constructing a value with no args gives a constructed value -/
theorem construct_nil (env : Env) (store : Store) (fuel : Nat) (tag : String) :
    Eval env store (fuel+1) (.construct tag []) (.val (.constructed tag []) store) := by
  exact .construct_ok .nil

/-- An empty record evaluates to an empty record value -/
theorem empty_record (env : Env) (store : Store) (fuel : Nat) :
    Eval env store (fuel+1) (.record []) (.val (.record []) store) := by
  exact .record .nil

/-- An empty array evaluates to an empty array value -/
theorem empty_array (env : Env) (store : Store) (fuel : Nat) :
    Eval env store (fuel+1) (.array []) (.val (.array []) store) := by
  exact .array .nil

/-- A while loop with a false literal condition returns undefined -/
theorem loop_false_lit (env : Env) (store : Store) (fuel : Nat)
    (body : IRExpr) :
    Eval env store (fuel+1+1+1) (.loop (.lit (.bool false)) body) (.val .undefined store) :=
  .loop (.cond_false (fuel := fuel+1) (.lit (fuel := fuel)) rfl)

/-- Pattern matching with a wildcard always succeeds -/
theorem match_wildcard (env : Env) (store : Store) (fuel : Nat)
    (sv : IRValue) (body : IRExpr) (result : EvalResult) :
    Eval env store fuel body result →
    EvalMatch env store fuel sv [.mk .wildcard body] result := by
  intro hbody
  exact EvalMatch.match_ok (bindings := []) rfl hbody

end LeanJS.Semantics
