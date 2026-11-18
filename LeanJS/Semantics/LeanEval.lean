/-
  Big-step semantics for the verified Lean core fragment.

  * Fuel-free inductive semantics (a derivation exists iff evaluation
    terminates without getting stuck).
  * Lean functions evaluate to `IRValue.leanClosure`, carrying the Lean source
    body. A multi-parameter `fun x y => b` is curried: it evaluates to a
    closure for `x` whose body is `fun y => b`, matching Lean's semantics and
    the curried application `f a b = (f a) b`. (An earlier version bound only
    the first parameter of an uncurried closure and gave the body an
    arbitrary IR expression.)
  * Primitive operators reuse the IR operator semantics.

  Fragment: identifiers, literals, `()`, parentheses, single-argument
  application, `fun` with one or more parameters, non-recursive `let`,
  `if … then … else …`, binary/unary operators, structure literals, array
  literals, field projection and `throw`.
-/
import LeanJS.Lean.AST
import LeanJS.Semantics.Relation
import LeanJS.Semantics.JSEval

namespace LeanJS.Semantics

open LeanJS.Lean
open LeanJS.IR

def leanLitToValue : LeanLit → IRValue
  | .natVal n => .number (Float.ofNat n)
  | .float f => .number f
  | .string s => .string s
  | .bool b => .bool b

def leanBinOpToIR : String → Option IRBinOp
  | "+" => some .add
  | "-" => some .sub
  | "*" => some .mul
  | "/" => some .div
  | "%" => some .mod
  | "==" => some .eq
  | "!=" => some .neq
  | "<" => some .lt
  | "<=" => some .lte
  | ">" => some .gt
  | ">=" => some .gte
  | "&&" => some .and
  | "||" => some .or
  | "++" => some .strConcat
  | _ => none

def leanUnaryOpToIR : String → Option IRUnaryOp
  | "-" => some .neg
  | "!" => some .not
  | _ => none

/-- Judgment forms of the Lean semantics (folded into one inductive so that
    proofs can use ordinary structural induction) -/
inductive LeanJ where
  | expr (env : Env) (st : Store) (e : LeanExpr)
  | fields (env : Env) (st : Store) (fs : List (String × LeanExpr)) (acc : List (String × IRValue))
  | elems (env : Env) (st : Store) (es : List LeanExpr) (acc : List IRValue)
  | apply (fv : IRValue) (av : IRValue) (st : Store)

set_option autoImplicit true in
inductive LeanSem : LeanJ → EvalResult → Prop where
  | ident :
      env.lookup x = some v →
      LeanSem (.expr env st (.ident x)) (.val v st)
  | lit :
      LeanSem (.expr env st (.lit l)) (.val (leanLitToValue l) st)
  | unit :
      LeanSem (.expr env st .unit) (.val .unit st)
  | paren :
      LeanSem (.expr env st e) r →
      LeanSem (.expr env st (.paren e)) r
  | lam_one :
      LeanSem (.expr env st (.lam [p] body)) (.val (.leanClosure env none p.name body) st)
  | lam_cons :
      ps ≠ [] →
      LeanSem (.expr env st (.lam (p :: ps) body)) (.val (.leanClosure env none p.name (.lam ps body)) st)
  | app_ok :
      LeanSem (.expr env st f) (.val fv s1) →
      LeanSem (.expr env s1 a) (.val av s2) →
      LeanSem (.apply fv av s2) r →
      LeanSem (.expr env st (.app f a)) r
  | app_fn_signal :
      LeanSem (.expr env st f) r → isSignal r →
      LeanSem (.expr env st (.app f a)) r
  | app_arg_signal :
      LeanSem (.expr env st f) (.val fv s1) →
      LeanSem (.expr env s1 a) r → isSignal r →
      LeanSem (.expr env st (.app f a)) r
  | let_ok :
      LeanSem (.expr env st v) (.val vv s) →
      LeanSem (.expr (env.extend x vv) s b) r →
      LeanSem (.expr env st (.«let» x ty v b)) r
  | let_signal :
      LeanSem (.expr env st v) r → isSignal r →
      LeanSem (.expr env st (.«let» x ty v b)) r
  | if_true :
      LeanSem (.expr env st c) (.val cv s) → isTruthy cv = true →
      LeanSem (.expr env s t) r →
      LeanSem (.expr env st (.«if» c t (some e))) r
  | if_false :
      LeanSem (.expr env st c) (.val cv s) → isTruthy cv = false →
      LeanSem (.expr env s e) r →
      LeanSem (.expr env st (.«if» c t (some e))) r
  | if_signal :
      LeanSem (.expr env st c) r → isSignal r →
      LeanSem (.expr env st (.«if» c t (some e))) r
  | binOp_ok :
      LeanSem (.expr env st l) (.val lv s1) →
      LeanSem (.expr env s1 rr) (.val rv s2) →
      leanBinOpToIR op = some irop →
      LeanSem (.expr env st (.binOp op l rr)) (evalBinOp irop lv rv s2)
  | binOp_left_signal :
      LeanSem (.expr env st l) r → isSignal r →
      LeanSem (.expr env st (.binOp op l rr)) r
  | binOp_right_signal :
      LeanSem (.expr env st l) (.val lv s1) →
      LeanSem (.expr env s1 rr) r → isSignal r →
      LeanSem (.expr env st (.binOp op l rr)) r
  | unaryOp_ok :
      LeanSem (.expr env st a) (.val v s) →
      leanUnaryOpToIR op = some irop →
      LeanSem (.expr env st (.unaryOp op a)) (evalUnaryOp irop v s)
  | unaryOp_signal :
      LeanSem (.expr env st a) r → isSignal r →
      LeanSem (.expr env st (.unaryOp op a)) r
  | structLit :
      LeanSem (.fields env st fields []) r →
      LeanSem (.expr env st (.structLit name fields)) r
  | arrayLit :
      LeanSem (.elems env st elems []) r →
      LeanSem (.expr env st (.arrayLit elems)) r
  | proj_ok :
      LeanSem (.expr env st e) (.val (.record fs) s) →
      fs.lookup k = some v →
      LeanSem (.expr env st (.proj e k)) (.val v s)
  | proj_signal :
      LeanSem (.expr env st e) r → isSignal r →
      LeanSem (.expr env st (.proj e k)) r
  | throw_ok :
      LeanSem (.expr env st e) (.val v s) →
      LeanSem (.expr env st (.«throw» e)) (.throw_ v s)
  | throw_signal :
      LeanSem (.expr env st e) r → isSignal r →
      LeanSem (.expr env st (.«throw» e)) r
  | fields_nil :
      LeanSem (.fields env st [] acc) (.val (.record acc.reverse) st)
  | fields_cons_ok :
      LeanSem (.expr env st e) (.val v s) →
      LeanSem (.fields env s rest ((k, v) :: acc)) r →
      LeanSem (.fields env st ((k, e) :: rest) acc) r
  | fields_cons_signal :
      LeanSem (.expr env st e) r → isSignal r →
      LeanSem (.fields env st ((k, e) :: rest) acc) r
  | elems_nil :
      LeanSem (.elems env st [] acc) (.val (.array acc.reverse) st)
  | elems_cons_ok :
      LeanSem (.expr env st e) (.val v s) →
      LeanSem (.elems env s rest (v :: acc)) r →
      LeanSem (.elems env st (e :: rest) acc) r
  | elems_cons_signal :
      LeanSem (.expr env st e) r → isSignal r →
      LeanSem (.elems env st (e :: rest) acc) r
  | apply_closure :
      LeanSem (.expr (callEnv cenv name [p] [av] (.leanClosure cenv name p body)) st body) r →
      LeanSem (.apply (.leanClosure cenv name p body) av st) (unwrapReturn r)

abbrev LeanEvalExpr (env : Env) (st : Store) (e : LeanExpr) (r : EvalResult) : Prop := LeanSem (.expr env st e) r
abbrev LeanEvalFields (env : Env) (st : Store) (fs : List (String × LeanExpr)) (acc : List (String × IRValue)) (r : EvalResult) : Prop := LeanSem (.fields env st fs acc) r
abbrev LeanEvalElems (env : Env) (st : Store) (es : List LeanExpr) (acc : List IRValue) (r : EvalResult) : Prop := LeanSem (.elems env st es acc) r
/-- Applying a Lean function value to one argument -/
abbrev LeanApply (fv av : IRValue) (st : Store) (r : EvalResult) : Prop := LeanSem (.apply fv av st) r

end LeanJS.Semantics
