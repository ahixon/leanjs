/-
  Big-step semantics for the verified JS core fragment.

  Design notes:
  * Fuel-free inductive semantics. A derivation exists exactly when the
    program terminates; "stuck" programs (e.g. calling a non-function,
    reading an unbound variable) simply have no derivation.
  * Values live in the shared `IRValue` domain, but JS functions evaluate to
    `IRValue.jsClosure`, which carries the *JS* source body. (An earlier
    version let a JS function evaluate to an IR closure with an arbitrary,
    unconstrained body, which made every simulation theorem false.)
  * Primitive operators reuse the IR operator semantics (`evalBinOp`,
    `evalUnaryOp`) through `jsBinOpToIR` / `jsUnaryOpToIR`. This is a model of
    JS, not full ECMAScript: e.g. `==`/`===` are both structural equality
    without coercion, and `null` and `undefined` are both modelled as
    `undefined`.
  * The core has no mutation: there is no assignment, so the store is
    threaded but never changed.
  * Block scoping: only a statement *list* can extend the environment (via
    `const`/`let`/`function` declarations), and the extension is scoped to
    the rest of that list. Blocks and `if` branches do not leak bindings.

  Fragment: identifiers, non-regex literals, parentheses, unary/binary
  operators, `?:`, calls, arrow functions and `function` expressions with
  simple identifier parameters, array literals (holes allowed), object
  literals with identifier keys, `.field` access; statements: expression,
  block, empty, `return`, `throw`, `if`/`else`, single-binding `const`/`let`
  declarations with an initializer, and `function` declarations.
-/
import LeanJS.JS.AST
import LeanJS.Semantics.Relation

namespace LeanJS.Semantics

open LeanJS.JS
open LeanJS.IR

/-! ## Helpers -/

/-- JS literal → value. Regular expressions are outside the core. -/
def jsLitToValue : Literal → Option IRValue
  | .string s => some (.string s)
  | .number n => some (.number n)
  | .bool b => some (.bool b)
  | .null => some .undefined
  | .undefined => some .undefined
  | .regex _ _ => none

def jsBinOpToIR : BinOp → Option IRBinOp
  | .add => some .add
  | .sub => some .sub
  | .mul => some .mul
  | .div => some .div
  | .mod => some .mod
  | .exp => some .exp
  | .eq => some .eq
  | .neq => some .neq
  | .strictEq => some .eq
  | .strictNeq => some .neq
  | .lt => some .lt
  | .lte => some .lte
  | .gt => some .gt
  | .gte => some .gte
  | .and => some .and
  | .or => some .or
  | .bitAnd => some .bitAnd
  | .bitOr => some .bitOr
  | .bitXor => some .bitXor
  | .shl => some .shl
  | .shr => some .shr
  | .ushr => some .ushr
  | .nullishCoalesce => none
  | .«in» => none
  | .«instanceof» => none

def jsUnaryOpToIR : UnaryOp → Option IRUnaryOp
  | .neg => some .neg
  | .pos => none
  | .not => some .not
  | .bitNot => some .bitNot
  | .typeof => some .typeof
  | .void => none
  | .delete => none

/-- A simple (non-destructuring, no default) parameter pattern -/
abbrev pid (n : String) : Pattern := .ident n none

/-- Name of a simple parameter pattern -/
def patName : Pattern → Option String
  | .ident n none => some n
  | _ => none

/-- Parameter names, if every parameter is a simple identifier -/
def simpleParamNames : List Pattern → Option (List String)
  | [] => some []
  | p :: ps => do
    let n ← patName p
    let ns ← simpleParamNames ps
    pure (n :: ns)

theorem simpleParamNames_map_pid (names : List String) :
    simpleParamNames (names.map pid) = some names := by
  induction names with
  | nil => rfl
  | cons n ns ih => simp [simpleParamNames, patName, pid, ih]

/-- Statements that bind a name in the enclosing statement list -/
def _root_.LeanJS.JS.Stmt.isDecl : Stmt → Bool
  | .varDecl .. => true
  | .funcDecl .. => true
  | .classDecl .. => true
  | _ => false

/-- How a call's body result becomes the call's result:
    `return v` and falling off the end of a block body. -/
def unwrapBlockResult : EvalResult → EvalResult
  | .return_ v s => .val v s
  | .val _ s => .val .undefined s
  | other => other

/-- Same unwrapping as IR's `ApplyFunc` (used for expression bodies) -/
def unwrapReturn : EvalResult → EvalResult
  | .return_ v s => .val v s
  | other => other

/-- Environment of a call: parameters bound, then the self-name (if any).
    This mirrors IR's `ApplyFunc`. -/
def callEnv (cenv : Env) (self : Option String) (params : List String)
    (args : List IRValue) (fv : IRValue) : Env :=
  let e := cenv.extendMany (params.zip args)
  match self with
  | some n => e.extend n fv
  | none => e

/-! ## Evaluation relation

  All judgments are folded into one inductive `JSSem` over a judgment form
  `JSJ`, so that proofs can use ordinary structural induction (Lean 4.17
  cannot recurse structurally over mutually inductive predicates). The
  familiar names (`JSEvalExpr`, `JSEvalStmts`, …) are abbreviations. -/

/-- Judgment forms of the JS semantics -/
inductive JSJ where
  | expr (env : Env) (st : Store) (e : Expr)
  | args (env : Env) (st : Store) (es : List Expr) (acc : List IRValue)
  | elems (env : Env) (st : Store) (es : List (Option Expr)) (acc : List IRValue)
  | props (env : Env) (st : Store) (ps : List Property) (acc : List (String × IRValue))
  | apply (fv : IRValue) (vs : List IRValue) (st : Store)
  | stmt (env : Env) (st : Store) (s : Stmt)
  | stmts (env : Env) (st : Store) (ss : List Stmt)

set_option autoImplicit true in
inductive JSSem : JSJ → EvalResult → Prop where
  | ident :
      env.lookup x = some v →
      JSSem (.expr env st (.ident x)) (.val v st)
  | literal :
      jsLitToValue lit = some v →
      JSSem (.expr env st (.literal lit)) (.val v st)
  | paren :
      JSSem (.expr env st e) r →
      JSSem (.expr env st (.paren e)) r
  | binary_ok :
      JSSem (.expr env st l) (.val lv s1) →
      jsBinOpToIR op = some irop →
      needsRight irop lv = true →
      JSSem (.expr env s1 r) (.val rv s2) →
      JSSem (.expr env st (.binary op l r)) (evalBinOp irop lv rv s2)
  | binary_short :
      JSSem (.expr env st l) (.val lv s1) →
      jsBinOpToIR op = some irop →
      needsRight irop lv = false →
      JSSem (.expr env st (.binary op l r)) (.val lv s1)
  | binary_left_signal :
      JSSem (.expr env st l) res → isSignal res →
      JSSem (.expr env st (.binary op l r)) res
  | binary_right_signal :
      JSSem (.expr env st l) (.val lv s1) →
      optNeedsRight (jsBinOpToIR op) lv = true →
      JSSem (.expr env s1 r) res → isSignal res →
      JSSem (.expr env st (.binary op l r)) res
  | unary_ok :
      JSSem (.expr env st a) (.val v s) →
      jsUnaryOpToIR op = some irop →
      JSSem (.expr env st (.unary op a)) (evalUnaryOp irop v s)
  | unary_signal :
      JSSem (.expr env st a) res → isSignal res →
      JSSem (.expr env st (.unary op a)) res
  | cond_true :
      JSSem (.expr env st c) (.val cv s) → isTruthy cv = true →
      JSSem (.expr env s t) res →
      JSSem (.expr env st (.conditional c t e)) res
  | cond_false :
      JSSem (.expr env st c) (.val cv s) → isTruthy cv = false →
      JSSem (.expr env s e) res →
      JSSem (.expr env st (.conditional c t e)) res
  | cond_signal :
      JSSem (.expr env st c) res → isSignal res →
      JSSem (.expr env st (.conditional c t e)) res
  | call_ok :
      JSSem (.expr env st f) (.val fv s1) →
      JSSem (.args env s1 args []) (.val (.array vs) s2) →
      JSSem (.apply fv vs s2) res →
      JSSem (.expr env st (.call f args)) res
  | call_callee_signal :
      JSSem (.expr env st f) res → isSignal res →
      JSSem (.expr env st (.call f args)) res
  | call_args_signal :
      JSSem (.expr env st f) (.val fv s1) →
      JSSem (.args env s1 args []) res → isSignal res →
      JSSem (.expr env st (.call f args)) res
  | function :
      simpleParamNames params = some names →
      JSSem (.expr env st (.function name params body false false)) (.val (.jsClosure env name names (.block body)) st)
  | arrow :
      simpleParamNames params = some names →
      JSSem (.expr env st (.arrowFunction params body false)) (.val (.jsClosure env none names body) st)
  | array :
      JSSem (.elems env st elems []) res →
      JSSem (.expr env st (.array elems)) res
  | object :
      JSSem (.props env st props []) res →
      JSSem (.expr env st (.object props)) res
  | member_ok :
      JSSem (.expr env st o) (.val (.record fs) s) →
      fs.lookup k = some v →
      JSSem (.expr env st (.member o (.ident k))) (.val v s)
  | member_missing :
      JSSem (.expr env st o) (.val (.record fs) s) →
      fs.lookup k = none →
      JSSem (.expr env st (.member o (.ident k))) (.val .undefined s)
  | member_signal :
      JSSem (.expr env st o) res → isSignal res →
      JSSem (.expr env st (.member o (.ident k))) res
  | args_nil :
      JSSem (.args env st [] acc) (.val (.array acc.reverse) st)
  | args_cons_ok :
      JSSem (.expr env st a) (.val v s) →
      JSSem (.args env s rest (v :: acc)) res →
      JSSem (.args env st (a :: rest) acc) res
  | args_cons_signal :
      JSSem (.expr env st a) res → isSignal res →
      JSSem (.args env st (a :: rest) acc) res
  | elems_nil :
      JSSem (.elems env st [] acc) (.val (.array acc.reverse) st)
  | elems_some_ok :
      JSSem (.expr env st e) (.val v s) →
      JSSem (.elems env s rest (v :: acc)) res →
      JSSem (.elems env st (some e :: rest) acc) res
  | elems_some_signal :
      JSSem (.expr env st e) res → isSignal res →
      JSSem (.elems env st (some e :: rest) acc) res
  | elems_hole :
      JSSem (.elems env st rest (.undefined :: acc)) res →
      JSSem (.elems env st (none :: rest) acc) res
  | props_nil :
      JSSem (.props env st [] acc) (.val (.record acc.reverse) st)
  | props_cons_ok :
      JSSem (.expr env st e) (.val v s) →
      JSSem (.props env s rest ((k, v) :: acc)) res →
      JSSem (.props env st (.prop (.ident k) e .init false false :: rest) acc) res
  | props_cons_signal :
      JSSem (.expr env st e) res → isSignal res →
      JSSem (.props env st (.prop (.ident k) e .init false false :: rest) acc) res
  | apply_expr_body :
      params.length = args.length →
      JSSem (.expr (callEnv cenv name params args (.jsClosure cenv name params (.expr e))) st e) res →
      JSSem (.apply (.jsClosure cenv name params (.expr e)) args st) (unwrapReturn res)
  | apply_block_body :
      params.length = args.length →
      JSSem (.stmts (callEnv cenv name params args (.jsClosure cenv name params (.block ss))) st ss) res →
      JSSem (.apply (.jsClosure cenv name params (.block ss)) args st) (unwrapBlockResult res)
  | stmt_expr :
      JSSem (.expr env st e) res →
      JSSem (.stmt env st (.expr e)) res
  | stmt_block :
      JSSem (.stmts env st ss) res →
      JSSem (.stmt env st (.block ss)) res
  | stmt_empty :
      JSSem (.stmt env st .empty) (.val .undefined st)
  | stmt_return_some :
      JSSem (.expr env st e) (.val v s) →
      JSSem (.stmt env st (.return_ (some e))) (.return_ v s)
  | stmt_return_some_signal :
      JSSem (.expr env st e) res → isSignal res →
      JSSem (.stmt env st (.return_ (some e))) res
  | stmt_return_none :
      JSSem (.stmt env st (.return_ none)) (.return_ .undefined st)
  | stmt_throw_ok :
      JSSem (.expr env st e) (.val v s) →
      JSSem (.stmt env st (.throw e)) (.throw_ v s)
  | stmt_throw_signal :
      JSSem (.expr env st e) res → isSignal res →
      JSSem (.stmt env st (.throw e)) res
  | stmt_if_true :
      JSSem (.expr env st c) (.val cv s) → isTruthy cv = true →
      JSSem (.stmt env s t) res →
      JSSem (.stmt env st (.ifStmt c t alt)) res
  | stmt_if_false :
      JSSem (.expr env st c) (.val cv s) → isTruthy cv = false →
      JSSem (.stmt env s e) res →
      JSSem (.stmt env st (.ifStmt c t (some e))) res
  | stmt_if_false_none :
      JSSem (.expr env st c) (.val cv s) → isTruthy cv = false →
      JSSem (.stmt env st (.ifStmt c t none)) (.val .undefined s)
  | stmt_if_signal :
      JSSem (.expr env st c) res → isSignal res →
      JSSem (.stmt env st (.ifStmt c t alt)) res
  | stmts_nil :
      JSSem (.stmts env st []) (.val .undefined st)
  | stmts_decl_ok :
      (kind = .const ∨ kind = .let) →
      JSSem (.expr env st init) (.val v s) →
      JSSem (.stmts (env.extend x v) s rest) res →
      JSSem (.stmts env st (.varDecl kind [.mk (.ident x none) (some init)] :: rest)) res
  | stmts_decl_signal :
      (kind = .const ∨ kind = .let) →
      JSSem (.expr env st init) res → isSignal res →
      JSSem (.stmts env st (.varDecl kind [.mk (.ident x none) (some init)] :: rest)) res
  | stmts_funcDecl :
      simpleParamNames params = some names →
      JSSem (.stmts (env.extend f (.jsClosure env (some f) names (.block body))) st rest) res →
      JSSem (.stmts env st (.funcDecl f params body false false :: rest)) res
  | stmts_stmt_ok :
      s.isDecl = false →
      JSSem (.stmt env st s) (.val v s1) →
      JSSem (.stmts env s1 rest) res →
      JSSem (.stmts env st (s :: rest)) res
  | stmts_stmt_signal :
      s.isDecl = false →
      JSSem (.stmt env st s) res → isSignal res →
      JSSem (.stmts env st (s :: rest)) res

/-- Expressions -/
abbrev JSEvalExpr (env : Env) (st : Store) (e : Expr) (r : EvalResult) : Prop := JSSem (.expr env st e) r
/-- Call arguments, accumulated in reverse (mirrors IR `EvalArgs`) -/
abbrev JSEvalArgs (env : Env) (st : Store) (es : List Expr) (acc : List IRValue) (r : EvalResult) : Prop := JSSem (.args env st es acc) r
/-- Array literal elements; a hole evaluates to `undefined` -/
abbrev JSEvalElems (env : Env) (st : Store) (es : List (Option Expr)) (acc : List IRValue) (r : EvalResult) : Prop := JSSem (.elems env st es acc) r
/-- Object literal properties `k: e` with identifier keys -/
abbrev JSEvalProps (env : Env) (st : Store) (ps : List Property) (acc : List (String × IRValue)) (r : EvalResult) : Prop := JSSem (.props env st ps acc) r
/-- Applying a function value to arguments -/
abbrev JSApply (fv : IRValue) (vs : List IRValue) (st : Store) (r : EvalResult) : Prop := JSSem (.apply fv vs st) r
/-- Single (non-declaration) statements -/
abbrev JSEvalStmt (env : Env) (st : Store) (s : Stmt) (r : EvalResult) : Prop := JSSem (.stmt env st s) r
/-- Statement lists; normal completion yields `undefined` -/
abbrev JSEvalStmts (env : Env) (st : Store) (ss : List Stmt) (r : EvalResult) : Prop := JSSem (.stmts env st ss) r

end LeanJS.Semantics
