/-
  Big-step evaluation relation for JS AST (core subset).

  Uses the shared `IRValue` domain. JS closures are stored as `IRValue.closure`
  with the closure body being an IR expression (set at function creation time).
  Function application delegates to the IR `ApplyFunc` relation for body evaluation.

  This hybrid approach avoids defining separate JS values while enabling
  forward simulation proofs: the simulation theorem provides the specific IR body
  (from translation) that makes the evaluation correspond.
-/
import LeanJS.JS.AST
import LeanJS.Semantics.Relation

namespace LeanJS.Semantics

open LeanJS.JS
open LeanJS.IR

/-! ## JS literal → IRValue conversion -/

def jsLitToValue : Literal → IRValue
  | .string s => .string s
  | .number n => .number n
  | .bool b => .bool b
  | .null => .undefined
  | .undefined => .undefined
  | .regex _ _ => .string "<regex>"

/-! ## JS operator → IR operator mappings -/

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

/-! ## Helper: extract parameter name from JS pattern -/

def extractParamName : Pattern → Option String
  | .ident name _ => some name
  | _ => none

def extractParamNames (params : List Pattern) : List String :=
  params.filterMap extractParamName

/-! ## Helpers (must be before mutual block) -/

/-- Interleave template quasi strings with expression values -/
def interleaveTemplate : List String → List IRValue → String
  | [], _ => ""
  | [s], _ => s
  | s :: rest, [] => s ++ interleaveTemplate rest []
  | s :: srest, v :: vrest =>
    let vs := match v with
      | .string sv => sv
      | .number n => toString n
      | .bool b => toString b
      | _ => ""
    s ++ vs ++ interleaveTemplate srest vrest

/-! ## JS big-step evaluation relation (core subset) -/

set_option maxHeartbeats 3200000 in
set_option autoImplicit true in
mutual

/-- Big-step evaluation for JS expressions.
    Uses shared IRValue domain; closures delegate to IR's ApplyFunc. -/
inductive JSEvalExpr : Env → Store → Nat → Expr → EvalResult → Prop where
  | fuel_zero :
      JSEvalExpr env store 0 e (.error "out of fuel")

  -- Identifier
  | ident_ok :
      env.lookup name = some v →
      JSEvalExpr env store (fuel+1) (.ident name) (.val v store)
  | ident_unbound :
      env.lookup name = none →
      JSEvalExpr env store (fuel+1) (.ident name) (.error s!"unbound variable: {name}")

  -- Literal
  | literal :
      JSEvalExpr env store (fuel+1) (.literal lit) (.val (jsLitToValue lit) store)

  -- This
  | this_ok :
      env.lookup "this" = some v →
      JSEvalExpr env store (fuel+1) .this (.val v store)
  | this_none :
      env.lookup "this" = none →
      JSEvalExpr env store (fuel+1) .this (.val .undefined store)

  -- Binary operator
  | binary_ok :
      JSEvalExpr env store fuel left (.val lv s1) →
      JSEvalExpr env s1 fuel right (.val rv s2) →
      jsBinOpToIR op = some irop →
      evalBinOp irop lv rv s2 = result →
      JSEvalExpr env store (fuel+1) (.binary op left right) result
  | binary_left_signal :
      JSEvalExpr env store fuel left r → isSignal r →
      JSEvalExpr env store (fuel+1) (.binary op left right) r
  | binary_right_signal :
      JSEvalExpr env store fuel left (.val lv s1) →
      JSEvalExpr env s1 fuel right r → isSignal r →
      JSEvalExpr env store (fuel+1) (.binary op left right) r

  -- Unary operator
  | unary_ok :
      JSEvalExpr env store fuel arg (.val v s) →
      jsUnaryOpToIR op = some irop →
      evalUnaryOp irop v s = result →
      JSEvalExpr env store (fuel+1) (.unary op arg) result
  | unary_signal :
      JSEvalExpr env store fuel arg r → isSignal r →
      JSEvalExpr env store (fuel+1) (.unary op arg) r

  -- Conditional (ternary)
  | conditional_true :
      JSEvalExpr env store fuel test (.val cv s) →
      isTruthy cv = true →
      JSEvalExpr env s fuel consequent result →
      JSEvalExpr env store (fuel+1) (.conditional test consequent alternate) result
  | conditional_false :
      JSEvalExpr env store fuel test (.val cv s) →
      isTruthy cv = false →
      JSEvalExpr env s fuel alternate result →
      JSEvalExpr env store (fuel+1) (.conditional test consequent alternate) result
  | conditional_signal :
      JSEvalExpr env store fuel test r → isSignal r →
      JSEvalExpr env store (fuel+1) (.conditional test consequent alternate) r

  -- Function call
  | call_ok :
      JSEvalExpr env store fuel callee (.val fv s1) →
      JSEvalArgs env s1 fuel args [] (.val (.array argVals) s2) →
      ApplyFunc fv argVals s2 fuel result →
      JSEvalExpr env store (fuel+1) (.call callee args) result
  | call_func_signal :
      JSEvalExpr env store fuel callee r → isSignal r →
      JSEvalExpr env store (fuel+1) (.call callee args) r
  | call_args_signal :
      JSEvalExpr env store fuel callee (.val fv s1) →
      JSEvalArgs env s1 fuel args [] r → isSignal r →
      JSEvalExpr env store (fuel+1) (.call callee args) r

  -- Function expression (creates closure with IR body placeholder)
  | function :
      paramNames = extractParamNames params →
      JSEvalExpr env store (fuel+1)
        (.function name params body async_ gen)
        (.val (.closure env name paramNames irBody) store)

  -- Arrow function
  | arrowFunction :
      paramNames = extractParamNames params →
      JSEvalExpr env store (fuel+1)
        (.arrowFunction params body async_)
        (.val (.closure env none paramNames irBody) store)

  -- Member access
  | member_ident_ok :
      JSEvalExpr env store fuel obj (.val (.record fields) s) →
      fields.lookup prop = some v →
      JSEvalExpr env store (fuel+1) (.member obj (.ident prop)) (.val v s)
  | member_ident_missing :
      JSEvalExpr env store fuel obj (.val (.record fields) s) →
      fields.lookup prop = none →
      JSEvalExpr env store (fuel+1) (.member obj (.ident prop)) (.val .undefined s)
  | member_signal :
      JSEvalExpr env store fuel obj r → isSignal r →
      JSEvalExpr env store (fuel+1) (.member obj prop) r

  -- Array literal
  | array :
      JSEvalElems env store fuel elements [] result →
      JSEvalExpr env store (fuel+1) (.array elements) result

  -- Object literal
  | object :
      JSEvalFields env store fuel properties [] result →
      JSEvalExpr env store (fuel+1) (.object properties) result

  -- Parenthesized expression
  | paren :
      JSEvalExpr env store fuel e result →
      JSEvalExpr env store (fuel+1) (.paren e) result

  -- Template literal (simplified: evaluates to string concatenation)
  | template_no_tag :
      tag = none →
      JSEvalTemplateExprs env store fuel exprs [] (.val (.array vals) s) →
      JSEvalExpr env store (fuel+1) (.template tag quasis exprs)
        (.val (.string (interleaveTemplate quasis vals)) s)

  -- New (constructor call)
  | new_ok :
      JSEvalExpr env store fuel callee (.val fv s1) →
      JSEvalArgs env s1 fuel args [] (.val (.array argVals) s2) →
      ApplyFunc fv argVals s2 fuel result →
      JSEvalExpr env store (fuel+1) (.«new» callee args) result

  -- Assignment (returns assigned value; env update happens at stmt level)
  | assign_simple :
      JSEvalExpr env store fuel right (.val v s) →
      JSEvalExpr env store (fuel+1) (.assign .assign target right) (.val v s)
  | assign_signal :
      JSEvalExpr env store fuel right r → isSignal r →
      JSEvalExpr env store (fuel+1) (.assign op target right) r

/-- Evaluate a list of JS argument expressions -/
inductive JSEvalArgs : Env → Store → Nat → List Expr → List IRValue →
    EvalResult → Prop where
  | nil :
      JSEvalArgs env store fuel [] acc (.val (.array acc.reverse) store)
  | cons_ok :
      JSEvalExpr env store fuel a (.val v s) →
      JSEvalArgs env s fuel rest (v :: acc) result →
      JSEvalArgs env store fuel (a :: rest) acc result
  | cons_signal :
      JSEvalExpr env store fuel a r → isSignal r →
      JSEvalArgs env store fuel (a :: rest) acc r

/-- Evaluate JS statements. Returns updated env and result. -/
inductive JSEvalStmt : Env → Store → Nat → Stmt → Env → EvalResult → Prop where
  | fuel_zero :
      JSEvalStmt env store 0 s env (.error "out of fuel")

  -- Expression statement
  | expr :
      JSEvalExpr env store fuel e result →
      JSEvalStmt env store (fuel+1) (.expr e) env result

  -- Block
  | block :
      JSEvalStmts env store fuel body env' result →
      JSEvalStmt env store (fuel+1) (.block body) env' result

  -- Variable declaration (const, no mutation)
  | varDecl_const_init :
      init = some initExpr →
      JSEvalExpr env store fuel initExpr (.val v s) →
      JSEvalStmt env store (fuel+1)
        (.varDecl .«const» [.mk (.ident name none) init])
        (env.extend name v) (.val .undefined s)
  | varDecl_const_init_signal :
      init = some initExpr →
      JSEvalExpr env store fuel initExpr r → isSignal r →
      JSEvalStmt env store (fuel+1)
        (.varDecl .«const» [.mk (.ident name none) init])
        env r

  -- Variable declaration (let, potentially mutable)
  | varDecl_let_init :
      init = some initExpr →
      JSEvalExpr env store fuel initExpr (.val v s) →
      JSEvalStmt env store (fuel+1)
        (.varDecl .«let» [.mk (.ident name none) init])
        (env.extend name v) (.val .undefined s)
  | varDecl_let_noinit :
      JSEvalStmt env store (fuel+1)
        (.varDecl .«let» [.mk (.ident name none) none])
        (env.extend name .undefined) (.val .undefined store)

  -- Return
  | return_some :
      JSEvalExpr env store fuel arg (.val v s) →
      JSEvalStmt env store (fuel+1) (.return_ (some arg)) env (.return_ v s)
  | return_none :
      JSEvalStmt env store (fuel+1) (.return_ none) env (.return_ .undefined store)
  | return_signal :
      JSEvalExpr env store fuel arg r → isSignal r →
      JSEvalStmt env store (fuel+1) (.return_ (some arg)) env r

  -- Throw
  | throw_ok :
      JSEvalExpr env store fuel arg (.val v s) →
      JSEvalStmt env store (fuel+1) (.throw arg) env (.throw_ v s)
  | throw_signal :
      JSEvalExpr env store fuel arg r → isSignal r →
      JSEvalStmt env store (fuel+1) (.throw arg) env r

  -- If-else
  | if_true :
      JSEvalExpr env store fuel test (.val cv s) →
      isTruthy cv = true →
      JSEvalStmt env s fuel cons env' result →
      JSEvalStmt env store (fuel+1) (.ifStmt test cons alt) env' result
  | if_false_some :
      JSEvalExpr env store fuel test (.val cv s) →
      isTruthy cv = false →
      JSEvalStmt env s fuel altStmt env' result →
      JSEvalStmt env store (fuel+1) (.ifStmt test cons (some altStmt)) env' result
  | if_false_none :
      JSEvalExpr env store fuel test (.val cv s) →
      isTruthy cv = false →
      JSEvalStmt env store (fuel+1) (.ifStmt test cons none) env (.val .undefined s)
  | if_signal :
      JSEvalExpr env store fuel test r → isSignal r →
      JSEvalStmt env store (fuel+1) (.ifStmt test cons alt) env r

  -- While loop
  | while_ :
      JSEvalLoop env store fuel test body result →
      JSEvalStmt env store (fuel+1) (.while_ test (.block [body])) env result

  -- Function declaration
  | funcDecl :
      paramNames = extractParamNames params →
      JSEvalStmt env store (fuel+1)
        (.funcDecl name params body async gen)
        (env.extend name (.closure env (some name) paramNames irBody))
        (.val .undefined store)

  -- Try-catch (no finalizer)
  | try_ok_no_fin :
      JSEvalStmts env store fuel block_ env' bodyResult →
      (∀ v s, bodyResult ≠ .throw_ v s) →
      JSEvalStmt env store (fuel+1) (.try_ block_ handler none) env' bodyResult
  | try_throw_no_fin :
      JSEvalStmts env store fuel block_ env' (.throw_ v s) →
      catchParam = (match handler with
        | some (.mk (some (.ident n _)) hbody) => some (n, hbody)
        | _ => none) →
      catchEnv = (match catchParam with
        | some (n, _) => env.extend n v
        | none => env) →
      catchBody = (match catchParam with
        | some (_, hb) => hb
        | none => []) →
      JSEvalStmts catchEnv s fuel catchBody catchEnv' result →
      JSEvalStmt env store (fuel+1) (.try_ block_ handler none) catchEnv' result

  -- Break / Continue
  | break_ :
      JSEvalStmt env store (fuel+1) (.break_ none) env (.break_ store)
  | continue_ :
      JSEvalStmt env store (fuel+1) (.continue_ none) env (.continue_ store)

  -- Empty statement
  | empty :
      JSEvalStmt env store (fuel+1) .empty env (.val .undefined store)

  -- For-of loop (simplified)
  | forOf :
      JSEvalExpr env store fuel right (.val (.array elems) s) →
      JSEvalForOf env s fuel varName elems result →
      JSEvalStmt env store (fuel+1)
        (.forOf (.varDecl .«const» [.mk (.ident varName none) none]) right (.block [body]))
        env result

/-- Evaluate a list of JS statements, threading environment -/
inductive JSEvalStmts : Env → Store → Nat → List Stmt → Env → EvalResult → Prop where
  | nil :
      JSEvalStmts env store fuel [] env (.val .undefined store)
  | cons_ok :
      JSEvalStmt env store fuel s env' (.val v s') →
      JSEvalStmts env' s' fuel rest finalEnv result →
      JSEvalStmts env store fuel (s :: rest) finalEnv result
  | cons_signal :
      JSEvalStmt env store fuel s env' result → isSignal result →
      JSEvalStmts env store fuel (s :: rest) env' result

/-- Evaluate a while loop in JS -/
inductive JSEvalLoop : Env → Store → Nat → Expr → Stmt → EvalResult → Prop where
  | fuel_zero :
      JSEvalLoop env store 0 test body (.error "out of fuel in loop")
  | cond_false :
      JSEvalExpr env store fuel test (.val cv s) →
      isTruthy cv = false →
      JSEvalLoop env store (fuel+1) test body (.val .undefined s)
  | body_val :
      JSEvalExpr env store fuel test (.val cv s) →
      isTruthy cv = true →
      JSEvalStmt env s fuel body env' (.val _ s') →
      JSEvalLoop env' s' fuel test body result →
      JSEvalLoop env store (fuel+1) test body result
  | body_break :
      JSEvalExpr env store fuel test (.val cv s) →
      isTruthy cv = true →
      JSEvalStmt env s fuel body env' (.break_ s') →
      JSEvalLoop env store (fuel+1) test body (.val .undefined s')
  | body_continue :
      JSEvalExpr env store fuel test (.val cv s) →
      isTruthy cv = true →
      JSEvalStmt env s fuel body env' (.continue_ s') →
      JSEvalLoop env' s' fuel test body result →
      JSEvalLoop env store (fuel+1) test body result
  | body_other :
      JSEvalExpr env store fuel test (.val cv s) →
      isTruthy cv = true →
      JSEvalStmt env s fuel body env' r →
      (∀ v' s', r ≠ .val v' s') → (∀ s', r ≠ .continue_ s') → (∀ s', r ≠ .break_ s') →
      JSEvalLoop env store (fuel+1) test body r
  | cond_signal :
      JSEvalExpr env store fuel test r → isSignal r →
      JSEvalLoop env store (fuel+1) test body r

/-- Evaluate for-of loop iteration -/
inductive JSEvalForOf : Env → Store → Nat → String → List IRValue →
    EvalResult → Prop where
  | nil :
      JSEvalForOf env store fuel varName [] (.val .undefined store)
  | cons_ok :
      JSEvalStmt (env.extend varName v) store fuel body env' (.val _ s') →
      JSEvalForOf env s' fuel varName rest result →
      JSEvalForOf env store fuel varName (v :: rest) result
  | cons_break :
      JSEvalStmt (env.extend varName v) store fuel body env' (.break_ s') →
      JSEvalForOf env store fuel varName (v :: rest) (.val .undefined s')
  | cons_signal :
      JSEvalStmt (env.extend varName v) store fuel body env' r →
      (∀ v' s', r ≠ .val v' s') → (∀ s', r ≠ .break_ s') →
      JSEvalForOf env store fuel varName (v :: rest) r

/-- Evaluate array literal elements (handling Option Expr for sparse arrays) -/
inductive JSEvalElems : Env → Store → Nat → List (Option Expr) → List IRValue →
    EvalResult → Prop where
  | nil :
      JSEvalElems env store fuel [] acc (.val (.array acc.reverse) store)
  | cons_some_ok :
      JSEvalExpr env store fuel e (.val v s) →
      JSEvalElems env s fuel rest (v :: acc) result →
      JSEvalElems env store fuel (some e :: rest) acc result
  | cons_none :
      JSEvalElems env store fuel rest (.undefined :: acc) result →
      JSEvalElems env store fuel (none :: rest) acc result
  | cons_signal :
      JSEvalExpr env store fuel e r → isSignal r →
      JSEvalElems env store fuel (some e :: rest) acc r

/-- Evaluate object property list -/
inductive JSEvalFields : Env → Store → Nat → List Property → List (String × IRValue) →
    EvalResult → Prop where
  | nil :
      JSEvalFields env store fuel [] acc (.val (.record acc.reverse) store)
  | cons_prop_ok :
      JSEvalExpr env store fuel key (.val (.string kname) s1) →
      JSEvalExpr env s1 fuel value (.val v s2) →
      JSEvalFields env s2 fuel rest ((kname, v) :: acc) result →
      JSEvalFields env store fuel (.prop key value .init false false :: rest) acc result
  | cons_signal :
      JSEvalExpr env store fuel key r → isSignal r →
      JSEvalFields env store fuel (.prop key value kind computed shorthand :: rest) acc r

/-- Evaluate template literal expressions -/
inductive JSEvalTemplateExprs : Env → Store → Nat → List Expr → List IRValue →
    EvalResult → Prop where
  | nil :
      JSEvalTemplateExprs env store fuel [] acc (.val (.array acc.reverse) store)
  | cons_ok :
      JSEvalExpr env store fuel e (.val v s) →
      JSEvalTemplateExprs env s fuel rest (v :: acc) result →
      JSEvalTemplateExprs env store fuel (e :: rest) acc result
  | cons_signal :
      JSEvalExpr env store fuel e r → isSignal r →
      JSEvalTemplateExprs env store fuel (e :: rest) acc r

end

end LeanJS.Semantics
