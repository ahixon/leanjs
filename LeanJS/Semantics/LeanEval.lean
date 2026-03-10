/-
  Big-step evaluation relation for Lean AST (core subset).

  Uses the shared `IRValue` domain. Lean closures store IR expression bodies
  (same approach as JSEval). Function application delegates to IR's `ApplyFunc`.

  Lean-specific: do-blocks, mutable variables (let mut), monadic bind,
  pattern matching with constructor patterns.
-/
import LeanJS.Lean.AST
import LeanJS.Semantics.Relation

namespace LeanJS.Semantics

open LeanJS.Lean
open LeanJS.IR

/-! ## Lean literal → IRValue conversion -/

def leanLitToValue : LeanLit → IRValue
  | .natVal n => .number (Float.ofNat n)
  | .float f => .number f
  | .string s => .string s
  | .bool b => .bool b

/-! ## Lean binary op string → IR binary op -/

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

/-! ## Lean pattern matching (must be before mutual block) -/

/-- Match a Lean pattern against an IRValue, returning bindings -/
def leanMatchPattern (pat : LeanPattern) (v : IRValue) : Option (List (String × IRValue)) :=
  match pat with
  | .wildcard => some []
  | .var name => some [(name, v)]
  | .lit l =>
    let expected := leanLitToValue l
    match expected, v with
    | .number a, .number b => if a == b then some [] else none
    | .string a, .string b => if a == b then some [] else none
    | .bool a, .bool b => if a == b then some [] else none
    | _, _ => none
  | .constructor tag bindings =>
    match v with
    | .constructed vtag args =>
      if tag == vtag && bindings.length == args.length then
        leanMatchPatterns bindings args
      else
        none
    | _ => none
where
  leanMatchPatterns : List LeanPattern → List IRValue → Option (List (String × IRValue))
    | [], [] => some []
    | p :: ps, v :: vs => do
      let b1 ← leanMatchPattern p v
      let b2 ← leanMatchPatterns ps vs
      return b1 ++ b2
    | _, _ => none

/-! ## Lean big-step evaluation relation (core subset) -/

set_option maxHeartbeats 3200000 in
set_option autoImplicit true in
mutual

/-- Big-step evaluation for Lean expressions -/
inductive LeanEvalExpr : Env → Store → Nat → LeanExpr → EvalResult → Prop where
  | fuel_zero :
      LeanEvalExpr env store 0 e (.error "out of fuel")

  -- Identifier
  | ident_ok :
      env.lookup name = some v →
      LeanEvalExpr env store (fuel+1) (.ident name) (.val v store)
  | ident_unbound :
      env.lookup name = none →
      LeanEvalExpr env store (fuel+1) (.ident name) (.error s!"unbound: {name}")

  -- Literal
  | lit :
      LeanEvalExpr env store (fuel+1) (.lit l) (.val (leanLitToValue l) store)

  -- Application
  | app_ok :
      LeanEvalExpr env store fuel fn (.val fv s1) →
      LeanEvalExpr env s1 fuel arg (.val av s2) →
      ApplyFunc fv [av] s2 fuel result →
      LeanEvalExpr env store (fuel+1) (.app fn arg) result
  | app_fn_signal :
      LeanEvalExpr env store fuel fn r → isSignal r →
      LeanEvalExpr env store (fuel+1) (.app fn arg) r
  | app_arg_signal :
      LeanEvalExpr env store fuel fn (.val fv s1) →
      LeanEvalExpr env s1 fuel arg r → isSignal r →
      LeanEvalExpr env store (fuel+1) (.app fn arg) r

  -- Lambda (creates closure with IR body placeholder)
  | lam :
      paramNames = params.map LeanParam.name →
      LeanEvalExpr env store (fuel+1)
        (.lam params body)
        (.val (.closure env none paramNames irBody) store)

  -- Let binding
  | let_ok :
      LeanEvalExpr env store fuel value (.val v s) →
      LeanEvalExpr (env.extend name v) s fuel body result →
      LeanEvalExpr env store (fuel+1) (.«let» name ty value body) result
  | let_signal :
      LeanEvalExpr env store fuel value r → isSignal r →
      LeanEvalExpr env store (fuel+1) (.«let» name ty value body) r

  -- Do-block
  | doBlock :
      LeanEvalDoBlock env store fuel elems result →
      LeanEvalExpr env store (fuel+1) (.doBlock elems) result

  -- If-then-else
  | if_true :
      LeanEvalExpr env store fuel condE (.val cv s) →
      isTruthy cv = true →
      LeanEvalExpr env s fuel then_ result →
      LeanEvalExpr env store (fuel+1) (.«if» condE then_ else_) result
  | if_false_some :
      LeanEvalExpr env store fuel condE (.val cv s) →
      isTruthy cv = false →
      LeanEvalExpr env s fuel elseExpr result →
      LeanEvalExpr env store (fuel+1) (.«if» condE then_ (some elseExpr)) result
  | if_false_none :
      LeanEvalExpr env store fuel condE (.val cv s) →
      isTruthy cv = false →
      LeanEvalExpr env store (fuel+1) (.«if» condE then_ none) (.val .unit s)
  | if_signal :
      LeanEvalExpr env store fuel condE r → isSignal r →
      LeanEvalExpr env store (fuel+1) (.«if» condE then_ else_) r

  -- Match
  | «match» :
      LeanEvalExpr env store fuel scrutinee (.val sv s) →
      LeanEvalMatchAlts env s fuel sv alts result →
      LeanEvalExpr env store (fuel+1) (.«match» scrutinee alts) result
  | match_signal :
      LeanEvalExpr env store fuel scrutinee r → isSignal r →
      LeanEvalExpr env store (fuel+1) (.«match» scrutinee alts) r

  -- Return
  | «return» :
      LeanEvalExpr env store fuel value (.val v s) →
      LeanEvalExpr env store (fuel+1) (.«return» value) (.return_ v s)
  | return_signal :
      LeanEvalExpr env store fuel value r → isSignal r →
      LeanEvalExpr env store (fuel+1) (.«return» value) r

  -- Struct literal
  | structLit :
      LeanEvalStructFields env store fuel fields [] result →
      LeanEvalExpr env store (fuel+1) (.structLit name fields) result

  -- Array literal
  | arrayLit :
      LeanEvalArrayElems env store fuel elements [] result →
      LeanEvalExpr env store (fuel+1) (.arrayLit elements) result

  -- Projection
  | proj_ok :
      LeanEvalExpr env store fuel expr (.val (.record fields) s) →
      fields.lookup field = some v →
      LeanEvalExpr env store (fuel+1) (.proj expr field) (.val v s)
  | proj_missing :
      LeanEvalExpr env store fuel expr (.val (.record fields) s) →
      fields.lookup field = none →
      LeanEvalExpr env store (fuel+1) (.proj expr field) (.error s!"missing field: {field}")
  | proj_signal :
      LeanEvalExpr env store fuel expr r → isSignal r →
      LeanEvalExpr env store (fuel+1) (.proj expr field) r

  -- Binary operator
  | binOp_ok :
      LeanEvalExpr env store fuel left (.val lv s1) →
      LeanEvalExpr env s1 fuel right (.val rv s2) →
      leanBinOpToIR op = some irop →
      evalBinOp irop lv rv s2 = result →
      LeanEvalExpr env store (fuel+1) (.binOp op left right) result
  | binOp_left_signal :
      LeanEvalExpr env store fuel left r → isSignal r →
      LeanEvalExpr env store (fuel+1) (.binOp op left right) r
  | binOp_right_signal :
      LeanEvalExpr env store fuel left (.val lv s1) →
      LeanEvalExpr env s1 fuel right r → isSignal r →
      LeanEvalExpr env store (fuel+1) (.binOp op left right) r

  -- Unary operator
  | unaryOp_ok :
      LeanEvalExpr env store fuel arg (.val v s) →
      leanUnaryOpToIR op = some irop →
      evalUnaryOp irop v s = result →
      LeanEvalExpr env store (fuel+1) (.unaryOp op arg) result
  | unaryOp_signal :
      LeanEvalExpr env store fuel arg r → isSignal r →
      LeanEvalExpr env store (fuel+1) (.unaryOp op arg) r

  -- Unit
  | unit :
      LeanEvalExpr env store (fuel+1) .unit (.val .unit store)

  -- Ref operations
  | refNew_ok :
      LeanEvalExpr env store fuel value (.val v s) →
      s.alloc v = (s', loc) →
      LeanEvalExpr env store (fuel+1) (.refNew value) (.val (.ref loc) s')
  | refGet_ok :
      LeanEvalExpr env store fuel ref (.val (.ref loc) s) →
      s.read loc = some v →
      LeanEvalExpr env store (fuel+1) (.refGet ref) (.val v s)
  | refSet_ok :
      LeanEvalExpr env store fuel ref (.val (.ref loc) s1) →
      LeanEvalExpr env s1 fuel value (.val v s2) →
      s2.write loc v = some s3 →
      LeanEvalExpr env store (fuel+1) (.refSet ref value) (.val .unit s3)

  -- Try-catch
  | try_ok :
      LeanEvalExpr env store fuel body bodyResult →
      (∀ v s, bodyResult ≠ .throw_ v s) →
      LeanEvalExpr env store (fuel+1) (.«try» body catchVar handler finalizer) bodyResult
  | try_throw :
      LeanEvalExpr env store fuel body (.throw_ v s) →
      catchEnv = (match catchVar with | some n => env.extend n v | none => env) →
      handlerExpr = (match handler with | some h => h | none => .unit) →
      LeanEvalExpr catchEnv s fuel handlerExpr result →
      LeanEvalExpr env store (fuel+1) (.«try» body catchVar handler finalizer) result

  -- Throw
  | «throw» :
      LeanEvalExpr env store fuel value (.val v s) →
      LeanEvalExpr env store (fuel+1) (.«throw» value) (.throw_ v s)

  -- Paren
  | paren :
      LeanEvalExpr env store fuel inner result →
      LeanEvalExpr env store (fuel+1) (.paren inner) result

  -- Hole (produces error)
  | hole :
      LeanEvalExpr env store (fuel+1) .hole (.error "hole")

/-- Evaluate a do-block element list -/
inductive LeanEvalDoBlock : Env → Store → Nat → List LeanDoElem → EvalResult → Prop where
  | nil :
      LeanEvalDoBlock env store fuel [] (.val .unit store)
  | singleton_eval :
      LeanEvalExpr env store fuel e result →
      LeanEvalDoBlock env store fuel [.eval e] result
  | cons_eval_ok :
      LeanEvalExpr env store fuel e (.val _ s) →
      LeanEvalDoBlock env s fuel rest result →
      rest ≠ [] →
      LeanEvalDoBlock env store fuel (.eval e :: rest) result
  | cons_eval_signal :
      LeanEvalExpr env store fuel e r → isSignal r →
      rest ≠ [] →
      LeanEvalDoBlock env store fuel (.eval e :: rest) r
  | cons_bind_ok :
      LeanEvalExpr env store fuel value (.val v s) →
      LeanEvalDoBlock (env.extend name v) s fuel rest result →
      LeanEvalDoBlock env store fuel (.bind name ty value :: rest) result
  | cons_bind_signal :
      LeanEvalExpr env store fuel value r → isSignal r →
      LeanEvalDoBlock env store fuel (.bind name ty value :: rest) r
  | cons_letDecl_ok :
      LeanEvalExpr env store fuel value (.val v s) →
      LeanEvalDoBlock (env.extend name v) s fuel rest result →
      LeanEvalDoBlock env store fuel (.letDecl name ty value :: rest) result
  | cons_letDecl_signal :
      LeanEvalExpr env store fuel value r → isSignal r →
      LeanEvalDoBlock env store fuel (.letDecl name ty value :: rest) r
  | cons_mutDecl_ok :
      LeanEvalExpr env store fuel value (.val v s) →
      s.alloc v = (s', loc) →
      LeanEvalDoBlock (env.extend name (.ref loc)) s' fuel rest result →
      LeanEvalDoBlock env store fuel (.mutDecl name ty value :: rest) result
  | cons_mutDecl_signal :
      LeanEvalExpr env store fuel value r → isSignal r →
      LeanEvalDoBlock env store fuel (.mutDecl name ty value :: rest) r
  | cons_reassign_ok :
      env.lookup name = some (.ref loc) →
      LeanEvalExpr env store fuel value (.val v s) →
      s.write loc v = some s' →
      LeanEvalDoBlock env s' fuel rest result →
      LeanEvalDoBlock env store fuel (.reassign name value :: rest) result
  | cons_doReturn :
      LeanEvalExpr env store fuel value (.val v s) →
      LeanEvalDoBlock env store fuel [.doReturn value] (.return_ v s)
  | cons_doReturn_signal :
      LeanEvalExpr env store fuel value r → isSignal r →
      LeanEvalDoBlock env store fuel [.doReturn value] r
  | cons_doIf_true :
      LeanEvalExpr env store fuel condE (.val cv s) →
      isTruthy cv = true →
      LeanEvalDoBlock env s fuel thenElems result →
      LeanEvalDoBlock env store fuel (.doIf condE thenElems elseElems :: rest) result
  | cons_doIf_false :
      LeanEvalExpr env store fuel condE (.val cv s) →
      isTruthy cv = false →
      LeanEvalDoBlock env s fuel elseElems result →
      LeanEvalDoBlock env store fuel (.doIf condE thenElems elseElems :: rest) result
  | cons_doWhile :
      LeanEvalDoWhile env store fuel condE body result →
      LeanEvalDoBlock env store fuel (.doWhile condE body :: rest) result

/-- Evaluate Lean match alternatives -/
inductive LeanEvalMatchAlts : Env → Store → Nat → IRValue →
    List LeanMatchAlt → EvalResult → Prop where
  | no_alts :
      LeanEvalMatchAlts env store fuel sv [] (.error "no matching alternative")
  | match_ok :
      leanMatchPattern pat sv = some bindings →
      LeanEvalExpr (env.extendMany bindings) store fuel body result →
      LeanEvalMatchAlts env store fuel sv (.mk pat body :: rest) result
  | match_fail :
      leanMatchPattern pat sv = none →
      LeanEvalMatchAlts env store fuel sv rest result →
      LeanEvalMatchAlts env store fuel sv (.mk pat body :: rest) result

/-- Evaluate Lean struct fields -/
inductive LeanEvalStructFields : Env → Store → Nat → List (String × LeanExpr) →
    List (String × IRValue) → EvalResult → Prop where
  | nil :
      LeanEvalStructFields env store fuel [] acc (.val (.record acc.reverse) store)
  | cons_ok :
      LeanEvalExpr env store fuel e (.val v s) →
      LeanEvalStructFields env s fuel rest ((name, v) :: acc) result →
      LeanEvalStructFields env store fuel ((name, e) :: rest) acc result
  | cons_signal :
      LeanEvalExpr env store fuel e r → isSignal r →
      LeanEvalStructFields env store fuel ((name, e) :: rest) acc r

/-- Evaluate Lean array elements -/
inductive LeanEvalArrayElems : Env → Store → Nat → List LeanExpr →
    List IRValue → EvalResult → Prop where
  | nil :
      LeanEvalArrayElems env store fuel [] acc (.val (.array acc.reverse) store)
  | cons_ok :
      LeanEvalExpr env store fuel e (.val v s) →
      LeanEvalArrayElems env s fuel rest (v :: acc) result →
      LeanEvalArrayElems env store fuel (e :: rest) acc result
  | cons_signal :
      LeanEvalExpr env store fuel e r → isSignal r →
      LeanEvalArrayElems env store fuel (e :: rest) acc r

/-- Evaluate Lean do-while loop -/
inductive LeanEvalDoWhile : Env → Store → Nat → LeanExpr → List LeanDoElem →
    EvalResult → Prop where
  | fuel_zero :
      LeanEvalDoWhile env store 0 condE body (.error "out of fuel in loop")
  | cond_false :
      LeanEvalExpr env store fuel condE (.val cv s) →
      isTruthy cv = false →
      LeanEvalDoWhile env store (fuel+1) condE body (.val .unit s)
  | body_ok :
      LeanEvalExpr env store fuel condE (.val cv s) →
      isTruthy cv = true →
      LeanEvalDoBlock env s fuel body (.val _ s') →
      LeanEvalDoWhile env s' fuel condE body result →
      LeanEvalDoWhile env store (fuel+1) condE body result
  | body_signal :
      LeanEvalExpr env store fuel condE (.val cv s) →
      isTruthy cv = true →
      LeanEvalDoBlock env s fuel body r →
      (∀ v' s', r ≠ .val v' s') →
      LeanEvalDoWhile env store (fuel+1) condE body r
  | cond_signal :
      LeanEvalExpr env store fuel condE r → isSignal r →
      LeanEvalDoWhile env store (fuel+1) condE body r

end

end LeanJS.Semantics
