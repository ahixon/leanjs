/-
  Inductive big-step evaluation relation for the LeanJS IR.

  Mirrors `partial def eval` as a kernel-transparent inductive,
  enabling formal proofs (determinism, fuel monotonicity, simulation).
  Each constructor corresponds to a clause of `eval` or its where-helpers.
-/
import LeanJS.Semantics.Value
import LeanJS.Semantics.BinOp
import LeanJS.Semantics.Match

namespace LeanJS.Semantics

open LeanJS.IR

/-- Predicate: result is not a `.val` (i.e., a control flow signal or error) -/
def isSignal : EvalResult → Prop
  | .val _ _ => False
  | _ => True

/-- A result is not a fuel exhaustion error -/
def notFuelError : EvalResult → Prop
  | .error "out of fuel" => False
  | .error "out of fuel in loop" => False
  | _ => True

instance : DecidablePred isSignal := fun r =>
  match r with
  | .val _ _ => .isFalse (by simp [isSignal])
  | .return_ _ _ => .isTrue (by simp [isSignal])
  | .break_ _ => .isTrue (by simp [isSignal])
  | .continue_ _ => .isTrue (by simp [isSignal])
  | .throw_ _ _ => .isTrue (by simp [isSignal])
  | .error _ => .isTrue (by simp [isSignal])

set_option maxHeartbeats 3200000 in
set_option autoImplicit true in
mutual

/-- Big-step evaluation relation for IR expressions -/
inductive Eval : Env → Store → Nat → IRExpr → EvalResult → Prop where
  -- Fuel exhaustion
  | fuel_zero :
      Eval env store 0 e (.error "out of fuel")

  -- Literals and variables
  | lit :
      Eval env store (fuel+1) (.lit v) (.val (irLitToValue v) store)
  | var_ok :
      env.lookup name = some v →
      Eval env store (fuel+1) (.var name) (.val v store)
  | var_unbound :
      env.lookup name = none →
      Eval env store (fuel+1) (.var name) (.error s!"unbound variable: {name}")
  | undefined :
      Eval env store (fuel+1) .undefined (.val .undefined store)
  | this_ok :
      env.lookup "this" = some v →
      Eval env store (fuel+1) .this (.val v store)
  | this_none :
      env.lookup "this" = none →
      Eval env store (fuel+1) .this (.val .undefined store)

  -- Let binding
  | let_ok :
      Eval env store fuel val (.val v s) →
      Eval (env.extend name v) s fuel body result →
      Eval env store (fuel+1) (.«let» name ty val body) result
  | let_signal :
      Eval env store fuel val r → isSignal r →
      Eval env store (fuel+1) (.«let» name ty val body) r

  -- Lambda
  | lam :
      paramNames = params.map Prod.fst →
      Eval env store (fuel+1)
        (.lam name params captures body async_ gen)
        (.val (.closure env name paramNames body) store)

  -- Application
  | app_ok :
      Eval env store fuel func (.val fv s1) →
      EvalArgs env s1 fuel args [] (.val (.array argVals) s2) →
      ApplyFunc fv argVals s2 fuel result →
      Eval env store (fuel+1) (.app func args) result
  | app_func_signal :
      Eval env store fuel func r → isSignal r →
      Eval env store (fuel+1) (.app func args) r
  | app_args_signal :
      Eval env store fuel func (.val fv s1) →
      EvalArgs env s1 fuel args [] r → isSignal r →
      Eval env store (fuel+1) (.app func args) r

  -- Binary operators
  | binOp_ok :
      Eval env store fuel left (.val lv s1) →
      Eval env s1 fuel right (.val rv s2) →
      evalBinOp op lv rv s2 = result →
      Eval env store (fuel+1) (.binOp op left right) result
  | binOp_left_signal :
      Eval env store fuel left r → isSignal r →
      Eval env store (fuel+1) (.binOp op left right) r
  | binOp_right_signal :
      Eval env store fuel left (.val lv s1) →
      Eval env s1 fuel right r → isSignal r →
      Eval env store (fuel+1) (.binOp op left right) r

  -- Unary operators
  | unaryOp_ok :
      Eval env store fuel arg (.val v s) →
      evalUnaryOp op v s = result →
      Eval env store (fuel+1) (.unaryOp op arg) result
  | unaryOp_signal :
      Eval env store fuel arg r → isSignal r →
      Eval env store (fuel+1) (.unaryOp op arg) r

  -- mkRef
  | mkRef_ok :
      Eval env store fuel val (.val v s) →
      s.alloc v = (s', loc) →
      Eval env store (fuel+1) (.mkRef val) (.val (.ref loc) s')
  | mkRef_signal :
      Eval env store fuel val r → isSignal r →
      Eval env store (fuel+1) (.mkRef val) r

  -- deref
  | deref_ok :
      Eval env store fuel ref (.val (.ref loc) s) →
      s.read loc = some v →
      Eval env store (fuel+1) (.deref ref) (.val v s)
  | deref_dangling :
      Eval env store fuel ref (.val (.ref loc) s) →
      s.read loc = none →
      Eval env store (fuel+1) (.deref ref) (.error s!"dangling ref: {repr loc}")
  | deref_non_ref :
      Eval env store fuel ref (.val v s) → (∀ loc, v ≠ .ref loc) →
      Eval env store (fuel+1) (.deref ref) (.error "deref of non-ref")
  | deref_signal :
      Eval env store fuel ref r → isSignal r →
      Eval env store (fuel+1) (.deref ref) r

  -- assign
  | assign_ok :
      Eval env store fuel ref (.val (.ref loc) s1) →
      Eval env s1 fuel val (.val v s2) →
      s2.write loc v = some s3 →
      Eval env store (fuel+1) (.assign ref val) (.val .unit s3)
  | assign_dangling :
      Eval env store fuel ref (.val (.ref loc) s1) →
      Eval env s1 fuel val (.val v s2) →
      s2.write loc v = none →
      Eval env store (fuel+1) (.assign ref val)
        (.error s!"dangling ref on write: {repr loc}")
  | assign_val_signal :
      Eval env store fuel ref (.val (.ref loc) s1) →
      Eval env s1 fuel val r → isSignal r →
      Eval env store (fuel+1) (.assign ref val) r
  | assign_non_ref :
      Eval env store fuel ref (.val v s) → (∀ loc, v ≠ .ref loc) →
      Eval env store (fuel+1) (.assign ref val) (.error "assign to non-ref")
  | assign_ref_signal :
      Eval env store fuel ref r → isSignal r →
      Eval env store (fuel+1) (.assign ref val) r

  -- Record
  | record :
      EvalFields env store fuel fields [] result →
      Eval env store (fuel+1) (.record fields) result

  -- Project
  | project_record_ok :
      Eval env store fuel expr (.val (.record fields) s) →
      fields.lookup field = some v →
      Eval env store (fuel+1) (.project expr field) (.val v s)
  | project_record_missing :
      Eval env store fuel expr (.val (.record fields) s) →
      fields.lookup field = none →
      Eval env store (fuel+1) (.project expr field)
        (.error s!"missing field: {field}")
  | project_constructed_tag :
      Eval env store fuel expr (.val (.constructed tag args) s) →
      field = "_tag" →
      Eval env store (fuel+1) (.project expr field) (.val (.string tag) s)
  | project_constructed_other :
      Eval env store fuel expr (.val (.constructed tag args) s) →
      field ≠ "_tag" →
      Eval env store (fuel+1) (.project expr field)
        (.error s!"cannot project {field} from constructed value")
  | project_non_record :
      Eval env store fuel expr (.val v s) →
      (∀ fs, v ≠ .record fs) → (∀ t a, v ≠ .constructed t a) →
      Eval env store (fuel+1) (.project expr field)
        (.error "project on non-record")
  | project_signal :
      Eval env store fuel expr r → isSignal r →
      Eval env store (fuel+1) (.project expr field) r

  -- ProjectIdx
  | projectIdx_string_record_ok :
      Eval env store fuel expr (.val rv s1) →
      Eval env s1 fuel idx (.val (.string field) s2) →
      rv = .record fields →
      fields.lookup field = some v →
      Eval env store (fuel+1) (.projectIdx expr idx) (.val v s2)
  | projectIdx_string_record_missing :
      Eval env store fuel expr (.val rv s1) →
      Eval env s1 fuel idx (.val (.string field) s2) →
      rv = .record fields →
      fields.lookup field = none →
      Eval env store (fuel+1) (.projectIdx expr idx)
        (.error s!"missing field: {field}")
  | projectIdx_string_non_record :
      Eval env store fuel expr (.val rv s1) →
      Eval env s1 fuel idx (.val (.string field) s2) →
      (∀ fs, rv ≠ .record fs) →
      Eval env store (fuel+1) (.projectIdx expr idx)
        (.error "projectIdx string on non-record")
  | projectIdx_number_array_ok :
      Eval env store fuel expr (.val rv s1) →
      Eval env s1 fuel idx (.val (.number n) s2) →
      rv = .array elems →
      i = n.toUInt32.toNat → i < elems.length →
      Eval env store (fuel+1) (.projectIdx expr idx)
        (.val (elems[i]!) s2)
  | projectIdx_number_array_oob :
      Eval env store fuel expr (.val rv s1) →
      Eval env s1 fuel idx (.val (.number n) s2) →
      rv = .array elems →
      n.toUInt32.toNat ≥ elems.length →
      Eval env store (fuel+1) (.projectIdx expr idx) (.val .undefined s2)
  | projectIdx_number_non_array :
      Eval env store fuel expr (.val rv s1) →
      Eval env s1 fuel idx (.val (.number n) s2) →
      (∀ es, rv ≠ .array es) →
      Eval env store (fuel+1) (.projectIdx expr idx)
        (.error "projectIdx number on non-array")
  | projectIdx_bad_index :
      Eval env store fuel expr (.val rv s1) →
      Eval env s1 fuel idx (.val iv s2) →
      (∀ s, iv ≠ .string s) → (∀ n, iv ≠ .number n) →
      Eval env store (fuel+1) (.projectIdx expr idx)
        (.error "projectIdx with non-string/number index")
  | projectIdx_idx_signal :
      Eval env store fuel expr (.val rv s1) →
      Eval env s1 fuel idx r → isSignal r →
      Eval env store (fuel+1) (.projectIdx expr idx) r
  | projectIdx_expr_signal :
      Eval env store fuel expr r → isSignal r →
      Eval env store (fuel+1) (.projectIdx expr idx) r

  -- Array
  | array :
      EvalElems env store fuel elements [] result →
      Eval env store (fuel+1) (.array elements) result

  -- Index
  | index_ok :
      Eval env store fuel arr (.val (.array elems) s1) →
      Eval env s1 fuel idx (.val (.number n) s2) →
      i = n.toUInt32.toNat → i < elems.length →
      Eval env store (fuel+1) (.index arr idx) (.val (elems[i]!) s2)
  | index_oob :
      Eval env store fuel arr (.val (.array elems) s1) →
      Eval env s1 fuel idx (.val (.number n) s2) →
      n.toUInt32.toNat ≥ elems.length →
      Eval env store (fuel+1) (.index arr idx) (.val .undefined s2)
  | index_bad_idx :
      Eval env store fuel arr (.val (.array elems) s1) →
      Eval env s1 fuel idx (.val v s2) → (∀ n, v ≠ .number n) →
      Eval env store (fuel+1) (.index arr idx)
        (.error "array index must be a number")
  | index_idx_signal :
      Eval env store fuel arr (.val (.array elems) s1) →
      Eval env s1 fuel idx r → isSignal r →
      Eval env store (fuel+1) (.index arr idx) r
  | index_non_array :
      Eval env store fuel arr (.val v s) → (∀ es, v ≠ .array es) →
      Eval env store (fuel+1) (.index arr idx)
        (.error "index on non-array")
  | index_arr_signal :
      Eval env store fuel arr r → isSignal r →
      Eval env store (fuel+1) (.index arr idx) r

  -- If
  | if_true :
      Eval env store fuel condE (.val cv s) →
      isTruthy cv = true →
      Eval env s fuel then_ result →
      Eval env store (fuel+1) (.«if» condE then_ else_) result
  | if_false :
      Eval env store fuel condE (.val cv s) →
      isTruthy cv = false →
      Eval env s fuel else_ result →
      Eval env store (fuel+1) (.«if» condE then_ else_) result
  | if_signal :
      Eval env store fuel condE r → isSignal r →
      Eval env store (fuel+1) (.«if» condE then_ else_) r

  -- Ternary (same as if)
  | ternary_true :
      Eval env store fuel condE (.val cv s) →
      isTruthy cv = true →
      Eval env s fuel then_ result →
      Eval env store (fuel+1) (.ternary condE then_ else_) result
  | ternary_false :
      Eval env store fuel condE (.val cv s) →
      isTruthy cv = false →
      Eval env s fuel else_ result →
      Eval env store (fuel+1) (.ternary condE then_ else_) result
  | ternary_signal :
      Eval env store fuel condE r → isSignal r →
      Eval env store (fuel+1) (.ternary condE then_ else_) r

  -- Loop
  | loop :
      EvalLoop env store fuel condE body result →
      Eval env store (fuel+1) (.loop condE body) result

  -- Seq
  | seq :
      EvalSeq env store fuel exprs result →
      Eval env store (fuel+1) (.seq exprs) result

  -- Return
  | return_ok :
      Eval env store fuel val (.val v s) →
      Eval env store (fuel+1) (.«return» val) (.return_ v s)
  | return_signal :
      Eval env store fuel val r → isSignal r →
      Eval env store (fuel+1) (.«return» val) r

  -- Break / Continue
  | «break» :
      Eval env store (fuel+1) .«break» (.break_ store)
  | «continue» :
      Eval env store (fuel+1) .«continue» (.continue_ store)

  -- Throw
  | throw_ok :
      Eval env store fuel val (.val v s) →
      Eval env store (fuel+1) (.throw val) (.throw_ v s)
  | throw_signal :
      Eval env store fuel val r → isSignal r →
      Eval env store (fuel+1) (.throw val) r

  -- TryCatch (no finalizer)
  | tryCatch_ok_no_fin :
      Eval env store fuel body bodyResult →
      (∀ v s, bodyResult ≠ .throw_ v s) →
      Eval env store (fuel+1) (.tryCatch body catchVar handler none) bodyResult
  | tryCatch_throw_no_fin :
      Eval env store fuel body (.throw_ v s) →
      catchEnv = (match catchVar with | some n => env.extend n v | none => env) →
      Eval catchEnv s fuel handler result →
      Eval env store (fuel+1) (.tryCatch body catchVar handler none) result

  -- TryCatch (with finalizer)
  | tryCatch_ok_fin_ok :
      Eval env store fuel body bodyResult →
      (∀ v s, bodyResult ≠ .throw_ v s) →
      afterCatch = bodyResult →
      finStore = (match afterCatch.getStore with | some s => s | none => store) →
      Eval env finStore fuel fin (.val finV finS) →
      result = (match afterCatch with
        | .val v _ => .val v finS
        | .return_ v _ => .return_ v finS
        | .break_ _ => .break_ finS
        | .continue_ _ => .continue_ finS
        | .throw_ v _ => .throw_ v finS
        | .error msg => .error msg) →
      Eval env store (fuel+1) (.tryCatch body catchVar handler (some fin)) result
  | tryCatch_throw_fin_ok :
      Eval env store fuel body (.throw_ tv ts) →
      catchEnv = (match catchVar with | some n => env.extend n tv | none => env) →
      Eval catchEnv ts fuel handler afterCatch →
      finStore = (match afterCatch.getStore with | some s => s | none => store) →
      Eval env finStore fuel fin (.val finV finS) →
      result = (match afterCatch with
        | .val v _ => .val v finS
        | .return_ v _ => .return_ v finS
        | .break_ _ => .break_ finS
        | .continue_ _ => .continue_ finS
        | .throw_ v _ => .throw_ v finS
        | .error msg => .error msg) →
      Eval env store (fuel+1) (.tryCatch body catchVar handler (some fin)) result
  | tryCatch_ok_fin_signal :
      Eval env store fuel body afterCatch →
      (∀ v s, afterCatch ≠ .throw_ v s) →
      notFuelError afterCatch →
      finStore = (match afterCatch.getStore with | some s => s | none => store) →
      Eval env finStore fuel fin finResult → isSignal finResult →
      Eval env store (fuel+1) (.tryCatch body catchVar handler (some fin)) finResult
  | tryCatch_throw_fin_signal :
      Eval env store fuel body (.throw_ tv ts) →
      catchEnv = (match catchVar with | some n => env.extend n tv | none => env) →
      Eval catchEnv ts fuel handler afterCatch →
      notFuelError afterCatch →
      finStore = (match afterCatch.getStore with | some s => s | none => store) →
      Eval env finStore fuel fin finResult → isSignal finResult →
      Eval env store (fuel+1) (.tryCatch body catchVar handler (some fin)) finResult

  -- Match
  | «match» :
      Eval env store fuel scrutinee (.val sv s) →
      EvalMatch env s fuel sv cases result →
      Eval env store (fuel+1) (.«match» scrutinee cases) result
  | match_signal :
      Eval env store fuel scrutinee r → isSignal r →
      Eval env store (fuel+1) (.«match» scrutinee cases) r

  -- Construct
  | construct_ok :
      EvalArgs env store fuel args [] (.val (.array argVals) s) →
      Eval env store (fuel+1) (.construct name args)
        (.val (.constructed name argVals) s)
  | construct_signal :
      EvalArgs env store fuel args [] r → isSignal r →
      Eval env store (fuel+1) (.construct name args) r

  -- NewObj
  | newObj_ok :
      Eval env store fuel callee (.val fv s1) →
      EvalArgs env s1 fuel args [] (.val (.array argVals) s2) →
      ApplyFunc fv argVals s2 fuel result →
      Eval env store (fuel+1) (.newObj callee args) result
  | newObj_callee_signal :
      Eval env store fuel callee r → isSignal r →
      Eval env store (fuel+1) (.newObj callee args) r
  | newObj_args_signal :
      Eval env store fuel callee (.val fv s1) →
      EvalArgs env s1 fuel args [] r → isSignal r →
      Eval env store (fuel+1) (.newObj callee args) r

  -- Async/generators (simplified: pass through)
  | «await» :
      Eval env store fuel expr result →
      Eval env store (fuel+1) (.«await» expr) result
  | yield_some :
      Eval env store fuel expr result →
      Eval env store (fuel+1) (.«yield» (some expr) delegate) result
  | yield_none :
      Eval env store (fuel+1) (.«yield» none delegate) (.val .undefined store)

  -- Spread (pass through)
  | spread :
      Eval env store fuel expr result →
      Eval env store (fuel+1) (.spread expr) result

/-- Evaluate a list of argument expressions -/
inductive EvalArgs : Env → Store → Nat → List IRExpr → List IRValue →
    EvalResult → Prop where
  | nil :
      EvalArgs env store fuel [] acc (.val (.array acc.reverse) store)
  | cons_ok :
      Eval env store fuel a (.val v s) →
      EvalArgs env s fuel rest (v :: acc) result →
      EvalArgs env store fuel (a :: rest) acc result
  | cons_signal :
      Eval env store fuel a r → isSignal r →
      EvalArgs env store fuel (a :: rest) acc r

/-- Apply a closure or value to arguments -/
inductive ApplyFunc : IRValue → List IRValue → Store → Nat →
    EvalResult → Prop where
  | closure_ok :
      callEnv = closureEnv.extendMany (params.zip args) →
      callEnv' = (match name with | some n => callEnv.extend n (.closure closureEnv name params body) | none => callEnv) →
      Eval callEnv' store fuel body bodyResult →
      result = (match bodyResult with | .return_ v s => .val v s | other => other) →
      ApplyFunc (.closure closureEnv name params body) args store fuel result
  | non_function :
      (∀ cenv n ps b, fv ≠ .closure cenv n ps b) →
      ApplyFunc fv args store fuel (.error "application of non-function")

/-- Evaluate record fields -/
inductive EvalFields : Env → Store → Nat → List (String × IRExpr) →
    List (String × IRValue) → EvalResult → Prop where
  | nil :
      EvalFields env store fuel [] acc (.val (.record acc.reverse) store)
  | cons_ok :
      Eval env store fuel e (.val v s) →
      EvalFields env s fuel rest ((name, v) :: acc) result →
      EvalFields env store fuel ((name, e) :: rest) acc result
  | cons_signal :
      Eval env store fuel e r → isSignal r →
      EvalFields env store fuel ((name, e) :: rest) acc r

/-- Evaluate array elements -/
inductive EvalElems : Env → Store → Nat → List IRExpr → List IRValue →
    EvalResult → Prop where
  | nil :
      EvalElems env store fuel [] acc (.val (.array acc.reverse) store)
  | cons_ok :
      Eval env store fuel e (.val v s) →
      EvalElems env s fuel rest (v :: acc) result →
      EvalElems env store fuel (e :: rest) acc result
  | cons_signal :
      Eval env store fuel e r → isSignal r →
      EvalElems env store fuel (e :: rest) acc r

/-- Evaluate a while loop -/
inductive EvalLoop : Env → Store → Nat → IRExpr → IRExpr →
    EvalResult → Prop where
  | fuel_zero :
      EvalLoop env store 0 condE body (.error "out of fuel in loop")
  | cond_false :
      Eval env store fuel condE (.val cv s) →
      isTruthy cv = false →
      EvalLoop env store (fuel+1) condE body (.val .undefined s)
  | body_val :
      Eval env store fuel condE (.val cv s) →
      isTruthy cv = true →
      Eval env s fuel body (.val _ s') →
      EvalLoop env s' fuel condE body result →
      EvalLoop env store (fuel+1) condE body result
  | body_continue :
      Eval env store fuel condE (.val cv s) →
      isTruthy cv = true →
      Eval env s fuel body (.continue_ s') →
      EvalLoop env s' fuel condE body result →
      EvalLoop env store (fuel+1) condE body result
  | body_break :
      Eval env store fuel condE (.val cv s) →
      isTruthy cv = true →
      Eval env s fuel body (.break_ s') →
      EvalLoop env store (fuel+1) condE body (.val .undefined s')
  | body_other :
      Eval env store fuel condE (.val cv s) →
      isTruthy cv = true →
      Eval env s fuel body r →
      (∀ v' s', r ≠ .val v' s') → (∀ s', r ≠ .continue_ s') → (∀ s', r ≠ .break_ s') →
      EvalLoop env store (fuel+1) condE body r
  | cond_signal :
      Eval env store fuel condE r → isSignal r →
      EvalLoop env store (fuel+1) condE body r

/-- Evaluate a sequence of expressions -/
inductive EvalSeq : Env → Store → Nat → List IRExpr → EvalResult → Prop where
  | nil :
      EvalSeq env store fuel [] (.val .undefined store)
  | singleton :
      Eval env store fuel e result →
      EvalSeq env store fuel [e] result
  | cons_ok :
      Eval env store fuel e (.val _ s) →
      EvalSeq env s fuel rest result →
      rest ≠ [] →
      EvalSeq env store fuel (e :: rest) result
  | cons_signal :
      Eval env store fuel e r → isSignal r →
      rest ≠ [] →
      EvalSeq env store fuel (e :: rest) r

/-- Try match cases in order -/
inductive EvalMatch : Env → Store → Nat → IRValue → List IRMatchCase →
    EvalResult → Prop where
  | no_cases :
      EvalMatch env store fuel scrutinee [] (.error "no matching case")
  | match_ok :
      matchPattern pat scrutinee = some bindings →
      Eval (env.extendMany bindings) store fuel body result →
      EvalMatch env store fuel scrutinee (.mk pat body :: rest) result
  | match_fail :
      matchPattern pat scrutinee = none →
      EvalMatch env store fuel scrutinee rest result →
      EvalMatch env store fuel scrutinee (.mk pat body :: rest) result

end

end LeanJS.Semantics
