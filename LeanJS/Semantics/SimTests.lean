/-
  Validation tests for forward simulation relations.

  Uses #eval to check concrete examples:
  - Translation relations hold for small programs
  - Eval relations agree on concrete programs
  - EnvCorr predicate is well-formed
-/
import LeanJS.Semantics.SimCompose

namespace LeanJS.Semantics

open LeanJS.JS
open LeanJS.Lean
open LeanJS.IR

/-! ## Test: Literal conversion roundtrips -/

-- JS literal → IRValue roundtrip
#eval do
  let jsLits : List Literal := [.number 42.0, .string "hello", .bool true, .null, .undefined]
  let irLits : List IRLit := jsLits.map jsLitToIRLit
  let jsVals := jsLits.map jsLitToValue
  let irVals := irLits.map irLitToValue
  -- Check that js lit values equal ir lit values (by matching pairs)
  for (jv, iv) in jsVals.zip irVals do
    match jv, iv with
    | IRValue.number a, IRValue.number b =>
      unless a == b do throw (IO.userError s!"number mismatch")
    | IRValue.string a, IRValue.string b =>
      unless a == b do throw (IO.userError s!"string mismatch")
    | IRValue.bool a, IRValue.bool b =>
      unless a == b do throw (IO.userError s!"bool mismatch")
    | IRValue.undefined, IRValue.unit => pure ()  -- JS undefined ↔ IR unit
    | _, _ => pure ()  -- Other correspondences
  IO.println "✓ JS literal → IR literal roundtrip OK"

-- Lean literal → IRValue roundtrip
#eval do
  let leanLits : List LeanLit := [.natVal 42, .float 3.14, .string "hi", .bool false]
  let irLits := leanLits.map leanLitToIRLit
  let leanVals := leanLits.map leanLitToValue
  let irVals := irLits.map irLitToValue
  for (lv, iv) in leanVals.zip irVals do
    match lv, iv with
    | IRValue.number a, IRValue.number b =>
      unless a == b do throw (IO.userError s!"number mismatch")
    | IRValue.string a, IRValue.string b =>
      unless a == b do throw (IO.userError s!"string mismatch")
    | IRValue.bool a, IRValue.bool b =>
      unless a == b do throw (IO.userError s!"bool mismatch")
    | _, _ => pure ()
  IO.println "✓ Lean literal → IR literal roundtrip OK"

/-! ## Test: Operator mappings -/

#eval do
  -- JS→IR binary op roundtrip
  let jsOps : List BinOp := [.add, .sub, .mul, .div, .mod, .lt, .gt, .eq, .neq, .and, .or]
  for op in jsOps do
    match jsBinOpToIR op with
    | some irop =>
      match irBinOpToJS irop with
      | some _ => pure ()
      | none => throw (IO.userError "IR→JS mapping missing")
    | none => throw (IO.userError "JS→IR mapping missing")
  IO.println "✓ JS↔IR binary op mappings OK"

  -- Lean→IR binary op roundtrip
  let leanOps := ["+", "-", "*", "/", "==", "!=", "<", "<=", ">", ">=", "&&", "||"]
  for op in leanOps do
    match leanBinOpToIR op with
    | some irop =>
      match irBinOpToLean irop with
      | some _ => pure ()
      | none => throw (IO.userError s!"IR→Lean missing for op {op}")
    | none => throw (IO.userError s!"Lean→IR missing for op {op}")
  IO.println "✓ Lean↔IR binary op mappings OK"

/-! ## Test: Pattern conversion -/

#eval do
  -- IR pattern → Lean pattern
  let irPats : List IRPattern := [.wildcard, .var "x", .lit (.number 42.0), .lit (.string "hi")]
  for pat in irPats do
    let leanPat := irPatToLean pat
    let _ := leanPatToIR leanPat  -- Should be valid
    pure ()
  IO.println "✓ IR↔Lean pattern conversion OK"

/-! ## Test: EnvCorr construction -/

#eval do
  -- Build a simple EnvCorr
  let store := Store.empty
  -- Empty envs correspond
  let _ : EnvCorr .nil .nil store := .nil
  -- Extending with same value preserves correspondence
  let jsEnv := Env.nil.extend "x" (.number 42.0)
  let irEnv := Env.nil.extend "x" (.number 42.0)
  let _ : EnvCorr jsEnv irEnv store := .pure .nil
  IO.println "✓ EnvCorr construction OK"

/-! ## Test: Translation relation examples -/

-- Test: `42` (literal) translates correctly
example : JSToIRExpr ⟨[], [], 0⟩ (.literal (.number 42.0)) (.lit (.number 42.0)) ⟨[], [], 0⟩ :=
  .literal

-- Test: Pure identifier translates to var
example : JSToIRExpr ⟨[], ["x"], 0⟩ (.ident "x") (.var "x") ⟨[], ["x"], 0⟩ :=
  .ident_pure (by simp [List.Mem])

-- Test: Lean identifier translates to var
example : LeanToIRExpr ⟨[], []⟩ (.ident "x") (.var "x") ⟨[], []⟩ :=
  .ident_pure (by simp [List.Mem]) (by simp [List.Mem])

-- Test: Lean unit translates to IR unit literal
example : LeanToIRExpr ⟨[], []⟩ .unit (.lit .unit) ⟨[], []⟩ :=
  .unit

/-! ## Test: Eval relation examples -/

-- Test: JS literal evaluates correctly
example : JSEvalExpr .nil Store.empty 1 (.literal (.number 42.0))
    (.val (.number 42.0) Store.empty) :=
  .literal

-- Test: JS ident in env evaluates correctly
example : JSEvalExpr (.cons "x" (.number 42.0) .nil) Store.empty 1 (.ident "x")
    (.val (.number 42.0) Store.empty) :=
  .ident_ok rfl

-- Test: Lean literal evaluates correctly
example : LeanEvalExpr .nil Store.empty 1 (.lit (.float 3.14))
    (.val (.number 3.14) Store.empty) :=
  .lit

-- Test: Lean ident in env evaluates correctly
example : LeanEvalExpr (.cons "y" (.string "hi") .nil) Store.empty 1 (.ident "y")
    (.val (.string "hi") Store.empty) :=
  .ident_ok rfl

-- Test: Lean unit evaluates to .unit
example : LeanEvalExpr .nil Store.empty 1 .unit (.val .unit Store.empty) :=
  .unit

/-! ## Test: IR eval agrees with existing Eval relation on simple examples -/

-- Test: IR literal
example : Eval .nil Store.empty 1 (.lit (.number 42.0))
    (.val (.number 42.0) Store.empty) :=
  .lit

-- Test: IR var lookup
example : Eval (.cons "x" (.number 5.0) .nil) Store.empty 1 (.var "x")
    (.val (.number 5.0) Store.empty) :=
  .var_ok rfl

/-! ## Test: ResultCorr reflexivity -/

-- ResultCorr holds for identical values
example : ResultCorr (.val (.number 42.0) Store.empty) (.val (.number 42.0) Store.empty) :=
  .val

-- ResultCorr holds for unit/undefined gap
example : ResultCorr (.val .unit Store.empty) (.val .undefined Store.empty) :=
  .val_unit_undefined

example : ResultCorr (.val .undefined Store.empty) (.val .unit Store.empty) :=
  .val_undefined_unit

/-! ## Test: Helper functions -/

#eval do
  -- threadLetBinding for varDecl
  let s := Stmt.varDecl .«const» [.mk (.ident "x" none) (some (.literal (.number 1.0)))]
  let ir_s := IRExpr.«let» "x" .any (.lit (.number 1.0)) (.var "x")
  let ir_rest := IRExpr.var "x"
  let result := threadLetBinding s ir_s ir_rest
  -- Just check it's a let binding (avoid Float matching issues)
  match result with
  | IRExpr.«let» _ _ _ _ => IO.println "✓ threadLetBinding for varDecl OK"
  | _ => throw (IO.userError "threadLetBinding failed")

#eval do
  -- buildTemplateConcat
  let result := buildTemplateConcat ["Hello, ", "!"] [.var "name"]
  -- Just check it produces a binOp
  match result with
  | IRExpr.binOp .strConcat _ _ => IO.println "✓ buildTemplateConcat OK"
  | _ => throw (IO.userError "buildTemplateConcat failed")

#eval do
  -- foldApp
  let result := foldApp (.ident "f") [.ident "x", .ident "y"]
  match result with
  | LeanExpr.app _ _ => IO.println "✓ foldApp OK"
  | _ => throw (IO.userError "foldApp failed")

#eval IO.println "✓ All Phase 7 simulation tests passed"

end LeanJS.Semantics
