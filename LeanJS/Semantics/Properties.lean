/-
  Sanity checks and basic theorems for the IR big-step semantics.
  Uses `#eval` smoke tests and `rfl`/`simp` theorems.
-/
import LeanJS.Semantics.Eval

namespace LeanJS.Semantics.Properties

open LeanJS.IR
open LeanJS.Semantics

-- ============================================================
-- Helper to extract value from EvalResult for testing
-- ============================================================

private def resultValue : EvalResult → Option IRValue
  | .val v _ => some v
  | _ => none

private def resultIsVal : EvalResult → Bool
  | .val _ _ => true
  | _ => false

private def fuel : Nat := 1000

-- ============================================================
-- #eval smoke tests
-- ============================================================

-- Literal evaluates to itself
#eval do
  let r := eval .nil Store.empty fuel (.lit (.number 42))
  match r with
  | .val (.number n) _ => return s!"lit number: {n}"
  | _ => return "FAIL"

-- String literal
#eval do
  let r := eval .nil Store.empty fuel (.lit (.string "hello"))
  match r with
  | .val (.string s) _ => return s!"lit string: {s}"
  | _ => return "FAIL"

-- Undefined
#eval do
  let r := eval .nil Store.empty fuel .undefined
  match r with
  | .val .undefined _ => return "undefined: ok"
  | _ => return "FAIL"

-- Let binding
#eval do
  let prog := IRExpr.«let» "x" .any (.lit (.number 7)) (.var "x")
  let r := eval .nil Store.empty fuel prog
  match r with
  | .val (.number n) _ => return s!"let binding: {n}"
  | _ => return "FAIL"

-- Nested let
#eval do
  let prog := IRExpr.«let» "x" .any (.lit (.number 1))
    (IRExpr.«let» "y" .any (.lit (.number 2))
      (.binOp .add (.var "x") (.var "y")))
  let r := eval .nil Store.empty fuel prog
  match r with
  | .val (.number n) _ => return s!"nested let: {n}"
  | _ => return "FAIL"

-- Function application
#eval do
  let double := IRExpr.lam (some "double") [("n", .number)] [] (.binOp .mul (.var "n") (.lit (.number 2)))
  let prog := IRExpr.«let» "double" .any double
    (.app (.var "double") [.lit (.number 21)])
  let r := eval .nil Store.empty fuel prog
  match r with
  | .val (.number n) _ => return s!"function app: {n}"
  | _ => return "FAIL"

-- Function with return
#eval do
  let f := IRExpr.lam none [("x", .any)] [] (.«return» (.binOp .add (.var "x") (.lit (.number 1))))
  let prog := IRExpr.app f [.lit (.number 5)]
  let r := eval .nil Store.empty fuel prog
  match r with
  | .val (.number n) _ => return s!"function return: {n}"
  | _ => return "FAIL"

-- Ref alloc, deref, assign
#eval do
  let prog := IRExpr.«let» "r" .any (.mkRef (.lit (.number 10)))
    (IRExpr.seq [
      .assign (.var "r") (.lit (.number 20)),
      .deref (.var "r")
    ])
  let r := eval .nil Store.empty fuel prog
  match r with
  | .val (.number n) _ => return s!"ref assign+deref: {n}"
  | _ => return "FAIL"

-- If-else
#eval do
  let prog := IRExpr.«if» (.lit (.bool true)) (.lit (.number 1)) (.lit (.number 2))
  let r := eval .nil Store.empty fuel prog
  match r with
  | .val (.number n) _ => return s!"if true: {n}"
  | _ => return "FAIL"

#eval do
  let prog := IRExpr.«if» (.lit (.bool false)) (.lit (.number 1)) (.lit (.number 2))
  let r := eval .nil Store.empty fuel prog
  match r with
  | .val (.number n) _ => return s!"if false: {n}"
  | _ => return "FAIL"

-- Loop with break
#eval do
  -- let i = ref 0; while(true) { i := deref(i) + 1; if deref(i) >= 5 then break }; deref(i)
  let prog := IRExpr.«let» "i" .any (.mkRef (.lit (.number 0)))
    (IRExpr.seq [
      .loop (.lit (.bool true))
        (IRExpr.seq [
          .assign (.var "i") (.binOp .add (.deref (.var "i")) (.lit (.number 1))),
          .«if» (.binOp .gte (.deref (.var "i")) (.lit (.number 5)))
            .«break»
            (.lit (.unit))
        ]),
      .deref (.var "i")
    ])
  let r := eval .nil Store.empty fuel prog
  match r with
  | .val (.number n) _ => return s!"loop+break: {n}"
  | _ => return "FAIL"

-- Record and project
#eval do
  let prog := IRExpr.project
    (.record [("x", .lit (.number 1)), ("y", .lit (.number 2))])
    "y"
  let r := eval .nil Store.empty fuel prog
  match r with
  | .val (.number n) _ => return s!"record project: {n}"
  | _ => return "FAIL"

-- Array and index
#eval do
  let prog := IRExpr.index
    (.array [.lit (.number 10), .lit (.number 20), .lit (.number 30)])
    (.lit (.number 1))
  let r := eval .nil Store.empty fuel prog
  match r with
  | .val (.number n) _ => return s!"array index: {n}"
  | _ => return "FAIL"

-- Pattern matching
#eval do
  let prog := IRExpr.«match»
    (.construct "Some" [.lit (.number 42)])
    [ .mk (.constructor "None" []) (.lit (.number 0)),
      .mk (.constructor "Some" ["val"]) (.var "val") ]
  let r := eval .nil Store.empty fuel prog
  match r with
  | .val (.number n) _ => return s!"match Some: {n}"
  | _ => return "FAIL"

-- Pattern match wildcard
#eval do
  let prog := IRExpr.«match»
    (.lit (.string "hello"))
    [ .mk (.lit (.string "world")) (.lit (.number 1)),
      .mk .wildcard (.lit (.number 2)) ]
  let r := eval .nil Store.empty fuel prog
  match r with
  | .val (.number n) _ => return s!"match wildcard: {n}"
  | _ => return "FAIL"

-- Try-catch
#eval do
  let prog := IRExpr.tryCatch
    (.throw (.lit (.string "oops")))
    (some "e")
    (.var "e")
    none
  let r := eval .nil Store.empty fuel prog
  match r with
  | .val (.string s) _ => return s!"try-catch: {s}"
  | _ => return "FAIL"

-- Try-catch with finalizer
#eval do
  -- Use a ref to verify finalizer runs
  let prog := IRExpr.«let» "log" .any (.mkRef (.lit (.string "")))
    (IRExpr.seq [
      .tryCatch
        (.seq [.assign (.var "log") (.lit (.string "body")), .lit (.unit)])
        none
        (.lit (.unit))
        (some (.assign (.var "log") (.binOp .strConcat (.deref (.var "log")) (.lit (.string "+fin"))))),
      .deref (.var "log")
    ])
  let r := eval .nil Store.empty fuel prog
  match r with
  | .val (.string s) _ => return s!"try-finally: {s}"
  | _ => return "FAIL"

-- Recursive function (factorial)
#eval do
  let fact := IRExpr.lam (some "fact") [("n", .number)] []
    (IRExpr.«if» (.binOp .lte (.var "n") (.lit (.number 1)))
      (.«return» (.lit (.number 1)))
      (.«return» (.binOp .mul (.var "n")
        (.app (.var "fact") [.binOp .sub (.var "n") (.lit (.number 1))]))))
  let prog := IRExpr.«let» "fact" .any fact
    (.app (.var "fact") [.lit (.number 5)])
  let r := eval .nil Store.empty fuel prog
  match r with
  | .val (.number n) _ => return s!"factorial(5): {n}"
  | _ => return "FAIL"

-- Closures capture environment
#eval do
  let prog := IRExpr.«let» "x" .any (.lit (.number 10))
    (IRExpr.«let» "f" .any
      (IRExpr.lam none [("y", .any)] [] (.binOp .add (.var "x") (.var "y")))
      -- x is captured in f's closure
      (IRExpr.«let» "x" .any (.lit (.number 999))
        (.app (.var "f") [.lit (.number 5)])))
  let r := eval .nil Store.empty fuel prog
  match r with
  | .val (.number n) _ => return s!"closure capture: {n}"  -- should be 15, not 1004
  | _ => return "FAIL"

-- String concat via add
#eval do
  let prog := IRExpr.binOp .add (.lit (.string "hello ")) (.lit (.string "world"))
  let r := eval .nil Store.empty fuel prog
  match r with
  | .val (.string s) _ => return s!"string concat: {s}"
  | _ => return "FAIL"

-- ============================================================
-- Verified properties via #eval assertions
-- (partial def is opaque to the kernel, so rfl/simp don't work)
-- ============================================================

/-- Assert that an eval result is a value matching a predicate -/
private def assertVal (label : String) (r : EvalResult) (pred : IRValue → Bool) : String :=
  match r with
  | .val v _ => if pred v then s!"{label}: PASS" else s!"{label}: FAIL (wrong value)"
  | .error msg => s!"{label}: ERROR ({msg})"
  | _ => s!"{label}: FAIL (not a value)"

-- Literal properties
#eval assertVal "lit_number" (eval .nil Store.empty 2 (.lit (.number 42)))
  (fun v => match v with | .number n => n == 42.0 | _ => false)

#eval assertVal "lit_string" (eval .nil Store.empty 2 (.lit (.string "abc")))
  (fun v => match v with | .string s => s == "abc" | _ => false)

#eval assertVal "lit_bool" (eval .nil Store.empty 2 (.lit (.bool true)))
  (fun v => match v with | .bool b => b == true | _ => false)

#eval assertVal "lit_unit" (eval .nil Store.empty 2 (.lit .unit))
  (fun v => match v with | .unit => true | _ => false)

-- Fuel exhaustion
#eval match eval .nil Store.empty 0 (.lit (.number 1)) with
  | .error _ => "fuel_exhaust: PASS"
  | _ => "fuel_exhaust: FAIL"

-- Break/continue signals
#eval match eval .nil Store.empty 2 .«break» with
  | .break_ _ => "break_signal: PASS"
  | _ => "break_signal: FAIL"

#eval match eval .nil Store.empty 2 .«continue» with
  | .continue_ _ => "continue_signal: PASS"
  | _ => "continue_signal: FAIL"

-- Variable lookup
#eval assertVal "var_found"
  (eval (.cons "x" (.number 7) .nil) Store.empty 2 (.var "x"))
  (fun v => match v with | .number n => n == 7.0 | _ => false)

#eval match eval .nil Store.empty 2 (.var "missing") with
  | .error _ => "var_unbound: PASS"
  | _ => "var_unbound: FAIL"

end LeanJS.Semantics.Properties
