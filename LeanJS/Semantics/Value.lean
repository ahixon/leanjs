/-
  Big-step operational semantics for LeanJS IR — Value domain

  Defines the semantic value type, environment (association list),
  mutable store (heap), and evaluation result with control flow signals.
-/
import LeanJS.IR.Core

namespace LeanJS.Semantics

open LeanJS.IR

/-- Heap location -/
structure Loc where
  n : Nat
  deriving BEq, Inhabited, Repr

mutual

/-- Semantic values produced by evaluation -/
inductive IRValue where
  | number (n : Float)
  | string (s : String)
  | bool (b : Bool)
  | unit
  | undefined
  | closure (env : Env) (name : Option String) (params : List String) (body : IRExpr)
  | record (fields : List (String × IRValue))
  | array (elements : List IRValue)
  | ref (loc : Loc)
  | constructed (tag : String) (args : List IRValue)

/-- Environment: association list mapping names to values -/
inductive Env where
  | nil : Env
  | cons : String → IRValue → Env → Env

end

namespace Env

def empty : Env := .nil

def lookup (env : Env) (name : String) : Option IRValue :=
  match env with
  | .nil => none
  | .cons n v rest => if n == name then some v else rest.lookup name

def extend (env : Env) (name : String) (v : IRValue) : Env :=
  .cons name v env

def extendMany (env : Env) (bindings : List (String × IRValue)) : Env :=
  bindings.foldl (fun acc (n, v) => acc.extend n v) env

def toList (env : Env) : List (String × IRValue) :=
  match env with
  | .nil => []
  | .cons n v rest => (n, v) :: rest.toList

end Env

instance : Inhabited Env := ⟨.nil⟩
instance : Inhabited IRValue := ⟨.undefined⟩

/-- Mutable store (heap) for refs -/
structure Store where
  cells : Array IRValue
  deriving Inhabited

namespace Store

def empty : Store := { cells := #[] }

def alloc (store : Store) (v : IRValue) : Store × Loc :=
  let loc := Loc.mk store.cells.size
  ({ cells := store.cells.push v }, loc)

def read (store : Store) (loc : Loc) : Option IRValue :=
  if loc.n < store.cells.size then
    some (store.cells[loc.n]!)
  else
    none

def write (store : Store) (loc : Loc) (v : IRValue) : Option Store :=
  if loc.n < store.cells.size then
    some { cells := store.cells.set! loc.n v }
  else
    none

end Store

/-- Evaluation result with control flow signals -/
inductive EvalResult where
  | val (v : IRValue) (store : Store)
  | return_ (v : IRValue) (store : Store)
  | break_ (store : Store)
  | continue_ (store : Store)
  | throw_ (v : IRValue) (store : Store)
  | error (msg : String)
  deriving Inhabited

namespace EvalResult

/-- Extract store from a result (if available) -/
def getStore : EvalResult → Option Store
  | .val _ s => some s
  | .return_ _ s => some s
  | .break_ s => some s
  | .continue_ s => some s
  | .throw_ _ s => some s
  | .error _ => none

end EvalResult

/-- Convert an IR literal to a semantic value -/
def irLitToValue : IRLit → IRValue
  | .number n => .number n
  | .string s => .string s
  | .bool b => .bool b
  | .unit => .unit

/-- Truthiness: JS-style coercion to bool -/
def isTruthy : IRValue → Bool
  | .bool b => b
  | .number n => n != 0.0
  | .string s => !s.isEmpty
  | .unit => false
  | .undefined => false
  | _ => true

end LeanJS.Semantics
