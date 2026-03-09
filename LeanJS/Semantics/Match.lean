/-
  Pattern matching for IR semantics.
  Returns bindings on successful match, none on failure.
-/
import LeanJS.Semantics.Value

namespace LeanJS.Semantics

open LeanJS.IR

/-- Try to match a pattern against a value, returning bindings on success -/
def matchPattern (pat : IRPattern) (v : IRValue) : Option (List (String × IRValue)) :=
  match pat with
  | .wildcard => some []
  | .var name => some [(name, v)]
  | .lit lit =>
    let expected := irLitToValue lit
    match expected, v with
    | .number a, .number b => if a == b then some [] else none
    | .string a, .string b => if a == b then some [] else none
    | .bool a, .bool b => if a == b then some [] else none
    | .unit, .unit => some []
    | _, _ => none
  | .constructor tag bindings =>
    match v with
    | .constructed vtag args =>
      if tag == vtag && bindings.length == args.length then
        some (bindings.zip args)
      else
        none
    | _ => none

end LeanJS.Semantics
