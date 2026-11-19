import ES.Builtins.Text.Number
import ES.Builtins.Text.RegExp
import ES.Builtins.Text.String
import ES.Builtins.Text.JSON

/-!
# Number, Math, BigInt, global functions (isNaN, parseInt, URI functions), JSON, String, RegExp, Symbol extras

spec: https://tc39.es/ecma262/

The parts are in `ES/Builtins/Text/`: `Number.lean` (Number, Math, BigInt, the global
functions), `RegExp.lean`, `String.lean`, `JSON.lean`; Unicode case conversion and normalization
are `ES/Unicode/Text.lean`'s.
-/

namespace ES.Builtins.Text

open ES (F64)

/-- This module's built-in behaviours. -/
def defs : Array BuiltinDef := numberDefs ++ regexpDefs ++ stringDefs ++ jsonDefs

/-- Creates this module's intrinsics in the realm being created (runs after `coreSetup`). -/
def setup : M Unit := do
  numberSetup
  regexpSetup
  stringSetup
  jsonSetup

end ES.Builtins.Text
