import Lake
open Lake DSL

/-- leanjs: JavaScript in Lean. `ES` is an ECMA-262 engine (parser, interpreter, standard library)
whose runtime is also the target of the JS → Lean compiler. -/
package leanjs where
  leanOptions := #[⟨`autoImplicit, false⟩]

/-- The ECMAScript engine: pure Lean, total functions, no `Float`. -/
@[default_target]
lean_lib ES

/-- `leanjs run file.js` / `leanjs compile file.js Out.lean` (JS → Lean over the engine's runtime). -/
@[default_target]
lean_exe leanjs where
  root := `Main

/-- test262 conformance runner: `lake exe test262 [paths] [-v] [-j N] [--update]`. -/
lean_exe test262 where
  root := `Test262

/-- Runs a script with the engine: `es file.js` / `es -e 'code'`. -/
@[default_target]
lean_exe es where
  root := `EsMain

/-- Parses every test262 test and checks parse-phase expectations. -/
lean_exe «es-parse-test» where
  root := `ParseTest262

/-- RegExp engine tests (corpora from `node ESTests/regex_corpus.js`). -/
lean_exe «es-regex-test» where
  root := `ESTests.Regex

/-- Checks of the Number/BigInt/Math/Date algorithms. -/
lean_exe «es-num-test» where
  root := `ESTests.Num
