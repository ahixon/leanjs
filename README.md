# lean-js

A transpiler between JavaScript and Lean 4, written in Lean. Both directions go
through a shared intermediate representation (IR). For a core fragment of each
language, the translation is **proved correct in Lean**: a terminating program
that does not get stuck is translated into a program with corresponding
behaviour. These proofs cover the code that actually runs, not just a model of it.

```
            JS ──JSToIR──▶ IR ──IRToJS──▶ JS
          Lean ─LeanToIR─▶ IR ─IRToLean─▶ Lean
```

## Building

Requires [elan](https://github.com/leanprover/elan); the toolchain
(`leanprover/lean4:v4.17.0`) is picked up from `lean-toolchain`.

```sh
lake build           # library + all proofs (~20 min cold, mostly the JS parser)
lake build lean-js   # the CLI, at .lake/build/bin/lean-js
./Test/run.sh        # test suite (see below)
```

On macOS the executable is linked with the system linker (`/usr/bin/ld`),
because recent macOS releases refuse to load binaries produced by the linker
bundled with Lean 4.17. This is configured in `lakefile.lean`.

## Usage

```
lean-js <command> <file>
```

| Command             | Pipeline                         | Verified path |
|---------------------|----------------------------------|---------------|
| `parse`             | JS → JS (parse and re-emit)      | –             |
| `ir`                | JS → IR (printed)                | yes           |
| `roundtrip`         | JS → IR → JS                     | yes           |
| `lean`              | JS → IR → Lean module            | no            |
| `lean-expr`         | JS → IR → Lean expression        | yes           |
| `lean-roundtrip`    | Lean → Lean (parse and re-emit)  | –             |
| `lean-ir-roundtrip` | Lean → IR → Lean                 | yes           |
| `js`                | Lean → IR → JS                   | yes           |
| `check`             | which pipelines are verified for a file, and why not | – |

If the input is in the verified core, commands marked "yes" use the verified
translators and print `[verified]` on stderr. Otherwise they fall back to the
original (legacy, unverified) translators and print `[unverified]` with the
reason, for example:

```
$ lean-js roundtrip Test/Core/closures.js
[verified] translated by the verified core translator
const makeAdder = n => x => x + n;
...
$ lean-js check Test/Fixtures/basic.js
Test/Fixtures/basic.js:
  JS → IR → JS    : not in verified core — unsupported: var declaration
  JS → IR → Lean  : not in verified core — unsupported: var declaration
```

A Lean file is in the core when it consists of non-recursive `def`s whose
bodies are in the Lean core below. Such a file is treated as the expression
`let f₁ := …; …; let fₙ := …; ()`.

## What is verified

### The core fragment

| | JS → IR | IR → JS | Lean → IR | IR → Lean |
|---|---|---|---|---|
| literals, variables | ✓ (no regex) | ✓ | ✓ | ✓ |
| unary/binary operators | ✓ (all mapped ops) | ✓ | ✓ | ✓ (no bitwise/`**`/`typeof`) |
| conditionals | `?:`, `if`/`else` | `?:`, `if`/`else` | `if … then … else` | ✓ |
| local bindings | `const`/`let x = e;` | ✓ | non-recursive `let` | ✓ |
| functions | arrow and `function` (incl. self-recursive), simple params | ✓ | `fun x y => …` (curried) | one-parameter, non-recursive |
| calls | ✓ | ✓ | one argument at a time | one argument |
| arrays, records | array literals (holes ok), `{k: e}` | ✓ incl. `.field` | `#[…]`, `{ k := e }`, `.field` | ✓ |
| `return`, `throw` | ✓ | ✓ | `throw` | `throw` |
| function declarations | ✓ (not hoisted) | ✓ | | |

Outside the core: mutation and assignment, loops, `break`/`continue`,
`try`/`catch`, `var`, classes, `this`, `new`, destructuring, templates,
async/generators, modules, Lean `do`-notation, `match`, and mutable references.

JS→IR also excludes `.field` access, because the semantics genuinely
disagree there: in JS a missing field is `undefined`, but in IR it is an error.

### The theorems

All proofs are complete: there is no `sorry`, and `Test/Axioms.lean` checks
that the theorems depend only on Lean's standard axioms (`propext`,
`Classical.choice`, `Quot.sound`).

**Per-pass forward simulation** (`LeanJS/Semantics/Sim*.lean`):

| Theorem | Statement (informally) |
|---|---|
| `sim_js_to_ir_expr`, `sim_js_to_ir_program` | JS evaluates to `r` (not an error) ⇒ the IR evaluates, for some fuel, to a corresponding `r'` |
| `sim_ir_to_js_expr`, `sim_ir_to_js_stmts` | IR evaluates to `r` (not an error) ⇒ the JS expression / statements evaluate to a corresponding result |
| `sim_lean_to_ir_expr` | Lean → IR |
| `sim_ir_to_lean_expr` | IR → Lean |

**End-to-end** (`LeanJS/Semantics/SimCompose.lean`): `js_roundtrip_expr`,
`js_roundtrip_program`, `lean_roundtrip_expr`, `js_to_lean_expr`,
`js_to_lean_program`, `lean_to_js_expr`, `lean_to_js_program`. The `*_prim`
corollaries give the simplest form: *a closed program that evaluates to a
number, string or boolean still evaluates to exactly that value after
translation*.

**The executable is covered.** The translators in `LeanJS/Trans/Core.lean`
are total functions. Each returns its output together with a proof that the
output is related to the input by the relation in
`LeanJS/Semantics/TransRel.lean`, so soundness holds by construction. The
theorems `jsRoundtrip_correct`, `jsToLean_correct`, `leanToJS_correct` and
`leanRoundtrip_correct` state correctness for the exact functions the CLI
calls.

**Non-vacuity.** `LeanJS/Semantics/SimTests.lean` instantiates the theorems
on concrete programs with concrete evaluation derivations, which shows the
hypotheses can actually be satisfied.

### How "corresponding" is defined

`LeanJS/Semantics/EnvCorr.lean` defines one correspondence, parameterised per
pass:

* numbers, strings and booleans correspond only to themselves;
* records and arrays correspond pointwise;
* a source closure corresponds to a target closure when their environments
  correspond and their bodies are related by the translation relation;
* IR `unit`/`undefined` map to JS `undefined` and to Lean `()`;
* results correspond when they have the same shape (value / `return` /
  `throw`), **the same store**, and corresponding values. For JS statement
  lists only completion matters, because statement values are unobservable.

### Assumptions and modelling choices

The proofs are only as meaningful as the semantics they are stated against.
Be aware of:

* **Programs must not go wrong.** As in CompCert, the theorems assume the
  source evaluation does not produce a runtime error, such as calling a
  non-function or applying `+` to incompatible values. They say nothing about
  programs that error or diverge. The semantics are big-step, so
  non-termination has no derivation.
* **The semantics are models, not ECMAScript or Lean.** The JS model shares
  the IR operator semantics (`LeanJS/Semantics/BinOp.lean`):
  * `==` and `===` are both structural equality without coercion, and `null`
    is identified with `undefined`;
  * `&&`/`||` evaluate both operands;
  * numbers are Lean `Float`s, and number-to-string conversion uses Lean's
    formatting;
  * function declarations are not hoisted;
  * a function's own name shadows a parameter with the same name.

  The Lean model is untyped and treats numeric literals as floats.
* **Trusted, unverified components:** the JS and Lean parsers and emitters,
  the IR printer, and the legacy translators used outside the core. The
  legacy translators have known semantic bugs. For example, the legacy
  JS→Lean path translates `function f(x) { x + 1; }`, which returns
  `undefined`, to `def f x := x + 1`.
* **Fuel.** Only the IR semantics is fuel-indexed; the theorems quantify the
  fuel existentially.

## Testing

`./Test/run.sh` (add `--update` to regenerate golden files) runs:

1. **Golden tests:** every CLI command on every fixture in `Test/Fixtures/`
   (legacy-path programs) and `Test/Core/` (core-fragment programs), compared
   with `Test/expected/`.
2. **Verified-path checks:** every `Test/Core` file must be translated by the
   verified translators.
3. **Behavioural tests (Node.js):** each `Test/Core/*.js` program and its
   round-tripped output are run, and the printed value of `result` must match.
   Each `Test/Core/*.lean` program is translated to JS and its `result`
   compared with `<file>.expected`.
4. **Axiom audit:** `Test/Axioms.lean` must not mention `sorryAx`.

`lake build` itself also runs the proof-level tests in `SimTests.lean`
(`#guard` checks on the translators and the non-vacuity theorems). CI
(`.github/workflows/ci.yml`) builds everything, fails on any `sorry`, and runs
the suite.

## Layout

```
LeanJS/JS/          JS AST, lexer, parser, emitter
LeanJS/Lean/        Lean AST, lexer, parser, emitter
LeanJS/IR/          IR definition and printer
LeanJS/Trans/       legacy translators (JSToIR, IRToJS, LeanToIR, IRToLean)
LeanJS/Trans/Core   verified, certified translators for the core fragment
LeanJS/Semantics/
  Value, BinOp, Relation      IR values and big-step semantics
  Determinism, FuelMono       IR metatheory
  JSEval, LeanEval            JS / Lean core semantics
  TransRel                    translation relations (the specification)
  EnvCorr                     value / environment / result correspondence
  SimJSToIR … SimIRToLean     per-pass simulation proofs
  SimCompose                  end-to-end theorems, translator correctness
  SimTests                    non-vacuity and translator tests
Main.lean           CLI
Test/               fixtures, golden outputs, runner, axiom audit
```
