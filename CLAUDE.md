# leanjs

JavaScript in Lean. `ES/` is an ECMA-262 engine in pure Lean (parser with all early errors,
interpreter, standard library; 99.8% of test262), so that JS programs have a semantics proofs can
use. Its runtime (`ES.M`, `ES.Value`) is also the target of the JS → Lean compiler (planned:
compiled functions are `BuiltinFn`s; correctness = compiled code equals the interpreter on the
same AST). Lean → JS is to be rebuilt later (emitting `ES.AST`). Used by the Zippy browser engine
(`../zippy`). Design, monad, conventions, deviations and limitations: `docs/es.md`.

## Commands
- `lake build` — the engine and `es`. `.lake/build/bin/es -e 'code'` / `es file.js` (`print` writes a line).
- `tools/fetch-test262.sh` then `lake exe test262 [paths] [-v] [-j N] [--filter T] [--update]` —
  test262 in worker processes (time limits); fails on regressions against
  `Tests/test262-baseline.txt`; `--update` records new passes (of the tests that ran). Proposal
  features and slow tests are skipped and counted, never dropped silently. Keep `-j` ≤ 4.
- `lake exe es-parse-test [paths]` (parse-phase checks), `es-regex-test`, `es-num-test`.
- `tools/spec.py` — spec-anchor report + purity check. Must pass.

## Core rules (enforced by tools/spec.py)
- Total functions only: no `partial`, `sorry`, `unsafe`. Structural recursion or fuel; fuel bounds
  come with an argument for why they suffice (in the fuel definition's docstring).
- No `Float`: numbers are `ES.F64` (exact). Fast implementations replace reference ones via
  `@[csimp]` + a proof, never `@[implemented_by]`.
- Every function implementing a spec step carries `spec: https://tc39.es/ecma262/#…` and its body
  follows the spec's numbered steps.
- Data-oriented: arenas (`Array` + `Nat` ids), updated in place. Never read the whole `State` as a
  value (use `readS` projections): a second reference makes the next arena update copy it. Never
  keep an old copy of a value alive across a step.
- When the spec and browsers (test262/V8) disagree, match browsers: `DEVIATION (docs/es.md Dn)`;
  known shortfalls: `LIMITATION (docs/es.md Ln)`, listed in docs/es.md.
