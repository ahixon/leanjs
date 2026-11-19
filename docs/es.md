# ES: the ECMAScript engine in Lean

`ES/` is an ECMA-262 implementation in pure Lean, written for the Zippy browser engine (where it
is the planned "Lean interpreter" of Zippy's docs/decisions.md J1: the reference semantics app
proofs reason about, and a second script engine next to V8) and now the core of leanjs: its
runtime is also the target of the JS → Lean compiler. Target: test262
(`tools/fetch-test262.sh`, then `lake exe test262`). It has no dependencies; `ES/Number.lean` is
the exact binary64 model (`ES.F64`).

The core rules of CLAUDE.md apply (`tools/spec.py` checks `ES/`): total functions,
no `partial`/`sorry`/`unsafe`/`implemented_by`/`Float`; every function implementing a spec
algorithm carries `spec: https://tc39.es/ecma262/#…` and its body follows the numbered steps
(comment the step numbers, `-- 3.` etc.); arenas with `Nat` ids; never keep an old copy of the
state alive across a step.

## Modules

| Module | What |
|---|---|
| `ES/Str.lean` | `JSStr`: String values as UTF-16 code units (`ByteArray`, LE) |
| `ES/AST.lean` | Syntax trees (`Expr`, `Stmt`, `Pattern`, `Func`, `Class`, `Program`), `SyntaxError` |
| `ES/Lexer.lean`, `ES/Parser.lean` | Source text → `Program`, with all early errors |
| `ES/Static.lean` | Static semantics the runtime uses (BoundNames, VarDeclaredNames, LexicallyScopedDeclarations, …) |
| `ES/Num.lean` | Number/BigInt algorithms over `F64` (ToString, StringToNumber, bitwise, `**`, `%`, Math, float16/32) |
| `ES/Regex.lean` | RegExp pattern parser, early errors, backtracking matcher (`compile`, `matchAt`) |
| `ES/Value.lean` | Values, objects (`Obj`, `Kind`), properties, environments, realms, `State`, the monad `M` |
| `ES/Object.lean` | Objects' internal methods (ordinary and exotic: arrays, strings, arguments, proxies, typed arrays, module namespaces) |
| `ES/Ops.lean` | Abstract operations: type conversion, testing/comparison, operations on objects, iterators |
| `ES/Interp.lean` | Evaluation of scripts/modules/functions, environments, classes, generators, async; the driver |
| `ES/Builtins/*.lean` | The intrinsics, one file per spec chapter |
| `ES/Realm.lean` | CreateIntrinsics, SetDefaultGlobalBindings, the built-in table |
| `Test262.lean` | test262 runner (exe `test262`); `EsMain.lean`: exe `es` (run a file) |

## The monad and the driver

All runtime semantics are written in `M α := State → Res α`. `Res` is `ok`, `err` (a throw
completion: the thrown value), `halt` (engine failure: out of fuel, unimplemented — not catchable),
or `req r s k`: a request `r` (call, construct, yield, await, resume) with its continuation `k`.

- Built-ins and abstract operations call functions with `call f this args` (a request), so they
  never depend on the interpreter. Getters, proxy traps, `valueOf` etc. all go through it.
- The driver (`drive` in `ES/Interp.lean`) answers requests: it evaluates function bodies (one
  level of call depth less: depth exhausted is a `RangeError`, like a stack overflow), and keeps
  suspended generator/async bodies' continuations by the coroutine object's id.
- Loops use `M.loop`/`M.repeatFrom`/`M.foldArr`/`M.forArr` (constant stack, bounded by fuel), never
  recursion on iteration count. Each JS-visible loop iteration and call takes one fuel step
  (`M.tick`).
- Recursion over the syntax tree is structural on a depth parameter (`n+1 → n`); the parser
  limits nesting so the bound suffices (the argument is in the parser's nesting limit docstring).

## Conventions

- Strings: `JSStr`; build literals once (`def kLength : JSStr := "length"` style top-level
  constants are fine; they are computed once).
- Numbers: `ES.F64` (exact, no `Float`).
- Errors: `throwError .typeError "msg"` (in `ES/Ops.lean`) creates the realm's error object.
- Spec deviations (to match browsers, per CLAUDE.md) are marked `DEVIATION (docs/es.md Dn)` and
  listed below; known shortfalls `LIMITATION (docs/es.md Ln)`.

## test262

`lake exe test262 [paths] [-v] [--update]` runs tests in processes of its own (batches, a
timeout each), compares with `Tests/test262-baseline.txt`, and fails on regressions. Features the
engine does not implement are listed (with counts) in the runner's skip list, never silently
dropped.

## Deviations and limitations

- L1: No garbage collector: the heap and environment arenas only grow.
- D1: RegExp with `u`/`v`: a match starting inside a surrogate pair starts at the pair (V8's
  behaviour; the spec would report lastIndex, which can be after the match's end). The built-ins
  use `captures[0]` for the match's `index` (`ES/Regex.lean`).
- L2: The parser rejects nesting deeper than 1000 levels, counting each link of long binary/member/
  call chains (a flat `a+b+…` of more than ~1000 operands is a SyntaxError).
- L3: Calls deeper than 4000 (`ES/Driver.lean`, `callDepth`) throw RangeError.
- L10: No locale data (ECMA-402 is not implemented): `toLocaleLowerCase`/`toLocaleUpperCase` use
  the locale-independent full case mappings (no Turkish/Lithuanian rules), `localeCompare`
  compares the NFC forms by code points (canonically equivalent Strings are equal), the
  `toLocaleString` methods are `toString` (`ES/Builtins/Text/`).
- L11: Strings are limited to 2^29 - 24 code units (V8's limit; longer results throw RangeError),
  BigInts to 2^30 bits (`Num.BigInt.maxBits`), JSON.parse (and its reviver walk) and JSON.stringify to
  nesting depth 5000 (RangeError), and one RegExp match to `Regex.defaultStepLimit` machine
  steps (RangeError).
- L4: Date: the local time zone is UTC (LocalTZA 0, no daylight saving), and the pure core has
  no clock: the current time is the host's `State.hostData` "now" when set, else a deterministic
  clock (1.7e12 ms plus 1 ms per 1000 fuel steps used: monotonic, so busy-wait loops end)
  (`ES/Builtins/Library.lean`, `currentTime`).
- D2: Sloppy function declarations and expressions have own `caller` and `arguments` properties
  with value null (non-writable, non-configurable), as in V8 (`ES/Function.lean`,
  `addLegacyFunctionProps`); the spec gives them none (Annex? forbids extensions for strict ones only).
- L20: Array buffers hold at most 2^31 bytes (`ES/Builtins/Buffers.lean`, `maxAllocBytes`; larger
  allocations and resizes throw RangeError) and accept a `maxByteLength` of at most 2^32.
- L21: Atomics: one agent and no `$262.agent`; `Atomics.wait` never blocks (it returns
  "not-equal" or, at once, "timed-out"), `Atomics.notify` finds no waiters; `Atomics.waitAsync`
  is not implemented.
- D20: `%TypedArray%.prototype.copyWithin` after its arguments' conversions shrank the buffer moves
  only the elements that still fit, as by memmove (browsers and test262), not the spec's byte loop
  that stops at the first out-of-range byte.
- L5: Source text is a Lean `String` (UTF-8), so code passed to `eval`/`Function` cannot contain
  lone surrogates (they become U+FFFD before parsing).
