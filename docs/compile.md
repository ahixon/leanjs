# JS → Lean for proofs

Goal: from a JavaScript program, generate Lean definitions — one per JS function and one for the
top-level code — that read like the program, mean exactly what the engine says it means, and are
the objects proofs talk about.

## Design: the interpreter is a fold of semantic combinators

Each syntax construct has a combinator in `ES.Sem` (`ES/Sem.lean`) that takes the denotations of
its sub-terms as computations:

```lean
abbrev CExpr := Ctx → M Value     -- an expression's denotation
abbrev CStmt := Ctx → M Compl     -- a statement's
def Sem.binary (op : BinOp) (l r : CExpr) : CExpr := fun ctx => do
  let lv ← l ctx; let rv ← r ctx; …   -- the spec's steps, as the interpreter had them
```

The interpreter becomes the fold: `denoteExpr (n+1) (.binary op l r) = Sem.binary op (denoteExpr n l)
(denoteExpr n r)` (with a depth parameter `n`, as now). Behaviour is unchanged (test262's
baseline checks it).

The compiler prints, for a function's syntax tree, the same fold unrolled:

```lean
def add_body : CStmt := Sem.ret (Sem.binary .add (Sem.ident "a") (Sem.ident "b"))
theorem add_body_eq : add_body = denoteStmts depth add_ast := rfl   -- definitional unfolding
```

So generated code is readable, and equal to the interpreter by construction (one `rfl` per
definition, or `simp only [denote…]` when the kernel needs help).

## Proofs about programs

- Lemmas about combinators, once for all programs: `Sem.binary .add` on two Numbers is `F64.add`;
  `Sem.ident x` reads the binding `x` resolves to; `Sem.ret`, `Sem.ifS`, loops (with invariants)…
- Lemmas about the runtime: property get/set on ordinary objects, `call` of a function object
  whose body is a generated definition (the driver's request answered by the body's denotation).
- A program-level statement then reads, e.g., `∀ a b : F64, run (callFn add_body [num a, num b]) =
  ok (num (a.add b))`.

## Depth parameter

Denotations carry the interpreter's structural depth `n` (it makes recursion total). For a tree of
height `h`, `denote n t` is the same for every `n > h` (a lemma: fuel monotonicity); generated
definitions are stated at `n = height + 1`.

## Status

- Done: expression and statement combinators (`ES.Sem` in `ES/Interp.lean`); the generator
  (`ES/Gen.lean`, `leanjs compile --defs`), whose `_eq` theorems are proved by `rfl`; a first
  lemma library (`JSProofs/Basic.lean`) and a worked proof (`JSProofs/Add.lean`: `add` returns the sum
  of two Numbers, for the generated definition and for the interpreter on `add`'s syntax tree).
- What makes `rfl` work: the interpreter maps sub-terms with `amap` (List.map), not `Array.map`
  (well-founded recursion does not unfold); syntactic decisions are AST data (`Expr.call`'s
  `directEval` flag), not string comparisons; theorems are stated at a symbolic depth `n + k`.
- Covered by combinators: identifiers, literals, templates, operators, conditionals, property
  access, calls, `new`, assignment (not destructuring), function expressions, array and object
  literals, sequences, `await`; blocks, declarations (identifier targets), `if`, `while`,
  `do-while`, `for`, `return`, `throw`, `break`/`continue`, labels, `try`, `switch`.
  `examples/constructs.js` generates no interpreter fallbacks.
- Still falling back to the interpreter (correct, but opaque in generated code): destructuring
  patterns, classes, `for-in`/`for-of`, `with`, tagged templates, regex literals, `yield`, `super`,
  dynamic `import()`, direct `eval`.
- Proof prerequisites in place: JSStr literals' equalities decide (`ofString` folds `String.toList`);
  JSStr equality is lawful (`LawfulBEq`, `LawfulHashable`), so `Std.HashMap` lemmas apply to
  environments; calls make no arguments object nothing can reach (`FuncInfo.usesArguments`).
- Call-proof library: `JSProofs/State.lean` (the monad and arena primitives as rewriting rules),
  `JSProofs/Loops.lean` (`foldArr` is `foldList`), `JSProofs/Env.lean` (environment operations stated
  over `State.envEntry`/`State.setEnv`, so `simp` threads the state: HasBinding, CreateMutableBinding,
  InitializeBinding, ResolveBinding, parameter binding, two-level identifier reads).
  `JSProofs/AddCall.lean` composes them: `add_fdi` (FunctionDeclarationInstantiation binds `a ↦ x`,
  `b ↦ y`), `add_body` (`evalFunctionBody` returns `x + y`), `add_call` (`callECMA`, with an object
  as `this`, returns `x + y` and restores the caller's realm and script). No `sorry`.
- Lessons for `simp`: `M` is an `abbrev` (else `pure x s` does not rewrite); fuel hypotheses read
  `s.fuel ≠ 0` (simp normalizes `0 < n`); simp cannot discharge `Bool`-valued `isDeclLike`
  side conditions or literal depths (`2 ≤ 999998`), so specialize those lemmas first; prove a step
  under `∃` with `refine ⟨?c, ?t, ?h, ?_⟩` and `conv => lhs; simp …`, which assigns the witnesses.
- A whole program: `JSProofs/AddScript.lean`'s `add_script` — run as the engine runs a script
  (ScriptEvaluation, the driver answering the call request), `function add(a, b) { return a + b }
  add(1, 2);` (examples/add_call.js) completes with the Number 3, from any state whose realm has an
  ordinary extensible global object without `add`, `%Function.prototype%`, and some fuel. Built from
  `JSProofs/Object.lean` (property maps, the heap, ordinary objects' internal methods via `Obj'.*`) and
  `JSProofs/Driver.lean` (`drive` answering a call).
- Keeping proofs cheap (the whole library builds in about a second):
  - simp lemmas are never proved by plain `rfl` (`Eq.trans rfl rfl`): `simp` applies `rfl` lemmas as
    definitional steps, and the kernel then checked whole goals by evaluating terms (JSStr byte arrays),
    taking minutes and gigabytes;
  - states are written with named updates (`State.setProp`, `State.allocObj`, `instState`, `gdiState`)
    that `simp` does not unfold, never with `{ s with heap := … }` chains;
  - intermediate states in a long proof are opaque variables (`obtain ⟨u, hu⟩ : ∃ u, f … = u`), not
    `let`s, which the elaborator unfolds;
  - key and string inequalities are proved facts (`PropMap.get?_insert_ne`), never decided in place.
- Prototype chains: `JSProofs/Proto.lean` — for chains of ordinary/function objects, [[HasProperty]],
  [[Get]] and [[Set]] agree with a pure walk of the chain (`ordLookup`), by induction over the chain
  (`hasProperty_chain`, `get_chain`, `set_chain`; at `maxDepth` for chains up to 9999 objects), and
  GetValue/PutValue of `o.key` follow (`getRefValue_prop`, `putRefValue_prop`). Example:
  `shadowing` (assigning an inherited writable property gives the object its own and leaves the
  prototype unchanged). Not covered yet: accessors (getters/setters are calls), exotic objects.
- Loops: `M.loop_inv` (JSProofs/Loops.lean: invariant, postcondition, decreasing measure) and the
  `while` rule `whileS_inv` (JSProofs/While.lean; `whileIter` is one iteration as `Sem.whileS` runs it).
  Integer Numbers: `JSProofs/NumInt.lean` — below 2^53 the engine's `addF`/`ltF` are `Int` `+`/`<`
  (`addF_int`, `ltF_int`, zero included). Environments: reading a binding in the first record or
  through to the function record, assigning a `let` binding (`setMutableBinding_decl`).
- A loop example: `JSProofs/Sum.lean` — `function sum(n) { let s = 0; let i = 0; while (i < n) { s = s + i;
  i = i + 1; } return s; }` (examples/sum.js): the body returns N(N−1)/2 for every natural N < 2^26
  (`sum_spec`, and `sum_interp_spec` for the interpreter on the syntax tree). Invariant: after k
  iterations `i = k`, `s = tri k`; one lemma per iteration kind (`iter_cont`, `iter_exit`), with
  intermediate states as opaque variables.
- The call of `sum`: `JSProofs/SumCall.lean` — FunctionDeclarationInstantiation with a parameter and
  lexical declarations (`sum_fdi`: exactly the shape `sum_spec` starts from), the body
  (`sum_body`), and the [[Call]] with `this` undefined (`sum_call`): returns N(N−1)/2.
  Environment allocation is a named update too (`State.pushEnv`, `allocEnv_eq`).
- `for` loops: `JSProofs/For.lean` — `forIter` (one iteration as `Sem.forS` runs it) and
  `perIterationEnv` (CreatePerIterationEnvironment; `perIterationEnv_one`). `JSProofs/SumFor.lean`:
  `for (let i = 0; i < n; i = i + 1) s = s + i` returns N(N−1)/2; each iteration's fresh environment
  is tracked by the invariant. The `for` statement inlines its iteration; after folding
  `perIterationEnv` back (`← perIterationEnv_def`) `erw` matches the loop with `forIter`.
  Environment chains: `identBody`/`resolveBody` steps, `identValue_skip0/1/2`, `resolveBinding_skip1`.
- Arrays: `JSProofs/Array.lean` — integers below 2^53 convert to their decimal digits (`toStr_int`), so
  `a[k]` reads the property `toString k`; [[Get]] of arrays is ordinary (`Obj'.get_array`);
  GetValue of `a[k]` and `a.key` (`getRefValue_index`, `getRefValue_name`). `JSProofs/Total.lean`:
  `total(a)` (a `for` loop over `a.length` adding `a[i]`) returns the sum of the elements, for arrays
  of fewer than 2^26 naturals below 2^26 (`total_spec`, `total_interp_spec`).
- Index keys: `JSProofs/StrIndex.lean` — `(JSStr.ofNat n).toArrayIndex? = some n` (the array exotic
  [[DefineOwnProperty]] parses its key): `JSStr.ofString` on characters below 256 as bytes,
  `toIndex?`'s loop as a fold over digits, the toolchain's `Nat.ofDigitChars_toDigits`; digit keys are
  not `"length"`. Numbers: `Conv.ofNat k = ofSmallInt k`, `toNat?`/`truncInt`/`toUint32` of small
  naturals (JSProofs/NumInt.lean).
- Array creation and writes: `JSProofs/ArrayWrite.lean` — `ArrayObj` (elements, writable `length`,
  nothing beyond); the exotic [[DefineOwnProperty]] appending at `length` and redefining an element,
  [[Set]] of an element, ArraySetLength to the current length; `array_literal` (an array literal of
  effect-free elements is a new `ArrayObj` with those elements); `putRefValue_element` (`a[k] = v`),
  `getRefValue_element`. Example: `JSProofs/ArrayWriteEx.lean` — `let a = [1, 2, 3]; a[1] = 5;
  return a[0] + a[1] + a[2]` returns 9 (`f_spec`, `f_interp_spec`).
- A loop that writes: `JSProofs/Double.lean` — `double(a)` (`a[i] = a[i] + a[i]` over `a.length`) leaves
  every element doubled (`double_spec`, `double_interp_spec`); the invariant is about the heap
  (`ArrayObj A len (dbl xs k)`: elements below `k` doubled), `arrayObj_congr` ignores indices past `len`.
- Full calls: `JSProofs/Calls.lean` — `callECMA_undef`: a plain call `g(args)` of a sloppy function
  returns `v` if its body does from any state the call sets up (fresh function environment, heap and
  existing environments unchanged), with a property of the final state carried through the heap.
  `JSProofs/TotalCall.lean` (`total_call`), `JSProofs/MoreCalls.lean` (`sumFor_call`, `double_call` — the
  array afterwards holds every element doubled — and `f_call`), each via its FDI and body lemmas.
- A whole script with two calls and state between them: `JSProofs/DTScript.lean` — examples/double_total.js
  (`let b = [3, 4, 5]; double(b); total(b);`) evaluates to 24 as ScriptEvaluation runs it, both call
  requests answered by the driver (`dt_script`). What makes the second call provable is a frame
  property of the first: `double_call` also states `Frame A s s'` (environments only added, objects
  other than the array and the realms unchanged) and the fuel it used, so `total` and `b` still resolve
  afterwards. Generic pieces: `Inst.instantiate_fn` (InstantiateFunctionObject for any simple
  function), the global record's declarative part (`createMutableBinding_global`,
  `initializeBinding_global`, `resolveBinding_global_decl`, `identValue_global_decl`), `call_req` (a
  statement `f(b)` asking the driver for the call).
- Writes past the end: `JSProofs/ArrayAppend.lean` — `a[len] = v` (`putRefValue_append`): OrdinarySet walks
  the prototype chain (`AbsentChain`: ordinary objects, functions, arrays — `Array.prototype` is an
  array — none with the index) and the array's [[DefineOwnProperty]] appends and moves `length`.
  `JSProofs/Iota.lean` — `iota(n)` (`let a = []; for (…) { a[i] = i; } return a;`) returns a new array
  holding 0, …, n − 1 (`iota_spec`, `iota_interp_spec`), assuming `Array.prototype`'s chain has no index
  property below `n`; the invariant (`HeapI`) keeps the objects that existed before the call unchanged,
  so that assumption, made about the starting state, holds at every write (`absentChain_mono`).
- The full call of `iota` (`JSProofs/IotaCall.lean`, `iota_call`): returns the new array and states what it
  leaves alone (the caller's environments, older objects, the realms) and the fuel it used.
- A script using a call's result: `JSProofs/ITScript.lean` — examples/iota_total.js
  (`let b = iota(5); total(b);`) evaluates to 10 (`it_script`). The `let` initializer is a call
  (`let_call_req`); the assumption that `Array.prototype`'s chain has no index property below 5 is
  about the starting state and is carried through GlobalDeclarationInstantiation, which changes the
  global object only at the keys `total` and `iota`, no index keys (`absentChain_mono_key`,
  `name_ne_index`).
- Scripts in general: `JSProofs/Script.lean`. For a non-strict script whose top level declares simple
  functions `fs` (distinct names) and `let` bindings `lets`, without Annex B functions:
  `gdi_simple` (GlobalDeclarationInstantiation ends in `instAll … fs (lets declared)`), `instAll_facts`
  (function `i` is object `heap.size + 2 i` with that code and realm, bound under its name; nothing else
  that existed changes), and `script_value` (the script's value is what its body, run from
  `scriptState`, drives to: `DrivesTo`, with `drivesTo_call` per answered call and `drivesTo_ok`).
  The loops are folds with an abstract step (`foldList_const`, `foldList_lets`, `foldList_fnsToInit`,
  `foldList_fns`). `DTScript.dt_script` and `ITScript.it_script` use them; a script proof is its
  statements and calls only. The global record's declarative part and the call statement `f(b)` are in
  `JSProofs/Global.lean`.
- Statements in general: `JSProofs/Stmts.lean` — `call_expr_req` (a call `f(e₁, …, eₙ)` of a function bound
  on the global object, arguments evaluating without effects: `args_pure`) asks the driver for the call;
  `exprStmt_req` and `let_req` wrap any expression that asks for one call as a statement or a global
  `let`. `JSProofs/AddTwice.lean` — examples/add_twice.js (`let r = add(1, 2); add(r, 4);`) evaluates to 7
  (`at_script`), from these and the script lemmas alone, with `add`'s call stating what it leaves alone
  (`AddTwice.add_call`).
- Statement lists, statement by statement: `JSProofs/Runs.lean` — `RunsTo eng r b w'` (`r`, its requests
  answered, ends in `b`, `w'`, under any continuation; `runsTo_ok`, `runsTo_bind`, `runsTo_call`,
  `runsTo_req1`), `StmtsRun` (one `RunsTo` fact per statement) and `stmts_run` (the list's completion,
  UpdateEmpty), `runs_funDecl`, `script_runs`. The three script proofs list their statements' facts
  instead of unrolling `Sem.stmts` by hand.
- Objects with methods: `JSProofs/Method.lean` — examples/method.js (`function inc() { this.n = this.n + 1;
  return this.n; } let o = { n: 0, inc: inc }; o.inc(); o.inc();`) evaluates to 2 (`me_script`). New
  pieces: `this` through the body's declarative record (`resolveThis_decl`), writing an own writable data
  property (`putRefValue_own`), the call with an object as `this` (`Calls.callECMA_obj`, `inc_call`:
  afterwards exactly `O.n = k + 1`), an object literal of data properties (`let_obj`, `cdp_ordinary`), a
  method call `e.m(…)` (`Stmts.method_call_req`), names bound on the global object
  (`Global.identValue_global_obj`).
- Closures: `JSProofs/Closure.lean` — examples/closure.js (`function make() { let n = 0; return function () {
  n = n + 1; return n; }; } let c = make(); c(); c();`) evaluates to 2 (`cl_script`). New pieces: an
  anonymous function expression (`instExpr`: its environment is the current lexical one), `make`'s call
  returning the closure with its environment `L` holding `n = 0` (`make_call`), reaching `n` from the
  closure's body through its block and function records (`identValue_captured`, `resolveBinding_captured`),
  the closure's call updating `n` in `L` after `make` has returned (`fn1_call`), and calling a function
  stored by a global `let` (`Stmts.call_decl_req`). `Script.instAll_facts` also states `d.privEnv = #[]`.
- Control flow for all inputs: `JSProofs/Max.lean` — `max(a, b)` (`if (a < b) { return b; } return a;`) returns
  `max x y` for every pair of integers below 2^26 in absolute value (`max_spec` by cases on `x < y`;
  `max_call`); examples/max.js (`let m = max(3, 7); max(m, 5);`) evaluates to 7 (`mx_script`).
- Exceptions: `JSProofs/Throw.lean` — `check(x)` (`if (x < 0) { throw x; } return x;`) returns `x` for every
  integer `x ≥ 0` and throws `x` for every `x < 0` (`check_call_ok`, `check_call_err`; `Calls.callECMA_undef_err`);
  the driver passes a callee's throw to the call's continuation (`drive_call_err`, `Script.drivesTo_call_err`,
  `Runs.runsTo_call_err`); `try_req`: the `try` statement asks for the call, and on the throw runs the
  `catch` clause (a new record with `e`, `bindPattern_ident_init`; assigning the global `let r`,
  `setMutableBinding_global_decl`). examples/throw.js (`let r = 0; try { r = check(0 - 7); } catch (e) {
  r = 0 - e; } r;`) evaluates to 7 (`th_script`).
- Nested calls: `JSProofs/Nested.lean` — `Runs eng n r b w'` (inductive: `r` ends in `.ok b w'`, each call request's
  callee driven one level deeper), closed under binding and handlers (`runs_bind`, `runs_tryCatch`), giving
  what driving yields (`drive_of_runs`); `callECMA_undef_runs` (a call whose body runs, making calls of its
  own); `runsTo_call_nested` (the script-level bridge). `twice(x)` (`return add(x, x);`) runs to `x + x` for
  every small integer (`twice_call`); examples/twice.js (`twice(21);`) evaluates to 42 (`tw_script`).
  `Script.instAll_facts` also states `d.env = ge`.
- Prototype methods: `JSProofs/ProtoM.lean` — examples/proto.js (`let p = { inc: inc }; let o = { __proto__: p, n: 0 };
  o.inc(); o.inc();`) evaluates to 2 (`pm_script`): [[SetPrototypeOf]] of a fresh object with its cycle check
  (`setPrototypeOf_fresh`; realm assumption: `Object.prototype` ordinary, prototype null), the method found on
  the prototype (`get_inc_proto` via `Obj'.get_chain`; `method_call_get_req`), `inc`'s call as in Method.lean.
- Recursion: `JSProofs/Rec.lean` — examples/rec.js (`function sum(n) { if (n < 1) return 0; return n + sum(n - 1); }`).
  `sum_call`: for every `k` with 0 + … + k < 2^26, the [[Call]] `sum(k)` at driver depth `m + 1 ≥ k + 1` runs
  (`Nested.Runs`) to `tsum k`, by induction on `k`: the body either returns 0 (`sum_spec_base`) or asks for
  `sum(k - 1)` and adds (`sum_spec_step`; `subF_nz` in NumInt), the inner call by the induction hypothesis one
  level down. `rc_script`: `sum(10)` evaluates to 55.
- Constructors: `JSProofs/Construct.lean` — [[Construct]] of a sloppy non-class function (`constructECMA_ord`: a fresh
  ordinary object with prototype `F.prototype`, the body run with `this` bound to it, the object returned when the
  body returns a non-object), `constructImpl_func`, and `.construct` requests for `DrivesTo`/`RunsTo`.
  `JSProofs/Ctor.lean` — examples/ctor.js (`function Counter() { this.n = 0; } Counter.prototype.inc = inc;
  let c = new Counter(); c.inc(); c.inc();`) evaluates to 2 (`ct_script`): a declared function's `prototype` object
  (`bindFn_proto`), `this.n = 0` creating `n` after looking up the chain (`ctr_construct`; realm assumption:
  `Object.prototype` has no `n` or `inc`), the assignment to `Counter.prototype.inc` (`set_proto_inc`), `new`
  as a request (`new_req`).
- Loops whose body makes calls: `JSProofs/LoopRuns.lean` — the loop rule over `Nested.Runs` (`loop_runs`: each
  iteration runs to `inl` with the invariant and a smaller measure, or to `inr`), `runs_loopRes_inl`/`_inr`, and
  `stmts3_runs`. `JSProofs/SumAdd.lean` — examples/sum_add.js (`for (let i = 0; i < n; i = i + 1) { s = add(s, i); }`):
  an iteration up to its request for `add` and its continuation for any state the callee leaves with the
  environments kept (`iterA_cont`), the call answered (`iterA_step`, `AddTwice.add_call`), the loop
  (`loopA_runs`), the `for` statement (`forSA_runs`), `sumAdd`'s body and call for every `N < 2^26`
  (`sumAdd_call`: 2 fuel per iteration), and `sa_script`: `sumAdd(10)` evaluates to 45.
- Strings: `JSProofs/Strings.lean` — `a + b` on strings is concatenation (`applyBinaryOp_add_str`), `s.length` on a
  primitive string its code-unit count (`getRefValue_str_length`), lengths add (`JSStr.length_append`).
  `JSProofs/Rep.lean` — examples/rep.js (`let s = ""; for (…; i < n; …) { s = s + "ab"; } return s;`): the loop
  proofs of SumFor with a string accumulator; `rep_call`: `rep(N)` returns `reps N` ("ab" repeated `N` times) for
  every `N < 2^26`, i.e. (`reps_eq`, via `JSStr.ofList_append`) `JSStr.ofString (String.join (List.replicate N "ab"))`
  (`rep_call_string`); `reps_length`: `2N` code units; `reps_five`: "ababababab"; `rp_script`: `rep(5).length`
  evaluates to 10.
- Numbers in strings: `JSProofs/Strings.lean` — Number::toString of a natural number below 2^53 is its decimal
  digits (`toStringDec_ofSmallInt`, `numberToJSStr_nat`), and `"…" + x` appends it (`applyBinaryOp_add_str_num`).
  `JSProofs/ListStr.lean` — examples/list.js (`s = s + i + ","` in a loop): `list_call_string`: `list(N)` returns
  `String.join ((List.range N).map fun k => toString k ++ ",")` for every `N < 2^26` (`lst_eq`); `ls_script`:
  `list(4)` evaluates to "0,1,2,3,".
- Indexing strings: `JSProofs/Strings.lean` — the key of `s[k]` is `k`'s numeral (`toPropertyKey_nat`), `a[k]` on a
  primitive string is the one-unit slice (`getRefValue_str_index`), and a slice of an encoded character list is the
  encoded character (`JSStr.slice_ofList`). `JSProofs/RepIndex.lean` — `rep_index`: `rep(n)[k]` is "a" at even and "b"
  at odd `k`, for every `k < 2n`; `ri_script`: `rep(5)[3]` (examples/rep_index.js) evaluates to "b".

## Stages

1. Expressions: move each `evalExpr` case into an `ES.Sem` combinator; the interpreter calls them.
2. Statements, patterns, classes, function bodies likewise.
3. The generator: per-function definitions + `_eq` theorems (`leanjs compile --defs`).
4. Lemma library and a worked example (a sorting function, an object with invariants).
- Runs with host steps (Zippy's docs/lean-engine.md): `JSProofs/HostRuns.lean` — `HR eng answer n h r b w h' k`: a run
  whose host requests (from any depth: `Req.host`, passed up through the frame stack) are answered by an
  embedder's `answer` over its own state (`drives`: no host requests; `host`; `call`: a callee so running, then
  the continuation). `hr_sound`: the embedder's loop (`driveHostAt`) gives that result, given fuel for the host
  steps (`call_ctx`: a caller's loop runs its callee's, via `finK`, `drive_call`, `drive_resumeFrame`;
  `pop_push`); `runMHost_of_hr` at the entry point; `hr_of_runs`/`hr_of_drivesTo` lift every existing proof.
