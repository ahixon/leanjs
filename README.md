# leanjs

JavaScript in Lean 4.

- **`ES/` — an ECMAScript engine in pure Lean.** A parser with all of ECMA-262's early errors, a
  RegExp engine, exact Number/BigInt/Date arithmetic (no `Float`), the full object model (proxies,
  typed arrays, module namespaces), generators, async functions and generators, modules with
  top-level await, and the standard library. Every function is total. It passes 99.8% of
  [test262](https://github.com/tc39/test262) (81,206 of 81,367 runs; proposals not yet in the
  standard are skipped and counted).
- **JS → Lean (in progress):** compiles JavaScript to Lean code over the engine's runtime, so
  compiled programs mean exactly what the engine says they mean.

```sh
lake build
.lake/build/bin/es -e 'class A { #x = 40; get x() { return this.#x + 2 } } new A().x'   # => 42
tools/fetch-test262.sh && lake exe test262 test/language -j 4
```

Design notes: `docs/es.md`. The earlier verified-core transpiler (its own JS model, IR and
simulation proofs) is in the git history before the `es-engine` branch.
