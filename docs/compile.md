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
  lemma library (`Proofs/Basic.lean`) and a worked proof (`Proofs/Add.lean`: `add` returns the sum
  of two Numbers, for the generated definition and for the interpreter on `add`'s syntax tree).
- What makes `rfl` work: the interpreter maps sub-terms with `amap` (List.map), not `Array.map`
  (well-founded recursion does not unfold); syntactic decisions are AST data (`Expr.call`'s
  `directEval` flag), not string comparisons; theorems are stated at a symbolic depth `n + k`.
- Next: combinators for the constructs still falling back to the interpreter (patterns, object and
  array literals, classes, for-in/of, try, switch); lemmas for calls (the driver running a
  function object's body) and for property access on ordinary objects; a whole-program example.

## Stages

1. Expressions: move each `evalExpr` case into an `ES.Sem` combinator; the interpreter calls them.
2. Statements, patterns, classes, function bodies likewise.
3. The generator: per-function definitions + `_eq` theorems (`leanjs compile --defs`).
4. Lemma library and a worked example (a sorting function, an object with invariants).
