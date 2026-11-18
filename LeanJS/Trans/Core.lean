/-
  Verified translators for the core fragment.

  Each translator is a total, structurally recursive function that returns
  its output *together with a proof* that the output is related to the input
  by the corresponding translation relation of `LeanJS.Semantics.TransRel`.
  Combined with the simulation theorems, this means every translation the
  CLI performs through this module is covered by the correctness proofs.

  Inputs outside the core fragment are rejected with a message saying which
  construct is unsupported; the CLI then falls back to the (unverified)
  legacy translators.
-/
import LeanJS.Semantics.TransRel

set_option linter.unusedVariables false

namespace LeanJS.Trans.Core

open LeanJS.JS
open LeanJS.Lean
open LeanJS.IR
open LeanJS.Semantics

abbrev Res (α : Type) := Except String α

/-! ## JS → IR -/

section JSToIR

/-- Name of a JS expression form, for diagnostics -/
def jsExprKind : JS.Expr → String
  | .this => "this"
  | .update .. => "++/--"
  | .assign .. => "assignment"
  | .«new» .. => "new"
  | .member _ (.computed _) => "computed member access"
  | .member .. => "member access (JS→IR: a missing field is `undefined` in JS but an error in IR)"
  | .sequence .. => "comma expression"
  | .template .. => "template literal"
  | .spread .. => "spread"
  | .await .. => "await"
  | .yield .. => "yield"
  | .literal (.regex ..) => "regular expression"
  | .function .. => "async/generator function or non-simple parameters"
  | .arrowFunction .. => "async arrow function or non-simple parameters"
  | _ => "expression"

def jsStmtKind : Stmt → String
  | .varDecl .var _ => "var declaration"
  | .varDecl .. => "declaration form (only `const`/`let x = e;` is supported)"
  | .while_ .. | .doWhile .. | .for_ .. | .forIn .. | .forOf .. => "loop"
  | .switch .. => "switch"
  | .try_ .. => "try/catch"
  | .break_ _ | .continue_ _ => "break/continue"
  | .classDecl .. => "class"
  | .importDecl .. | .exportNamed .. | .exportDefault .. | .exportAll .. => "import/export"
  | .labeled .. => "label"
  | .debugger => "debugger"
  | .funcDecl .. => "async/generator function or non-simple parameters"
  | _ => "statement"

def optParams (params : List Pattern) : Res (List String) :=
  match simpleParamNames params with
  | some ns => pure ns
  | none => throw "unsupported: destructuring or default parameters"

mutual

def jsExpr : (e : JS.Expr) → Res {ir // JSToIRExpr e ir}
  | .ident x => pure ⟨_, .ident⟩
  | .literal (.string s) => pure ⟨_, .str⟩
  | .literal (.number n) => pure ⟨_, .num⟩
  | .literal (.bool b) => pure ⟨_, .bool⟩
  | .literal .null => pure ⟨_, .null⟩
  | .literal .undefined => pure ⟨_, .undef⟩
  | .paren e => do
    let ⟨e', h⟩ ← jsExpr e
    pure ⟨e', .paren h⟩
  | .binary op l r =>
    match hop : jsBinOpToIR op with
    | none => throw s!"unsupported operator: {repr op}"
    | some _ => do
      let ⟨l', hl⟩ ← jsExpr l
      let ⟨r', hr⟩ ← jsExpr r
      pure ⟨_, .binary hl hr hop⟩
  | .unary op a =>
    match hop : jsUnaryOpToIR op with
    | none => throw s!"unsupported operator: {repr op}"
    | some _ => do
      let ⟨a', ha⟩ ← jsExpr a
      pure ⟨_, .unary ha hop⟩
  | .conditional c t e => do
    let ⟨c', hc⟩ ← jsExpr c
    let ⟨t', ht⟩ ← jsExpr t
    let ⟨e', he⟩ ← jsExpr e
    pure ⟨_, .cond hc ht he⟩
  | .call f args => do
    let ⟨f', hf⟩ ← jsExpr f
    let ⟨args', ha⟩ ← jsExprs args
    pure ⟨_, .call hf ha⟩
  | .arrowFunction params (.expr b) false =>
    match hp : simpleParamNames params with
    | none => throw "unsupported: destructuring or default parameters"
    | some _ => do
      let ⟨b', hb⟩ ← jsExpr b
      pure ⟨_, .arrow_expr hp hb⟩
  | .arrowFunction params (.block [.return_ (some b)]) false =>
    match hp : simpleParamNames params with
    | none => throw "unsupported: destructuring or default parameters"
    | some _ => do
      let ⟨b', hb⟩ ← jsExpr b
      pure ⟨_, .arrow_block hp (.ret hb)⟩
  | .arrowFunction params (.block ss) false =>
    match hp : simpleParamNames params with
    | none => throw "unsupported: destructuring or default parameters"
    | some _ => do
      let ⟨b', hb⟩ ← jsStmts ss
      pure ⟨_, .arrow_block hp (.general hb)⟩
  | .function name params [.return_ (some b)] false false =>
    match hp : simpleParamNames params with
    | none => throw "unsupported: destructuring or default parameters"
    | some _ => do
      let ⟨b', hb⟩ ← jsExpr b
      pure ⟨_, .function hp (.ret hb)⟩
  | .function name params ss false false =>
    match hp : simpleParamNames params with
    | none => throw "unsupported: destructuring or default parameters"
    | some _ => do
      let ⟨b', hb⟩ ← jsStmts ss
      pure ⟨_, .function hp (.general hb)⟩
  | .array elems => do
    let ⟨es, h⟩ ← jsElems elems
    pure ⟨_, .array h⟩
  | .object props => do
    let ⟨fs, h⟩ ← jsProps props
    pure ⟨_, .object h⟩
  | e => throw s!"unsupported: {jsExprKind e}"

def jsExprs : (es : List JS.Expr) → Res {es' // JSToIRExprs es es'}
  | [] => pure ⟨_, .nil⟩
  | e :: es => do
    let ⟨e', h⟩ ← jsExpr e
    let ⟨es', hs⟩ ← jsExprs es
    pure ⟨_, .cons h hs⟩

def jsElems : (es : List (Option JS.Expr)) → Res {es' // JSToIRElems es es'}
  | [] => pure ⟨_, .nil⟩
  | some e :: es => do
    let ⟨e', h⟩ ← jsExpr e
    let ⟨es', hs⟩ ← jsElems es
    pure ⟨_, .some h hs⟩
  | none :: es => do
    let ⟨es', hs⟩ ← jsElems es
    pure ⟨_, .hole hs⟩

def jsProps : (ps : List Property) → Res {fs // JSToIRProps ps fs}
  | [] => pure ⟨_, .nil⟩
  | .prop (.ident k) e .init false false :: ps => do
    let ⟨e', h⟩ ← jsExpr e
    let ⟨fs, hs⟩ ← jsProps ps
    pure ⟨_, .cons h hs⟩
  | _ :: _ => throw "unsupported: object property form (only `key: value` with identifier keys)"

def jsStmts : (ss : List Stmt) → Res {ir // JSToIRStmts ss ir}
  | [] => pure ⟨_, .nil⟩
  | .varDecl .const [.mk (.ident x none) (some init)] :: rest => do
    let ⟨i', hi⟩ ← jsExpr init
    let ⟨r', hr⟩ ← jsStmts rest
    pure ⟨_, .decl (.inl rfl) hi hr⟩
  | .varDecl .let [.mk (.ident x none) (some init)] :: rest => do
    let ⟨i', hi⟩ ← jsExpr init
    let ⟨r', hr⟩ ← jsStmts rest
    pure ⟨_, .decl (.inr rfl) hi hr⟩
  | .funcDecl f params [.return_ (some b)] false false :: rest =>
    match hp : simpleParamNames params with
    | none => throw "unsupported: destructuring or default parameters"
    | some _ => do
      let ⟨b', hb⟩ ← jsExpr b
      let ⟨r', hr⟩ ← jsStmts rest
      pure ⟨_, .funcDecl hp (.ret hb) hr⟩
  | .funcDecl f params body false false :: rest =>
    match hp : simpleParamNames params with
    | none => throw "unsupported: destructuring or default parameters"
    | some _ => do
      let ⟨b', hb⟩ ← jsStmts body
      let ⟨r', hr⟩ ← jsStmts rest
      pure ⟨_, .funcDecl hp (.general hb) hr⟩
  | [s] =>
    match hd : s.isDecl with
    | true => throw s!"unsupported: {jsStmtKind s}"
    | false => do
      let ⟨s', h⟩ ← jsStmt s
      pure ⟨_, .last hd h⟩
  | s :: s2 :: rest =>
    match hd : s.isDecl with
    | true => throw s!"unsupported: {jsStmtKind s}"
    | false => do
      let ⟨s', h⟩ ← jsStmt s
      let ⟨r', hr⟩ ← jsStmts (s2 :: rest)
      pure ⟨_, .cons hd h hr (by simp)⟩

def jsStmt : (s : Stmt) → Res {ir // JSToIRStmt s ir}
  | .expr e => do
    let ⟨e', h⟩ ← jsExpr e
    pure ⟨_, .expr h⟩
  | .block ss => do
    let ⟨b, h⟩ ← jsStmts ss
    pure ⟨_, .block h⟩
  | .empty => pure ⟨_, .empty⟩
  | .return_ (some e) => do
    let ⟨e', h⟩ ← jsExpr e
    pure ⟨_, .return_some h⟩
  | .return_ none => pure ⟨_, .return_none⟩
  | .throw e => do
    let ⟨e', h⟩ ← jsExpr e
    pure ⟨_, .throw h⟩
  | .ifStmt c t (some e) => do
    let ⟨c', hc⟩ ← jsExpr c
    let ⟨t', ht⟩ ← jsStmt t
    let ⟨e', he⟩ ← jsStmt e
    pure ⟨_, .if_else hc ht he⟩
  | .ifStmt c t none => do
    let ⟨c', hc⟩ ← jsExpr c
    let ⟨t', ht⟩ ← jsStmt t
    pure ⟨_, .if_noelse hc ht⟩
  | s => throw s!"unsupported: {jsStmtKind s}"

end

end JSToIR

/-! ## IR → JS -/

section IRToJS

/-- Lambda bodies that read better as a statement block -/
def preferBlock : IRExpr → Bool
  | .«let» .. | .seq _ | .«return» _ | .throw _ | .«if» .. => true
  | _ => false

mutual

def irExpr : (e : IRExpr) → Res {e' // IRToJSExpr e e'}
  | .var x => pure ⟨_, .var⟩
  | .lit (.number n) => pure ⟨_, .num⟩
  | .lit (.string s) => pure ⟨_, .str⟩
  | .lit (.bool b) => pure ⟨_, .bool⟩
  | .lit .unit => pure ⟨_, .unit⟩
  | .undefined => pure ⟨_, .undef⟩
  | .binOp op l r =>
    match hop : irBinOpToJS op with
    | none => throw "unsupported operator"
    | some _ => do
      let ⟨l', hl⟩ ← irExpr l
      let ⟨r', hr⟩ ← irExpr r
      pure ⟨_, .binOp hl hr hop⟩
  | .unaryOp op a =>
    match hop : irUnaryOpToJS op with
    | none => throw "unsupported operator"
    | some _ => do
      let ⟨a', ha⟩ ← irExpr a
      pure ⟨_, .unaryOp ha hop⟩
  | .«if» c t e => do
    let ⟨c', hc⟩ ← irExpr c
    let ⟨t', ht⟩ ← irExpr t
    let ⟨e', he⟩ ← irExpr e
    pure ⟨_, .if_ hc ht he⟩
  | .app f args => do
    let ⟨f', hf⟩ ← irExpr f
    let ⟨args', ha⟩ ← irExprs args
    pure ⟨_, .app hf ha⟩
  | .«let» x _ v b => do
    let ⟨v', hv⟩ ← irExpr v
    let ⟨b', hb⟩ ← irExpr b
    pure ⟨_, .let_ hv hb⟩
  | .lam none _ _ body false false =>
    if preferBlock body then do
      let ⟨ss, h⟩ ← irStmts .tail body
      pure ⟨_, .lam_block h⟩
    else
      match irExpr body with
      | .ok ⟨b', h⟩ => pure ⟨_, .lam_expr h⟩
      | .error _ => do
        let ⟨ss, h⟩ ← irStmts .tail body
        pure ⟨_, .lam_block h⟩
  | .lam (some _) _ _ body false false => do
    let ⟨ss, h⟩ ← irStmts .tail body
    pure ⟨_, .lam_named h⟩
  | .record fs => do
    let ⟨ps, h⟩ ← irFields fs
    pure ⟨_, .record h⟩
  | .project e _ => do
    let ⟨e', h⟩ ← irExpr e
    pure ⟨_, .project h⟩
  | .array es => do
    let ⟨es', h⟩ ← irExprs es
    pure ⟨_, .array h⟩
  | _ => throw "unsupported IR construct for JS expression"

def irExprs : (es : List IRExpr) → Res {es' // IRToJSExprs es es'}
  | [] => pure ⟨_, .nil⟩
  | e :: es => do
    let ⟨e', h⟩ ← irExpr e
    let ⟨es', hs⟩ ← irExprs es
    pure ⟨_, .cons h hs⟩

def irFields : (fs : List (String × IRExpr)) → Res {ps // IRToJSFields fs ps}
  | [] => pure ⟨_, .nil⟩
  | (_, e) :: fs => do
    let ⟨e', h⟩ ← irExpr e
    let ⟨ps, hs⟩ ← irFields fs
    pure ⟨_, .cons h hs⟩

def irStmts (m : StmtMode) : (e : IRExpr) → Res {ss // IRToJSStmts m e ss}
  | .«let» x ty (.lam (some f) ps caps body false false) b =>
    if hxf : f = x then by
      subst hxf
      exact do
        let ⟨ss, hs⟩ ← irStmts .tail body
        let ⟨rs, hr⟩ ← irStmts m b
        pure ⟨_, .funcDecl hs hr⟩
    else do
      let ⟨v', hv⟩ ← irExpr (.lam (some f) ps caps body false false)
      let ⟨ss, hb⟩ ← irStmts m b
      pure ⟨_, .let_ hv hb⟩
  | .«let» x _ v b => do
    let ⟨v', hv⟩ ← irExpr v
    let ⟨ss, hb⟩ ← irStmts m b
    pure ⟨_, .let_ hv hb⟩
  | .«if» c t e => do
    let ⟨c', hc⟩ ← irExpr c
    let ⟨ts, ht⟩ ← irStmts m t
    let ⟨es, he⟩ ← irStmts m e
    match es, he with
    | [], he => pure ⟨_, .if_noelse hc ht he⟩
    | [.ifStmt c2 t2 e2], he => pure ⟨_, .if_elseif hc ht he rfl⟩
    | _ :: _, he => pure ⟨_, .if_ hc ht he⟩
  | .seq es => irSeq m es
  | .«return» e => do
    let ⟨e', h⟩ ← irExpr e
    pure ⟨_, .ret h⟩
  | .throw e => do
    let ⟨e', h⟩ ← irExpr e
    pure ⟨_, .throw h⟩
  | .undefined => pure ⟨_, .undef⟩
  | .lit .unit => pure ⟨_, .unit⟩
  | e => do
    let ⟨e', h⟩ ← irExpr e
    match m with
    | .tail => pure ⟨_, .expr_tail h⟩
    | .discard => pure ⟨_, .expr_discard h⟩

def irSeq (m : StmtMode) : (es : List IRExpr) → Res {ss // IRToJSStmts m (.seq es) ss}
  | [] => throw "unsupported: empty sequence"
  | [e] => do
    let ⟨ss, h⟩ ← irStmts m e
    pure ⟨_, .seq_one h⟩
  | e :: e2 :: rest => do
    let ⟨ss, h⟩ ← irStmts .discard e
    let ⟨rs, hr⟩ ← irSeq m (e2 :: rest)
    match rs, hr with
    | [], hr => pure ⟨_, .seq_last h hr (by simp)⟩
    | r :: rs, hr =>
      match hnd : noDecls ss with
      | true => pure ⟨_, .seq_flat h hnd hr (by simp)⟩
      | false => pure ⟨_, .seq_block h hr (by simp)⟩

end

end IRToJS

/-! ## Lean → IR -/

section LeanToIR

/-- Curried IR lambdas for `fun p₁ … pₙ => body` -/
def leanLam {body : LeanExpr} {body' : IRExpr} (hb : LeanToIRExpr body body') :
    (ps : List LeanParam) → ps ≠ [] → {ir // LeanToIRExpr (.lam ps body) ir}
  | [p], _ => ⟨_, .lam_one hb⟩
  | p :: q :: qs, _ =>
    let ⟨ir, h⟩ := leanLam hb (q :: qs) (by simp)
    ⟨_, .lam_cons (by simp) h⟩

def leanExprKind : LeanExpr → String
  | .bind .. | .doBlock _ => "do-notation"
  | .«match» .. => "match"
  | .«while» .. | .«for» .. => "loop"
  | .«return» _ => "return"
  | .arrayIdx .. => "array indexing"
  | .refNew _ | .refGet _ | .refSet .. => "mutable references"
  | .«try» .. => "try/catch"
  | .hole => "hole"
  | .«if» _ _ none => "`if` without `else`"
  | .lam [] _ => "fun with no parameters"
  | _ => "expression"

mutual

def leanExpr : (e : LeanExpr) → Res {ir // LeanToIRExpr e ir}
  | .ident x => pure ⟨_, .ident⟩
  | .lit l => pure ⟨_, .lit⟩
  | .unit => pure ⟨_, .unit⟩
  | .paren e => do
    let ⟨e', h⟩ ← leanExpr e
    pure ⟨_, .paren h⟩
  | .lam (p :: ps) body => do
    let ⟨b', hb⟩ ← leanExpr body
    pure (leanLam hb (p :: ps) (by simp))
  | .app f a => do
    let ⟨f', hf⟩ ← leanExpr f
    let ⟨a', ha⟩ ← leanExpr a
    pure ⟨_, .app hf ha⟩
  | .«let» x _ v b => do
    let ⟨v', hv⟩ ← leanExpr v
    let ⟨b', hb⟩ ← leanExpr b
    pure ⟨_, .let_ hv hb⟩
  | .«if» c t (some e) => do
    let ⟨c', hc⟩ ← leanExpr c
    let ⟨t', ht⟩ ← leanExpr t
    let ⟨e', he⟩ ← leanExpr e
    pure ⟨_, .if_ hc ht he⟩
  | .binOp op l r =>
    match hop : leanBinOpToIR op with
    | none => throw s!"unsupported operator: {op}"
    | some _ => do
      let ⟨l', hl⟩ ← leanExpr l
      let ⟨r', hr⟩ ← leanExpr r
      pure ⟨_, .binOp hl hr hop⟩
  | .unaryOp op a =>
    match hop : leanUnaryOpToIR op with
    | none => throw s!"unsupported operator: {op}"
    | some _ => do
      let ⟨a', ha⟩ ← leanExpr a
      pure ⟨_, .unaryOp ha hop⟩
  | .structLit _ fs => do
    let ⟨fs', h⟩ ← leanFields fs
    pure ⟨_, .structLit h⟩
  | .arrayLit es => do
    let ⟨es', h⟩ ← leanExprs es
    pure ⟨_, .arrayLit h⟩
  | .proj e _ => do
    let ⟨e', h⟩ ← leanExpr e
    pure ⟨_, .proj h⟩
  | .«throw» e => do
    let ⟨e', h⟩ ← leanExpr e
    pure ⟨_, .throw h⟩
  | e => throw s!"unsupported: {leanExprKind e}"

def leanExprs : (es : List LeanExpr) → Res {es' // LeanToIRExprs es es'}
  | [] => pure ⟨_, .nil⟩
  | e :: es => do
    let ⟨e', h⟩ ← leanExpr e
    let ⟨es', hs⟩ ← leanExprs es
    pure ⟨_, .cons h hs⟩

def leanFields : (fs : List (String × LeanExpr)) → Res {fs' // LeanToIRFields fs fs'}
  | [] => pure ⟨_, .nil⟩
  | (_, e) :: fs => do
    let ⟨e', h⟩ ← leanExpr e
    let ⟨fs', hs⟩ ← leanFields fs
    pure ⟨_, .cons h hs⟩

end

end LeanToIR

/-! ## IR → Lean -/

section IRToLean

/-- Arguments after the first must be atoms (see `IRToLeanAtoms`) -/
def irLeanAtoms : (es : List IRExpr) → Res {es' // IRToLeanAtoms es es'}
  | [] => pure ⟨_, .nil⟩
  | .var x :: es => do
    let ⟨es', hs⟩ ← irLeanAtoms es
    pure ⟨_, .cons .var .var hs⟩
  | .lit (.number n) :: es => do
    let ⟨es', hs⟩ ← irLeanAtoms es
    pure ⟨_, .cons .lit .num hs⟩
  | .lit (.string s) :: es => do
    let ⟨es', hs⟩ ← irLeanAtoms es
    pure ⟨_, .cons .lit .str hs⟩
  | .lit (.bool b) :: es => do
    let ⟨es', hs⟩ ← irLeanAtoms es
    pure ⟨_, .cons .lit .bool hs⟩
  | .lit .unit :: es => do
    let ⟨es', hs⟩ ← irLeanAtoms es
    pure ⟨_, .cons .lit .unit hs⟩
  | .undefined :: es => do
    let ⟨es', hs⟩ ← irLeanAtoms es
    pure ⟨_, .cons .undef .undef hs⟩
  | _ :: _ => throw "unsupported for Lean: arguments after the first must be variables or literals"

mutual

def irLean : (e : IRExpr) → Res {e' // IRToLeanExpr e e'}
  | .var x => pure ⟨_, .var⟩
  | .lit (.number n) => pure ⟨_, .num⟩
  | .lit (.string s) => pure ⟨_, .str⟩
  | .lit (.bool b) => pure ⟨_, .bool⟩
  | .lit .unit => pure ⟨_, .unit⟩
  | .undefined => pure ⟨_, .undef⟩
  | .«let» x _ v b => do
    let ⟨v', hv⟩ ← irLean v
    let ⟨b', hb⟩ ← irLean b
    pure ⟨_, .let_ hv hb⟩
  | .lam none (p :: ps) _ body false false => do
    let ⟨b', hb⟩ ← irLean body
    pure ⟨_, .lam hb (by simp)⟩
  | .app f (a :: as) => do
    let ⟨f', hf⟩ ← irLean f
    let ⟨a', ha⟩ ← irLean a
    let ⟨as', hs⟩ ← irLeanAtoms as
    pure ⟨_, .app hf ha hs⟩
  | .binOp op l r =>
    match hop : irBinOpToLean op with
    | none => throw "unsupported operator for Lean"
    | some _ => do
      let ⟨l', hl⟩ ← irLean l
      let ⟨r', hr⟩ ← irLean r
      pure ⟨_, .binOp hl hr hop⟩
  | .unaryOp op a =>
    match hop : irUnaryOpToLean op with
    | none => throw "unsupported operator for Lean"
    | some _ => do
      let ⟨a', ha⟩ ← irLean a
      pure ⟨_, .unaryOp ha hop⟩
  | .«if» c t e => do
    let ⟨c', hc⟩ ← irLean c
    let ⟨t', ht⟩ ← irLean t
    let ⟨e', he⟩ ← irLean e
    pure ⟨_, .if_ hc ht he⟩
  | .record fs => do
    let ⟨fs', h⟩ ← irLeanFields fs
    pure ⟨_, .record h⟩
  | .array es => do
    let ⟨es', h⟩ ← irLeanExprs es
    pure ⟨_, .array h⟩
  | .project e _ => do
    let ⟨e', h⟩ ← irLean e
    pure ⟨_, .project h⟩
  | .throw e => do
    let ⟨e', h⟩ ← irLean e
    pure ⟨_, .throw h⟩
  | .lam (some _) .. => throw "unsupported for Lean: named function (`function` declaration or expression; use an arrow function)"
  | .lam none [] .. => throw "unsupported for Lean: function with no parameters"
  | .lam .. => throw "unsupported for Lean: async or generator function"
  | .app .. => throw "unsupported for Lean: call with no arguments"
  | .seq _ => throw "unsupported for Lean: statement sequence"
  | .«return» _ => throw "unsupported for Lean: return"
  | _ => throw "unsupported IR construct for Lean"

def irLeanExprs : (es : List IRExpr) → Res {es' // IRToLeanExprs es es'}
  | [] => pure ⟨_, .nil⟩
  | e :: es => do
    let ⟨e', h⟩ ← irLean e
    let ⟨es', hs⟩ ← irLeanExprs es
    pure ⟨_, .cons h hs⟩

def irLeanFields : (fs : List (String × IRExpr)) → Res {fs' // IRToLeanFields fs fs'}
  | [] => pure ⟨_, .nil⟩
  | (_, e) :: fs => do
    let ⟨e', h⟩ ← irLean e
    let ⟨fs', hs⟩ ← irLeanFields fs
    pure ⟨_, .cons h hs⟩

end

end IRToLean

end LeanJS.Trans.Core
