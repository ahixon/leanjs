import ES.AST
import Std.Data.HashSet

/-!
# Static semantics of declarations (what the runtime instantiates)

spec: https://tc39.es/ecma262/#sec-syntax-directed-operations-scope-analysis (8.2)

Recursion over statements is structural on a depth parameter `n` (the parser's nesting limit
bounds statement nesting far below `declDepth`).
-/

namespace ES

open Std (HashSet)

/-- A var-scoped declaration: a `var` declarator's pattern, or a function declaration at the top
level of a function/script. -/
inductive VarScoped where
  | pat (p : Pattern)
  | func (f : Func)

/-- A lexically scoped declaration. -/
inductive LexScoped where
  | binding (kind : VarKind) (p : Pattern)
  | func (f : Func)
  | cls (c : Class)

/-- Depth bound for the walks below (statement nesting; the parser's nesting limit is lower). -/
def declDepth : Nat := 100000

/-- BoundNames of a binding pattern. spec: https://tc39.es/ecma262/#sec-static-semantics-boundnames -/
def boundNamesN : Nat → Pattern → Array JSStr
  | 0, _ => #[]
  | n + 1, p => match p with
    | .ident x => #[x]
    | .expr _ => #[]
    | .obj props rest =>
      let a := props.foldl (fun acc (pp : PatProp) => match pp with
        | .mk _ t _ => acc ++ boundNamesN n t) #[]
      match rest with | some r => a ++ boundNamesN n r | none => a
    | .arr elems rest =>
      let a := elems.foldl (fun acc e => match e with
        | some (.mk t _) => acc ++ boundNamesN n t
        | none => acc) #[]
      match rest with | some r => a ++ boundNamesN n r | none => a

def boundNames (p : Pattern) : Array JSStr := boundNamesN declDepth p

def LexScoped.names : LexScoped → Array JSStr
  | .binding _ p => boundNames p
  | .func f => match f.name with | some x => #[x] | none => #[]
  | .cls c => match c.name with | some x => #[x] | none => #[]

def LexScoped.isConstant : LexScoped → Bool
  | .binding k _ => k == .const || k == .using || k == .awaitUsing
  | _ => false

def VarScoped.names : VarScoped → Array JSStr
  | .pat p => boundNames p
  | .func f => match f.name with | some x => #[x] | none => #[]

/-- VarScopedDeclarations of a statement (not looking into functions; function declarations in
blocks are lexical). spec: https://tc39.es/ecma262/#sec-static-semantics-varscopeddeclarations -/
def varScopedN : Nat → Stmt → Array VarScoped
  | 0, _ => #[]
  | n + 1, s => match s with
    | .varDecl .var ds => ds.map fun (d : VarDeclarator) => match d with | .mk p _ => .pat p
    | .block body => body.foldl (fun acc s => acc ++ varScopedN n s) #[]
    | .ifS _ c a => varScopedN n c ++ (match a with | some a => varScopedN n a | none => #[])
    | .whileS _ b | .doWhile b _ | .with _ b => varScopedN n b
    | .labeled _ b => match b with
      | .funDecl _ => #[]
      | b => varScopedN n b
    | .forS init _ _ b =>
      (match init with
       | some (.decl .var ds) => ds.map fun (d : VarDeclarator) => match d with | .mk p _ => .pat p
       | _ => #[]) ++ varScopedN n b
    | .forIn lhs _ b | .forOf lhs _ b _ =>
      (match lhs with
       | .decl .var p _ => #[.pat p]
       | _ => #[]) ++ varScopedN n b
    | .tryS blk h fin =>
      blk.foldl (fun acc s => acc ++ varScopedN n s) #[] ++
      (match h with | some (.mk _ body) => body.foldl (fun acc s => acc ++ varScopedN n s) #[] | none => #[]) ++
      (match fin with | some f => f.foldl (fun acc s => acc ++ varScopedN n s) #[] | none => #[])
    | .switch _ cases => cases.foldl (fun acc (c : SwitchCase) => match c with
        | .mk _ body => body.foldl (fun acc s => acc ++ varScopedN n s) acc) #[]
    | .exportDecl (.decl s) => varScopedN n s
    | _ => #[]

/-- TopLevelVarScopedDeclarations of a function body or script: also the top-level function
declarations (and labelled ones).
spec: https://tc39.es/ecma262/#sec-static-semantics-toplevelvarscopeddeclarations -/
def topLevelVarScoped (body : Array Stmt) : Array VarScoped :=
  body.foldl (fun acc s => acc ++ go s) #[]
where
  go (s : Stmt) : Array VarScoped := match s with
    | .funDecl f => #[.func f]
    | .labeled _ b => labeled declDepth b
    | s => varScopedN declDepth s
  labeled : Nat → Stmt → Array VarScoped
    | 0, _ => #[]
    | n + 1, s => match s with
      | .funDecl f => #[.func f]
      | .labeled _ b => labeled n b
      | s => varScopedN declDepth s

/-- TopLevelVarDeclaredNames spec: https://tc39.es/ecma262/#sec-static-semantics-toplevelvardeclarednames -/
def topLevelVarDeclaredNames (body : Array Stmt) : Array JSStr :=
  (topLevelVarScoped body).foldl (fun acc d => acc ++ d.names) #[]

/-- The lexically scoped declaration a statement makes directly (if any). -/
def stmtLexScoped (topLevel : Bool) : Stmt → Array LexScoped
  | .varDecl k ds =>
    if k == .var then #[] else ds.map fun (d : VarDeclarator) => match d with | .mk p _ => .binding k p
  | .classDecl c => #[.cls c]
  | .funDecl f => if topLevel then #[] else #[.func f]
  | .labeled _ b => labeledFn topLevel declDepth b
  | .exportDecl (.decl s) => stmtLexScoped topLevel s
  | .exportDecl (.defaultFunc f) => #[.func f]
  | .exportDecl (.defaultClass c) => #[.cls c]
  | _ => #[]
where
  labeledFn (topLevel : Bool) : Nat → Stmt → Array LexScoped
    | 0, _ => #[]
    | n + 1, s => match s with
      | .funDecl f => if topLevel then #[] else #[.func f]
      | .labeled _ b => labeledFn topLevel n b
      | _ => #[]

/-- LexicallyScopedDeclarations of a block's (or case clauses') statement list.
spec: https://tc39.es/ecma262/#sec-static-semantics-lexicallyscopeddeclarations -/
def lexicallyScoped (body : Array Stmt) : Array LexScoped :=
  body.foldl (fun acc s => acc ++ stmtLexScoped false s) #[]

/-- TopLevelLexicallyScopedDeclarations (function bodies, scripts: function declarations are
var-scoped there). spec: https://tc39.es/ecma262/#sec-static-semantics-toplevellexicallyscopeddeclarations -/
def topLevelLexicallyScoped (body : Array Stmt) : Array LexScoped :=
  body.foldl (fun acc s => acc ++ stmtLexScoped true s) #[]

/-- Module code: LexicallyScopedDeclarations of a ModuleItemList (function declarations are
lexical in modules). -/
def moduleLexicallyScoped (body : Array Stmt) : Array LexScoped := lexicallyScoped body

/-- The statements of a switch's clauses (one statement list for LexicallyScopedDeclarations). -/
def caseBodies (cases : Array SwitchCase) : Array Stmt :=
  cases.foldl (fun acc (c : SwitchCase) => match c with | .mk _ b => acc ++ b) #[]

/-- Annex B.3.2: the function declarations in blocks (and switch clauses, and B.3.3's `if`
statements) of a function body or script that also get a `var` binding: those whose name, as a
`var`, would not conflict with a lexical declaration of an enclosing block, nor with
`excluded` (e.g. the parameter names, or the top level's lexical names). Plain
FunctionDeclarations only (not generators or async functions).
spec: https://tc39.es/ecma262/#sec-block-level-function-declarations-web-legacy-compatibility-semantics -/
def annexBFunctions (body : Array Stmt) (excluded : Array JSStr) : Array Func :=
  stmtsWalk declDepth body excluded
where
  /-- The lexical names of a block other than plain function declarations (which may be
  duplicated in sloppy blocks). -/
  blockLex (ss : Array Stmt) : Array JSStr :=
    (lexicallyScoped ss).foldl (fun acc d => match d with
      | .func f => if f.isAsync || f.isGenerator then acc ++ d.names else acc
      | d => acc ++ d.names) #[]
  stmtsWalk : Nat → Array Stmt → Array JSStr → Array Func
    | 0, _, _ => #[]
    | n + 1, ss, ex => ss.foldl (fun acc s => acc ++ stmtWalk n s ex) #[]
  /-- A function declaration directly in a block whose outer lexical names are `ex`. -/
  blockFns : Nat → Array Stmt → Array JSStr → Array Func
    | 0, _, _ => #[]
    | n + 1, ss, ex =>
      -- (this block's own function declarations may repeat a candidate's name; enclosing blocks'
      -- may not)
      let ex' := ex ++ blockLex ss
      let exNested := ex ++ (lexicallyScoped ss).foldl (fun acc d => acc ++ d.names) #[]
      ss.foldl (fun acc s => acc ++ (match s with
        | .funDecl f =>
          if f.isAsync || f.isGenerator then #[] else
          match f.name with
          | some x => if ex'.contains x then #[] else #[f]
          | none => #[]
        | _ => #[]) ++ stmtWalk n s exNested) #[]
  stmtWalk : Nat → Stmt → Array JSStr → Array Func
    | 0, _, _ => #[]
    | n + 1, s, ex => match s with
      | .block b => blockFns n b ex
      | .ifS _ c a =>
        -- (B.3.3: a function declaration as an if's branch is as if in a block)
        let one (st : Stmt) := match st with
          | .funDecl _ => blockFns n #[st] ex
          | st => stmtWalk n st ex
        one c ++ (match a with | some a => one a | none => #[])
      | .whileS _ b | .doWhile b _ | .with _ b | .labeled _ b => stmtWalk n b ex
      | .forS init _ _ b =>
        let ex' := match init with
          | some (.decl k ds) => if k == .var then ex else
              ex ++ ds.foldl (fun acc (d : VarDeclarator) => match d with | .mk p _ => acc ++ boundNames p) #[]
          | _ => ex
        stmtWalk n b ex'
      | .forIn lhs _ b | .forOf lhs _ b _ =>
        let ex' := match lhs with
          | .decl k p _ => if k == .var then ex else ex ++ boundNames p
          | _ => ex
        stmtWalk n b ex'
      | .tryS blk h fin =>
        blockFns n blk ex ++
        (match h with
         | some (.mk p body) =>
           -- (B.3.4: a catch parameter that is a simple identifier does not conflict)
           let ex' := match p with
             | some (.ident _) | none => ex
             | some p => ex ++ boundNames p
           blockFns n body ex'
         | none => #[]) ++
        (match fin with | some f => blockFns n f ex | none => #[])
      | .switch _ cases => blockFns n (caseBodies cases) ex
      | _ => #[]

/-- The ids of a list of functions (to recognize them when their declarations are evaluated). -/
def funcIds (fs : Array Func) : HashSet Nat := fs.foldl (fun acc f => acc.insert f.info.id) {}

/-- Whether a body's lexical declarations include `using`/`await using` ones (and an `await using`). -/
def usingKinds (decls : Array LexScoped) : Bool × Bool :=
  decls.foldl (fun (u, a) d => match d with
    | .binding .using _ => (true, a)
    | .binding .awaitUsing _ => (true, true)
    | _ => (u, a)) (false, false)

/-- FunctionDeclarationInstantiation's static facts for a function.
spec: https://tc39.es/ecma262/#sec-functiondeclarationinstantiation (steps 5-18) -/
def analyzeFDI (kind : FuncKind) (strict usesArguments paramsHaveExpressions : Bool)
    (params : Array Param) (body : FuncBody) : FDIInfo :=
  -- 5-6.
  let paramNames := params.foldl (fun acc (p : Param) => match p with | .mk t _ _ => acc ++ boundNames t) #[]
  let hasDuplicates := (paramNames.foldl (fun (acc : HashSet JSStr × Bool) nm =>
    (acc.1.insert nm, acc.2 || acc.1.contains nm)) ({}, false)).2
  let stmts := match body with | .stmts b => b | .expr _ => #[]
  -- 9-11.
  let varDecls := topLevelVarScoped stmts
  let varNames := varDecls.foldl (fun (acc : Array JSStr) dd => acc ++ dd.names) #[]
  let lexDecls := topLevelLexicallyScoped stmts
  let lexNames := lexDecls.foldl (fun (acc : Array JSStr) dd => acc ++ dd.names) #[]
  -- 12-14.
  let functionNames := varDecls.reverse.foldl (fun names dd => match dd with
    | .func fn => match fn.name with
      | some nm => if names.contains nm then names else #[nm] ++ names
      | none => names
    | .pat _ => names) (#[] : Array JSStr)
  let hasFunctions := varDecls.any fun dd => match dd with | .func _ => true | _ => false
  -- 15-18. (thisMode is lexical exactly for arrow functions)
  let argumentsNeeded :=
    kind != .arrow && !paramNames.contains "arguments" &&
    !(!paramsHaveExpressions && (functionNames.contains "arguments" || lexNames.contains "arguments")) &&
    kind != .classField && kind != .classStaticBlock && usesArguments
  { paramNames, hasDuplicates, varNames, hasFunctions, functionNames,
    hasLexical := !lexDecls.isEmpty, lexNames, argumentsNeeded,
    hasAnnexB := !strict && !(annexBFunctions stmts (paramNames ++ lexNames)).isEmpty,
    usesDispose := (usingKinds lexDecls).1 }

end ES
