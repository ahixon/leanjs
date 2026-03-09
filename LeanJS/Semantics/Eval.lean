/-
  Big-step operational semantics for the LeanJS IR.

  `eval env store fuel expr` evaluates `expr` in environment `env` with
  mutable store `store`, using `fuel` to bound recursion depth.
  Returns an `EvalResult` carrying the resulting value (or control flow signal)
  and updated store.
-/
import LeanJS.Semantics.Value
import LeanJS.Semantics.BinOp
import LeanJS.Semantics.Match

namespace LeanJS.Semantics

open LeanJS.IR

/-- Core big-step evaluator for IR expressions -/
partial def eval (env : Env) (store : Store) (fuel : Nat) (e : IRExpr) : EvalResult :=
  match fuel with
  | 0 => .error "out of fuel"
  | fuel' + 1 =>
  match e with
  -- Literals and variables
  | .lit v => .val (irLitToValue v) store
  | .var name =>
    match env.lookup name with
    | some v => .val v store
    | none => .error s!"unbound variable: {name}"
  | .undefined => .val .undefined store
  | .this =>
    match env.lookup "this" with
    | some v => .val v store
    | none => .val .undefined store

  -- Let binding
  | .«let» name _ty val body =>
    match eval env store fuel' val with
    | .val v s => eval (env.extend name v) s fuel' body
    | other => other

  -- Lambda: capture current environment
  | .lam name params _captures body _async _gen =>
    let paramNames := params.map Prod.fst
    .val (.closure env name paramNames body) store

  -- Function application
  | .app func args =>
    match eval env store fuel' func with
    | .val fv s1 =>
      match evalArgs env s1 fuel' args [] with
      | .val (.array argVals) s2 =>
        applyFunc fv argVals s2 fuel'
      | other => other
    | other => other

  -- Binary operators
  | .binOp op left right =>
    match eval env store fuel' left with
    | .val lv s1 =>
      match eval env s1 fuel' right with
      | .val rv s2 => evalBinOp op lv rv s2
      | other => other
    | other => other

  -- Unary operators
  | .unaryOp op arg =>
    match eval env store fuel' arg with
    | .val v s => evalUnaryOp op v s
    | other => other

  -- Mutable references
  | .mkRef val =>
    match eval env store fuel' val with
    | .val v s =>
      let (s', loc) := s.alloc v
      .val (.ref loc) s'
    | other => other

  | .deref ref =>
    match eval env store fuel' ref with
    | .val (.ref loc) s =>
      match s.read loc with
      | some v => .val v s
      | none => .error s!"dangling ref: {repr loc}"
    | .val _ _ => .error "deref of non-ref"
    | other => other

  | .assign ref val =>
    match eval env store fuel' ref with
    | .val (.ref loc) s1 =>
      match eval env s1 fuel' val with
      | .val v s2 =>
        match s2.write loc v with
        | some s3 => .val .unit s3
        | none => .error s!"dangling ref on write: {repr loc}"
      | other => other
    | .val _ _ => .error "assign to non-ref"
    | other => other

  -- Records
  | .record fields => evalFields env store fuel' fields []

  | .project expr field =>
    match eval env store fuel' expr with
    | .val (.record fields) s =>
      match fields.lookup field with
      | some v => .val v s
      | none => .error s!"missing field: {field}"
    | .val (.constructed tag _) s =>
      if field == "_tag" then .val (.string tag) s
      else .error s!"cannot project {field} from constructed value"
    | .val _ _ => .error "project on non-record"
    | other => other

  | .projectIdx expr idx =>
    match eval env store fuel' expr with
    | .val rv s1 =>
      match eval env s1 fuel' idx with
      | .val (.string field) s2 =>
        match rv with
        | .record fields =>
          match fields.lookup field with
          | some v => .val v s2
          | none => .error s!"missing field: {field}"
        | _ => .error "projectIdx string on non-record"
      | .val (.number n) s2 =>
        match rv with
        | .array elems =>
          let i := n.toUInt32.toNat
          if i < elems.length then .val (elems[i]!) s2
          else .val .undefined s2
        | _ => .error "projectIdx number on non-array"
      | .val _ _ => .error "projectIdx with non-string/number index"
      | other => other
    | other => other

  -- Arrays
  | .array elements => evalElems env store fuel' elements []

  | .index arr idx =>
    match eval env store fuel' arr with
    | .val (.array elems) s1 =>
      match eval env s1 fuel' idx with
      | .val (.number n) s2 =>
        let i := n.toUInt32.toNat
        if i < elems.length then .val (elems[i]!) s2
        else .val .undefined s2
      | .val _ _ => .error "array index must be a number"
      | other => other
    | .val _ _ => .error "index on non-array"
    | other => other

  -- Control flow
  | .«if» cond then_ else_ =>
    match eval env store fuel' cond with
    | .val cv s =>
      if isTruthy cv then eval env s fuel' then_
      else eval env s fuel' else_
    | other => other

  | .ternary cond then_ else_ =>
    match eval env store fuel' cond with
    | .val cv s =>
      if isTruthy cv then eval env s fuel' then_
      else eval env s fuel' else_
    | other => other

  | .loop cond body =>
    evalLoop env store fuel' cond body

  | .seq exprs =>
    evalSeq env store fuel' exprs

  | .«return» val =>
    match eval env store fuel' val with
    | .val v s => .return_ v s
    | other => other

  | .«break» => .break_ store
  | .«continue» => .continue_ store

  | .throw val =>
    match eval env store fuel' val with
    | .val v s => .throw_ v s
    | other => other

  | .tryCatch body catchVar handler finalizer =>
    let bodyResult := eval env store fuel' body
    let afterCatch := match bodyResult with
      | .throw_ v s =>
        let catchEnv := match catchVar with
          | some name => env.extend name v
          | none => env
        eval catchEnv s fuel' handler
      | other => other
    match finalizer with
    | some fin =>
      let finStore := match afterCatch.getStore with
        | some s => s
        | none => store
      match eval env finStore fuel' fin with
      | .val _ s => match afterCatch with
        | .val v _ => .val v s
        | .return_ v _ => .return_ v s
        | .break_ _ => .break_ s
        | .continue_ _ => .continue_ s
        | .throw_ v _ => .throw_ v s
        | .error msg => .error msg
      | other => other
    | none => afterCatch

  -- Pattern matching
  | .«match» scrutinee cases =>
    match eval env store fuel' scrutinee with
    | .val sv s => evalMatch env s fuel' sv cases
    | other => other

  -- Construction
  | .construct name args =>
    match evalArgs env store fuel' args [] with
    | .val (.array argVals) s => .val (.constructed name argVals) s
    | other => other

  | .newObj callee args =>
    match eval env store fuel' callee with
    | .val fv s1 =>
      match evalArgs env s1 fuel' args [] with
      | .val (.array argVals) s2 =>
        applyFunc fv argVals s2 fuel'
      | other => other
    | other => other

  -- Async/generators (simplified: pass through)
  | .«await» expr => eval env store fuel' expr
  | .«yield» (some expr) _ => eval env store fuel' expr
  | .«yield» none _ => .val .undefined store

  -- Special
  | .spread expr => eval env store fuel' expr

where
  /-- Evaluate a list of argument expressions -/
  evalArgs (env : Env) (store : Store) (fuel : Nat) (args : List IRExpr)
      (acc : List IRValue) : EvalResult :=
    match args with
    | [] => .val (.array acc.reverse) store
    | a :: rest =>
      match eval env store fuel a with
      | .val v s => evalArgs env s fuel rest (v :: acc)
      | other => other

  /-- Apply a closure or value to arguments -/
  applyFunc (fv : IRValue) (args : List IRValue) (store : Store) (fuel : Nat)
      : EvalResult :=
    match fv with
    | .closure closureEnv name params body =>
      let callEnv := closureEnv.extendMany (params.zip args)
      let callEnv := match name with
        | some n => callEnv.extend n fv
        | none => callEnv
      match eval callEnv store fuel body with
      | .return_ v s => .val v s
      | other => other
    | _ => .error "application of non-function"

  /-- Evaluate record fields -/
  evalFields (env : Env) (store : Store) (fuel : Nat)
      (fields : List (String × IRExpr)) (acc : List (String × IRValue))
      : EvalResult :=
    match fields with
    | [] => .val (.record acc.reverse) store
    | (name, e) :: rest =>
      match eval env store fuel e with
      | .val v s => evalFields env s fuel rest ((name, v) :: acc)
      | other => other

  /-- Evaluate array elements -/
  evalElems (env : Env) (store : Store) (fuel : Nat)
      (elems : List IRExpr) (acc : List IRValue) : EvalResult :=
    match elems with
    | [] => .val (.array acc.reverse) store
    | e :: rest =>
      match eval env store fuel e with
      | .val v s => evalElems env s fuel rest (v :: acc)
      | other => other

  /-- Evaluate a while loop -/
  evalLoop (env : Env) (store : Store) (fuel : Nat) (cond body : IRExpr)
      : EvalResult :=
    match fuel with
    | 0 => .error "out of fuel in loop"
    | fuel' + 1 =>
      match eval env store fuel' cond with
      | .val cv s =>
        if !isTruthy cv then .val .undefined s
        else
          match eval env s fuel' body with
          | .val _ s' => evalLoop env s' fuel' cond body
          | .continue_ s' => evalLoop env s' fuel' cond body
          | .break_ s' => .val .undefined s'
          | other => other
      | other => other

  /-- Evaluate a sequence of expressions -/
  evalSeq (env : Env) (store : Store) (fuel : Nat) (exprs : List IRExpr)
      : EvalResult :=
    match exprs with
    | [] => .val .undefined store
    | [e] => eval env store fuel e
    | e :: rest =>
      match eval env store fuel e with
      | .val _ s => evalSeq env s fuel rest
      | other => other

  /-- Try match cases in order -/
  evalMatch (env : Env) (store : Store) (fuel : Nat) (scrutinee : IRValue)
      (cases : List IRMatchCase) : EvalResult :=
    match cases with
    | [] => .error "no matching case"
    | .mk pat body :: rest =>
      match matchPattern pat scrutinee with
      | some bindings => eval (env.extendMany bindings) store fuel body
      | none => evalMatch env store fuel scrutinee rest

end LeanJS.Semantics
