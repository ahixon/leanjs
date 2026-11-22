import JSProofs.ArrayRules

/-!
# The `js` tactic's step, by the computation's head symbol (zippy docs/react-proofs.md)

`js_step` (the `macro_rules` in `Auto.lean`, `Calls2.lean`, `Rules3.lean`, `ArrayRules.lean`) tries each rule in turn;
a rule that does not apply still makes Lean unfold both computations to compare them, which costs more as the
states grow. `js_go` looks at the goal instead — the computation in `WP … x s Q` (and the statement-list, `if`, and
argument-list goals) — and applies the one rule for its head symbol.
-/

open Lean Elab Tactic Meta

namespace Logic


/-- The rule for a goal, by the head symbols of its computation (`none`: no rule). -/
def ruleFor (t : Lean.Expr) : MetaM (Option (TSyntax `tactic)) := do
  let t := (← instantiateMVars t).consumeMData
  let fn := t.getAppFn
  let some name := fn.constName? | return none
  if name == ``StmtsWP then
    let args := t.getAppArgs
    let l ← whnfR (args[args.size - 5]!)
    if l.isAppOf ``List.cons then return some (← `(tactic| rw [StmtsWP_cons]))
    if l.isAppOf ``List.nil then return some (← `(tactic| rw [StmtsWP_nil]))
    return none
  unless name == ``WP do return none
  let args := t.getAppArgs
  let x := (args[args.size - 3]!).consumeMData
  let some hx := x.getAppFn.constName? | return none
  let xa := x.getAppArgs
  let sub (i : Nat) : Option Name := (xa[i]?).bind (·.getAppFn.constName?)
  match hx with
  | ``ES.Sem.stmts => return some (← `(tactic| apply wp_stmts (by simp [depth]; omega)))
  | ``ES.Sem.varDecl => return some (← `(tactic| apply wp_varDecl))
  | ``ES.Sem.declVar => return some (← `(tactic| apply wp_declVarC (by simp [depth]; omega)))
  | ``ES.Sem.exprStmt => return some (← `(tactic| apply wp_exprStmt))
  | ``ES.Sem.ret => return some (← `(tactic| apply wp_ret (by simp_all [FDI.fdiCtx, Sem.inner])))
  | ``ES.Sem.ifS => return some (← `(tactic| apply wp_ifS))
  | ``ES.Sem.block => return some (← `(tactic| apply wp_block (by rfl)))
  | ``ES.Sem.tryS => return some (← `(tactic| apply wp_tryS))
  | ``ES.Sem.ident => return some (← `(tactic| apply wp_identC (by simp [depth]; omega)))
  | ``ES.Sem.lit => return some (← `(tactic| apply wp_lit))
  | ``ES.Sem.binary => return some (← `(tactic| apply wp_binary))
  | ``ES.Sem.logical =>
    let op := xa[0]?
    if op.any (·.isConstOf ``ES.LogOp.and) then return some (← `(tactic| apply wp_and))
    if op.any (·.isConstOf ``ES.LogOp.or) then return some (← `(tactic| apply wp_or))
    return none
  | ``ES.Sem.cond => return some (← `(tactic| apply wp_cond))
  | ``ES.Sem.unary => return some (← `(tactic| apply wp_not))
  | ``ES.Sem.object => return some (← `(tactic| apply wp_object))
  | ``ES.Sem.seq => return some (← `(tactic| apply wp_seqExpr))
  | ``ES.Sem.getValue => return some (← `(tactic| apply wp_getMemberC))
  | ``ES.Sem.call => return some (← `(tactic| apply wp_callIdentC (by simp [depth]; omega)))
  | ``ES.Sem.update => return some (← `(tactic| apply wp_postIncIdentC (by simp [depth]; omega)))
  | ``ES.Sem.assign =>
    match sub 0 with
    | some ``ES.Sem.identRef => return some (← `(tactic| apply wp_assignIdentC (by simp [depth]; omega)))
    | some ``ES.Sem.memberRef =>
      let key := (xa[0]!).getAppArgs[1]?
      if key.any (·.isAppOf ``ES.Sem.Key.computed) then return some (← `(tactic| apply wp_assignIdxC))
      return some (← `(tactic| apply wp_assignMemberC))
    | _ => return none
  | ``ES.Sem.assignOp =>
    match sub 1 with
    | some ``ES.Sem.identRef => return some (← `(tactic| apply wp_assignOpIdentC (by simp [depth]; omega) (by decide)))
    | some ``ES.Sem.memberRef => return some (← `(tactic| apply wp_assignOpMemberC (by decide)))
    | _ => return none
  | ``ES.Sem.binaryOp =>
    let op := xa[0]?
    if op.any (·.isConstOf ``ES.BinOp.seq) then return some (← `(tactic| apply wp_seq))
    if op.any (·.isConstOf ``ES.BinOp.sne) then return some (← `(tactic| apply wp_sne))
    return some (← `(tactic| apply wp_numOp (by decide)))
  | ``ite => return some (← `(tactic| apply wp_ite))
  | _ => return none

/-- One step of a frame proof for an explicit final state, by the state's head symbol (`frame_refl` only when the
final state is the start, syntactically). -/
def frameRuleFor (t : Lean.Expr)
    (facts : Syntax.TSepArray [`Lean.Parser.Tactic.simpStar, `Lean.Parser.Tactic.simpErase,
      `Lean.Parser.Tactic.simpLemma] ",") :
    MetaM (Option (TSyntax `tactic)) := do
  let t := (← instantiateMVars t).consumeMData
  unless t.isAppOf ``Logic.Frame do return none
  let args := t.getAppArgs
  let s := args[args.size - 2]!
  let w := (args[args.size - 1]!).consumeMData
  if w == s then return some (← `(tactic| exact frame_refl _ _))
  let some hw := w.getAppFn.constName? | return none
  match hw with
  | ``ES.State.restore => return some (← `(tactic| apply frame_restore))
  | ``Logic.bodyState => return some (← `(tactic| apply frame_bodyState))
  | ``ES.State.allocObj => return some (← `(tactic| apply frame_allocObj))
  | ``ES.State.setEnv => return some (← `(tactic| first
      | (apply frame_setEnv_new (he := by simp))
      | (apply frame_setEnv_decl_in (he := by simp [$facts,*]) (hent := by js_norm [$facts,*]) (hin := by simp))))
  | ``ES.State.setProp => return some (← `(tactic| first
      | (apply frame_setProp_new (ho := by simp))
      | (apply frame_setProp_in (ho := by simp [$facts,*]) (hin := by simp))))
  | _ => return none

/-- Frame steps until the start. -/
elab "frame_go'" "[" facts:Lean.Parser.Tactic.simpArg,* "]" : tactic => do
  let rec loop : Nat → TacticM Unit
    | 0 => throwError "frame_go': too many steps"
    | k + 1 => do
      let gs ← getGoals
      if gs.isEmpty then return
      let some tac ← frameRuleFor (← getMainTarget) ⟨facts.elemsAndSeps⟩ | throwError "frame_go': no rule for this goal"
      evalTactic tac
      loop k
  loop 1000

/-- One step by the goal's head symbol. -/
elab "js_go" : tactic => do
  let some tac ← ruleFor (← getMainTarget) | throwError "js_go: no rule for this goal"
  evalTactic tac

/-- `js` with `js_go` for its steps. -/
macro_rules
  | `(tactic| js [$xs,*]) => `(tactic| repeat' (first | js_go | js_norm [*, $xs,*] | js_split))

end Logic
