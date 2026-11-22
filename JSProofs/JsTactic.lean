import JSProofs.FuncExpr

/-!
# The `js` tactic's step, by the computation's head symbol (zippy docs/react-proofs.md)

`js_step` (the `macro_rules` in `Auto.lean`, `Calls2.lean`, `Rules3.lean`, `ArrayRules.lean`) tries each rule in turn;
a rule that does not apply still makes Lean unfold both computations to compare them, which costs more as the
states grow. `js_go` looks at the goal instead — the computation in `WP … x s Q` (and the statement-list, `if`, and
argument-list goals) — and applies the one rule for its head symbol.
-/

open Lean Elab Tactic Meta

namespace Logic


/-- A rule's side condition (fuel, bounds): arithmetic after the body states' lemmas. Run as its own tactic step so
that a failure makes the rule fail (a `(by …)` argument would be logged and replaced by `sorry`). -/
macro "js_side" : tactic => `(tactic| first | omega | (simp [depth, js_simp] <;> omega) | (simp [depth, js_simp]; done))

/-- The rule for a goal, by the head symbols of its computation (`none`: no rule). -/
def ruleFor (t : Lean.Expr) : MetaM (Option (TSyntax `tactic)) := do
  let t := (← instantiateMVars t).consumeMData
  let fn := t.getAppFn
  let some name := fn.constName? | return none
  if name == ``Logic.ForWP then
    return some (← `(tactic| (refine for_iter ?s1 ?s2 ?_; (case s1 => js_side); (case s2 => js_side))))
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
  | ``ES.Sem.stmts => return some (← `(tactic| (refine wp_stmts ?s1 ?_; (case s1 => js_side))))
  | ``ES.Sem.varDecl => return some (← `(tactic| apply wp_varDecl))
  | ``ES.Sem.declVar => return some (← `(tactic| (refine wp_declVarC ?s1 ?_; (case s1 => js_side))))
  | ``ES.Sem.exprStmt => return some (← `(tactic| apply wp_exprStmt))
  | ``ES.Sem.ret => return some (← `(tactic| (refine wp_ret ?s1 ?_; (case s1 => simp_all [FDI.fdiCtx, ES.Sem.inner]))))
  | ``ES.Sem.ifS => return some (← `(tactic| apply wp_ifS))
  | ``ES.Sem.block => return some (← `(tactic| (refine wp_block ?s1 ?_; (case s1 => rfl))))
  | ``ES.Sem.tryS => return some (← `(tactic| apply wp_tryS))
  | ``ES.Sem.ident => return some (← `(tactic| (refine wp_identC ?s1 ?_; (case s1 => js_side))))
  | ``ES.Sem.lit => return some (← `(tactic| apply wp_lit))
  | ``ES.Sem.binary => return some (← `(tactic| apply wp_binary))
  | ``ES.Sem.logical =>
    let op := xa[0]?
    if op.any (·.isConstOf ``ES.LogOp.and) then return some (← `(tactic| apply wp_and))
    if op.any (·.isConstOf ``ES.LogOp.or) then return some (← `(tactic| apply wp_or))
    return none
  | ``ES.Sem.cond => return some (← `(tactic| apply wp_cond))
  | ``ES.Sem.forS => return some (← `(tactic| apply wp_forVar))
  | ``ES.Sem.unary => return some (← `(tactic| apply wp_not))
  | ``ES.Sem.object => return some (← `(tactic| apply wp_object))
  | ``ES.Sem.func => return some (← `(tactic| (refine wp_funcExpr ⟨rfl, rfl, rfl, rfl, rfl⟩ ?s1 ?_; (case s1 => (simp only [js_simp]; assumption)))))
  | ``ES.Sem.seq => return some (← `(tactic| apply wp_seqExpr))
  | ``ES.Sem.getValue => return some (← `(tactic| apply wp_getMemberC))
  | ``ES.Sem.call => return some (← `(tactic| (refine wp_callIdentC ?s1 ?_; (case s1 => js_side))))
  | ``ES.Sem.update => return some (← `(tactic| (refine wp_postIncIdentC ?s1 ?_; (case s1 => js_side))))
  | ``ES.Sem.assign =>
    match sub 0 with
    | some ``ES.Sem.identRef => return some (← `(tactic| (refine wp_assignIdentC ?s1 ?_; (case s1 => js_side))))
    | some ``ES.Sem.memberRef =>
      let key := (xa[0]!).getAppArgs[1]?
      if key.any (·.isAppOf ``ES.Sem.Key.computed) then return some (← `(tactic| apply wp_assignIdxC))
      return some (← `(tactic| apply wp_assignMemberC))
    | _ => return none
  | ``ES.Sem.assignOp =>
    match sub 1 with
    | some ``ES.Sem.identRef => return some (← `(tactic| (refine wp_assignOpIdentC ?s1 ?s2 ?_; (case s1 => js_side); (case s2 => decide))))
    | some ``ES.Sem.memberRef => return some (← `(tactic| (refine wp_assignOpMemberC ?s1 ?_; (case s1 => decide))))
    | _ => return none
  | ``ES.Sem.binaryOp =>
    let op := xa[0]?
    if op.any (·.isConstOf ``ES.BinOp.seq) then return some (← `(tactic| apply wp_seq))
    if op.any (·.isConstOf ``ES.BinOp.sne) then return some (← `(tactic| apply wp_sne))
    if op.any (·.isConstOf ``ES.BinOp.lt) then return some (← `(tactic| apply wp_ltNum))
    return some (← `(tactic| (refine wp_numOp ?s1 ?_; (case s1 => decide))))
  | ``ite => return some (← `(tactic| apply wp_ite))
  | ``Pure.pure => return some (← `(tactic| apply wp_pure))
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
  if w.isFVar then
    -- (a callee's final state: extend through the frame hypothesis about it)
    for decl in ← getLCtx do
      let ty ← instantiateMVars decl.type
      if ty.isAppOf ``Logic.Frame && (ty.getAppArgs[ty.getAppNumArgs - 1]!) == w then
        let h := mkIdent decl.userName
        return some (← `(tactic| (refine frame_extend ?_ $h ?s1 ?s2 ?s3; (case s1 => simp [$facts,*]); (case s2 => simp [$facts,*]); (case s3 => simp))))
    return none
  let some hw := w.getAppFn.constName? | return none
  match hw with
  | ``ES.State.restore => return some (← `(tactic| apply frame_restore))
  | ``Logic.bodyState => return some (← `(tactic| apply frame_bodyState))
  | ``ES.State.allocObj => return some (← `(tactic| apply frame_allocObj))
  | ``ES.State.withFuel => return some (← `(tactic| apply frame_withFuel))
  | ``ES.State.setEnv =>
    let ev := (w.getAppArgs[2]!).consumeMData
    if ev.isAppOf ``ES.Env.withBindings then
      return some (← `(tactic| (refine frame_setEnv_with_in ?_ (he := ?s1) (hent := ?s2) (hd := ?s3) (hin := ?s4) _; (case s1 => simp [$facts,*]); (case s2 => js_norm [$facts,*]); (case s3 => js_norm [$facts,*]); (case s4 => simp))))
    if ev.isAppOf ``ES.Env.decl then
      return some (← `(tactic| (refine frame_setEnv_decl_in ?_ (he := ?s1) (hent := ?s2) (hin := ?s3) _; (case s1 => simp [$facts,*]); (case s2 => js_norm [$facts,*]); (case s3 => simp))))
    return some (← `(tactic| (refine frame_setEnv_new ?_ (he := ?s1) _; (case s1 => simp))))
  | ``ES.State.setProp => return some (← `(tactic| first
      | (refine frame_setProp_new ?_ (ho := ?s1) _ _; (case s1 => simp))
      | (refine frame_setProp_in ?_ (ho := ?s1) (hin := ?s2) _; (case s1 => simp [$facts,*]); (case s2 => simp))))
  | _ => return none

/-- Frame steps until the start. -/
elab "frame_go'" "[" facts:Lean.Parser.Tactic.simpArg,* "]" : tactic => do
  let rec loop : Nat → TacticM Unit
    | 0 => throwError "frame_go': too many steps"
    | k + 1 => do
      let gs ← getGoals
      if gs.isEmpty then return
      withMainContext do
        let some tac ← frameRuleFor (← getMainTarget) ⟨facts.elemsAndSeps⟩ |
          throwError m!"frame_go': no rule for {← getMainTarget}"
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

namespace Logic

@[simp] theorem restore_restore (x a b : ES.State) : (x.restore a).restore b = x.restore b := rfl

/-- A footprint of existing records only avoids a record created later. -/
theorem binds_avoid {fp : Footprint} {s sd : ES.State} (h : fp.binds.all (fun q => decide (q.1 < s.envs.size)) = true)
    (hle : s.envs.size ≤ sd.envs.size) : fp.binds.all (fun q => q.1 != sd.envs.size) = true := by
  rw [List.all_eq_true] at h ⊢
  intro q hq
  have hlt : q.1 < s.envs.size := of_decide_eq_true (h q hq)
  simp only [bne_iff_ne, ne_eq]
  intro heq
  rw [heq] at hlt
  exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hlt hle)

/-- A premise about a state framed from `s` with an empty footprint, from the same premise about `s`. -/
macro "transfer" hF:term "," h:term : tactic => `(tactic| first
  | exact $h
  | exact heap_frame $hF $h
  | exact envs_frame $hF $h
  | (rw [objEntry_frame0 $hF]; exact $h; assumption)
  | (rw [envEntry_frame0 $hF]; exact $h; assumption))

end Logic
