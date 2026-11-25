import JSProofs.FactsForm

/-!
# Discharging obligations from facts (zippy docs/react-proofs.md, "Composition in Lean")

`facts_compose` leaves each callee's precondition as an obligation stated after the frames that lead to its call:
`∀ w …, Frame fp s w → … → ∃ p, U.Pre … w ∧ …`. These are discharged where the facts are: the facts at the start,
and the facts each earlier step's postcondition hands on (`P1`, `PRu`, `PC`, …), carried to the call by
`facts_frame`.

* `facts_prove` proves `Facts.holds L w` from the fact lists at `w` in the context: each fact of `L` is found among
  theirs (by its kind and key, then unified: unknowns in `L`, such as an obligation's witnesses, are assigned by the
  match). A fact with unknowns is matched only when one candidate fits (repeated while that settles more), so a guess
  never picks the wrong object; facts left unmatched are left as goals.
* `facts_obligation X ob as n := by tac` declares `n`, the obligation `ob` of `X` with the binders before it: what
  `X` needs proved.
-/

open Lean Meta Elab Command
open Logic Logic.FactsForm

namespace Logic.FactsDischarge

/-- A fact's kind and key: what candidates must share. -/
def factKey (f : Expr) : MetaM (Name × String) := do
  let f ← whnfR (← instantiateMVars f)
  let c := f.getAppFn.constName?.getD .anonymous
  let args := f.getAppArgs
  let key : String :=
    if c == ``Logic.Fact.prop || c == ``Logic.Fact.propP then (keyLit? args[1]!).getD "?"
    else if c == ``Logic.Fact.bind then (strLit? args[2]!).getD "?"
    else ""
  return (c, key)

/-- The fact lists at `w` in the context: each hypothesis, its list's elements and their keys. -/
def sourcesAt (w : Expr) : MetaM (Array (Expr × Expr × Array (Expr × Name × String))) := do
  let mut out := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← whnfR (← instantiateMVars d.type)
    unless ty.isAppOfArity ``Logic.Facts.holds 2 do continue
    unless ty.appArg! == w do continue
    let L := ty.appFn!.appArg!
    let some elems ← listElems L 4096 | continue
    let keyed ← elems.mapM fun e => do
      let (c, k) ← factKey e
      return (e, c, k)
    out := out.push (d.toExpr, L, keyed)
  return out

/-- Proves goal `g : Facts.holds L w` from the fact lists at `w` in its context: the goals left (facts not found)
and their kinds and keys. -/
def proveFacts (g : MVarId) : TermElabM (List MVarId × Array String × Nat) := g.withContext do
  let t ← whnfR (← instantiateMVars (← g.getType))
  unless t.isAppOfArity ``Logic.Facts.holds 2 do throwError "facts_prove: not `Facts.holds L w`: {t}"
  let L := t.appFn!.appArg!
  let w := t.appArg!
  let some goals ← listElems L 4096 | throwError "facts_prove: the facts are not a list"
  let srcs ← sourcesAt w
  let cands ← goals.mapM fun f => do
    let (c, k) ← factKey f
    let mut out : Array (Expr × Expr × Nat × Expr) := #[]
    for (h, Ls, keyed) in srcs do
      for i in [:keyed.size] do
        let (e, c', k') := keyed[i]!
        if c' == c && (k == k' || k == "?" || k' == "?") then out := out.push (h, Ls, i, e)
    return out
  let mut proofs : Array (Option Expr) := goals.map fun _ => none
  let mut progress := true
  while progress do
    progress := false
    for j in [:goals.size] do
      if proofs[j]!.isSome then continue
      let f ← instantiateMVars goals[j]!
      let ground := !f.hasExprMVar
      let mut fits : Array (Expr × Expr × Nat × Expr) := #[]
      for cnd in cands[j]! do
        let (_, _, _, e) := cnd
        let saved ← saveState
        let ok ← try withReducible (isDefEq e f) catch _ => pure false
        saved.restore
        if ok then
          fits := fits.push cnd
          if ground then break
      if fits.size == 1 || (ground && fits.size ≥ 1) then
        let (h, Ls, i, e) := fits[0]!
        let _ ← withReducible (isDefEq e f)
        let hm ← mkDecideProof (← mkAppM ``LT.lt #[mkNatLit i, ← mkAppM ``List.length #[Ls]])
        let gi ← mkAppOptM ``Logic.Facts.get #[Ls, w, h, mkNatLit i, hm]
        proofs := proofs.set! j (some gi)
        progress := true
  let mut left : Array MVarId := #[]
  let mut miss : Array String := #[]
  let mut hl ← mkAppOptM ``Logic.Facts.holds_nil #[w]
  let mut tl := mkApp (mkConst ``List.nil [Level.zero]) (mkConst ``Logic.Fact)
  for k in (List.range goals.size).reverse do
    let f ← instantiateMVars goals[k]!
    let fh := mkApp2 (mkConst ``Logic.Fact.holds) f w
    let p ← match proofs[k]! with
      | some p => mkExpectedTypeHint p fh
      | none => do
        let mv ← mkFreshExprSyntheticOpaqueMVar fh `fact
        left := left.push mv.mvarId!
        let (c, key) ← factKey f
        miss := miss.push s!"{c.componentsRev.head!}:{key}"
        pure mv
    hl ← mkAppOptM ``Logic.Facts.holds_cons #[f, tl, w, p, hl]
    tl := mkApp3 (mkConst ``List.cons [Level.zero]) (mkConst ``Logic.Fact) f tl
  g.assign (← mkExpectedTypeHint hl t)
  return (left.reverse.toList, miss, goals.size)

/-- `facts_prove`: see the module docstring. -/
elab "facts_prove" : tactic => Tactic.withMainContext do
  let (left, miss, n) ← proveFacts (← Tactic.getMainGoal)
  Tactic.replaceMainGoal left
  logInfo m!"facts_prove: {n - left.length} of {n} facts found; not found: {miss}"

/-- `Prod.fst (a, b)` → `a`, `Prod.snd (a, b)` → `b`, throughout (one pass). -/
def reduceProjs1 (e : Expr) : Expr :=
  e.replace fun t =>
    if (t.isAppOfArity ``Prod.fst 3 || t.isAppOfArity ``Prod.snd 3) then
      let p := t.appArg!
      if p.isAppOfArity ``Prod.mk 4 then
        some (if t.isAppOfArity ``Prod.fst 3 then p.appFn!.appArg! else p.appArg!)
      else none
    else none

/-- `reduceProjs1` until nothing is left to reduce (a tuple of `n` reduces in at most `n` passes). -/
def reduceProjs (e : Expr) (fuel : Nat := 4096) : Expr := Id.run do
  let mut e := e
  for _ in [:fuel] do
    let e' := reduceProjs1 e
    if e' == e then return e
    e := e'
  return e

/-- A tuple of fresh unknowns for type `T` (nested `Prod` to the right). -/
partial def tupleMVars (T : Expr) : MetaM (Expr × Array Expr) := do
  let T ← whnfR T
  if T.isAppOfArity ``Prod 2 then
    let a ← mkFreshExprMVar T.appFn!.appArg!
    let (b, ms) ← tupleMVars T.appArg!
    return (← mkAppM ``Prod.mk #[a, b], #[a] ++ ms)
  let m ← mkFreshExprMVar T
  return (m, #[m])

/-- `facts_exists`: the goal's leading `∃`s opened with fresh unknowns (a tuple's components each one), to be
assigned by the facts that match. -/
elab "facts_exists" : tactic => Tactic.withMainContext do
  let mut g ← Tactic.getMainGoal
  let mut n := 0
  for _ in [:64] do
    let t ← whnfR (← instantiateMVars (← g.getType))
    unless t.isAppOfArity ``Exists 2 do break
    let α := t.appFn!.appArg!
    let P := t.appArg!
    let (wit, _) ← if (← whnfR α).isAppOfArity ``Prod 2 then tupleMVars α else do pure (← mkFreshExprMVar α, #[])
    let body := reduceProjs (P.beta #[wit]).headBeta
    let g' ← mkFreshExprSyntheticOpaqueMVar body
    let lvl ← getLevel α
    g.assign (mkApp4 (mkConst ``Exists.intro [lvl]) α P wit g')
    g := g'.mvarId!
    n := n + 1
  Tactic.replaceMainGoal [g]
  logInfo m!"facts_exists: {n} opened"

/-- One `∃` opened with fresh unknowns (a tuple's components each one): the goal for the body. -/
def openExists (g : MVarId) : MetaM (Option MVarId) := g.withContext do
  let t ← whnfR (← instantiateMVars (← g.getType))
  unless t.isAppOfArity ``Exists 2 do return none
  let α := t.appFn!.appArg!
  let P := t.appArg!
  let (wit, _) ← if (← whnfR α).isAppOfArity ``Prod 2 then tupleMVars α else do pure (← mkFreshExprMVar α, #[])
  let body := reduceProjs (P.beta #[wit]).headBeta
  let g' ← mkFreshExprSyntheticOpaqueMVar body
  g.assign (mkApp4 (mkConst ``Exists.intro [← getLevel α]) α P wit g')
  return some g'.mvarId!

/-- What a collection found. -/
structure Collected where
  matched : Nat := 0
  startFacts : Array String := #[]
  noPath : Array String := #[]
  pures : Array Expr := #[]
  stuck : Array Expr := #[]
  closed : Nat := 0
  steps : Nat := 0

/-- A hypothesis that is a conjunction or an existential, taken apart (its parts as hypotheses). -/
partial def destructure (g : MVarId) (h : FVarId) (fuel : Nat := 64) : MetaM MVarId := do
  if fuel == 0 then return g
  let ty ← g.withContext do whnfR (← instantiateMVars (← h.getType))
  unless ty.isAppOfArity ``And 2 || ty.isAppOfArity ``Exists 2 do return g
  let subs ← g.cases h
  let some sg := subs[0]? | return g
  let mut g := sg.mvarId
  for f in sg.fields do
    if f.isFVar then g ← destructure g f.fvarId! (fuel - 1)
  return g

/-- The frames in the context: `(proof, from, to)`. -/
def framesIn : MetaM (Array (Expr × Expr × Expr)) := do
  let mut out := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← whnfR (← instantiateMVars d.type)
    if ty.isAppOfArity ``Logic.Frame 3 then out := out.push (d.toExpr, ty.appFn!.appArg!, ty.appArg!)
  return out

/-- A frame from `a` to `b` composed from the context's (breadth first): its proof. -/
def framePath (a b : Expr) : MetaM (Option Expr) := do
  if a == b then return none
  let fs ← framesIn
  let mut seen : Array Expr := #[a]
  let mut queue : Array (Expr × Expr) := #[]
  for (p, x, y) in fs do
    if x == a && !seen.contains y then queue := queue.push (y, p); seen := seen.push y
  let mut i := 0
  while i < queue.size do
    let (st, pf) := queue[i]!
    if st == b then return some pf
    for (p, x, y) in fs do
      if x == st && !seen.contains y then
        queue := queue.push (y, ← mkAppM ``Logic.frame_trans #[pf, p]); seen := seen.push y
    i := i + 1
  return none

/-- The fact lists in the context (a spec's `Pre` too: its facts), each with its state. -/
def factLists : MetaM (Array (Expr × Expr)) := do
  let mut out := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    try
      let h ← factsOf d.toExpr
      let ty ← whnfR (← instantiateMVars (← inferType h))
      out := out.push (h, ty.appArg!)
    catch _ => pure ()
  return out

/-- The goal `Facts.holds L w`: every fact list in the context carried to `w` (as hypotheses), then matched. -/
def collectFacts (g : MVarId) (top : Array FVarId) (s0 : Expr) (st : IO.Ref Collected) : TermElabM Unit := do
  let g ← g.withContext do
    let t ← whnfR (← instantiateMVars (← g.getType))
    let w := t.appArg!
    let mut g := g
    for (h, a) in ← factLists do
      if a == w then continue
      let some pf ← framePath a w | continue
      -- a frame through a footprint that is a variable (`fpWL`) cannot be reflected: that source is skipped
      let saved ← saveState
      try
        let (L', prf, _, _) ← carry h pf
        let (_, g') ← (← g.assert `carried (mkApp2 (mkConst ``Logic.Facts.holds) L' w) prf).intro1P
        g := g'
      catch _ => saved.restore
    return g
  let (left, miss, n) ← proveFacts g
  let path ← g.withContext do
    let t ← whnfR (← instantiateMVars (← g.getType))
    pure (← framePath s0 t.appArg!).isSome
  let _ := top
  let found := n - left.length
  st.modify fun c =>
    let sf := if path then c.startFacts ++ miss else c.startFacts
    let np := if path then c.noPath else c.noPath ++ miss
    { c with matched := c.matched + found, startFacts := sf, noPath := np }

/-- Walks an obligation: introduces (taking apart conjunctions and existentials), opens `∃`s with unknowns, splits
`∧`s, matches fact lists; the rest is closed by an assumption or counted (a premise the top can state, or stuck). -/
partial def collectGoal (g : MVarId) (top : Array FVarId) (s0 : Expr) (st : IO.Ref Collected) (fuel : Nat := 100000) :
    TermElabM Unit := do
  if fuel == 0 then return
  let t0 ← g.withContext do instantiateMVars (← g.getType)
  -- a distinctness (`a ≠ b`, `¬ P`) is one premise, not an implication to introduce
  let t ← if t0.isAppOfArity ``Ne 3 || t0.isAppOfArity ``Not 1 then pure t0 else g.withContext (whnfR t0)
  -- progress on stderr
  st.modify fun c => { c with steps := c.steps + 1 }
  let c ← st.get
  if c.steps % 25 == 0 then
    IO.eprintln s!"collect: {c.steps} steps, {c.matched} found, {c.startFacts.size} start facts, {c.pures.size} pures, {c.stuck.size} stuck, head {t.getAppFn.constName?.getD `fvar}"
    (← IO.getStderr).flush
  if t.isForall then
    let (h, g') ← g.intro1P
    let g'' ← destructure g' h
    return ← collectGoal g'' top s0 st (fuel - 1)
  if t.isAppOfArity ``Exists 2 then
    if let some g' ← openExists g then return ← collectGoal g' top s0 st (fuel - 1)
  if t.isAppOfArity ``And 2 then
    let (a, b) ← g.withContext do
      let a ← mkFreshExprSyntheticOpaqueMVar t.appFn!.appArg!
      let b ← mkFreshExprSyntheticOpaqueMVar t.appArg!
      g.assign (mkApp4 (mkConst ``And.intro) t.appFn!.appArg! t.appArg! a b)
      pure (a, b)
    collectGoal a.mvarId! top s0 st (fuel - 1)
    collectGoal b.mvarId! top s0 st (fuel - 1)
    return
  if t.isAppOfArity ``Logic.Facts.holds 2 then
    return ← collectFacts g top s0 st
  -- a definition (a spec's `Pre`) whose unfolding is a conjunction, an `∃`, a `∀` or facts: unfolded
  if let some c := t.getAppFn.constName? then
    unless c == ``Logic.Frame do
      if let some u ← g.withContext (unfoldDefinition? t) then
        let u ← g.withContext (whnfR u)
        if u.isForall || u.isAppOfArity ``And 2 || u.isAppOfArity ``Exists 2 || u.isAppOfArity ``Logic.Facts.holds 2 then
          return ← collectGoal (← g.replaceTargetDefEq u) top s0 st (fuel - 1)
  -- the rest: an assumption, or counted
  -- an assumption with the same head, matched reducibly (an unrestricted `assumption` unfolds definitions)
  let ok ← g.withContext do
    let goal ← instantiateMVars (← g.getType)
    let hd := goal.getAppFn
    let mut found := false
    for d in ← getLCtx do
      if found || d.isImplementationDetail then continue
      let ty ← instantiateMVars d.type
      unless ty.getAppFn == hd do continue
      let saved ← saveState
      if ← (try withReducible (isDefEq ty goal) catch _ => pure false) then
        g.assign d.toExpr; found := true
      else saved.restore
    pure found
  if ok then st.modify fun c => { c with closed := c.closed + 1 }; return
  let isLocal ← g.withContext do
    let t ← instantiateMVars (← g.getType)
    pure (t.hasAnyFVar fun f => !top.contains f)
  if isLocal then st.modify fun c => { c with stuck := c.stuck.push t }
  else st.modify fun c => { c with pures := c.pures.push t }

/-- `facts_collect s`: walks the goal (an obligation) as `collectGoal` does from start state `s`, and reports. -/
elab "facts_collect " s:term : tactic => Tactic.withMainContext do
  let s0 ← Term.elabTerm s none
  let top := (← getLCtx).getFVarIds
  let st ← IO.mkRef ({} : Collected)
  collectGoal (← Tactic.getMainGoal) top s0 st
  let c ← st.get
  let showSome (es : Array Expr) : MetaM (Array Format) := (es.extract 0 12).mapM fun e => do
    return Format.text (((← ppExpr e).pretty.take 160).toString)
  logInfo m!"facts_collect: {c.matched} facts found, {c.closed} closed by assumption; {c.startFacts.size} start facts to state ({c.startFacts.extract 0 40}); {c.noPath.size} facts with no frame from the start ({c.noPath.extract 0 40}); {c.pures.size} pure premises; {c.stuck.size} stuck"
  let mut heads : Array (Name × Nat) := #[]
  for e in c.stuck do
    let hn := e.getAppFn.constName?.getD (if e.isForall then `forall else `other)
    match heads.findIdx? (·.1 == hn) with
    | some i => heads := heads.modify i fun (n, k) => (n, k + 1)
    | none => heads := heads.push (hn, 1)
  logInfo m!"stuck by head: {heads}"
  let eqs := (c.stuck.filter (·.isAppOfArity ``Eq 3)).extract 0 6
  for e in eqs do
    logInfo m!"stuck eq: {((← ppExpr e).pretty.take 300).toString}"
  let mut pheads : Array (Name × Nat) := #[]
  for e in c.pures do
    let hn := e.getAppFn.constName?.getD (if e.isForall then `forall else `other)
    match pheads.findIdx? (·.1 == hn) with
    | some i => pheads := pheads.modify i fun (n, k) => (n, k + 1)
    | none => pheads := pheads.push (hn, 1)
  logInfo m!"pures by head: {pheads}"
  Tactic.replaceMainGoal []

/-- `facts_obligation X ob as n := by tac`: see the module docstring. -/
syntax (name := factsObligation) "facts_obligation " ident ident " as " ident " := " term : command

@[command_elab factsObligation] def elabFactsObligation : CommandElab := fun stx => do
  let X ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo stx[1]
  let ob := stx[2].getId
  let n := stx[4].getId
  let ns ← getCurrNamespace
  liftTermElabM do
    let ci ← getConstInfo X
    forallTelescope ci.type fun xs _ => do
      let some k ← xs.findIdxM? (fun x => return (← x.fvarId!.getUserName) == ob)
        | throwError "facts_obligation: {X} has no premise {ob}"
      let before := xs.extract 0 k
      let goal ← inferType xs[k]!
      let pf ← Term.elabTermEnsuringType stx[6] goal
      Term.synthesizeSyntheticMVarsNoPostponing
      let ty ← instantiateMVars (← mkForallFVars before goal)
      let val ← instantiateMVars (← mkLambdaFVars before pf)
      if val.hasMVar then throwError "facts_obligation: the proof has holes"
      addDecl (.thmDecl { name := ns ++ n, levelParams := ci.levelParams, type := ty, value := val })

end Logic.FactsDischarge
