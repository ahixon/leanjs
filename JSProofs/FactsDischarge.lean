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

/-- Fact goals and pure goals left for the fixed point. -/
initialize pendingFacts : IO.Ref (Array MVarId) ← IO.mkRef #[]
initialize pendingPures : IO.Ref (Array MVarId) ← IO.mkRef #[]


/-- A fact's kind and key: what candidates must share. -/
def factKey (f : Expr) : MetaM (Name × String) := do
  let f ← whnfR (← instantiateMVars f)
  let c := f.getAppFn.constName?.getD .anonymous
  let args := f.getAppArgs
  -- objects and records name the key where nothing else does (unknown ones match anything: `?`)
  let atom (e : Expr) : String := if e.hasExprMVar then "?" else toString e
  let key : String :=
    if c == ``Logic.Fact.prop || c == ``Logic.Fact.propP then (keyLit? args[1]!).getD "?"
    else if c == ``Logic.Fact.bind then (strLit? args[2]!).getD "?"
    else if c == ``Logic.Fact.kindP || c == ``Logic.Fact.objP || c == ``Logic.Fact.proto then atom args[0]!
    else if c == ``Logic.Fact.record || c == ``Logic.Fact.recordIs then atom args[0]!
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

/-- Unmatched facts that had candidates of the same kind and key: (goal fact, a candidate), for diagnosis. -/
initialize nearMisses : IO.Ref (Array (Format × Format)) ← IO.mkRef #[]

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
        if !ground then
          let f' ← instantiateMVars f
          if (toString (← ppExpr f')).contains "false false false" then
            logInfo m!"proveFacts fixed false flags: {← ppExpr f'}\n  from {← ppExpr (← instantiateMVars e)} ({fits.size} fit)"
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
        if let some (_, _, _, e) := cands[k]![0]? then
          if (← nearMisses.get).size < 400 && !f.hasExprMVar then
            let fe ← ppExpr f
            let ee ← ppExpr (← instantiateMVars e)
            nearMisses.modify (·.push (fe, ee))
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
  -- a definition (`PLex`, `PreEx`, `Post`) whose unfolding is a conjunction or an existential: unfolded first
  let (g, ty) ← if ty.isAppOfArity ``And 2 || ty.isAppOfArity ``Exists 2 then pure (g, ty) else g.withContext do
      match ← unfoldDefinition? ty with
      | some u =>
        let u ← whnfR u
        if u.isAppOfArity ``And 2 || u.isAppOfArity ``Exists 2 then
          pure (← g.replaceLocalDeclDefEq h u, u)
        else pure (g, ty)
      | none => pure (g, ty)
  unless ty.isAppOfArity ``And 2 || ty.isAppOfArity ``Exists 2 do return g
  let subs ← g.cases h
  let some sg := subs[0]? | return g
  let mut g := sg.mvarId
  for f in sg.fields do
    if f.isFVar then g ← destructure g f.fvarId! (fuel - 1)
  return g

/-- A fact list's existential facts made exact (opened into the context): a property read under `∃ a b, …` becomes
`Fact.prop o k r`; a binding `∃ bd, b = some bd ∧ Q bd` becomes `Fact.bind e oG x (· = some bd)`, `Q bd` hypotheses.
The new facts are a new hypothesis. -/
partial def normalizeFacts (g : MVarId) (h : Expr) : MetaM MVarId := do
  let some (L, w) ← g.withContext do
      let ty ← whnfR (← instantiateMVars (← inferType h))
      if ty.isAppOfArity ``Logic.Facts.holds 2 then pure (some (ty.appFn!.appArg!, ty.appArg!)) else pure none
    | return g
  let some elems ← g.withContext (listElems L 4096) | return g
  let mut g := g
  let mut newFacts : Array (Expr × Expr) := #[]
  for i in [:elems.size] do
    let f ← whnfR elems[i]!
    let c := f.getAppFn.constName?.getD .anonymous
    unless c == ``Logic.Fact.propP || c == ``Logic.Fact.bind do continue
    let args := f.getAppArgs
    let P := if c == ``Logic.Fact.propP then args[2]! else args[3]!
    let body := if P.isLambda then P.bindingBody! else P
    unless body.isAppOfArity ``Exists 2 do continue
    let (gi, hty) ← g.withContext do
      let hm ← mkDecideProof (← mkAppM ``LT.lt #[mkNatLit i, ← mkAppM ``List.length #[L]])
      let gi ← mkAppOptM ``Logic.Facts.get #[L, w, h, mkNatLit i, hm]
      let hty ← whnf (mkApp2 (mkConst ``Logic.Fact.holds) elems[i]! w)
      pure (← mkExpectedTypeHint gi hty, hty)
    let (fv, g1) ← (← g.assert `nf hty gi).intro1P
    let (pieces, g2) ← openAll g1 fv
    g := g2
    let fact? ← g.withContext do
      let tys ← pieces.mapM fun x => do instantiateMVars (← inferType x)
      let some ilt := tys.findIdx? (·.isAppOfArity ``LT.lt 4) | return none
      if c == ``Logic.Fact.propP then
        let some ieq := tys.findIdx? fun t => t.isAppOfArity ``Eq 3 && t.appFn!.appArg!.isAppOfArity ``ES.PropMap.get? 2 | return none
        let r := tys[ieq]!.appArg!
        let nf := mkApp3 (mkConst ``Logic.Fact.prop) args[0]! args[1]! r
        return some (nf, ← mkAppM ``And.intro #[pieces[ilt]!, pieces[ieq]!])
      else
        let some idl := tys.findIdx? fun t => (declLikeOf? w t).isSome | return none
        let some ieq := tys.findIdx? fun t => t.isAppOfArity ``Eq 3 && t.appFn!.appArg!.isAppOf ``GetElem?.getElem? | return none
        let r := tys[ieq]!.appArg!
        let some (_, bs, _) := declLikeOf? w tys[idl]! | return none
        let pred ← withLocalDeclD `b (← mkAppM ``Option #[mkConst ``ES.Binding]) fun b => do mkLambdaFVars #[b] (← mkEq b r)
        let nf := mkApp4 (mkConst ``Logic.Fact.bind) args[0]! args[1]! args[2]! pred
        let exPred ← withLocalDeclD `bs' (← inferType bs) fun bs' => do
          mkLambdaFVars #[bs'] (mkAnd (← declLikeEq w args[0]! bs' args[1]!) (pred.beta #[← mkAppM ``GetElem?.getElem? #[bs', args[2]!]]))
        return some (nf, ← mkAppM ``And.intro #[pieces[ilt]!, ← mkAppOptM ``Exists.intro #[none, exPred, bs,
          ← mkAppM ``And.intro #[pieces[idl]!, pieces[ieq]!]]])
    if let some p := fact? then newFacts := newFacts.push p
  if newFacts.isEmpty then return g
  g.withContext do
    let mut hl ← mkAppOptM ``Logic.Facts.holds_nil #[w]
    let mut tl := mkApp (mkConst ``List.nil [Level.zero]) (mkConst ``Logic.Fact)
    for (f, pf) in newFacts.reverse do
      let fh ← whnf (mkApp2 (mkConst ``Logic.Fact.holds) f w)
      hl ← mkAppOptM ``Logic.Facts.holds_cons #[f, tl, w, ← mkExpectedTypeHint pf fh, hl]
      tl := mkApp3 (mkConst ``List.cons [Level.zero]) (mkConst ``Logic.Fact) f tl
    let (_, gE) ← (← g.assert `exact (mkApp2 (mkConst ``Logic.Facts.holds) tl w) hl).intro1P
    return gE
where
  /-- A hypothesis taken apart through `∧` and `∃`: its pieces, the goal. -/
  openAll (g : MVarId) (fv : FVarId) : MetaM (Array Expr × MVarId) := do
    let ty ← g.withContext do whnfR (← instantiateMVars (← fv.getType))
    unless ty.isAppOfArity ``And 2 || ty.isAppOfArity ``Exists 2 do return (#[mkFVar fv], g)
    let subs ← g.cases fv
    let some sg := subs[0]? | return (#[], g)
    let mut g := sg.mvarId
    let mut out := #[]
    for f in sg.fields do
      if f.isFVar then
        let (ps, g') ← openAll g f.fvarId!
        out := out ++ ps; g := g'
    return (out, g)

/-- The hypotheses that state single facts (a property read as `some p`, an object's existence or kind, a record's
lookup `bs[x]? = some b` with its record in the context), as a fact list per state (new hypotheses). -/
def rawFacts (g : MVarId) (decls : Array LocalDecl) : MetaM MVarId := g.withContext do
  let mut byState : Array (Expr × Array (Expr × Expr)) := #[]
  let push (acc : Array (Expr × Array (Expr × Expr))) (w f p : Expr) : Array (Expr × Array (Expr × Expr)) :=
    match acc.findIdx? (·.1 == w) with
    | some i => acc.modify i fun (w', l) => (w', l.push (f, p))
    | none => acc.push (w, #[(f, p)])
  -- existence and record hypotheses in the whole context (for kinds and lookups)
  let ctx := (← getLCtx).foldl (init := #[]) fun acc d => if d.isImplementationDetail then acc else acc.push d
  for d in decls do
    let t ← instantiateMVars d.type
    -- a property read `(w.objEntry o).props.get? k = some p`
    if let some (_, lhs, rhs) := t.eq? then
      if lhs.isAppOfArity ``ES.PropMap.get? 2 && rhs.isAppOfArity ``Option.some 2 then
        let pm := lhs.appFn!.appArg!
        if pm.isAppOfArity ``ES.Obj.props 1 && pm.appArg!.isAppOfArity ``ES.State.objEntry 2 then
          let w := pm.appArg!.appFn!.appArg!
          let o := pm.appArg!.appArg!
          let f := mkApp3 (mkConst ``Logic.Fact.prop) o lhs.appArg! rhs
          let pf ← mkAppOptM ``Logic.prop_fact_of #[w, o, lhs.appArg!, rhs.appArg!, d.toExpr]
          byState := push byState w f pf
          continue
      -- a kind `(w.objEntry o).kind = K`, the object's existence in the context
      if lhs.isAppOfArity ``ES.Obj.kind 1 && lhs.appArg!.isAppOfArity ``ES.State.objEntry 2 then
        let w := lhs.appArg!.appFn!.appArg!
        let o := lhs.appArg!.appArg!
        for e in ctx do
          let et ← instantiateMVars e.type
          if let some o' := sizeLtOf? w et ``ES.State.heap then
            if o' == o then
              let P ← withLocalDeclD `K (mkConst ``ES.Kind) fun K => do mkLambdaFVars #[K] (← mkEq K rhs)
              let f := mkApp2 (mkConst ``Logic.Fact.kindP) o P
              let pf ← mkAppOptM ``Logic.kind_fact_of #[w, o, rhs, e.toExpr, d.toExpr]
              byState := push byState w f pf
              break
        continue
      -- a lookup `bs[x]? = some b`, its record in the context
      if lhs.isAppOf ``GetElem?.getElem? && rhs.isAppOfArity ``Option.some 2 && lhs.getAppNumArgs ≥ 2 then
        let bs := lhs.getAppArgs[lhs.getAppNumArgs - 2]!
        let x := lhs.getAppArgs[lhs.getAppNumArgs - 1]!
        for e in ctx do
          let et ← instantiateMVars e.type
          if let some (_, lhs2, rhs2) := et.eq? then
            if lhs2.isAppOfArity ``Scope.declLike? 1 && rhs2.isAppOfArity ``Option.some 2 then
              let pr := rhs2.appArg!
              if pr.isAppOfArity ``Prod.mk 4 && pr.appFn!.appArg! == bs then
                let ee := lhs2.appArg!
                if ee.isAppOfArity ``ES.State.envEntry 2 then
                  let w := ee.appFn!.appArg!
                  let env := ee.appArg!
                  let oG := pr.appArg!
                  let pred ← withLocalDeclD `b (← mkAppM ``Option #[mkConst ``ES.Binding]) fun b => do
                    mkLambdaFVars #[b] (← mkEq b rhs)
                  let f := mkApp4 (mkConst ``Logic.Fact.bind) env oG x pred
                  let pf ← mkAppOptM ``Logic.bind_fact_of #[w, env, bs, oG, x, rhs.appArg!, e.toExpr, d.toExpr]
                  byState := push byState w f pf
                  break
        continue
    -- an existence `o < w.heap.size`
    if t.isAppOfArity ``LT.lt 4 then
      let sz := t.appArg!
      if sz.isAppOfArity ``Array.size 2 && sz.appArg!.isAppOfArity ``ES.State.heap 1 then
        let w := sz.appArg!.appArg!
        let o := t.appFn!.appArg!
        let f := mkApp2 (mkConst ``Logic.Fact.kindP) o (mkLambda `K .default (mkConst ``ES.Kind) (mkConst ``True))
        let pf ← mkAppM ``And.intro #[d.toExpr, mkConst ``True.intro]
        byState := push byState w f pf
  let mut g := g
  for (w, items) in byState do
    let mut hl ← mkAppOptM ``Logic.Facts.holds_nil #[w]
    let mut tl := mkApp (mkConst ``List.nil [Level.zero]) (mkConst ``Logic.Fact)
    for (f, pf) in items.reverse do
      let fh ← whnf (mkApp2 (mkConst ``Logic.Fact.holds) f w)
      hl ← mkAppOptM ``Logic.Facts.holds_cons #[f, tl, w, ← mkExpectedTypeHint pf fh, hl]
      tl := mkApp3 (mkConst ``List.cons [Level.zero]) (mkConst ``Logic.Fact) f tl
    let (_, g') ← (← g.assert `rawf (mkApp2 (mkConst ``Logic.Facts.holds) tl w) hl).intro1P
    g := g'
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
  let (left, _, n) ← proveFacts g
  let _ := top; let _ := s0
  let found := n - left.length
  st.modify fun c => { c with matched := c.matched + found }
  pendingFacts.modify (· ++ left.toArray)

/-- A pure goal that is a fact in disguise, made a fact goal (proved back from it): a lookup `bs[x]? = r` in a record
map a hypothesis gives (a binding fact), a prototype (a prototype fact), a record's existence `e < w.envs.size` (a
record fact). The new goal, or `none`. -/
def toFactGoal (g : MVarId) : MetaM (Option MVarId) := g.withContext do
  let goal ← instantiateMVars (← g.getType)
  let mkGoal (f w : Expr) : MetaM Expr := mkFreshExprSyntheticOpaqueMVar (mkApp2 (mkConst ``Logic.Fact.holds) f w) `fact
  if let some (_, lhs, rhs) := goal.eq? then
    -- a lookup in a record's map
    if lhs.isAppOf ``GetElem?.getElem? && lhs.getAppNumArgs ≥ 2 then
      let bs := lhs.getAppArgs[lhs.getAppNumArgs - 2]!
      let x := lhs.getAppArgs[lhs.getAppNumArgs - 1]!
      for d in ← getLCtx do
        if d.isImplementationDetail then continue
        let t ← instantiateMVars d.type
        if let some (_, l2, r2) := t.eq? then
          if l2.isAppOfArity ``Scope.declLike? 1 && r2.isAppOfArity ``Option.some 2 then
            let pr := r2.appArg!
            if pr.isAppOfArity ``Prod.mk 4 && pr.appFn!.appArg! == bs && l2.appArg!.isAppOfArity ``ES.State.envEntry 2 then
              let w := l2.appArg!.appFn!.appArg!
              let e := l2.appArg!.appArg!
              let oG := pr.appArg!
              let pred ← withLocalDeclD `b (← mkAppM ``Option #[mkConst ``ES.Binding]) fun b => do
                mkLambdaFVars #[b] (← mkEq b rhs)
              let f := mkApp4 (mkConst ``Logic.Fact.bind) e oG x pred
              let F ← mkGoal f w
              let pf ← mkAppOptM ``Logic.Fact.bind_get #[e, oG, x, pred, w, bs, d.toExpr, F]
              g.assign (← mkExpectedTypeHint pf goal)
              return some F.mvarId!
    -- a prototype
    if lhs.isAppOfArity ``ES.Obj.proto 1 && lhs.appArg!.isAppOfArity ``ES.State.objEntry 2 then
      let w := lhs.appArg!.appFn!.appArg!
      let o := lhs.appArg!.appArg!
      let F ← mkGoal (mkApp2 (mkConst ``Logic.Fact.proto) o rhs) w
      g.assign (← mkExpectedTypeHint (mkProj ``And 1 F) goal)
      return some F.mvarId!
  -- a record's existence
  if goal.isAppOfArity ``LT.lt 4 then
    let sz := goal.appArg!
    if sz.isAppOfArity ``Array.size 2 && sz.appArg!.isAppOfArity ``ES.State.envs 1 then
      let w := sz.appArg!.appArg!
      let e := goal.appFn!.appArg!
      let oG ← mkFreshExprMVar (← mkAppM ``Option #[mkConst ``ES.EnvId])
      let F ← mkGoal (mkApp2 (mkConst ``Logic.Fact.record) e oG) w
      g.assign (← mkExpectedTypeHint (mkProj ``And 0 F) goal)
      return some F.mvarId!
  return none

/-- The hypotheses already normalized. -/
initialize normalized : IO.Ref (Array FVarId) ← IO.mkRef #[]

/-- A goal `Fact.holds f w`: matched against the fact lists at `w` in its context (one candidate fits, or `f` has no
unknowns and one does). -/
def matchOne (g : MVarId) : MetaM Bool := g.withContext do
  if ← g.isAssigned then return true
  let t ← instantiateMVars (← g.getType)
  unless t.isAppOfArity ``Logic.Fact.holds 2 do return false
  let f := t.appFn!.appArg!
  let w := t.appArg!
  let (c, k) ← factKey f
  let ground := !f.hasExprMVar
  let mut fits : Array (Expr × Expr × Nat × Expr) := #[]
  for (h, Ls, keyed) in ← sourcesAt w do
    for i in [:keyed.size] do
      let (e, c', k') := keyed[i]!
      unless c' == c && (k == k' || k == "?" || k' == "?") do continue
      let saved ← saveState
      let ok ← try withReducible (isDefEq e f) catch _ => pure false
      saved.restore
      if ok then
        fits := fits.push (h, Ls, i, e)
        if ground then break
    if ground && fits.size ≥ 1 then break
  unless fits.size == 1 || (ground && fits.size ≥ 1) do return false
  let (h, Ls, i, e) := fits[0]!
  let before := f.hasExprMVar
  let _ ← withReducible (isDefEq e f)
  -- diagnosis: a match that fixes flags to `false`
  if before then
    let f' ← instantiateMVars f
    if (toString (← ppExpr f')).contains "false false false" then
      logInfo m!"matched (fixing false flags): {← ppExpr f'}\n  from {← ppExpr (← instantiateMVars e)} ({fits.size} fit)"
  let hm ← mkDecideProof (← mkAppM ``LT.lt #[mkNatLit i, ← mkAppM ``List.length #[Ls]])
  let gi ← mkAppOptM ``Logic.Facts.get #[Ls, w, h, mkNatLit i, hm]
  g.assign (← mkExpectedTypeHint gi t)
  return true

/-- A pure goal closed by a hypothesis with its head, matched reducibly. -/
def assumeOne (g : MVarId) : MetaM Bool := g.withContext do
  if ← g.isAssigned then return true
  let goal ← instantiateMVars (← g.getType)
  let hd := goal.getAppFn
  let ground := !goal.hasExprMVar
  -- a pure goal never assigns unknowns (a hypothesis that fits may be unrelated): it waits until facts have
  unless ground do return false
  let mut fits : Array LocalDecl := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    unless ty.getAppFn == hd do continue
    let saved ← saveState
    let ok ← try withReducible (isDefEq ty goal) catch _ => pure false
    saved.restore
    if ok then
      fits := fits.push d
      if ground || fits.size > 1 then break
  unless fits.size == 1 || (ground && fits.size ≥ 1) do return false
  let _ ← withReducible (isDefEq (← instantiateMVars fits[0]!.type) goal)
  g.assign fits[0]!.toExpr
  return true

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
    let (h, gI) ← g.intro1P
    let gD ← destructure gI h
    -- the fact lists among what was introduced: their existential facts made exact
    let gN ← gD.withContext do
      let mut gc := gD
      let mut fresh : Array LocalDecl := #[]
      for d in ← getLCtx do
        if d.isImplementationDetail then continue
        if d.userName.toString.startsWith "exact" || d.userName.toString.startsWith "nf" || d.userName.toString.startsWith "rawf" then continue
        unless (← normalized.get).contains d.fvarId do
          normalized.modify (·.push d.fvarId)
          fresh := fresh.push d
          try gc ← normalizeFacts gc d.toExpr catch _ => pure ()
      -- single-fact hypotheses as fact lists
      try gc ← rawFacts gc fresh catch _ => pure ()
      pure gc
    return ← collectGoal gN top s0 st (fuel - 1)
  if t.isAppOfArity ``Exists 2 then
    if let some g' ← openExists g then return ← collectGoal g' top s0 st (fuel - 1)
  if t.isAppOfArity ``And 2 then
    let (a, b) ← g.withContext do
      let a ← mkFreshExprSyntheticOpaqueMVar t.appFn!.appArg!
      let b ← mkFreshExprSyntheticOpaqueMVar t.appArg!
      g.assign (mkApp4 (mkConst ``And.intro) t.appFn!.appArg! t.appArg! a b)
      pure (a, b)
    -- the right first: a spec's `Pre` puts its facts last, and they assign what its pure premises read
    collectGoal b.mvarId! top s0 st (fuel - 1)
    collectGoal a.mvarId! top s0 st (fuel - 1)
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
  -- an assumption with the same head, matched reducibly, alone when the goal has unknowns
  let ok ← assumeOne g
  if ok then st.modify fun c => { c with closed := c.closed + 1 }; return
  -- a fact in disguise: a fact goal
  if let some F ← toFactGoal g then pendingFacts.modify (·.push F); return
  pendingPures.modify (·.push g)

/-- A fuel bound (`k ≤ w.fuel`, `s.fuel ≤ w.fuel + k`, …) by `omega` over the fuel hypotheses alone: each `x.fuel` made
a fresh number in a small context (the context's other hypotheses are not scanned), the proof put back. -/
def fuelOne (g : MVarId) : TermElabM Bool := g.withContext do
  if ← g.isAssigned then return true
  let goal ← instantiateMVars (← g.getType)
  if goal.hasExprMVar then return false
  let isArith (t : Expr) : Bool := t.isAppOfArity ``LE.le 4 || t.isAppOfArity ``LT.lt 4
  let hasFuel (t : Expr) : Bool := (t.find? fun e => e.isAppOfArity ``ES.State.fuel 1).isSome
  unless isArith goal && hasFuel goal do return false
  -- the atoms `x.fuel` of the goal and the fuel hypotheses
  let mut cand : Array (Expr × Expr) := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let t ← instantiateMVars d.type
    if isArith t && hasFuel t && !t.hasExprMVar then cand := cand.push (d.toExpr, t)
  let mut atoms : Array Expr := #[]
  for t in #[goal] ++ cand.map (·.2) do
    let es : Array Expr := Id.run <| Expr.foldlM (fun (acc : Array Expr) e => pure (if e.isAppOfArity ``ES.State.fuel 1 then acc.push e else acc)) #[] t
    for e in es do
      if !atoms.contains e then atoms := atoms.push e
  let abstract (t : Expr) (vals : Array Expr) : Expr :=
    t.replace fun e => match atoms.findIdx? (· == e) with
      | some i => some vals[i]!
      | none => none
  -- only what mentions nothing but the atoms
  let pure0 (t : Expr) : Bool := !(abstract t (atoms.map fun _ => mkNatLit 0)).hasFVar
  unless pure0 goal do return false
  let hs := cand.filter fun (_, t) => pure0 t
  let natTy := mkConst ``Nat
  let r ← withLCtx {} #[] do
    withLocalDecls (atoms.mapIdx fun i _ => (Name.mkSimple s!"f{i}", .default, fun _ => pure natTy)) fun fvs => do
      let hTys := hs.map fun (_, t) => abstract t fvs
      withLocalDecls (hTys.mapIdx fun i t => (Name.mkSimple s!"h{i}", .default, fun _ => pure t)) fun hfs => do
        let mv ← mkFreshExprSyntheticOpaqueMVar (abstract goal fvs)
        let saved ← saveState
        try
          let rem ← Tactic.run mv.mvarId! (Tactic.evalTactic (← `(tactic| omega)))
          unless rem.isEmpty do saved.restore; return none
          return some (← instantiateMVars (← mkLambdaFVars (fvs ++ hfs) (← instantiateMVars mv)))
        catch _ => saved.restore; return none
  let some lam := r | return false
  let pf := mkAppN lam (atoms ++ hs.map (·.1))
  g.assign (← mkExpectedTypeHint pf goal)
  return true

/-- A lookup `bs[x]? = r` in a record whose map `bs` a hypothesis gives: from a binding fact at that state. -/
def lookupOne (g : MVarId) : MetaM Bool := g.withContext do
  if ← g.isAssigned then return true
  let goal ← instantiateMVars (← g.getType)
  let some (_, lhs, _) := goal.eq? | return false
  unless lhs.isAppOf ``GetElem?.getElem? && lhs.getAppNumArgs ≥ 2 do return false
  let bs := lhs.getAppArgs[lhs.getAppNumArgs - 2]!
  let x := lhs.getAppArgs[lhs.getAppNumArgs - 1]!
  -- the record's hypothesis: its state
  let mut found : Option (Expr × Expr) := none
  for d in ← getLCtx do
    if found.isSome || d.isImplementationDetail then continue
    let t ← instantiateMVars d.type
    if let some (_, l2, r2) := t.eq? then
      if l2.isAppOfArity ``Scope.declLike? 1 && r2.isAppOfArity ``Option.some 2 then
        let pr := r2.appArg!
        if pr.isAppOfArity ``Prod.mk 4 && pr.appFn!.appArg! == bs && l2.appArg!.isAppOfArity ``ES.State.envEntry 2 then
          found := some (d.toExpr, l2.appArg!.appFn!.appArg!)
  let some (hd, w) := found | return false
  for (h, Ls, keyed) in ← sourcesAt w do
    for i in [:keyed.size] do
      let (e, c, k) := keyed[i]!
      unless c == ``Logic.Fact.bind && (k == (strLit? x).getD "?" || k == "?") do continue
      let saved ← saveState
      try
        let hm ← mkDecideProof (← mkAppM ``LT.lt #[mkNatLit i, ← mkAppM ``List.length #[Ls]])
        let gi ← mkAppOptM ``Logic.Facts.get #[Ls, w, h, mkNatLit i, hm]
        let gi ← mkExpectedTypeHint gi (mkApp2 (mkConst ``Logic.Fact.holds) e w)
        let pf ← mkAppOptM ``Logic.Fact.bind_get #[none, none, none, none, w, bs, hd, gi]
        if ← withReducible (isDefEq (← whnfR (← inferType pf)) goal) then
          g.assign (← mkExpectedTypeHint pf goal); return true
        saved.restore
      catch _ => saved.restore
  return false

/-- A prototype `(w.objEntry o).proto = p` from one stated at a state framed to `w` (frames keep prototypes). -/
def protoOne (g : MVarId) : MetaM Bool := g.withContext do
  if ← g.isAssigned then return true
  let goal ← instantiateMVars (← g.getType)
  let some (_, lhs, _) := goal.eq? | return false
  unless lhs.isAppOfArity ``ES.Obj.proto 1 && lhs.appArg!.isAppOfArity ``ES.State.objEntry 2 do return false
  let w := lhs.appArg!.appFn!.appArg!
  let o := lhs.appArg!.appArg!
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let t ← instantiateMVars d.type
    let some (_, l2, _) := t.eq? | continue
    unless l2.isAppOfArity ``ES.Obj.proto 1 && l2.appArg!.isAppOfArity ``ES.State.objEntry 2 do continue
    unless l2.appArg!.appArg! == o do continue
    let w' := l2.appArg!.appFn!.appArg!
    if w' == w then
      if ← withReducible (isDefEq t goal) then g.assign d.toExpr; return true
      continue
    let some pf ← framePath w' w | continue
    -- the object's existence at `w'`
    for e in ← getLCtx do
      let et ← instantiateMVars e.type
      if let some o' := sizeLtOf? w' et ``ES.State.heap then
        if o' == o then
          let saved ← saveState
          try
            let r ← mkAppOptM ``Logic.proto_frame #[none, w', w, o, none, pf, e.toExpr, d.toExpr]
            if ← withReducible (isDefEq (← inferType r) goal) then g.assign r; return true
            saved.restore
          catch _ => saved.restore
  return false

/-- Pure goals and fact goals retried in turn (the pure ones assign what the facts' objects are) until nothing
changes: the rounds taken. -/
def fixedPoint (st : IO.Ref Collected) (rounds : Nat := 64) : TermElabM Nat := do
  for r in [:rounds] do
    let mut progress := false
    let ps ← pendingPures.get
    let mut ps' := #[]
    for g in ps do
      if (← assumeOne g) || (← fuelOne g) || (← lookupOne g) || (← protoOne g) then
        progress := true; st.modify fun c => { c with closed := c.closed + 1 }
      else ps' := ps'.push g
    pendingPures.set ps'
    let fs ← pendingFacts.get
    let mut fs' := #[]
    for g in fs do
      if ← matchOne g then
        progress := true; st.modify fun c => { c with matched := c.matched + 1 }
      else fs' := fs'.push g
    pendingFacts.set fs'
    unless progress do return r + 1
  return rounds

/-- What is left after the fixed point, classified: facts (a start fact, or none reachable), pure goals (a premise
the top can state, or stuck on a local). -/
def classifyLeft (top : Array FVarId) (s0 : Expr) (st : IO.Ref Collected) : MetaM Unit := do
  let mut shown := 0
  for g in ← pendingFacts.get do
    -- diagnosis: a few facts about known objects with same-key candidates at their state
    if shown < 6 then
      let r ← g.withContext do
        let t ← instantiateMVars (← g.getType)
        let f := t.appFn!.appArg!
        let fw ← whnfR f
        let (c, key) ← factKey f
        unless c == ``Logic.Fact.prop do return none
        if (← instantiateMVars fw.getAppArgs[0]!).hasExprMVar then return none
        let mut cs : Array Format := #[]
        for (_, _, keyed) in ← sourcesAt t.appArg! do
          for (e, c', k') in keyed do
            if c' == c && k' == key && cs.size < 3 then cs := cs.push (← ppExpr (← instantiateMVars e))
        if cs.isEmpty then return none
        return some (← ppExpr f, cs)
      if let some (fe, cs) := r then
        shown := shown + 1
        logInfo m!"left fact: {((toString fe).take 300).toString}\n  candidates: {cs.map fun x => ((toString x).take 300).toString}"
  for g in ← pendingFacts.get do
    g.withContext do
      let t ← instantiateMVars (← g.getType)
      let f := t.appFn!.appArg!
      let (c, key) ← factKey f
      let fw ← whnfR f
      let mut obj := ""
      if c == ``Logic.Fact.prop || c == ``Logic.Fact.propP then
        let o ← instantiateMVars fw.getAppArgs[0]!
        let op ← ppExpr o
        obj := if o.hasExprMVar then "?" else op.pretty
      let item := s!"{c.componentsRev.head!}:{obj}:{key}"
      let path := (← framePath s0 t.appArg!).isSome
      st.modify fun cl => if path then { cl with startFacts := cl.startFacts.push item }
        else { cl with noPath := cl.noPath.push item }
  let mut shownStuck := 0
  for g in ← pendingPures.get do
    let isLocal ← g.withContext do
      let t ← instantiateMVars (← g.getType)
      let isLocal := t.hasAnyFVar fun f => !top.contains f
      st.modify fun c => if isLocal then { c with stuck := c.stuck.push t } else { c with pures := c.pures.push t }
      pure isLocal
    if isLocal && shownStuck < 12 then
      shownStuck := shownStuck + 1
      g.withContext do
        let t ← instantiateMVars (← g.getType)
        let locals := (← getLCtx).foldl (init := #[]) fun acc d =>
          if !top.contains d.fvarId && t.containsFVar d.fvarId then acc.push d.userName else acc
        logInfo m!"stuck: {((toString (← ppExpr t)).take 260).toString}\n  locals: {locals}"

/-- `facts_collect s`: walks the goal (an obligation) as `collectGoal` does from start state `s`, and reports. -/
elab "facts_collect " s:term : tactic => Tactic.withMainContext do
  let s0 ← Term.elabTerm s none
  let top := (← getLCtx).getFVarIds
  let st ← IO.mkRef ({} : Collected)
  pendingFacts.set #[]; pendingPures.set #[]
  collectGoal (← Tactic.getMainGoal) top s0 st
  let rounds ← fixedPoint st
  classifyLeft top s0 st
  let c ← st.get
  logInfo m!"fixed point: {rounds} rounds"
  let showSome (es : Array Expr) : MetaM (Array Format) := (es.extract 0 12).mapM fun e => do
    return Format.text (((← ppExpr e).pretty.take 160).toString)
  logInfo m!"facts_collect: {c.matched} facts found, {c.closed} closed by assumption; {c.startFacts.size} start facts to state ({c.startFacts}); {c.noPath.size} facts with no frame from the start ({c.noPath.extract 0 40}); {c.pures.size} pure premises; {c.stuck.size} stuck"
  let mut heads : Array (Name × Nat) := #[]
  for e in c.stuck do
    let hn := e.getAppFn.constName?.getD (if e.isForall then `forall else `other)
    match heads.findIdx? (·.1 == hn) with
    | some i => heads := heads.modify i fun (n, k) => (n, k + 1)
    | none => heads := heads.push (hn, 1)
  logInfo m!"stuck by head: {heads}"
  let nm ← nearMisses.get
  logInfo m!"near misses: {nm.size}"
  for (a, b) in nm.extract 0 8 do
    logInfo m!"near miss:\n  goal {((toString a).take 400).toString}\n  cand {((toString b).take 400).toString}"
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

/-- A composite's statement opened up to its premise `obn`: its values as unknowns, the context's parameters and the
start state kept as locals; `k` gets the premise's type and the premises before it. -/
partial def openTop (ty : Expr) (obn : Name) (hyps : Array (Name × Expr))
    (k : Expr → Array (Name × Expr) → TermElabM Unit) : TermElabM Unit := do
  let keep : List Name := [`eng, `σ, `answer, `HI, `s, `h]
  match ty with
  | .forallE n d b _ =>
    if ← isProp d then
      if n == obn then k d hyps
      else openTop (b.instantiate1 (← mkFreshExprMVar d)) obn (hyps.push (n, d)) k
    else if keep.contains n then
      withLocalDeclD n d fun x => openTop (b.instantiate1 x) obn hyps k
    else
      openTop (b.instantiate1 (← mkFreshExprMVar d (userName := n))) obn hyps k
  | _ => throwError "facts_collect_top: no premise {obn}"

/-- The premises as hypotheses, then `k`. -/
partial def withHyps (hyps : Array (Name × Expr)) (i : Nat) (k : TermElabM Unit) : TermElabM Unit := do
  if h : i < hyps.size then
    withLocalDeclD hyps[i].1 hyps[i].2 fun _ => withHyps hyps (i + 1) k
  else k

/-- `facts_collect_top X ob`: `X`'s binders opened — its values (objects, records' data, numbers, flags…) as unknowns
that matching assigns, the context's parameters and the start state `s` kept, its premises as hypotheses — and its
obligation `ob` walked as `facts_collect` does; reports. -/
elab "facts_collect_top " X:ident ob:ident : command => do
  let Xn ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo X
  let obn := ob.getId
  liftTermElabM do
    let ci ← getConstInfo Xn
    openTop ci.type obn #[] fun obTy hyps => do
      withHyps hyps 0 do
        let some s ← (← getLCtx).findFromUserName? `s |>.map (·.toExpr) |> pure | throwError "no s"
        let top := (← getLCtx).getFVarIds
        let st ← IO.mkRef ({} : Collected)
        pendingFacts.set #[]; pendingPures.set #[]
        let g ← mkFreshExprSyntheticOpaqueMVar obTy
        collectGoal g.mvarId! top s st
        let rounds ← fixedPoint st
        classifyLeft top s st
        let c ← st.get
        logInfo m!"facts_collect_top: {c.matched} facts found, {c.closed} closed by assumption, fixed point {rounds} rounds; {c.startFacts.size} start facts; {c.noPath.size} unreachable; {c.pures.size} pure premises; {c.stuck.size} stuck"
        let mut props : Array String := #[]
        for x in c.startFacts do if x.startsWith "prop" then props := props.push x
        logInfo m!"start facts (props): {props}"

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
