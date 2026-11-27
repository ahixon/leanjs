import JSProofs.FactsDischarge

/-!
# `facts_instantiate`: a theorem of `facts_top`'s instantiated, some of its premises discharged

`facts_instantiate N := T (σ := …) … using tac` elaborates `T` (a `facts_top` theorem: binders, start facts `hX`, pure
premises `hP`, a conclusion) with the given arguments, tries `tac` on each conjunct of `hP` (a host's lemmas, say), and
declares `N`: the same conclusion from `hX`, the conjuncts `tac` did not prove (one premise), and what `tac` left to
prove (one premise each, statements over the binders alone; a conjunct whose leftovers name its own locals is kept
whole). The binders left unknown are `N`'s binders.
-/

open Lean Meta Elab Command Term Tactic

namespace Logic.FactsInstantiate

/-- The conjuncts of a right-nested conjunction. -/
partial def conjuncts (t : Expr) : Array Expr :=
  if t.isAppOfArity ``And 2 then #[t.appFn!.appArg!] ++ conjuncts t.appArg! else #[t]

/-- A right-nested conjunction's proof from its conjuncts' types and proofs (at least one). -/
def mkConj (ts ps : Array Expr) : Expr := Id.run do
  let n := ts.size
  let mut ty := ts[n - 1]!
  let mut pf := ps[n - 1]!
  for i in (List.range (n - 1)).reverse do
    pf := mkApp4 (Lean.mkConst ``And.intro) ts[i]! ty ps[i]! pf
    ty := mkAnd ts[i]! ty
  return pf

/-- The suffixes of a right-nested conjunction's conjuncts: `suf[i]` = `ts[i] ∧ … ∧ ts[n-1]` (shared, built once). -/
def conjSuffixes (ts : Array Expr) : Array Expr := Id.run do
  let n := ts.size
  let mut suf : Array Expr := Array.replicate n (Lean.mkConst ``True)
  suf := suf.set! (n - 1) ts[n - 1]!
  for i in (List.range (n - 1)).reverse do
    suf := suf.set! i (mkAnd ts[i]! suf[i + 1]!)
  return suf

/-- The conjuncts' proofs from one of the conjunction (`And.left`/`And.right` along it). -/
def projConj (ts : Array Expr) (h : Expr) : Array Expr := Id.run do
  let n := ts.size
  let suf := conjSuffixes ts
  let mut out := #[]
  let mut cur := h
  for i in [:n] do
    if i == n - 1 then
      out := out.push cur
    else
      out := out.push (mkApp3 (Lean.mkConst ``And.left) ts[i]! suf[i + 1]! cur)
      cur := mkApp3 (Lean.mkConst ``And.right) ts[i]! suf[i + 1]! cur
  return out

/-- Progress, with the resident memory (Linux). -/
def note (m : String) : IO Unit := do
  let rss ← (try
      let st ← IO.FS.readFile "/proc/self/status"
      pure ((st.splitOn "\n").find? (·.startsWith "VmRSS:") |>.getD "")
    catch _ => pure "")
  -- (a file: a command's own output is held until it ends)
  let h ← IO.FS.Handle.mk "facts_instantiate.progress" .append
  h.putStrLn s!"[{(rss.drop 6).trim}] {m}"; h.flush

syntax factsArg := "(" ident " := " term ")"
syntax (name := factsInstantiate) "facts_instantiate " ident " := " ident factsArg* " using " tacticSeq : command

@[command_elab factsInstantiate] def elabFactsInstantiate : CommandElab := fun stx => do
  note "facts_instantiate: start"
  let n := stx[1].getId
  let tn := stx[3].getId
  let args := stx[4].getArgs
  let tac := stx[6]
  let ns ← getCurrNamespace
  liftTermElabM do
    let some tn ← (try some <$> realizeGlobalConstNoOverloadWithInfo (mkIdent tn) catch _ => pure none)
      | throwError "facts_instantiate: unknown theorem {tn}"
    note "resolved"
    let ci ← getConstInfo tn
    let lvls := ci.levelParams.map mkLevelParam
    -- every binder an unknown, at once (an application elaborated binder by binder instantiates the huge type at
    -- each); the named ones given; the last two the start facts and the pure premises
    note "telescope"
    -- (the binders up to `hP`: the conclusion's own premises stay in the conclusion)
    let ty := ci.type.instantiateLevelParams ci.levelParams lvls
    let rec countTo (t : Expr) (i : Nat) : Option Nat :=
      match t with
      | .forallE n _ b _ => if n == `hP then some (i + 1) else countTo b (i + 1)
      | _ => none
    let some nb := countTo ty 0 | throwError "facts_instantiate: {tn} has no premise hP"
    let (xs, _, concl) ← forallMetaTelescopeReducing ty (some nb)
    note s!"opened {xs.size}"
    unless xs.size ≥ 2 do throwError "facts_instantiate: no premises"
    for a in args do
      let nm := a[1].getId
      let some i ← xs.findIdxM? (fun x => do return (← x.mvarId!.getDecl).userName == nm)
        | throwError "facts_instantiate: {tn} has no binder {nm}"
      let v ← elabTerm a[3] (← inferType xs[i]!)
      synthesizeSyntheticMVarsNoPostponing
      unless ← isDefEq xs[i]! v do throwError "facts_instantiate: {nm} := {a[3]} does not fit"
    let tX ← instantiateMVars (← inferType xs[xs.size - 2]!)
    let tP ← instantiateMVars (← inferType xs[xs.size - 1]!)
    let concl ← instantiateMVars concl
    if (concl.find? (fun x => x == xs[xs.size - 1]! || x == xs[xs.size - 2]!)).isSome then
      throwError "facts_instantiate: the conclusion names the premises"
    let e := mkAppN (Lean.mkConst tn lvls) (xs.extract 0 (xs.size - 2))
    note "premises"
    let cs := conjuncts tP
    note s!"{cs.size} conjuncts"
    -- the binders given (assigned before any tactic runs)
    let preA ← (xs.extract 0 (xs.size - 2)).filterM fun x => x.mvarId!.isAssigned
    let preSet : Std.HashSet MVarId := preA.foldl (fun acc x => acc.insert x.mvarId!) {}
    -- each conjunct: proved by `tac` (its leftover goals premises), or kept
    let mut proved : Array (Option Expr) := #[]
    let mut extra : Array MVarId := #[]
    let mut nProved : Nat := 0
    for c in cs do
      if proved.size % 200 == 0 then note s!"conjunct {proved.size}"
      let saved ← saveState
      if (c.find? fun x => x.isConstOf ``Logic.Fact.closed).isSome then
        let str := (toString (← ppExpr c)).replace "\n" " "
        note s!"TRY {proved.size}: {(str.drop (str.length - 250)).toString}"
      -- (a timeout, a runtime exception, is caught too: the conjunct kept)
      let r ← tryCatchRuntimeEx (do try
          let isC := (c.find? fun x => x.isConstOf ``Logic.Fact.closed).isSome
          let cUnk ← Logic.FactsDischarge.unknownsOf #[c]
          if isC then note "  unknowns"
          let _ := preSet
          let g ← mkFreshExprSyntheticOpaqueMVar c
          -- (no error recovery: a failed step fails the attempt, not leaves its goal)
          -- (a budget per attempt: a runaway attempt fails, logged, instead of taking the machine's memory)
          let hb0 ← IO.getNumHeartbeats
          let rs ← withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := 400000000 * 1000, initHeartbeats := hb0 }) do
            Term.withoutErrToSorry (Tactic.run g.mvarId! (Tactic.withoutRecover (evalTactic tac)))
          -- (the tactic may specialize the theorem's unknowns, a host lemma fixing a value, but only to terms over the
          -- unknowns: not to a local of its proof)
          -- (an elaboration error is logged, not thrown, and aborts the tactic: its goal comes back unsolved, unassigned;
          -- a failure. The message is not printed: its terms can be huge, and it prints with the options it was logged with.)
          unless ← g.mvarId!.isAssigned do throwError "facts_instantiate: the tactic made no progress"
          if (← getThe Core.State).messages.hasErrors then throwError "facts_instantiate: the tactic logged an error"
          if isC then note "  tactic done"
          let badBinder ← (cUnk.map mkMVar).anyM fun x => do
            unless ← x.mvarId!.isAssigned do return false
            return (← instantiateMVars x).hasFVar
          -- (nor the conjunct itself left over a local: an unknown in it given one)
          let badBinder := badBinder || (← instantiateMVars c).hasFVar
          if isC && badBinder then note "  bad binder"
          if badBinder then throwError "facts_instantiate: the tactic assigned an unknown a local"
          -- leftovers: statements over the binders (unknowns) alone
          if isC then note "  checked binders"
          let ok ← rs.allM fun r => do return !(← instantiateMVars (← r.getType)).hasFVar
          if isC then note s!"  leftovers ok={ok}"
          if isC && !ok then
            for r in rs do
              let t ← instantiateMVars (← r.getType)
              if t.hasFVar then
                let str ← withOptions (fun o => (o.set `pp.maxSteps (400 : Nat)).setBool `pp.deepTerms false) do
                  pure ((toString (← r.withContext (ppExpr t))).replace "\n" " ")
                note s!"    on locals: {← r.getTag}: {str.take 300}"
          pure (if ok then some (g, rs) else none)
        catch ex => do
          if (c.find? fun x => x.isConstOf ``Logic.Fact.closed).isSome then
            -- (printed with a capped printer: a message's terms can be huge)
            let str ← withOptions (fun o => (o.set `pp.maxSteps (400 : Nat)).setBool `pp.deepTerms false) do
              pure ((toString (← ex.toMessageData.format)).replace "\n" " ")
            note s!"  error: {str.take 6000}"
          pure none) (fun ex => do
            if (c.find? fun x => x.isConstOf ``Logic.Fact.closed).isSome then note "  runtime exception (timeout?)"
            let _ := ex
            pure none)
      match r with
      | some (g, rs) =>
        -- leftovers an earlier proof left already (the same page fact, the same statement): merged
        for m in rs do
          unless ← isProp (← m.getType) do continue
          let t ← instantiateMVars (← m.getType)
          for e in extra do
            if ← e.isAssigned then continue
            if t == (← instantiateMVars (← e.getType)) then
              m.assign (mkMVar e)
              break
        let rs := (← rs.filterM fun m => do return !(← m.isAssigned))
        if nProved < 3 then
          for m in rs do
            let str := (toString (← ppExpr (← instantiateMVars (← m.getType)))).replace "\n" " "
            note s!"LEFT {(← m.getDecl).userName}: {str.take 300}"
        proved := proved.push (some g)
        extra := extra ++ rs.toArray
        nProved := nProved + 1
      | none =>
        saved.restore
        proved := proved.push none
    let keptTys := (cs.zip proved).filterMap fun (c, p) => if p.isNone then some c else none
    logInfo m!"facts_instantiate: {nProved} of {cs.size} pure premises proved, {extra.size} left to prove, {keptTys.size} kept"
    -- the theorem over the binders left (each unassigned unknown a local, in binder order, the unknown assigned it:
    -- `abstractMVars` walks a shared term as a tree), `hX`, the kept conjuncts, the leftovers
    let rest0 ← (xs.extract 0 (xs.size - 2)).filterM fun x => do return !(← x.mvarId!.isAssigned)
    -- the leftovers that are data (a lemma's argument the goal does not fix): binders, before the propositions
    let extraL ← extra.filterM fun m => do return !(← m.isAssigned)
    let extraData ← extraL.filterM fun m => do return !(← isProp (← m.getType))
    let extraP ← extraL.filterM fun m => do isProp (← m.getType)
    -- unknowns of no binder (a hole in a given argument, a lemma's): binders, first
    let restIds := rest0.map (·.mvarId!)
    let others ← (← Logic.FactsDischarge.unknownsOf (#[tX, tP, concl] ++ (← (extraP ++ extraData).mapM (·.getType)))).filterM
      fun m => do return !restIds.contains m && !extraP.contains m && !extraData.contains m && !(← m.isAssigned)
    let rest1 := others.map mkMVar ++ rest0 ++ extraData.map mkMVar
    -- (in dependency order: a binder after the unknowns its type names, as a renaming by the tactic may move them)
    let mut rest : Array Expr := #[]
    let mut left := rest1
    while !left.isEmpty do
      let leftIds := left.map (·.mvarId!)
      let mut next : Array Expr := #[]
      let mut keep : Array Expr := #[]
      for x in left do
        let us ← Logic.FactsDischarge.unknownsOf #[← instantiateMVars (← x.mvarId!.getType)]
        if us.any (fun u => u != x.mvarId! && leftIds.contains u) then keep := keep.push x else next := next.push x
      if next.isEmpty then throwError "facts_instantiate: the binders' types depend on each other in a cycle"
      rest := rest ++ next
      left := keep
    note s!"{rest.size} binders left ({others.size} unknowns of no binder, {extraData.size} data leftovers)"
    let rec withVars (i : Nat) (fvs : Array Expr) (k : Array Expr → TermElabM Unit) : TermElabM Unit := do
      if h : i < rest.size then
        let x := rest[i]
        let d ← x.mvarId!.getDecl
        let ty ← instantiateMVars d.type
        withLocalDecl d.userName .default ty fun fv => do
          x.mvarId!.assign fv
          withVars (i + 1) (fvs.push fv) k
      else k fvs
    withVars 0 #[] fun vars => do
    let tX ← instantiateMVars tX
    let concl ← instantiateMVars concl
    let keptTys ← keptTys.mapM instantiateMVars
    let extraTys ← extraP.mapM fun m => do instantiateMVars (← m.getType)
    let keptConj := if keptTys.isEmpty then Lean.mkConst ``True else
      keptTys.extract 0 (keptTys.size - 1) |>.foldr (init := keptTys[keptTys.size - 1]!) mkAnd
    withLocalDeclD `hX tX fun hX => withLocalDeclD `hP keptConj fun hP => do
    let zs ← extraTys.mapIdxM fun i t => do pure (Name.mkSimple s!"hZ{i}", t)
    withLocalDeclsDND zs fun zfs => do
      for (m, z) in extraP.zip zfs do m.assign z
      note "building"
      let keptPfs := if keptTys.isEmpty then #[] else projConj keptTys hP
      let mut pfs : Array Expr := #[]
      let mut k := 0
      for p in proved do
        match p with
        | some g => pfs := pfs.push (← instantiateMVars g)
        | none => pfs := pfs.push keptPfs[k]!; k := k + 1
      let csI ← cs.mapM instantiateMVars
      let val ← instantiateMVars (mkApp2 e hX (mkConj csI pfs))
      let bs := vars ++ #[hX, hP] ++ zfs
      note "abstracting"
      let typ ← mkForallFVars bs concl
      let val ← mkLambdaFVars bs val
      note "adding"
      addDecl (.thmDecl { name := ns ++ n, levelParams := ci.levelParams, type := typ, value := val })
      note "added"
      logInfo m!"facts_instantiate: {ns ++ n} declared ({vars.size} binders)"

end Logic.FactsInstantiate
