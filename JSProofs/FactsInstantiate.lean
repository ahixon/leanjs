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
    let (xs, _, concl) ← forallMetaTelescope (ci.type.instantiateLevelParams ci.levelParams lvls)
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
    -- each conjunct: proved by `tac` (its leftover goals premises), or kept
    let mut proved : Array (Option Expr) := #[]
    let mut extra : Array MVarId := #[]
    let mut nProved : Nat := 0
    for c in cs do
      if proved.size % 200 == 0 then note s!"conjunct {proved.size}"
      let saved ← saveState
      let g ← mkFreshExprSyntheticOpaqueMVar c
      let r ← try
          -- (the binders' unknowns are not the tactic's to assign: a deeper depth)
          let rs ← withNewMCtxDepth (Tactic.run g.mvarId! (evalTactic tac))
          -- leftovers: statements over the binders (unknowns) alone
          let ok ← rs.allM fun r => do return !(← instantiateMVars (← r.getType)).hasFVar
          pure (if ok then some rs else none)
        catch _ => pure none
      match r with
      | some rs =>
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
    let rest ← (xs.extract 0 (xs.size - 2)).filterM fun x => do return !(← x.mvarId!.isAssigned)
    note s!"{rest.size} binders left"
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
    let extraTys ← extra.mapM fun m => do instantiateMVars (← m.getType)
    let keptConj := if keptTys.isEmpty then Lean.mkConst ``True else
      keptTys.extract 0 (keptTys.size - 1) |>.foldr (init := keptTys[keptTys.size - 1]!) mkAnd
    withLocalDeclD `hX tX fun hX => withLocalDeclD `hP keptConj fun hP => do
    let zs ← extraTys.mapIdxM fun i t => do pure (Name.mkSimple s!"hZ{i}", t)
    withLocalDeclsDND zs fun zfs => do
      for (m, z) in extra.zip zfs do m.assign z
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
