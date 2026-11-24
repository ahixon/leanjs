import JSProofs.FactsForm

/-!
# Composing specs in Lean (zippy docs/react-proofs.md, "Composition in Lean")

`facts_compose X := T | hC => U by tac …` declares `X`: `T.ofPre` with its callee contract `hC`, `∀ w …, Frame fp s w →
… → WP … (callImpl f this args) w Q`, discharged by `U` (a spec `facts_form` has processed). `U`'s variables are found
by unifying its call with the contract's; those left open are existential. The contract is replaced by an obligation,
`∀ w …, ∃ (U's open variables), U.Pre … w ∧ (U's other premises not closed by the contract's hypotheses)`, and `tac`
proves `U`'s postcondition gives the contract's (default: as is, or `simp_all`/`omega`). So no callee premise is
restated: the obligation is proved where the facts are known (`Pre_frame`, `facts_apart`).

This replaces `tools/react_commit/compose.py` and the generators built on it.
-/

open Lean Meta Elab Command Term

namespace Logic.FactsCompose

/-- The binder names of a `∀` telescope. -/
def binderNames (t : Expr) : Array Name := Id.run do
  let mut t := t
  let mut ns := #[]
  while t.isForall do
    ns := ns.push t.bindingName!
    t := t.bindingBody!
  return ns

/-- Tries `tac` on a goal `t` in the current context: its proof when it closes the goal. -/
def tryTac (t : Expr) (tac : Syntax) : TermElabM (Option Expr) := do
  let mv ← mkFreshExprSyntheticOpaqueMVar t
  let saved ← saveState
  try
    let rem ← Tactic.run mv.mvarId! (Tactic.evalTactic tac)
    if rem.isEmpty then return some (← instantiateMVars mv)
    saved.restore
    return none
  catch _ =>
    saved.restore
    return none

/-- `∃ xs, b` -/
def mkExistsFVars (xs : Array Expr) (b : Expr) : MetaM Expr :=
  xs.foldrM (fun x acc => do mkAppM ``Exists #[← mkLambdaFVars #[x] acc]) b

/-- A contract `x` discharged by spec `U`: with `ob? = none` the obligation's type; with `some ob` (a local of that
type) the contract's proof. -/
def armWork (x : Expr) (U : Name) (post : Syntax) (ob? : Option Expr) (ctx : Array (Name × Expr))
    (cstr : Option Syntax) : TermElabM Expr := do
  let ct ← inferType x
  forallTelescope ct fun bs body => do
    unless body.isAppOf ``Logic.WP do throwError "facts_compose: {x} is not a contract (∀ …, WP …): {body}"
    let uOf ← mkConstWithFreshMVarLevels (Name.mkStr U "ofPre")
    let uTy ← inferType uOf
    let names := binderNames uTy
    let (ms, _, uc) ← forallMetaTelescope uTy
    unless uc.isAppOf ``Logic.WP do throwError "facts_compose: {U}.ofPre does not conclude WP"
    let ba := body.getAppArgs
    let ua := uc.getAppArgs
    unless ba.size == ua.size do throwError "facts_compose: WP arities differ"
    for i in [:ba.size - 1] do
      unless ← isDefEq ba[i]! ua[i]! do
        throwError "facts_compose: {U}'s call does not match {x}'s at argument {i}:{indentExpr ba[i]!}\nvs{indentExpr ua[i]!}"
    let some ip := names.findIdx? (· == `hpre) | throwError "facts_compose: {U}.ofPre has no `hpre`"
    -- the context's parameters (engine, host, its invariant) are the caller's
    for k in [:ip] do
      if let some (_, c) := ctx.find? (·.1 == names[k]!) then
        if (← instantiateMVars ms[k]!).isMVar then
          unless ← isDefEq ms[k]! c do throwError "facts_compose: {U}'s {names[k]!} is not the caller's"
    -- the variables left open: existential
    let openIdx ← (List.range ip).toArray.filterM fun k => do return (← instantiateMVars ms[k]!).isMVar
    let opens := openIdx.map (ms[·]!)
    let decls ← openIdx.mapM fun k => do
      return (Name.mkSimple ("u_" ++ names[k]!.toString), ← instantiateMVars (← inferType ms[k]!))
    withLocalDeclsDND decls fun exs => do
      for m in opens, e in exs do m.mvarId!.assign e
      let preTy ← instantiateMVars (← inferType ms[ip]!)
      -- the other premises: closed by the contract's hypotheses where `assumption`/`omega` can, the rest obligations
      let auto ← `(tactic| first | assumption | omega)
      let mut closed : Array (Option Expr) := #[]
      -- the arm's constraint first (outermost: `hob.2`), then `U`'s premises left
      let mut rest : Array Expr := #[]
      if let some c := cstr then
        rest := rest.push (← instantiateMVars (← Term.elabTermEnsuringType c (mkSort .zero)))
      for k in [ip + 1:ms.size] do
        let t ← instantiateMVars (← inferType ms[k]!)
        let p? ← if exs.any (t.containsFVar ·.fvarId!) then pure none else tryTac t auto
        closed := closed.push p?
        if p?.isNone then rest := rest.push t
      let conj := rest.foldr (fun t acc => mkAnd acc t) preTy
      match ob? with
      | none => mkForallFVars bs (← mkExistsFVars exs conj)
      | some ob =>
        -- the contract's proof: open the obligation, apply `U.ofPre`, adapt the postcondition
        let hob := mkAppN ob bs
        let rec open_ (j : Nat) (h : Expr) : TermElabM Expr := do
          if j < exs.size then
            let e := exs[j]!
            let pBody ← instantiateMVars (← whnf (← inferType h))
            let lam := pBody.appArg!
            withLocalDeclD `hx (← instantiateMVars (Expr.headBeta (mkApp lam e))) fun hx => do
              let inner ← open_ (j + 1) hx
              let f ← mkLambdaFVars #[e, hx] inner
              mkAppM ``Exists.elim #[h, f]
          else
            -- `h : (Pre ∧ r₁) ∧ r₂ …` (left-nested)
            let hob := h
            let mut cur := h
            let mut rs : Array Expr := #[]
            for _ in rest do
              rs := rs.push (← mkAppM ``And.right #[cur])
              cur ← mkAppM ``And.left #[cur]
            let mut ri := if cstr.isSome then 1 else 0
            let mut args : Array Expr := #[]
            for k in [:ms.size] do
              if k < ip then args := args.push (← instantiateMVars ms[k]!)
              else if k == ip then args := args.push cur
              else
                match closed[k - ip - 1]! with
                | some p => args := args.push p
                | none => args := args.push rs[ri]!; ri := ri + 1
            let hw := mkAppN uOf args
            let qU := (← instantiateMVars (← inferType hw)).appArg!
            let qC := body.appArg!
            let pt ← mkPostGoal qU qC
            -- the post tactic sees the opened obligation as `hob`
            withLetDecl `hob (← inferType hob) hob fun hobv => do
              let some hq ← tryTac pt post
                | throwError "facts_compose: the postcondition of {U} does not give {x}'s:{indentExpr pt}"
              mkLetFVars #[hobv] (← mkAppM ``Logic.wp_mono #[hw, hq])
        mkLambdaFVars bs (← open_ 0 hob)
where
  /-- `∀ b w h', qU b w h' → qC b w h'` -/
  mkPostGoal (qU qC : Expr) : MetaM Expr := do
    let ty ← inferType qU
    forallTelescope ty fun ys _ => do
      mkForallFVars ys (← mkArrow (Expr.headBeta (mkAppN qU ys)) (Expr.headBeta (mkAppN qC ys)))

syntax compArm := " | " ident " => " ident (" with " term)? (" by " tacticSeq)?

/-- `facts_compose X := T | hC => U by tac …`: see the module docstring. -/
syntax (name := factsCompose) "facts_compose " ident " := " ident (compArm)+ : command

@[command_elab factsCompose] def elabFactsCompose : CommandElab := fun stx => do
  let newName := stx[1].getId
  let T ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo stx[3]
  let ns ← getCurrNamespace
  let arms ← stx[4].getArgs.mapM fun a => do
    let c := a[1].getId
    let U ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo a[3]
    let cstr : Option Syntax := if a[4].isNone then none else some a[4][1]
    let tac : Syntax ← if a[5].isNone then
        `(tacticSeq| intro b w' h' hq; first | exact hq | simp_all | omega)
      else pure a[5][1]
    return (c, U, tac, cstr)
  liftTermElabM do
    let tOf := Name.mkStr T "ofPre"
    let ci ← getConstInfo tOf
    forallTelescope ci.type fun xs concl => do
      let mut ctx : Array (Name × Expr) := #[]
      for x in xs do
        let nm ← x.fvarId!.getUserName
        if [`eng, `σ, `answer, `HI].contains nm then ctx := ctx.push (nm, x)
      let mut obls : Array (Name × Expr) := #[]
      let mut which : Array (Option Nat) := #[]
      for x in xs do
        let nm ← x.fvarId!.getUserName
        match arms.findIdx? (·.1 == nm) with
        | some a =>
          let (_, U, tac, cstr) := arms[a]!
          let t ← armWork x U (← `(tactic| ($(⟨tac⟩)))) none ctx cstr
          which := which.push (some obls.size)
          obls := obls.push (Name.mkSimple s!"ob_{nm}", t)
        | none => which := which.push none
      for (c, _, _, _) in arms do
        unless obls.any (·.1 == Name.mkSimple s!"ob_{c}") do throwError "facts_compose: {T}.ofPre has no premise {c}"
      withLocalDeclsDND obls fun obs => do
        let mut args : Array Expr := #[]
        let mut bs : Array Expr := #[]
        for x in xs, w in which do
          match w with
          | some j =>
            let nm ← x.fvarId!.getUserName
            let some a := arms.findIdx? (·.1 == nm) | unreachable!
            let (_, U, tac, cstr) := arms[a]!
            args := args.push (← armWork x U (← `(tactic| ($(⟨tac⟩)))) (some obs[j]!) ctx cstr)
            bs := bs.push obs[j]!
          | none =>
            args := args.push x
            bs := bs.push x
        let val := mkAppN (mkConst tOf (ci.levelParams.map mkLevelParam)) args
        let ty ← instantiateMVars (← mkForallFVars bs concl)
        let val ← instantiateMVars (← mkLambdaFVars bs val)
        if ty.hasMVar || val.hasMVar then throwError "facts_compose: metavariables left in {newName}"
        let X := ns ++ newName
        addDecl (.thmDecl { name := X, levelParams := ci.levelParams, type := ty, value := val })
        -- `X` as a callee: `X.ofPre` (its obligations are among the premises after `hpre`), `T`'s `Pre`, `L`, `Pre_frame`
        let lps := ci.levelParams.map mkLevelParam
        addDecl (.thmDecl { name := Name.mkStr X "ofPre", levelParams := ci.levelParams, type := ty, value := Lean.mkConst X lps })
        for (sfx, isDef) in [("Pre", true), ("L", true), ("Pre_frame", false)] do
          let c ← getConstInfo (Name.mkStr T sfx)
          let v := Lean.mkConst c.name (c.levelParams.map mkLevelParam)
          if isDef then
            addDecl (.defnDecl (mkDefinitionValEx (Name.mkStr X sfx) c.levelParams c.type v .abbrev .safe []))
          else
            addDecl (.thmDecl { name := Name.mkStr X sfx, levelParams := c.levelParams, type := c.type, value := v })
        logInfo m!"{ns ++ newName}: {T} with {arms.size} contracts as obligations"

end Logic.FactsCompose
