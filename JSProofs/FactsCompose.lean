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

/-- The opened obligation, as post tactics see it (`hob.get`): wrapped so `omega`/`simp_all` leave it alone (it holds
every callee premise; unwrapped, they decompose it, and that does not fit in memory). -/
structure Ob (P : Prop) : Prop where
  get : P

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
    (cstr : Option Syntax) (uinsts : Array (Name × Syntax) := #[]) : TermElabM Expr := do
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
    -- the arm's instantiations of `U`'s variables
    for (nm, stx) in uinsts do
      let some k := names.findIdx? (· == nm) | throwError "facts_compose: {U} has no variable {nm}"
      let e ← Term.elabTermEnsuringType stx (← instantiateMVars (← inferType ms[k]!))
      Term.synthesizeSyntheticMVarsNoPostponing
      unless ← isDefEq ms[k]! e do throwError "facts_compose: {U}'s {nm} cannot be {e}"
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
      -- the arm's constraint first (outermost: `hob.get.2`), then `U`'s premises left
      let mut rest : Array Expr := #[]
      if let some c := cstr then
        rest := rest.push (← instantiateMVars (← Term.elabTermEnsuringType c (mkSort .zero)))
      for k in [ip + 1:ms.size] do
        let t ← instantiateMVars (← inferType ms[k]!)
        -- only fuel bounds (`k ≤ w.fuel`) and the host invariant are closed here; omega on anything else is costly
        let simple := t.isAppOfArity ``LE.le 4 || t.isAppOfArity ``LT.lt 4 || (ctx.any fun (nm, c) => nm == `HI && t.getAppFn == c)
        let p? ← if exs.any (t.containsFVar ·.fvarId!) || !simple then pure none else tryTac t auto
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
            -- the post tactic sees the opened obligation as `hob.get`
            let obTy := mkApp (mkConst ``Ob) (← inferType hob)
            withLetDecl `hob obTy (mkApp2 (mkConst ``Ob.mk) (← inferType hob) hob) fun hobv => do
              let mv ← mkFreshExprSyntheticOpaqueMVar pt
              let rem ← try Term.withoutErrToSorry (Tactic.run mv.mvarId! (Tactic.evalTactic post))
                catch e => throwError "facts_compose: the postcondition of {U} does not give {x}'s:{indentExpr pt}\n{e.toMessageData}"
              unless rem.isEmpty do
                throwError "facts_compose: the postcondition of {U} does not give {x}'s: goals left {rem.map (MessageData.ofGoal ·)}"
              mkLetFVars #[hobv] (← mkAppM ``Logic.wp_mono #[hw, ← instantiateMVars mv])
        mkLambdaFVars bs (← open_ 0 hob)
where
  /-- `∀ b w h', qU b w h' → qC b w h'` -/
  mkPostGoal (qU qC : Expr) : MetaM Expr := do
    let ty ← inferType qU
    forallTelescope ty fun ys _ => do
      mkForallFVars ys (← mkArrow (Expr.headBeta (mkAppN qU ys)) (Expr.headBeta (mkAppN qC ys)))

syntax compInst := " (" ident " := " term ")"
syntax compArm := " | " ident " => " ident (compInst)* (" with " term)? (" by " tacticSeq)?
/-- A premise of `T` proved in place. -/
syntax compProof := " | " ident " := " term

/-- `facts_compose X := T | hC => U by tac …`: see the module docstring. -/
syntax (name := factsCompose) "facts_compose " ident (ppSpace bracketedBinder)* " := " ident (compInst)*
  (atomic(compProof) <|> compArm)+ : command

/-- `T.ofPre`'s binders, those named in `insts` instantiated (elaborated after the binders before them): the
arguments for `T.ofPre`, the binders left, the conclusion. -/
partial def telescopeInst {α} (ty : Expr) (insts : Array (Name × Syntax)) (args locals : Array Expr)
    (k : Array Expr → Array Expr → Expr → TermElabM α) (extras : Array Syntax := #[]) : TermElabM α := do
  let ty ← whnfR ty
  match ty with
  | .forallE n d b bi =>
    -- the composite's own binders, after the context's parameters (they may mention `σ`, `HI`)
    if !extras.isEmpty && ![`eng, `σ, `answer, `HI].contains n then
      return ← Term.elabBinders extras fun ex => telescopeInst ty insts args (locals ++ ex) k
    if let some (_, stx) := insts.find? (·.1 == n) then
      -- `e` may use a new binder of the same name (`(n := n + 2)`): kept when it does
      withLocalDecl n bi d fun x0 => do
        let e ← instantiateMVars (← Term.elabTermEnsuringType stx d)
        Term.synthesizeSyntheticMVarsNoPostponing
        let locals := if e.containsFVar x0.fvarId! then locals.push x0 else locals
        telescopeInst (b.instantiate1 e) insts (args.push e) locals k extras
    else
      withLocalDecl n bi d fun x => telescopeInst (b.instantiate1 x) insts (args.push x) (locals.push x) k extras
  | _ => k args locals ty

@[command_elab factsCompose] def elabFactsCompose : CommandElab := fun stx => do
  let newName := stx[1].getId
  let extraBs := stx[2].getArgs
  let T ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo stx[4]
  let ns ← getCurrNamespace
  let insts := stx[5].getArgs.map fun a => (a[1].getId, a[3])
  let proofs := stx[6].getArgs.filter (·.getKind == ``compProof) |>.map fun a => (a[1].getId, a[3])
  let arms ← (stx[6].getArgs.filter (·.getKind == ``compArm)).mapM fun a => do
    let c := a[1].getId
    let U ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo a[3]
    let ui := a[4].getArgs.map fun i => (i[1].getId, i[3])
    let cstr : Option Syntax := if a[5].isNone then none else some a[5][1]
    let tac : Syntax ← if a[6].isNone then
        `(tacticSeq| intro b w' h' hq; first | exact hq | simp_all | omega)
      else pure a[6][1]
    return (c, U, tac, cstr, ui)
  liftTermElabM do
    let tOf := Name.mkStr T "ofPre"
    let ci ← getConstInfo tOf
    -- the premises proved in place are instantiated like variables
    telescopeInst (extras := extraBs) ci.type (insts ++ proofs) #[] #[] fun args0 xs concl => do
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
          let (_, U, tac, cstr, ui) := arms[a]!
          let t ← armWork x U (← `(tactic| ($(⟨tac⟩)))) none ctx cstr ui
          which := which.push (some obls.size)
          obls := obls.push (Name.mkSimple s!"ob_{nm}", t)
        | none => which := which.push none
      for (c, _, _, _, _) in arms do
        unless obls.any (·.1 == Name.mkSimple s!"ob_{c}") do throwError "facts_compose: {T}.ofPre has no premise {c}"
      withLocalDeclsDND obls fun obs => do
        let mut args := args0
        let mut bs : Array Expr := #[]
        for x in xs, w in which do
          match w with
          | some j =>
            let nm ← x.fvarId!.getUserName
            let some a := arms.findIdx? (·.1 == nm) | unreachable!
            let (_, U, tac, cstr, ui) := arms[a]!
            let d ← armWork x U (← `(tactic| ($(⟨tac⟩)))) (some obs[j]!) ctx cstr ui
            args := args.map fun y => if y == x then d else y
            bs := bs.push obs[j]!
          | none => bs := bs.push x
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
