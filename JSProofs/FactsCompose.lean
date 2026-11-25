import JSProofs.FactsForm
import JSProofs.Hide

/-!
# Composing specs in Lean (zippy docs/react-proofs.md, "Composition in Lean")

`facts_compose X := T | hC => U by tac …` declares `X`: `T.ofPre` with its callee contract `hC`, `∀ w …, Frame fp s w →
… → WP … (callImpl f this args) w Q`, discharged by `U` (a spec `facts_form` has processed). `U`'s variables are found
by unifying its call with the contract's; those left open are existential. The contract is replaced by an obligation,
`∀ w …, ∃ (U's open variables), U.Pre … w ∧ (U's other premises not closed by the contract's hypotheses)`, and `tac`
proves `U`'s postcondition gives the contract's (default: `exact`, as is; `simp_all`/`omega` over a context of
contracts is too costly to try by default). So no callee premise is
restated: the obligation is proved where the facts are known (`Pre_frame`, `facts_apart`).

This replaces `tools/react_commit/compose.py` and the generators built on it.
-/

open Lean Meta Elab Command Term

namespace Logic.FactsCompose

/-- Phase timing on stderr (`set_option diagnostics true`). -/
def tick (what : String) (t0 : Nat) : CoreM Nat := do
  let t ← IO.monoMsNow
  if (← getOptions).getBool `diagnostics false then
    IO.eprintln s!"facts_compose: {what} {t - t0} ms"
    (← IO.getStderr).flush
  return t

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

/-- The open variables as one tuple `τ₀ × (τ₁ × …)` (when no variable's type mentions another): the tuple type,
its universe level, and the variables' projections from a tuple `p`. -/
def tupleOf (exs : Array Expr) : MetaM (Option (Expr × Level × (Expr → Array Expr))) := do
  let tys ← exs.mapM fun x => do instantiateMVars (← inferType x)
  if tys.any (fun t => exs.any (t.containsFVar ·.fvarId!)) then return none
  let lvls ← tys.mapM fun t => do
    let l ← getLevel t
    return (← instantiateLevelMVars l).normalize
  let n := tys.size
  -- the suffix types `τ_k × … × τ_{n-1}` and their levels, from the end
  let mut sufT : Array Expr := Array.replicate n (mkConst ``Unit)
  let mut sufL : Array Level := Array.replicate n levelZero
  sufT := sufT.set! (n - 1) tys[n - 1]!
  sufL := sufL.set! (n - 1) lvls[n - 1]!
  for k' in [:n - 1] do
    let k := n - 2 - k'
    let u := lvls[k]!.dec.getD levelZero
    let v := sufL[k + 1]!.dec.getD levelZero
    sufT := sufT.set! k (mkApp2 (mkConst ``Prod [u, v]) tys[k]! sufT[k + 1]!)
    sufL := sufL.set! k (mkLevelMax' lvls[k]! sufL[k + 1]!)
  let projs (p : Expr) : Array Expr := Id.run do
    let mut out : Array Expr := #[]
    let mut r := p
    for k in [:n - 1] do
      let u := lvls[k]!.dec.getD levelZero
      let v := sufL[k + 1]!.dec.getD levelZero
      out := out.push (mkApp3 (mkConst ``Prod.fst [u, v]) tys[k]! sufT[k + 1]! r)
      r := mkApp3 (mkConst ``Prod.snd [u, v]) tys[k]! sufT[k + 1]! r
    out.push r
  return some (sufT[0]!, sufL[0]!, projs)

/-- A contract `x` discharged by spec `U`: with `ob? = none` the obligation's type; with `some ob` (a local of that
type) the contract's proof. -/
def armWork (x : Expr) (U : Name) (post : Syntax) (ob? : Option Expr) (ctx : Array (Name × Expr))
    (cstr : Option Syntax) (uinsts : Array (Name × Syntax) := #[]) (same : Bool := false)
    (callerVars : Array Expr := #[]) : TermElabM Expr := do
  let ct0 ← inferType x
  -- a contract hidden from simp (`Hide P`): `P`
  let hidden := ct0.isAppOfArity ``Logic.Hide 1
  let ct := if hidden then ct0.appArg! else ct0
  let wrapHide (e : Expr) : Expr := if hidden then mkApp2 (mkConst ``Logic.Hide.mk) ct e else e
  let tA ← tick s!"{U}: arm start" (← IO.monoMsNow)
  forallTelescope ct fun bs body => do
    unless body.isAppOf ``Logic.WP do throwError "facts_compose: {x} is not a contract (∀ …, WP …): {body}"
    let uOf ← mkConstWithFreshMVarLevels (Name.mkStr U "ofPre")
    let uTy ← inferType uOf
    let names := binderNames uTy
    let (ms, _, uc) ← forallMetaTelescope uTy
    let tA ← tick s!"{U}: {ms.size} binders opened" tA
    unless uc.isAppOf ``Logic.WP do throwError "facts_compose: {U}.ofPre does not conclude WP"
    let ba := body.getAppArgs
    let ua := uc.getAppArgs
    unless ba.size == ua.size do throwError "facts_compose: WP arities differ"
    for i in [:ba.size - 1] do
      unless ← isDefEq ba[i]! ua[i]! do
        throwError "facts_compose: {U}'s call does not match {x}'s at argument {i}:{indentExpr ba[i]!}\nvs{indentExpr ua[i]!}"
    let some ip := names.findIdx? (· == `hpre) | throwError "facts_compose: {U}.ofPre has no `hpre`"
    let tA ← tick s!"{U}: call unified" tA
    -- the arm's instantiations of `U`'s variables
    for (nm, stx) in uinsts do
      let some k := names.findIdx? (· == nm) | throwError "facts_compose: {U} has no variable {nm}"
      let e ← Term.elabTermEnsuringType stx (← instantiateMVars (← inferType ms[k]!))
      Term.synthesizeSyntheticMVarsNoPostponing
      unless ← isDefEq ms[k]! e do throwError "facts_compose: {U}'s {nm} cannot be {e}"
    -- `same`: the callee's variables still open take the caller's of the same name and type (never `d`)
    if same then
      for k in [:ip] do
        if names[k]! != `d && (← instantiateMVars ms[k]!).isMVar then
          for c in callerVars do
            if (← c.fvarId!.getUserName) == names[k]! then
              let saved ← saveState
              unless ← isDefEq ms[k]! c do saved.restore
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
    let t0 ← tick s!"{U}: instantiated, {decls.size} open" tA
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
      let t1 ← tick s!"{U}: {rest.size} premises left" t0
      match ob? with
      | none =>
        -- many variables: one tuple (opening it is one elimination, not one per variable)
        let tup? ← if exs.size > 6 then tupleOf exs else pure none
        let ex ← match tup? with
          | some (T, _, projs) => withLocalDeclD `p T fun p => do
              mkAppM ``Exists #[← mkLambdaFVars #[p] (conj.replaceFVars exs (projs p))]
          | none => mkExistsFVars exs conj
        let r ← mkForallFVars bs ex
        let _ ← tick s!"{U}: obligation built" t1
        return r
      | some ob =>
        -- the contract's proof: open the obligation, apply `U.ofPre`, adapt the postcondition
        let hob := mkAppN ob bs
        -- the proof once the obligation is opened: `h : (Pre ∧ r₁) ∧ r₂ …` (left-nested), the variables `exs`
        let finish (h : Expr) : TermElabM Expr := do
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
            let preTyU ← instantiateMVars (← inferType cur)
            let qU := (← instantiateMVars (← inferType hw)).appArg!
            let qC := body.appArg!
            let pt ← mkPostGoal qU qC
            -- the post tactic sees the opened obligation as `hob.get`, the callee's `Pre` as `hpreU`
            let obTy := mkApp (mkConst ``Ob) (← inferType hob)
            withLetDecl `hpreU preTyU cur fun hprev => do
            withLetDecl `hob obTy (mkApp2 (mkConst ``Ob.mk) (← inferType hob) hob) fun hobv => do
              let mv ← mkFreshExprSyntheticOpaqueMVar pt
              let rem ← try Term.withoutErrToSorry (Tactic.run mv.mvarId! (Tactic.evalTactic post))
                catch e => throwError "facts_compose: the postcondition of {U} does not give {x}'s:{indentExpr pt}\n{e.toMessageData}"
              unless rem.isEmpty do
                throwError "facts_compose: the postcondition of {U} does not give {x}'s: goals left {rem.map (MessageData.ofGoal ·)}"
              mkLetFVars #[hprev, hobv] (← mkAppM ``Logic.wp_mono #[hw, ← instantiateMVars mv])
        let rec open_ (j : Nat) (h : Expr) : TermElabM Expr := do
          if j < exs.size then
            let e := exs[j]!
            let pBody ← instantiateMVars (← whnf (← inferType h))
            let lam := pBody.appArg!
            withLocalDeclD `hx (← instantiateMVars (Expr.headBeta (mkApp lam e))) fun hx => do
              let inner ← open_ (j + 1) hx
              let f ← mkLambdaFVars #[e, hx] inner
              mkAppM ``Exists.elim #[h, f]
          else finish h
        let tup? ← if exs.size > 6 then tupleOf exs else pure none
        let r ← match tup? with
          | none => open_ 0 hob
          | some (T, lvl, projs) =>
            -- one elimination of the tuple; the proof built over the variables, then they are its projections
            withLocalDeclD `h conj fun h => do
              let inner ← instantiateMVars (← finish h)
              withLocalDeclD `p T fun p => do
                let ps := projs p
                let conjP := conj.replaceFVars exs ps
                withLocalDeclD `hp conjP fun hp => do
                  let f ← mkLambdaFVars #[p, hp] (inner.replaceFVars (exs.push h) (ps.push hp))
                  let lam ← mkLambdaFVars #[p] conjP
                  return mkAppN (mkConst ``Exists.elim [lvl]) #[T, lam, body, hob, f]
        let t2 ← tick s!"{U}: proof built" t1
        let r ← mkLambdaFVars bs r
        let _ ← tick s!"{U}: proof abstracted" t2
        return wrapHide r
where
  /-- `∀ b w h', qU b w h' → qC b w h'` -/
  mkPostGoal (qU qC : Expr) : MetaM Expr := do
    let ty ← inferType qU
    forallTelescope ty fun ys _ => do
      mkForallFVars ys (← mkArrow (Expr.headBeta (mkAppN qU ys)) (Expr.headBeta (mkAppN qC ys)))

syntax compInst := " (" ident " := " term ")"
syntax compArm := " | " ident " => " ident (compInst)* (&" same")? (" with " term)? (" by " tacticSeq)?
/-- A premise of `T` proved in place. -/
syntax compProof := " | " ident " := " term

/-- `facts_compose X := T | hC => U by tac …`: see the module docstring. -/
syntax (name := factsCompose) "facts_compose " ident (ppSpace bracketedBinder)* " := " ident (compInst)*
  (atomic(compProof) <|> compArm)+ : command

/-- `T.ofPre`'s binders, those named in `insts` instantiated (elaborated after the binders before them; one that
mentions a later variable is elaborated once the variables are all bound, at the first explicit premise): the
arguments for `T.ofPre`, the binders left, the conclusion. The composite's own implicit binders come after the
context's parameters (`eng`, `σ`, `answer`, `HI`), its explicit ones (hypotheses over `T`'s variables) before `T`'s
first explicit premise. -/
partial def telescopeInst {α} (ty : Expr) (insts : Array (Name × Syntax)) (args locals : Array Expr)
    (k : Array Expr → Array Expr → Expr → TermElabM α) (extras : Array Syntax := #[])
    (late : Array Syntax := #[]) (pending : Array (Expr × Syntax) := #[]) (split : Bool := true)
    (subs : Array (Expr × Expr) := #[]) : TermElabM α := do
  -- an instantiated variable's placeholder (still in scope under its name) replaced by its value in later values
  let sub (e : Expr) : Expr := subs.foldl (fun e (x, v) => e.replaceFVar x v) e
  if split && !extras.isEmpty then
    let (imp, exp) := extras.partition fun b => b.getKind == ``Lean.Parser.Term.implicitBinder ||
      b.getKind == ``Lean.Parser.Term.strictImplicitBinder || b.getKind == ``Lean.Parser.Term.instBinder
    return ← telescopeInst ty insts args locals k imp (late ++ exp) pending false subs
  let ty ← whnfR ty
  -- the deferred instantiations and the late binders, once `T`'s variables are bound
  let settle (ty : Expr) (args locals : Array Expr) (k' : Expr → Array Expr → Array Expr → TermElabM α) :
      TermElabM α := do
    let mut ty := ty; let mut args := args; let mut locals := locals
    for (x, stx) in pending do
      let d ← x.fvarId!.getType
      let e := sub (← instantiateMVars (← Term.elabTermEnsuringType stx d))
      Term.synthesizeSyntheticMVarsNoPostponing
      locals := locals.filter (· != x)
      for y in locals do
        if (← y.fvarId!.getType).containsFVar x.fvarId! then
          throwError "facts_compose: the instantiation of {← x.fvarId!.getUserName} is needed by a later variable's type"
      ty := ty.replaceFVar x e
      args := args.map (·.replaceFVar x e)
    if late.isEmpty then k' ty args locals
    else Term.elabBinders late fun ex => k' ty args (locals ++ ex)
  match ty with
  | .forallE n d b bi =>
    -- the composite's own binders, after the context's parameters (they may mention `σ`, `HI`)
    if !extras.isEmpty && ![`eng, `σ, `answer, `HI].contains n then
      return ← Term.elabBinders extras fun ex => telescopeInst ty insts args (locals ++ ex) k #[] late pending false subs
    if bi == .default && (!pending.isEmpty || !late.isEmpty) then
      return ← settle ty args locals fun ty args locals => telescopeInst ty insts args locals k #[] #[] #[] false subs
    if let some (_, stx) := insts.find? (·.1 == n) then
      -- `e` may use a new binder of the same name (`(n := n + 2)`): kept when it does
      withLocalDecl n bi d fun x0 => do
        let st ← saveState
        let r ← try
            let e ← Term.withoutErrToSorry do
              let e ← Term.elabTermEnsuringType stx d
              Term.synthesizeSyntheticMVarsNoPostponing
              instantiateMVars e
            pure (some (sub e))
          catch _ => st.restore; pure none
        match r with
        | some e =>
          let keepX := e.containsFVar x0.fvarId!
          let locals := if keepX then locals.push x0 else locals
          let subs := if keepX then subs else subs.push (x0, e)
          telescopeInst (← Core.betaReduce (b.instantiate1 e)) insts (args.push e) locals k extras late pending false subs
        | none =>
          telescopeInst (b.instantiate1 x0) insts (args.push x0) (locals.push x0) k extras late (pending.push (x0, stx)) false subs
    else
      withLocalDecl n bi d fun x => telescopeInst (b.instantiate1 x) insts (args.push x) (locals.push x) k extras late pending false subs
  | _ =>
    if !pending.isEmpty || !late.isEmpty then
      settle ty args locals fun ty args locals => k args locals ty
    else k args locals ty

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
    let same := !a[5].isNone
    let cstr : Option Syntax := if a[6].isNone then none else some a[6][1]
    let tac : Syntax ← if a[7].isNone then
        `(tacticSeq| intro b w' h' hq; exact hq)
      else pure a[7][1]
    return (c, U, tac, cstr, ui, same)
  liftTermElabM do
    let tOf := Name.mkStr T "ofPre"
    let ci ← getConstInfo tOf
    -- the premises proved in place are instantiated like variables
    let tS ← tick s!"{T}: start" (← IO.monoMsNow)
    telescopeInst (extras := extraBs) ci.type (insts ++ proofs) #[] #[] fun args0 xs concl => do
      let _ ← tick s!"{T}: instantiations done ({xs.size} binders)" tS
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
          let (_, U, tac, cstr, ui, same) := arms[a]!
          let t ← armWork x U (← `(tactic| ($(⟨tac⟩)))) none ctx cstr ui same xs
          which := which.push (some obls.size)
          obls := obls.push (Name.mkSimple s!"ob_{nm}", t)
        | none => which := which.push none
      for (c, _, _, _, _, _) in arms do
        unless obls.any (·.1 == Name.mkSimple s!"ob_{c}") do throwError "facts_compose: {T}.ofPre has no premise {c}"
      withLocalDeclsDND obls fun obs => do
        let mut args := args0
        let mut bs : Array Expr := #[]
        for x in xs, w in which do
          match w with
          | some j =>
            let nm ← x.fvarId!.getUserName
            let some a := arms.findIdx? (·.1 == nm) | unreachable!
            let (_, U, tac, cstr, ui, same) := arms[a]!
            let d ← armWork x U (← `(tactic| ($(⟨tac⟩)))) (some obs[j]!) ctx cstr ui same xs
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
