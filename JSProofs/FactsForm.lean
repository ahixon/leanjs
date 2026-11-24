import Lean
import JSProofs.Facts

/-!
# A spec's facts form, derived in Lean (zippy docs/react-proofs.md, "Composition in Lean")

`facts_form T` declares `T.facts`: `T` with its premises about the state `s` that read an object's property
(`(s.objEntry o).props.get? k = r`), its kind (any statement about `(s.objEntry o).kind`) or its existence
(`o < s.heap.size`) replaced by one premise `Facts.holds L s`, over atoms `a` that name each such object `o` by an index
`i` (`a.obj i = o`). Its proof is `T`, each replaced premise a projection of the list. The statement is built from
`T`'s elaborated type, not from its text, so it follows `T` as `T` changes.

Other premises stay as they are (bindings, fuel, callees' contracts, facts about values).
-/

open Lean Meta Elab Command

namespace Logic.FactsForm

/-- The shape of a premise about `s`. -/
inductive Shape where
  /-- `(s.objEntry o).props.get? k = r` -/
  | prop (o k r : Expr)
  /-- `o < s.heap.size` -/
  | lt (o : Expr)
  /-- `P (s.objEntry o).kind` (`P` a lambda) -/
  | kindP (o P : Expr)
  deriving Inhabited

def Shape.obj : Shape → Expr
  | .prop o _ _ | .lt o | .kindP o _ => o

/-- `e` is `s.objEntry o`: `o`. -/
def objEntryOf? (s e : Expr) : Option Expr :=
  if e.isAppOfArity ``ES.State.objEntry 2 && e.appFn!.appArg! == s then some e.appArg! else none

/-- The first object `o` with `(s.objEntry o).kind` in `t`. -/
def kindObj? (s t : Expr) : Option Expr :=
  (t.find? fun e => e.isAppOfArity ``ES.Obj.kind 1 && (objEntryOf? s e.appArg!).isSome).bind
    fun e => objEntryOf? s e.appArg!

def shapeOf? (s t : Expr) : MetaM (Option Shape) := do
  let t ← instantiateMVars t
  unless t.containsFVar s.fvarId! do return none
  -- (s.objEntry o).props.get? k = r
  if let some (_, lhs, r) := t.eq? then
    if lhs.isAppOfArity ``ES.PropMap.get? 2 && !r.containsFVar s.fvarId! then
      let pm := lhs.appFn!.appArg!
      let k := lhs.appArg!
      if pm.isAppOfArity ``ES.Obj.props 1 && !k.containsFVar s.fvarId! then
        if let some o := objEntryOf? s pm.appArg! then
          unless o.containsFVar s.fvarId! do return some (.prop o k r)
  -- o < s.heap.size
  if t.isAppOfArity ``LT.lt 4 then
    let o := t.appFn!.appArg!
    let sz := t.appArg!
    if sz.isAppOfArity ``Array.size 2 && sz.appArg!.isAppOfArity ``ES.State.heap 1 && sz.appArg!.appArg! == s &&
        !o.containsFVar s.fvarId! then
      return some (.lt o)
  -- P (s.objEntry o).kind, `s` nowhere else
  if let some o := kindObj? s t then
    unless o.containsFVar s.fvarId! do
      let pat := mkApp (mkConst ``ES.Obj.kind) (mkApp2 (mkConst ``ES.State.objEntry) s o)
      let body ← kabstract t pat
      unless body.containsFVar s.fvarId! do
        return some (.kindP o (mkLambda `K .default (mkConst ``ES.Kind) body))
  return none

/-- The fact for a shape, its object atom `i`. -/
def factOf (a i : Expr) : Shape → Expr
  | .prop _ k r => mkApp4 (mkConst ``Fact.prop) a i k r
  | .lt _ => mkApp3 (mkConst ``Fact.kindP) a i (mkLambda `K .default (mkConst ``ES.Kind) (mkConst ``True))
  | .kindP _ P => mkApp3 (mkConst ``Fact.kindP) a i P

/-- The premise, from the fact's statement `p` (about `a.obj i`) and `h : a.obj i = o`. -/
def premiseOf (s ai h p : Expr) : Shape → MetaM Expr
  | .prop o k r => do
    let x := mkBVar 0
    let motive := mkLambda `x .default (mkConst ``ES.ObjId)
      (← mkEq (mkApp2 (mkConst ``ES.PropMap.get?) (mkApp (mkConst ``ES.Obj.props) (mkApp2 (mkConst ``ES.State.objEntry) s x)) k) r)
    let p2 ← mkAppM ``And.right #[p]
    return mkAppN (mkConst ``Eq.subst [Level.one]) #[mkConst ``ES.ObjId, motive, ai, o, h, p2]
  | .lt o => do
    let p1 ← mkAppM ``And.left #[p]
    let motive ← withLocalDeclD `x (mkConst ``ES.ObjId) fun x => do
      mkLambdaFVars #[x] (← mkAppM ``LT.lt #[x, ← mkAppM ``Array.size #[mkApp (mkConst ``ES.State.heap) s]])
    return mkAppN (mkConst ``Eq.subst [Level.one]) #[mkConst ``ES.ObjId, motive, ai, o, h, p1]
  | .kindP o P => do
    let p2 ← mkAppM ``And.right #[p]
    let motive := mkLambda `x .default (mkConst ``ES.ObjId)
      (mkApp P (mkApp (mkConst ``ES.Obj.kind) (mkApp2 (mkConst ``ES.State.objEntry) s (mkBVar 0))))
    return mkAppN (mkConst ``Eq.subst [Level.one]) #[mkConst ``ES.ObjId, motive, ai, o, h, p2]

/-- `Scope.declLike? (s.envEntry E) = some (bG, oG)`: `(E, bG, oG)`. -/
def declLikeOf? (s t : Expr) : Option (Expr × Expr × Expr) := do
  let (_, lhs, rhs) ← t.eq?
  guard (lhs.isAppOfArity ``Scope.declLike? 1)
  let ee := lhs.appArg!
  guard (ee.isAppOfArity ``ES.State.envEntry 2 && ee.appFn!.appArg! == s)
  guard (rhs.isAppOfArity ``Option.some 2)
  let pr := rhs.appArg!
  guard (pr.isAppOfArity ``Prod.mk 4)
  return (ee.appArg!, pr.appFn!.appArg!, pr.appArg!)

/-- `bG[x]? = r`: `(bG, x, r)`. -/
def lookupOf? (t : Expr) : Option (Expr × Expr × Expr) := do
  let (_, lhs, r) ← t.eq?
  guard (lhs.isAppOf ``GetElem?.getElem?)
  let args := lhs.getAppArgs
  guard (args.size ≥ 2)
  return (args[args.size - 2]!, args[args.size - 1]!, r)

/-- `E < s.envs.size`: `E`. -/
def envLtOf? (s t : Expr) : Option Expr := do
  guard (t.isAppOfArity ``LT.lt 4)
  let sz := t.appArg!
  guard (sz.isAppOfArity ``Array.size 2 && sz.appArg!.isAppOfArity ``ES.State.envs 1 && sz.appArg!.appArg! == s)
  return t.appFn!.appArg!

/-- A record whose bindings map is eliminated: its term, map, outer record, and record premise's binder. -/
structure Rec where
  e : Expr
  bG : Expr
  oG : Expr
  decl : Nat
  deriving Inhabited

/-- What becomes of a binder. -/
inductive Role where
  | kept
  | map (r : Nat)
  | decl (r : Nat)
  | envLt (r : Nat)
  | lookup (r : Nat) (x v : Expr) (m : Nat)
  | obj (sh : Shape) (m : Nat)
  deriving Inhabited

/-- Declares `T.facts`. -/
def factsForm (n : Name) : TermElabM Unit := do
  let ci ← getConstInfo n
  forallTelescope ci.type fun xs concl => do
    let some s ← xs.findM? (fun x => return (← x.fvarId!.getUserName) == `s) | throwError "{n}: no binder `s`"
    let tys ← xs.mapM fun x => do instantiateMVars (← inferType x)
    let sid := s.fvarId!
    -- records whose map is used only by its record premise and lookups
    let mut recs : Array Rec := #[]
    for i in [:xs.size] do
      if let some (E, bG, oG) := declLikeOf? s tys[i]! then
        if bG.isFVar && !E.containsFVar sid && !oG.containsFVar sid && !recs.any (·.bG == bG) then
          let g := bG.fvarId!
          let ok := !concl.containsFVar g && (List.range xs.size).all fun j =>
            j == i || xs[j]! == bG || !tys[j]!.containsFVar g ||
              (match lookupOf? tys[j]! with
               | some (m, x, v) => m == bG && !x.containsFVar g && !v.containsFVar g && !v.containsFVar sid
               | none => false)
          if ok then recs := recs.push ⟨E, bG, oG, i⟩
    -- roles; facts: the records first, then the others in binder order
    let mut roles : Array Role := #[]
    let mut objs : Array Expr := #[]
    let mut nf := recs.size
    for i in [:xs.size] do
      let t := tys[i]!
      if let some r := recs.findIdx? (·.bG == xs[i]!) then roles := roles.push (.map r); continue
      if let some r := recs.findIdx? (·.decl == i) then roles := roles.push (.decl r); continue
      if let some (m, x, v) := lookupOf? t then
        if let some r := recs.findIdx? (·.bG == m) then
          roles := roles.push (.lookup r x v nf); nf := nf + 1; continue
      if let some E := envLtOf? s t then
        if let some r := recs.findIdx? (·.e == E) then roles := roles.push (.envLt r); continue
      match ← shapeOf? s t with
      | some sh =>
        unless objs.contains sh.obj do objs := objs.push sh.obj
        roles := roles.push (.obj sh nf); nf := nf + 1
      | none => roles := roles.push .kept
    let kept := (List.range xs.size).filter (fun i => match roles[i]! with | .kept => true | _ => false) |>.map (xs[·]!)
    withLocalDeclD `a (mkConst ``Atoms) fun a => do
    withLocalDeclsDND (objs.mapIdx fun j _ => (Name.mkSimple s!"i{j}", mkConst ``Nat)) fun is => do
    let oeqs ← objs.mapIdxM fun j o => do
      return (Name.mkSimple s!"ha{j}", ← mkEq (mkApp2 (mkConst ``Atoms.obj) a is[j]!) o)
    withLocalDeclsDND oeqs fun hs => do
    let eeqs ← recs.mapIdxM fun r rc => do
      return (Name.mkSimple s!"hb{r}", ← mkEq (mkApp2 (mkConst ``Atoms.env) a (mkNatLit r)) rc.e)
    withLocalDeclsDND eeqs fun hbs => do
    let jOf (o : Expr) : Nat := (objs.findIdx? (· == o)).getD 0
    let mut fs : Array Expr := recs.mapIdx fun r rc => mkApp3 (mkConst ``Fact.record) a (mkNatLit r) rc.oG
    for i in [:xs.size] do
      match roles[i]! with
      | .lookup r x v _ =>
        let P ← withLocalDeclD `b (← mkAppM ``Option #[mkConst ``ES.Binding]) fun b => do
          mkLambdaFVars #[b] (← mkEq b v)
        fs := fs.push (mkApp5 (mkConst ``Fact.bind) a (mkNatLit r) recs[r]!.oG x P)
      | .obj sh _ => fs := fs.push (factOf a is[jOf sh.obj]! sh)
      | _ => pure ()
    let L ← mkListLit (mkApp (mkConst ``Fact) a) fs.toList
    withLocalDeclD `hf (mkApp3 (mkConst ``Facts.holds) a L s) fun hf => do
    let get (m : Nat) : MetaM Expr := do
      let hm ← mkDecideProof (← mkAppM ``LT.lt #[mkNatLit m, mkNatLit fs.size])
      return mkAppN (mkConst ``Facts.get) #[a, L, s, hf, mkNatLit m, hm]
    -- the records' maps, obtained from their facts, then `T`
    let rec go (r : Nat) (bss hds : Array Expr) : MetaM Expr := do
      if h : r < recs.size then
        let rc := recs[r]
        let ex ← mkAppM ``And.right #[← get r]
        withLocalDeclD `bs (← inferType rc.bG) fun bs => do
          let ae := mkApp2 (mkConst ``Atoms.env) a (mkNatLit r)
          let hdTy ← mkEq (mkApp (mkConst ``Scope.declLike?) (mkApp2 (mkConst ``ES.State.envEntry) s ae))
            (← mkAppM ``Option.some #[← mkAppM ``Prod.mk #[bs, rc.oG]])
          withLocalDeclD `hd hdTy fun hd => do
            let body ← go (r + 1) (bss.push bs) (hds.push hd)
            mkAppM ``Exists.elim #[ex, ← mkLambdaFVars #[bs, hd] body]
      else
        let mut args : Array Expr := #[]
        for i in [:xs.size] do
          match roles[i]! with
          | .kept => args := args.push xs[i]!
          | .map r => args := args.push bss[r]!
          | .decl r =>
            let rc := recs[r]!
            let motive ← withLocalDeclD `E (mkConst ``ES.EnvId) fun E => do
              mkLambdaFVars #[E] (← mkEq (mkApp (mkConst ``Scope.declLike?) (mkApp2 (mkConst ``ES.State.envEntry) s E))
                (← mkAppM ``Option.some #[← mkAppM ``Prod.mk #[bss[r]!, rc.oG]]))
            args := args.push (mkAppN (mkConst ``Eq.subst [Level.one])
              #[mkConst ``ES.EnvId, motive, mkApp2 (mkConst ``Atoms.env) a (mkNatLit r), rc.e, hbs[r]!, hds[r]!])
          | .envLt r =>
            let motive ← withLocalDeclD `E (mkConst ``ES.EnvId) fun E => do
              mkLambdaFVars #[E] (← mkAppM ``LT.lt #[E, ← mkAppM ``Array.size #[mkApp (mkConst ``ES.State.envs) s]])
            args := args.push (mkAppN (mkConst ``Eq.subst [Level.one])
              #[mkConst ``ES.EnvId, motive, mkApp2 (mkConst ``Atoms.env) a (mkNatLit r), recs[r]!.e, hbs[r]!,
                ← mkAppM ``And.left #[← get r]])
          | .lookup r x v m =>
            let P ← withLocalDeclD `b (← mkAppM ``Option #[mkConst ``ES.Binding]) fun b => do
              mkLambdaFVars #[b] (← mkEq b v)
            args := args.push (mkAppN (mkConst ``Fact.bind_get)
              #[a, mkNatLit r, recs[r]!.oG, x, P, s, bss[r]!, hds[r]!, ← get m])
          | .obj sh m =>
            let j := jOf sh.obj
            args := args.push (← premiseOf s (mkApp2 (mkConst ``Atoms.obj) a is[j]!) hs[j]! (← get m) sh)
        return mkAppN (mkConst n (ci.levelParams.map mkLevelParam)) args
    let val ← go 0 #[] #[]
    let bs := kept.toArray ++ #[a] ++ is ++ hs ++ hbs ++ #[hf]
    let ty ← instantiateMVars (← mkForallFVars bs concl)
    let val ← instantiateMVars (← mkLambdaFVars bs val)
    addDecl (.thmDecl { name := n ++ `facts, levelParams := ci.levelParams, type := ty, value := val })
    logInfo m!"{n ++ `facts}: {fs.size} facts ({recs.size} records, {objs.size} objects); {kept.length} premises kept"

elab "facts_form " id:ident : command => do
  let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  liftTermElabM (factsForm n)

end Logic.FactsForm
