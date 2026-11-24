import Lean
import JSProofs.Facts

/-!
# A spec's facts form, derived in Lean (zippy docs/react-proofs.md, "Composition in Lean")

`facts_form T` declares `T.facts`: `T` with its premises about the state `s` replaced by one premise
`Facts.holds (a := A) L s`, where `A` lists the objects and records they name. The premises replaced:

* an object's property, `(s.objEntry o).props.get? k = r`;
* its existence, `o < s.heap.size`, and any statement about its kind, `P (s.objEntry o).kind`;
* a record's bindings, `Scope.declLike? (s.envEntry E) = some (bG, oG)` with the lookups `bG[x]? = r`, and
  `E < s.envs.size` (the map `bG` is then no longer a parameter: the proof obtains it from the record's fact);
* frame-closed statements, `∀ w …, Frame fp s w → …` (after unfolding definitions such as `DomRead`), with `fp`
  reflected into a footprint over `A`.

`A` is a list of `T`'s own terms, so `A.obj i` reduces to the object it names: each replaced premise is its fact's
statement up to definitional unfolding, and the proof is `T` applied to projections of the list. The statement is
built from `T`'s elaborated type, not its text, so it follows `T` as `T` changes. Other premises stay as they are.
-/

open Lean Meta Elab Command

namespace Logic.FactsForm

/-- `e` is `s.objEntry o`: `o`. -/
def objEntryOf? (s e : Expr) : Option Expr :=
  if e.isAppOfArity ``ES.State.objEntry 2 && e.appFn!.appArg! == s then some e.appArg! else none

/-- The first object `o` with `(s.objEntry o).kind` in `t`. -/
def kindObj? (s t : Expr) : Option Expr :=
  (t.find? fun e => e.isAppOfArity ``ES.Obj.kind 1 && (objEntryOf? s e.appArg!).isSome).bind
    fun e => objEntryOf? s e.appArg!

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

/-- `x < s.<field>.size`: `x`. -/
def sizeLtOf? (s t : Expr) (field : Name) : Option Expr := do
  guard (t.isAppOfArity ``LT.lt 4)
  let sz := t.appArg!
  guard (sz.isAppOfArity ``Array.size 2 && sz.appArg!.isAppOfArity field 1 && sz.appArg!.appArg! == s)
  let x := t.appFn!.appArg!
  guard (!x.containsFVar s.fvarId!)
  return x

/-- The atoms: objects and records by index, added as they are met. -/
structure AtomsB where
  objs : Array Expr := #[]
  envs : Array Expr := #[]

def AtomsB.obj (A : AtomsB) (o : Expr) : AtomsB × Nat :=
  match A.objs.findIdx? (· == o) with
  | some i => (A, i)
  | none => ({ A with objs := A.objs.push o }, A.objs.size)

def AtomsB.env (A : AtomsB) (e : Expr) : AtomsB × Nat :=
  match A.envs.findIdx? (· == e) with
  | some i => (A, i)
  | none => ({ A with envs := A.envs.push e }, A.envs.size)

/-- The elements of a list term (`[]`, `::`, `++`), unfolding definitions; `fuel` bounds the unfoldings (a list
written through more than 64 definitions is not reflected, and its premise is kept). -/
def listElems (l : Expr) : Nat → MetaM (Option (Array Expr))
  | 0 => return none
  | fuel + 1 => do
    let l ← whnfR l
    if l.isAppOfArity ``List.nil 1 then return some #[]
    if l.isAppOfArity ``List.cons 3 then
      let some rest ← listElems l.appArg! fuel | return none
      return some (#[l.appFn!.appArg!] ++ rest)
    if l.isAppOfArity ``HAppend.hAppend 6 then
      let some x ← listElems l.appFn!.appArg! fuel | return none
      let some y ← listElems l.appArg! fuel | return none
      return some (x ++ y)
    if let some l' ← unfoldDefinition? l then return ← listElems l' fuel
    return none

/-- A footprint term reflected into an `SFoot` over the atoms (its objects and records added), unfolding
definitions; `fuel` bounds the unfoldings (a footprint written through more is not reflected, its premise kept). -/
def reflectFoot (A : AtomsB) (fp : Expr) : Nat → MetaM (Option (AtomsB × Expr))
  | 0 => return none
  | fuel + 1 => do
    let fp ← whnfR fp
    if fp.isAppOfArity ``Logic.Footprint.union 2 then
      let some (A, f) ← reflectFoot A fp.appFn!.appArg! fuel | return none
      let some (A, g) ← reflectFoot A fp.appArg! fuel | return none
      return some (A, mkApp2 (mkConst ``SFoot.union) f g)
    if fp.isAppOfArity ``Logic.Footprint.mk 3 then
      let args := fp.getAppArgs
      let some bs ← listElems args[0]! 4096 | return none
      let some ps ← listElems args[1]! 4096 | return none
      let mut A := A
      let mut bs' : Array Expr := #[]
      for b in bs do
        let b ← whnfR b
        unless b.isAppOfArity ``Prod.mk 4 do return none
        let (A', i) := A.env b.appFn!.appArg!
        A := A'
        bs' := bs'.push (← mkAppM ``Prod.mk #[mkNatLit i, b.appArg!])
      let mut ps' : Array Expr := #[]
      for p in ps do
        let p ← whnfR p
        unless p.isAppOfArity ``Prod.mk 4 do return none
        let (A', i) := A.obj p.appFn!.appArg!
        A := A'
        ps' := ps'.push (← mkAppM ``Prod.mk #[mkNatLit i, p.appArg!])
      let bl ← mkListLit (← mkAppM ``Prod #[mkConst ``Nat, mkConst ``ES.JSStr]) bs'.toList
      let pl ← mkListLit (← mkAppM ``Prod #[mkConst ``Nat, mkConst ``ES.PropKey]) ps'.toList
      return some (A, mkApp3 (mkConst ``SFoot.mk) bl pl args[2]!)
    if let some fp' ← unfoldDefinition? fp then return ← reflectFoot A fp' fuel
    return none

/-- Unfolds `t`'s head until it is a `∀` (at most four definitions). -/
def unfoldToForall (t : Expr) : MetaM (Option Expr) := do
  let mut t := t
  for _ in [:4] do
    if t.isForall then return some t
    match ← unfoldDefinition? t with
    | some t' => t := t'.headBeta
    | none => return none
  return if t.isForall then some t else none

/-- The frame binder of a telescope: `Frame fp s w`. -/
def frameIdx? (s : Expr) (bs : Array Expr) : MetaM (Option Nat) :=
  bs.findIdxM? fun b => do
    let ty ← inferType b
    return ty.isAppOfArity ``Logic.Frame 3 && ty.appFn!.appArg! == s

/-- A frame-closed premise `∀ w …, Frame fp s w → …` (its head unfolded): the unfolded type, the footprint, and
`P w := ∀ (the other binders), body`. -/
def closedOf? (s t : Expr) : MetaM (Option (Expr × Expr × Expr)) := do
  let some t ← unfoldToForall t | return none
  forallTelescope t fun bs body => do
    let some j ← frameIdx? s bs | return none
    let fr ← inferType bs[j]!
    let w := fr.appArg!
    let some iw := bs.findIdx? (· == w) | return none
    let fp := fr.appFn!.appFn!.appArg!
    if fp.containsFVar s.fvarId! then return none
    for k in [:bs.size] do
      if k != j && (← inferType bs[k]!).containsFVar s.fvarId! then return none
    if body.containsFVar s.fvarId! then return none
    -- a callee's contract (it calls a function) stays a premise: a composite discharges it
    if (body.find? fun e => e.isConst && e.constName!.getString! == "callImpl").isSome then return none
    let others := (List.range bs.size).filter (fun k => k != j && k != iw) |>.map (bs[·]!)
    let P ← mkLambdaFVars #[w] (← mkForallFVars others.toArray body)
    return some (t, fp, P)

/-- What becomes of a binder. -/
inductive Role where
  | kept
  | map (r : Nat)
  | decl (r : Nat)
  | envLt (r : Nat)
  /-- the fact at `m`, the premise its statement's right (`true`) or left (`false`) part -/
  | direct (m : Nat) (right : Bool)
  | lookup (r : Nat) (m : Nat)
  /-- a closed fact at `m`, the premise's type unfolded to `t` -/
  | closed (m : Nat) (t : Expr)
  /-- `E < s.envs.size` of a whole record (`whole[r]`) -/
  | wholeLt (r : Nat)
  deriving Inhabited

/-- A record whose bindings map is eliminated. -/
structure Rec where
  e : Expr
  bG : Expr
  oG : Expr
  decl : Nat
  deriving Inhabited

/-- `Scope.declLike? (s.envEntry e) = some (bs, oG)`. -/
def declLikeEq (s e bs oG : Expr) : MetaM Expr := do
  mkEq (mkApp (mkConst ``Scope.declLike?) (mkApp2 (mkConst ``ES.State.envEntry) s e))
    (← mkAppM ``Option.some #[← mkAppM ``Prod.mk #[bs, oG]])

/-- `fun b => b = v` over `Option Binding`. -/
def eqPred (v : Expr) : MetaM Expr := do
  withLocalDeclD `b (← mkAppM ``Option #[mkConst ``ES.Binding]) fun b => do mkLambdaFVars #[b] (← mkEq b v)

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
    -- the other records: whole (their maps stay parameters)
    let mut whole : Array Rec := #[]
    for i in [:xs.size] do
      if let some (E, bG, oG) := declLikeOf? s tys[i]! then
        if !recs.any (·.decl == i) && !E.containsFVar sid && !bG.containsFVar sid && !oG.containsFVar sid &&
            !recs.any (·.e == E) && !whole.any (·.e == E) then
          whole := whole.push ⟨E, bG, oG, i⟩
    let mut A : AtomsB := { envs := recs.map (·.e) ++ whole.map (·.e) }
    -- facts (the records first, then the others in binder order), each built once the atoms are complete
    let mut mk : Array (Expr → MetaM Expr) :=
      recs.mapIdx fun r rc a => pure (mkApp3 (mkConst ``Fact.record) a (mkNatLit r) rc.oG)
    let mut roles : Array Role := #[]
    for i in [:xs.size] do
      let t := tys[i]!
      if let some r := recs.findIdx? (·.bG == xs[i]!) then roles := roles.push (.map r); continue
      if let some r := recs.findIdx? (·.decl == i) then roles := roles.push (.decl r); continue
      if let some r := whole.findIdx? (·.decl == i) then
        let rc := whole[r]!
        roles := roles.push (.direct mk.size true)
        mk := mk.push fun a => pure (mkApp4 (mkConst ``Fact.recordIs) a (mkNatLit (recs.size + r)) rc.bG rc.oG)
        continue
      if let some (mp, x, v) := lookupOf? t then
        if let some r := recs.findIdx? (·.bG == mp) then
          let oG := recs[r]!.oG
          roles := roles.push (.lookup r mk.size)
          mk := mk.push fun a => do return mkApp5 (mkConst ``Fact.bind) a (mkNatLit r) oG x (← eqPred v)
          continue
      if let some E := sizeLtOf? s t ``ES.State.envs then
        if let some r := recs.findIdx? (·.e == E) then roles := roles.push (.envLt r); continue
        if let some r := whole.findIdx? (·.e == E) then
          -- its record fact may come later: its index is found once all facts are listed
          roles := roles.push (.wholeLt r); continue
      unless t.containsFVar sid do roles := roles.push .kept; continue
      -- an object's property
      if let some (_, lhs, v) := t.eq? then
        if lhs.isAppOfArity ``ES.PropMap.get? 2 && !v.containsFVar sid && !lhs.appArg!.containsFVar sid then
          let pm := lhs.appFn!.appArg!
          if pm.isAppOfArity ``ES.Obj.props 1 then
            if let some o := objEntryOf? s pm.appArg! then
              unless o.containsFVar sid do
                let (A', j) := A.obj o
                A := A'
                let k := lhs.appArg!
                roles := roles.push (.direct mk.size true)
                mk := mk.push fun a => pure (mkApp4 (mkConst ``Fact.prop) a (mkNatLit j) k v)
                continue
      -- an object's existence
      if let some o := sizeLtOf? s t ``ES.State.heap then
        let (A', j) := A.obj o
        A := A'
        roles := roles.push (.direct mk.size false)
        mk := mk.push fun a => pure (mkApp3 (mkConst ``Fact.kindP) a (mkNatLit j)
          (mkLambda `K .default (mkConst ``ES.Kind) (mkConst ``True)))
        continue
      -- its kind
      if let some o := kindObj? s t then
        unless o.containsFVar sid do
          let pat := mkApp (mkConst ``ES.Obj.kind) (mkApp2 (mkConst ``ES.State.objEntry) s o)
          let body ← kabstract t pat
          unless body.containsFVar sid do
            let (A', j) := A.obj o
            A := A'
            let P := mkLambda `K .default (mkConst ``ES.Kind) body
            roles := roles.push (.direct mk.size true)
            mk := mk.push fun a => pure (mkApp3 (mkConst ``Fact.kindP) a (mkNatLit j) P)
            continue
      -- frame-closed
      if let some (tu, fp, P) ← closedOf? s t then
        if let some (A', sf) ← reflectFoot A fp 64 then
          A := A'
          roles := roles.push (.closed mk.size tu)
          mk := mk.push fun a => pure (mkApp3 (mkConst ``Fact.closed) a sf P)
          continue
      roles := roles.push .kept
    let a := mkApp2 (mkConst ``Atoms.mk) (← mkListLit (mkConst ``ES.ObjId) A.objs.toList)
      (← mkListLit (mkConst ``ES.EnvId) A.envs.toList)
    let fs ← mk.mapM (· a)
    let L ← mkListLit (mkApp (mkConst ``Fact) a) fs.toList
    let kept := (List.range xs.size).filter (fun i => match roles[i]! with | .kept => true | _ => false) |>.map (xs[·]!)
    withLocalDeclD `hf (mkApp3 (mkConst ``Facts.holds) a L s) fun hf => do
    let get (m : Nat) : MetaM Expr := do
      let hm ← mkDecideProof (← mkAppM ``LT.lt #[mkNatLit m, mkNatLit fs.size])
      return mkAppN (mkConst ``Facts.get) #[a, L, s, hf, mkNatLit m, hm]
    -- the records' maps, obtained from their facts, then `T`
    let rec go (r : Nat) (bss hds : Array Expr) : MetaM Expr := do
      if h : r < recs.size then
        let rc := recs[r]
        let ex ← mkAppM ``And.right #[← get r]
        let mapTy ← inferType rc.bG
        let motive ← withLocalDeclD `bs mapTy fun bs => do
          mkLambdaFVars #[bs] (← declLikeEq s (mkApp2 (mkConst ``Atoms.env) a (mkNatLit r)) bs rc.oG)
        withLocalDeclD `bs mapTy fun bs => do
          withLocalDeclD `hd (← declLikeEq s rc.e bs rc.oG) fun hd => do
            let body ← go (r + 1) (bss.push bs) (hds.push hd)
            return mkAppN (mkConst ``Exists.elim [Level.one]) #[mapTy, motive, concl, ex, ← mkLambdaFVars #[bs, hd] body]
      else
        let mut args : Array Expr := #[]
        for i in [:xs.size] do
          match roles[i]! with
          | .kept => args := args.push xs[i]!
          | .map r => args := args.push bss[r]!
          | .decl r => args := args.push hds[r]!
          | .envLt r => args := args.push (← mkAppM ``And.left #[← get r])
          | .wholeLt r =>
            let some m := (List.range xs.size).findSome? fun k =>
              if k == whole[r]!.decl then (match roles[k]! with | .direct m _ => some m | _ => none) else none
              | throwError "whole record"
            args := args.push (← mkAppM ``And.left #[← get m])
          | .lookup r m =>
            let rc := recs[r]!
            let some (_, x, v) := lookupOf? tys[i]! | throwError "lookup"
            args := args.push (mkAppN (mkConst ``Fact.bind_get)
              #[a, mkNatLit r, rc.oG, x, ← eqPred v, s, bss[r]!, hds[r]!, ← get m])
          | .direct m right => args := args.push (← mkAppM (if right then ``And.right else ``And.left) #[← get m])
          | .closed m tu =>
            let hc ← get m
            let prf ← forallTelescope tu fun bs _ => do
              let some j ← frameIdx? s bs | throwError "closed"
              let w := (← inferType bs[j]!).appArg!
              let some iw := bs.findIdx? (· == w) | throwError "closed"
              let others := (List.range bs.size).filter (fun k => k != j && k != iw) |>.map (bs[·]!)
              mkLambdaFVars bs (mkAppN hc (#[w, bs[j]!] ++ others.toArray))
            args := args.push prf
        return mkAppN (mkConst n (ci.levelParams.map mkLevelParam)) args
    let val ← go 0 #[] #[]
    let bs := kept.toArray ++ #[hf]
    let ty ← instantiateMVars (← mkForallFVars bs concl)
    let val ← instantiateMVars (← mkLambdaFVars bs val)
    addDecl (.thmDecl { name := n ++ `facts, levelParams := ci.levelParams, type := ty, value := val })
    let nc := roles.foldl (fun c r => match r with | .closed .. => c + 1 | _ => c) 0
    logInfo m!"{n ++ `facts}: {fs.size} facts ({recs.size} records, {A.objs.size} objects, {nc} frame-closed); {kept.length} premises kept"

elab "facts_form " id:ident : command => do
  let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  liftTermElabM (factsForm n)

end Logic.FactsForm
