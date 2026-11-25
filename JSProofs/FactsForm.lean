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
    -- a projection of a definition (`(fp X).props`)
    let isProjApp ← match l.getAppFn with
      | .proj .. => pure true
      | .const c _ => do pure (← getProjectionFnInfo? c).isSome
      | _ => pure false
    if isProjApp then
      let l' ← whnf l
      if l' != l then return ← listElems l' fuel
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
    -- facts (the records first, then the others in binder order), each built once the atoms are complete
    let mut mk : Array (Expr → MetaM Expr) :=
      recs.map fun rc _ => pure (mkApp2 (mkConst ``Fact.record) rc.e rc.oG)
    let mut roles : Array Role := #[]
    for i in [:xs.size] do
      let t := tys[i]!
      if let some r := recs.findIdx? (·.bG == xs[i]!) then roles := roles.push (.map r); continue
      if let some r := recs.findIdx? (·.decl == i) then roles := roles.push (.decl r); continue
      if let some r := whole.findIdx? (·.decl == i) then
        let rc := whole[r]!
        roles := roles.push (.direct mk.size true)
        mk := mk.push fun _ => pure (mkApp3 (mkConst ``Fact.recordIs) rc.e rc.bG rc.oG)
        continue
      if let some (mp, x, v) := lookupOf? t then
        if let some r := recs.findIdx? (·.bG == mp) then
          let oG := recs[r]!.oG
          let E := recs[r]!.e
          roles := roles.push (.lookup r mk.size)
          mk := mk.push fun _ => do return mkApp4 (mkConst ``Fact.bind) E oG x (← eqPred v)
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
                let k := lhs.appArg!
                roles := roles.push (.direct mk.size true)
                mk := mk.push fun _ => pure (mkApp3 (mkConst ``Fact.prop) o k v)
                continue
      -- an object's existence
      if let some o := sizeLtOf? s t ``ES.State.heap then
        roles := roles.push (.direct mk.size false)
        mk := mk.push fun _ => pure (mkApp2 (mkConst ``Fact.kindP) o
          (mkLambda `K .default (mkConst ``ES.Kind) (mkConst ``True)))
        continue
      -- its kind
      if let some o := kindObj? s t then
        unless o.containsFVar sid do
          let pat := mkApp (mkConst ``ES.Obj.kind) (mkApp2 (mkConst ``ES.State.objEntry) s o)
          let body ← kabstract t pat
          unless body.containsFVar sid do
            let P := mkLambda `K .default (mkConst ``ES.Kind) body
            roles := roles.push (.direct mk.size true)
            mk := mk.push fun _ => pure (mkApp2 (mkConst ``Fact.kindP) o P)
            continue
      -- frame-closed
      if let some (tu, fp, P) ← closedOf? s t then
        roles := roles.push (.closed mk.size tu)
        mk := mk.push fun _ => pure (mkApp2 (mkConst ``Fact.closed) fp P)
        continue
      roles := roles.push .kept
    let fs ← mk.mapM (· (mkConst ``Unit.unit))
    let L ← mkListLit (mkConst ``Fact) fs.toList
    let kept := (List.range xs.size).filter (fun i => match roles[i]! with | .kept => true | _ => false) |>.map (xs[·]!)
    withLocalDeclD `hf (mkApp2 (mkConst ``Facts.holds) L s) fun hf => do
    let get (m : Nat) : MetaM Expr := do
      let hm ← mkDecideProof (← mkAppM ``LT.lt #[mkNatLit m, mkNatLit fs.size])
      return mkAppN (mkConst ``Facts.get) #[L, s, hf, mkNatLit m, hm]
    -- the records' maps, obtained from their facts, then `T`
    let rec go (r : Nat) (bss hds : Array Expr) : MetaM Expr := do
      if h : r < recs.size then
        let rc := recs[r]
        let ex ← mkAppM ``And.right #[← get r]
        let mapTy ← inferType rc.bG
        let motive ← withLocalDeclD `bs mapTy fun bs => do
          mkLambdaFVars #[bs] (← declLikeEq s rc.e bs rc.oG)
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
              #[rc.e, rc.oG, x, ← eqPred v, s, bss[r]!, hds[r]!, ← get m])
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
    -- `T.L` the facts; `T.Pre vars s` the facts about values alone and the facts at `s`; `T.ofPre`; `T.Pre_frame`
    let hvar? ← xs.findM? (fun x => return (← x.fvarId!.getUserName) == `h)
    let isContract (t : Expr) : Bool := (t.find? fun e => e.isConst && e.constName!.getString! == "callImpl").isSome
    let mut vars : Array Expr := #[]
    let mut pures : Array Expr := #[]
    let mut others : Array Expr := #[]
    for x in kept do
      let t ← inferType x
      if !(← isProp t) then vars := vars.push x
      else if isContract t || t.containsFVar sid || (hvar?.map (t.containsFVar ·.fvarId!)).getD false then
        others := others.push x
      else pures := pures.push x
    let lps := ci.levelParams.map mkLevelParam
    let varsL := vars.filter (· != s)
    let lName := Name.mkStr n "L"
    addDecl (.defnDecl (mkDefinitionValEx lName ci.levelParams
      (← instantiateMVars (← mkForallFVars varsL (mkApp (mkConst ``List [Level.zero]) (mkConst ``Fact))))
      (← instantiateMVars (← mkLambdaFVars varsL L)) .abbrev .safe []))
    let Lc := mkAppN (mkConst lName lps) varsL
    let ptys ← pures.mapM fun p => inferType p
    let conj := ptys.foldr (fun pt acc => mkAnd pt acc) (mkApp2 (mkConst ``Facts.holds) Lc s)
    let preName := Name.mkStr n "Pre"
    addDecl (.defnDecl (mkDefinitionValEx preName ci.levelParams
      (← instantiateMVars (← mkForallFVars vars (mkSort .zero)))
      (← instantiateMVars (← mkLambdaFVars vars conj)) .abbrev .safe []))
    let preApp := mkAppN (mkConst preName lps) vars
    withLocalDeclD `hpre preApp fun hpre => do
      -- the conjuncts: the `k`-th is `.2.….2.1`, the facts the last `.2`s
      let mut cur := hpre
      let mut pargs : Array Expr := #[]
      for _ in pures do
        pargs := pargs.push (mkProj ``And 0 cur)
        cur := mkProj ``And 1 cur
      let mut fargs : Array Expr := #[]
      let mut pi := 0
      for x in kept do
        if pures.contains x then fargs := fargs.push pargs[pi]!; pi := pi + 1
        else fargs := fargs.push x
      fargs := fargs.push cur
      let v2 := mkAppN (mkConst (n ++ `facts) lps) fargs
      let bs2 := vars ++ #[hpre] ++ others
      let ty2 ← instantiateMVars (← mkForallFVars bs2 concl)
      let val2 ← instantiateMVars (← mkLambdaFVars bs2 v2)
      addDecl (.thmDecl { name := Name.mkStr n "ofPre", levelParams := ci.levelParams, type := ty2, value := val2 })
      -- through a frame missing the facts' places, `Pre` holds at the frame's end
      withLocalDeclD `w (mkConst ``ES.State) fun w => do
      withLocalDeclD `fp (mkConst ``Logic.Footprint) fun fp => do
      withLocalDeclD `hF (mkApp3 (mkConst ``Logic.Frame) fp s w) fun hF => do
      withLocalDeclD `hap (mkApp2 (mkConst ``Facts.Apart) fp Lc) fun hap => do
        let varsW := vars.map fun x => if x == s then w else x
        let concl3 := mkAppN (mkConst preName lps) varsW
        let last := mkAppN (mkConst ``Facts.frame) #[fp, s, w, hF, Lc, hap, cur]
        let ptysW := ptys
        let mut acc := last
        let mut accTy := mkApp2 (mkConst ``Facts.holds) Lc w
        for k in (List.range pures.size).reverse do
          acc := mkApp4 (mkConst ``And.intro) ptysW[k]! accTy pargs[k]! acc
          accTy := mkAnd ptysW[k]! accTy
        let bs3 := vars ++ #[w, fp, hpre, hF, hap]
        let ty3 ← instantiateMVars (← mkForallFVars bs3 concl3)
        let val3 ← instantiateMVars (← mkLambdaFVars bs3 acc)
        addDecl (.thmDecl { name := Name.mkStr n "Pre_frame", levelParams := ci.levelParams, type := ty3, value := val3 })
    let nc := roles.foldl (fun c r => match r with | .closed .. => c + 1 | _ => c) 0
    logInfo m!"{n ++ `facts}: {fs.size} facts ({recs.size + whole.size} records, {nc} frame-closed); {kept.length} premises kept; L, Pre, ofPre, Pre_frame declared"

/-- A fact's place reflected over the atoms (its objects and records added). -/
def reflectLoc (A : AtomsB) (loc : Expr) : MetaM (Option (AtomsB × Expr)) := do
  let loc ← whnf loc
  let args := loc.getAppArgs
  match loc.getAppFn.constName? with
  | some ``Logic.Loc.pure => return some (A, mkConst ``RLoc.pure)
  | some ``Logic.Loc.obj => return some (A, mkApp (mkConst ``RLoc.obj) args[0]!)
  | some ``Logic.Loc.prop =>
    let (A, i) := A.obj args[0]!; return some (A, mkApp2 (mkConst ``RLoc.prop) (mkNatLit i) args[1]!)
  | some ``Logic.Loc.bind =>
    let (A, i) := A.env args[0]!; return some (A, mkApp2 (mkConst ``RLoc.bind) (mkNatLit i) args[1]!)
  | some ``Logic.Loc.record => return some (A, mkApp (mkConst ``RLoc.record) args[0]!)
  | some ``Logic.Loc.recordAll =>
    let (A, i) := A.env args[0]!; return some (A, mkApp (mkConst ``RLoc.recordAll) (mkNatLit i))
  | some ``Logic.Loc.objAll =>
    let (A, i) := A.obj args[0]!; return some (A, mkApp (mkConst ``RLoc.objAll) (mkNatLit i))
  | some ``Logic.Loc.closed =>
    let some (A, f) ← reflectFoot A args[0]! 64 | return none
    return some (A, mkApp (mkConst ``RLoc.closed) f)
  | _ => return none

/-- `facts_apart` proves `Facts.Apart fp L` (`L` a list of facts) by reflection, leaving `Atoms.Wf` of the objects and
records both name: that they are distinct. -/
elab "facts_apart_wf" : tactic => Tactic.withMainContext do
  let g ← Tactic.getMainGoal
  let t ← whnfR (← instantiateMVars (← g.getType))
  unless t.isAppOfArity ``Logic.Facts.Apart 2 do throwError "facts_apart_wf: not `Facts.Apart fp L`: {t}"
  let fp := t.appFn!.appArg!
  let L := t.appArg!
  let some elems ← listElems L 4096 | throwError "facts_apart: the facts are not a list"
  let mut A : AtomsB := {}
  let mut rs : Array Expr := #[]
  for x in elems do
    let some (A', r) ← reflectLoc A (mkApp (mkConst ``Fact.loc) x) | throwError "facts_apart: a place not reflected: {x}"
    A := A'
    rs := rs.push r
  let some (A', sf) ← reflectFoot A fp 64 | throwError "facts_apart: the footprint not reflected: {fp}"
  A := A'
  let U := mkApp2 (mkConst ``Atoms.mk) (← mkListLit (mkConst ``ES.ObjId) A.objs.toList)
    (← mkListLit (mkConst ``ES.EnvId) A.envs.toList)
  let rsL ← mkListLit (mkConst ``RLoc) rs.toList
  let hw ← mkFreshExprSyntheticOpaqueMVar (mkApp (mkConst ``Atoms.Wf) U) `wf
  let lhs ← mkAppM ``List.map #[mkConst ``Fact.loc, L]
  let rhs ← mkAppM ``List.map #[mkApp (mkConst ``RLoc.eval) U, rsL]
  let hl ← mkExpectedTypeHint (← mkEqRefl lhs) (← mkEq lhs rhs)
  let chk ← mkAppM ``List.all #[rsL, mkApp2 (mkConst ``RLoc.apart) U sf]
  let hc ← mkExpectedTypeHint (← mkEqRefl (mkConst ``Bool.true)) (← mkEq chk (mkConst ``Bool.true))
  let prf := mkAppN (mkConst ``Facts.apart_refl) #[U, hw, sf, L, rsL, hl, hc]
  unless ← isDefEq (← inferType prf) t do throwError "facts_apart: the footprint is not its reflection"
  g.assign prf
  Tactic.replaceMainGoal [hw.mvarId!]


/-- A key's literal (`PropKey.str (JSStr.ofString "x")`, `JSStr.ofString "x"`). -/
def strLit? (e : Expr) : Option String :=
  let e := e.consumeMData
  if e.isAppOfArity ``ES.JSStr.ofString 1 then
    match e.appArg!.consumeMData with
    | .lit (.strVal x) => some x
    | _ => none
  else none

def keyLit? (e : Expr) : Option String :=
  let e := e.consumeMData
  if e.isAppOfArity ``ES.PropKey.str 1 then (strLit? e.appArg!).map ("str:" ++ ·) else strLit? e

/-- Whether two keys are equal: known, or `none`. -/
def keyEq? (a b : Expr) : Option Bool :=
  if a == b then some true
  else match keyLit? a, keyLit? b with
    | some x, some y => some (x == y)
    | _, _ => none

/-- A reflected footprint's entries: bindings and properties, by atom index. -/
partial def sfootEntries (sf : Expr) : MetaM (Array (Nat × Expr) × Array (Nat × Expr)) := do
  if sf.isAppOfArity ``SFoot.union 2 then
    let (b1, p1) ← sfootEntries sf.appFn!.appArg!
    let (b2, p2) ← sfootEntries sf.appArg!
    return (b1 ++ b2, p1 ++ p2)
  if sf.isAppOfArity ``SFoot.mk 3 then
    let args := sf.getAppArgs
    let some bs ← listElems args[0]! 4096 | throwError "facts_apart: footprint"
    let some ps ← listElems args[1]! 4096 | throwError "facts_apart: footprint"
    let ent (q : Expr) : Option (Nat × Expr) := do
      guard (q.isAppOfArity ``Prod.mk 4)
      let i ← q.appFn!.appArg!.rawNatLit? <|> q.appFn!.appArg!.nat?
      return (i, q.appArg!)
    return (bs.filterMap ent, ps.filterMap ent)
  throwError "facts_apart: footprint {sf}"

/-- The pairs of atoms a reflected place needs distinct against the footprint's entries (`none`: it is inside). -/
def placePairs (A : AtomsB) (fbs fps : Array (Nat × Expr)) (r : Expr) :
    MetaM (Option (Array (Nat × Nat) × Array (Nat × Nat))) := do
  let args := r.getAppArgs
  let idx (e : Expr) : Nat := (e.rawNatLit? <|> e.nat?).getD 0
  let _ := A
  let mut po : Array (Nat × Nat) := #[]
  let mut pe : Array (Nat × Nat) := #[]
  match r.getAppFn.constName? with
  | some ``RLoc.prop =>
    let o := idx args[0]!; let k := args[1]!
    for (j, k') in fps do
      match keyEq? k k' with
      | some false => pure ()
      | _ => if j == o then return none else po := po.push (o, j)
  | some ``RLoc.bind =>
    let e := idx args[0]!; let x := args[1]!
    for (j, x') in fbs do
      match keyEq? x x' with
      | some false => pure ()
      | _ => if j == e then return none else pe := pe.push (e, j)
  | some ``RLoc.recordAll =>
    let e := idx args[0]!
    for (j, _) in fbs do
      if j == e then return none else pe := pe.push (e, j)
  | some ``RLoc.objAll =>
    let o := idx args[0]!
    for (j, _) in fps do
      if j == o then return none else po := po.push (o, j)
  | _ => pure ()
  return some (po, pe)

/-- Reflects a fact list and a footprint: the atoms, the places, the footprint, its entries. -/
def reflectAll (fp L : Expr) : MetaM (AtomsB × Array Expr × Array Expr × Expr × Array (Nat × Expr) × Array (Nat × Expr)) := do
  let some elems ← listElems L 4096 | throwError "facts: the facts are not a list: {L}"
  let mut A : AtomsB := {}
  let mut rs : Array Expr := #[]
  for x in elems do
    let some (A', r) ← reflectLoc A (mkApp (mkConst ``Fact.loc) x) | throwError "facts: a place not reflected: {x}"
    A := A'
    rs := rs.push r
  let some (A', sf) ← reflectFoot A fp 64 | throwError "facts: the footprint not reflected: {fp}"
  A := A'
  let (fbs, fps) ← sfootEntries sf
  return (A, elems, rs, sf, fbs, fps)

/-- A proof of `x ≠ y` by assumption or `omega`, if one closes it. -/
def closeNe (x y : Expr) : TermElabM (Option Expr) := do
  let mv ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``Ne #[x, y]) `ne
  let saved ← saveState
  let tac ← `(tactic| first | assumption | exact Ne.symm (by assumption) | omega)
  try
    let rem ← Term.withoutErrToSorry <| Tactic.run mv.mvarId! (Tactic.withoutRecover (Tactic.evalTactic tac))
    if rem.isEmpty then return some (← instantiateMVars mv) else saved.restore; return none
  catch _ => saved.restore; return none

/-- `Facts.Apart fp L` from the needed pairs' proofs (`ne`: a proof or the goal left). -/
def apartProof (fp L : Expr) (A : AtomsB) (rs : Array Expr) (sf : Expr) (po pe : Array (Nat × Nat))
    (neO neE : Array Expr) : MetaM Expr := do
  let U := mkApp2 (mkConst ``Atoms.mk) (← mkListLit (mkConst ``ES.ObjId) A.objs.toList)
    (← mkListLit (mkConst ``ES.EnvId) A.envs.toList)
  let pairTy ← mkAppM ``Prod #[mkConst ``Nat, mkConst ``Nat]
  let mkPairs (l : Array (Nat × Nat)) : MetaM Expr := do
    mkListLit pairTy (← l.toList.mapM fun (i, j) => mkAppM ``Prod.mk #[mkNatLit i, mkNatLit j])
  let poL ← mkPairs po
  let peL ← mkPairs pe
  let allOf (ps : Array Expr) : MetaM Expr := ps.foldrM (fun p acc => mkAppM ``And.intro #[p, acc]) (mkConst ``True.intro)
  let rsL ← mkListLit (mkConst ``RLoc) rs.toList
  let lhs ← mkAppM ``List.map #[mkConst ``Fact.loc, L]
  let rhs ← mkAppM ``List.map #[mkApp (mkConst ``RLoc.eval) U, rsL]
  let hl ← mkExpectedTypeHint (← mkEqRefl lhs) (← mkEq lhs rhs)
  let chk ← mkAppM ``List.all #[rsL, mkApp3 (mkConst ``RLoc.covered) sf poL peL]
  let hc ← mkExpectedTypeHint (← mkEqRefl (mkConst ``Bool.true)) (← mkEq chk (mkConst ``Bool.true))
  let neTy (sel : Name) : MetaM Expr := withLocalDeclD `p pairTy fun p => do
    mkLambdaFVars #[p] (← mkAppM ``Ne #[← mkAppM sel #[U, ← mkAppM ``Prod.fst #[p]], ← mkAppM sel #[U, ← mkAppM ``Prod.snd #[p]]])
  let ho ← mkExpectedTypeHint (← allOf neO) (mkApp2 (mkApp (mkConst ``AllP) pairTy) (← neTy ``Atoms.obj) poL)
  let he ← mkExpectedTypeHint (← allOf neE) (mkApp2 (mkApp (mkConst ``AllP) pairTy) (← neTy ``Atoms.env) peL)
  let prf := mkAppN (mkConst ``Facts.apart_pairs) #[U, sf, L, rsL, poL, peL, hl, hc, ho, he]
  -- (the reflection's evaluation is the footprint by definition: left to the kernel, whose lazy unfolding is cheap
  -- where the elaborator's is not)
  mkExpectedTypeHint prf (mkApp2 (mkConst ``Logic.Facts.Apart) fp L)

/-- `facts_apart` proves `Facts.Apart fp L` (`L` a list of facts) by reflection, leaving one goal `o ≠ o'` (or
`e ≠ e'`) for each object (record) of a fact and of the footprint under the same key — closed here when an assumption
or `omega` does — and failing when a fact's place is in the footprint. -/
elab "facts_apart" : tactic => Tactic.withMainContext do
  let g ← Tactic.getMainGoal
  let t ← whnfR (← instantiateMVars (← g.getType))
  unless t.isAppOfArity ``Logic.Facts.Apart 2 do throwError "facts_apart: not `Facts.Apart fp L`: {t}"
  let fp := t.appFn!.appArg!
  let L := t.appArg!
  let (A, elems, rs, sf, fbs, fps) ← reflectAll fp L
  let dedup (l : Array (Nat × Nat)) : Array (Nat × Nat) := l.foldl (fun acc p => if acc.contains p then acc else acc.push p) #[]
  let mut po : Array (Nat × Nat) := #[]
  let mut pe : Array (Nat × Nat) := #[]
  for r in rs, x in elems do
    let some (a, b) ← placePairs A fbs fps r | throwError "facts_apart: {x}'s place is in the footprint"
    po := po ++ a; pe := pe ++ b
  po := dedup po; pe := dedup pe
  let mut left : Array MVarId := #[]
  let mut neO : Array Expr := #[]
  for (i, j) in po do
    match ← closeNe A.objs[i]! A.objs[j]! with
    | some p => neO := neO.push p
    | none => let mv ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``Ne #[A.objs[i]!, A.objs[j]!]) `ne
              left := left.push mv.mvarId!; neO := neO.push mv
  let mut neE : Array Expr := #[]
  for (i, j) in pe do
    match ← closeNe A.envs[i]! A.envs[j]! with
    | some p => neE := neE.push p
    | none => let mv ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``Ne #[A.envs[i]!, A.envs[j]!]) `ne
              left := left.push mv.mvarId!; neE := neE.push mv
  g.assign (← apartProof fp L A rs sf po pe neO neE)
  Tactic.replaceMainGoal left.toList

/-- `h`, or its last conjunct (a spec's `Pre`: pure premises, then the facts), as `Facts.holds L s`. -/
partial def factsOf (h : Expr) : MetaM Expr := do
  let ty ← whnfR (← instantiateMVars (← inferType h))
  if ty.isAppOfArity ``Logic.Facts.holds 2 then return h
  if ty.isAppOfArity ``And 2 then return ← factsOf (mkProj ``And 1 h)
  let ty' ← whnf ty
  if ty'.isAppOfArity ``Logic.Facts.holds 2 then return ← mkExpectedTypeHint h ty'
  if ty'.isAppOfArity ``And 2 then return ← factsOf (← mkExpectedTypeHint (mkProj ``And 1 h) ty'.appArg!)
  throwError "facts: {h} is not `Facts.holds L s` (nor a `Pre`)"

/-- The facts of `hE : Facts.holds L s` that the frame `hFE : Frame fp s w` misses (each needed distinctness closed
by an assumption or `omega`), carried to `w`: `(L', its proof)`. -/
def carry (hE hFE : Expr) : TermElabM (Expr × Expr × Nat × Nat) := do
  let hE ← factsOf hE
  let hTy ← whnfR (← instantiateMVars (← inferType hE))
  let fTy ← whnfR (← instantiateMVars (← inferType hFE))
  unless fTy.isAppOfArity ``Logic.Frame 3 do throwError "facts: not a frame: {fTy}"
  let L := hTy.appFn!.appArg!
  let s := hTy.appArg!
  let fp := fTy.appFn!.appFn!.appArg!
  let w := fTy.appArg!
  unless ← isDefEq fTy.appFn!.appArg! s do throwError "facts: the frame does not start at {s}"
  let (A, elems, rs, _, fbs, fps) ← reflectAll fp L
  -- the facts kept: their pairs closed
  let mut cache : Array ((Bool × Nat × Nat) × Option Expr) := #[]
  let mut keep : Array Nat := #[]
  for k in [:elems.size] do
    let some (a, b) ← placePairs A fbs fps rs[k]! | continue
    let mut ok := true
    for (i, j) in a do
      if ok then
        match cache.find? (·.1 == (true, i, j)) with
        | some (_, r) => ok := r.isSome
        | none => let r ← closeNe A.objs[i]! A.objs[j]!; cache := cache.push ((true, i, j), r); ok := r.isSome
    for (i, j) in b do
      if ok then
        match cache.find? (·.1 == (false, i, j)) with
        | some (_, r) => ok := r.isSome
        | none => let r ← closeNe A.envs[i]! A.envs[j]!; cache := cache.push ((false, i, j), r); ok := r.isSome
    if ok then keep := keep.push k
  let L' ← mkListLit (mkConst ``Logic.Fact) (keep.toList.map (elems[·]!))
  -- `Facts.holds L' s`, picked from `h`
  let mut hl ← mkAppOptM ``Logic.Facts.holds_nil #[s]
  let mut tl := mkApp (mkConst ``List.nil [Level.zero]) (mkConst ``Logic.Fact)
  for k in keep.reverse do
    let hm ← mkDecideProof (← mkAppM ``LT.lt #[mkNatLit k, ← mkAppM ``List.length #[L]])
    let gk ← mkAppOptM ``Logic.Facts.get #[L, s, hE, mkNatLit k, hm]
    hl ← mkAppOptM ``Logic.Facts.holds_cons #[elems[k]!, tl, s, gk, hl]
    tl := mkApp3 (mkConst ``List.cons [Level.zero]) (mkConst ``Logic.Fact) elems[k]! tl
  -- its places apart from `fp`
  let (A2, _, rs2, sf2, fbs2, fps2) ← reflectAll fp L'
  let mut po : Array (Nat × Nat) := #[]
  let mut pe : Array (Nat × Nat) := #[]
  for r in rs2 do
    let some (a, b) ← placePairs A2 fbs2 fps2 r | throwError "facts: internal"
    po := po ++ a; pe := pe ++ b
  let dedup (l : Array (Nat × Nat)) : Array (Nat × Nat) := l.foldl (fun acc p => if acc.contains p then acc else acc.push p) #[]
  po := dedup po; pe := dedup pe
  let neO ← po.mapM fun (i, j) => do
    let some p ← closeNe A2.objs[i]! A2.objs[j]! | throwError "facts: internal ne"
    return p
  let neE ← pe.mapM fun (i, j) => do
    let some p ← closeNe A2.envs[i]! A2.envs[j]! | throwError "facts: internal ne"
    return p
  let hap ← apartProof fp L' A2 rs2 sf2 po pe neO neE
  let prf ← mkAppOptM ``Logic.Facts.frame #[fp, s, w, hFE, L', hap, hl]
  let ty := mkApp2 (mkConst ``Logic.Facts.holds) L' w
  return (L', prf, keep.size, elems.size)

/-- `facts_frame h hF as h'`: from `h : Facts.holds L s` and `hF : Frame fp s w`, `h' : Facts.holds L' w` with `L'`
the facts of `L` whose places `fp` misses, each needed distinctness closed by an assumption or `omega` (the others
dropped). -/
elab "facts_frame " h:term:max hF:term:max " as " n:ident : tactic => Tactic.withMainContext do
  let hE ← Term.elabTerm h none
  let hFE ← Term.elabTerm hF none
  let (L', prf, nk, ne) ← carry hE hFE
  let fTy ← whnfR (← instantiateMVars (← inferType hFE))
  let ty := mkApp2 (mkConst ``Logic.Facts.holds) L' fTy.appArg!
  let g ← Tactic.getMainGoal
  let (_, g') ← (← g.assert n.getId ty prf).intro1P
  Tactic.replaceMainGoal [g']
  logInfo m!"facts_frame: {nk} of {ne} facts kept"

/-- `facts_get h` (`h : Facts.holds L s`) closes the goal with one of `L`'s facts: its statement, either half (the
existence, the read), or a binding's predicate read in a record whose map an assumption gives. -/
elab "facts_get " h:term:max : tactic => Tactic.withMainContext do
  let hE ← factsOf (← Term.elabTerm h none)
  let hTy ← whnfR (← instantiateMVars (← inferType hE))
  let L := hTy.appFn!.appArg!
  let s := hTy.appArg!
  let some elems ← listElems L 4096 | throwError "facts_get: the facts are not a list"
  let g ← Tactic.getMainGoal
  let goal0 ← instantiateMVars (← g.getType)
  -- a definition at the head (`Writable bm x`) unfolded once: the candidates are matched reducibly
  let goal ← match goal0.getAppFn.constName? with
    | some c => if [``Eq, ``And, ``Exists, ``LT.lt, ``Ne, ``Not].contains c then pure goal0 else
        match ← unfoldDefinition? goal0 with
        | some u => pure u.headBeta
        | none => pure goal0
    | none => pure goal0
  let goal ← match goal.getAppFn with
    | .proj .. => whnf goal
    | _ => pure goal
  -- the records' maps in the context
  let decls ← (← getLCtx).foldlM (init := #[]) fun acc d => do
    if d.isImplementationDetail then return acc
    let t ← instantiateMVars d.type
    if (declLikeOf? s t).isSome then return acc.push d.toExpr else return acc
  for k in [:elems.size] do
    let hm ← mkDecideProof (← mkAppM ``LT.lt #[mkNatLit k, ← mkAppM ``List.length #[L]])
    let gk ← mkAppOptM ``Logic.Facts.get #[L, s, hE, mkNatLit k, hm]
    let gk0 := gk
    let ty ← whnf (← instantiateMVars (mkApp (mkProj ``Logic.Fact 1 elems[k]!) s))
    let gk ← mkExpectedTypeHint gk ty
    let mut cands : Array Expr := #[gk]
    if ty.isAppOfArity ``And 2 then
      cands := cands ++ #[← mkExpectedTypeHint (mkProj ``And 0 gk) ty.appFn!.appArg!,
        ← mkExpectedTypeHint (mkProj ``And 1 gk) ty.appArg!]
    let f ← whnfR elems[k]!
    if f.isAppOfArity ``Logic.Fact.bind 4 then
      for hd in decls do
        let gkF ← mkExpectedTypeHint gk0 (mkApp2 (mkConst ``Logic.Fact.holds) elems[k]! s)
        try cands := cands.push (← mkAppOptM ``Logic.Fact.bind_get #[none, none, none, none, s, none, hd, gkF])
        catch _ => pure ()
    for c in cands do
      let saved ← saveState
      try
        if ← withReducible (isDefEq (← inferType c) goal) then
          g.assign c
          Tactic.replaceMainGoal []
          return
        saved.restore
      catch _ => saved.restore
  throwError "facts_get: no fact of {h} ({elems.size} facts at {s}) gives the goal{indentExpr goal}"

elab "facts_form " id:ident : command => do
  let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  liftTermElabM (factsForm n)

/-! ## A spec's postcondition as facts

`facts_post T` (`T.ofPre` declared: by `facts_form` or `facts_compose`) declares `T.PL vars`, the conjuncts of `T`'s
postcondition `fun v w h' => …` that are facts about `w` (an object's property read as `= some p` or under
existentials; a record with lookups of its bindings, `∃ bm, Scope.declLike? (w.envEntry E) = some (bm, oG) ∧ …`),
`T.post_facts : post v w h' → Facts.holds (T.PL vars) w ∧ (the other conjuncts)`, and `T.PLex objs w`: the facts with
every variable but the objects, records and functions existential (what a later step can be told about this one's
result). An existence the post does not state (`o < w.heap.size`) follows from the read (a missing object has no
properties, a missing record no bindings). -/

/-- `∀ xs, b` with `xs` implicit. -/
def mkForallImplicit (xs : Array Expr) (b : Expr) : MetaM Expr := do
  let t ← mkForallFVars xs b
  let rec go (t : Expr) (n : Nat) : Expr :=
    match n, t with
    | n + 1, .forallE nm d bd _ => .forallE nm d (go bd n) .implicit
    | _, t => t
  return go t xs.size

/-- The first `n` binders of a `∀`/`fun` made explicit. -/
def explicitBinders (t : Expr) (n : Nat) : Expr :=
  match n, t with
  | n + 1, .forallE nm d b _ => .forallE nm d (explicitBinders b n) .default
  | n + 1, .lam nm d b _ => .lam nm d (explicitBinders b n) .default
  | _, t => t

/-- `∃ xs, b`. -/
def existsFVars (xs : Array Expr) (b : Expr) : MetaM Expr :=
  xs.foldrM (fun x acc => do mkAppM ``Exists #[← mkLambdaFVars #[x] acc]) b

/-- The conjuncts of a right-nested `∧`. -/
partial def conjuncts (e : Expr) : Array Expr :=
  if e.isAppOfArity ``And 2 then #[e.appFn!.appArg!] ++ conjuncts e.appArg! else #[e]

/-- `(w.objEntry o).props.get? k` in `t`: `(o, k, the read)`. -/
def propRead? (w t : Expr) : Option (Expr × Expr × Expr) :=
  (t.find? fun e => e.isAppOfArity ``ES.PropMap.get? 2 && e.appFn!.appArg!.isAppOfArity ``ES.Obj.props 1 &&
    (objEntryOf? w e.appFn!.appArg!.appArg!).isSome).bind fun e => do
      let o ← objEntryOf? w e.appFn!.appArg!.appArg!
      return (o, e.appArg!, e)

/-- `bm[x]?` in `t`: `(x, the lookup)`. -/
def lookupRead? (bm t : Expr) : Option (Expr × Expr) :=
  (t.find? fun e => e.isAppOf ``GetElem?.getElem? && e.getAppNumArgs ≥ 2 &&
    e.getAppArgs[e.getAppNumArgs - 2]! == bm).map fun e => (e.getAppArgs[e.getAppNumArgs - 1]!, e)

/-- Every conjunct of nested `∧`s with its projections (`false`: `.1`, `true`: `.2`, outermost first). -/
partial def flatConj (e : Expr) (path : Array Bool := #[]) : Array (Expr × Array Bool) :=
  if e.isAppOfArity ``And 2 then flatConj e.appFn!.appArg! (path.push false) ++ flatConj e.appArg! (path.push true)
  else #[(e, path)]

def projPath (h : Expr) (path : Array Bool) : Expr :=
  path.foldl (fun acc b => mkProj ``And (if b then 1 else 0) acc) h

/-- A proof of `¬ P none` for a read's predicate (`none = some …`, possibly under `∃` and `∧`). -/
def bySimp (t : Expr) : TermElabM (Option Expr) := do
  let mv ← mkFreshExprSyntheticOpaqueMVar t
  let saved ← saveState
  try
    let tac ← `(tactic| simp only [reduceCtorEq, false_and, and_false, exists_false, exists_const, not_false_eq_true, Option.some_ne_none, Option.noConfusion])
    let rem ← Term.withoutErrToSorry <| Tactic.run mv.mvarId! (Tactic.withoutRecover (Tactic.evalTactic tac))
    if rem.isEmpty then return some (← instantiateMVars mv) else saved.restore; return none
  catch _ => saved.restore; return none

/-- `fun x => body` with `pat` abstracted, when nothing of `avoid` is left. -/
def abstractOut (pat t : Expr) (ty : Expr) (avoid : Array Expr) : MetaM (Option Expr) := do
  let b ← kabstract t pat
  let P := mkLambda `r .default ty b
  if avoid.any (fun a => P.containsFVar a.fvarId!) then return none
  return some P

/-- The conjuncts with their proofs, `∧` split and `∃ x, …` (of a value, mentioning `w`) opened: `k` gets them, the
variables opened, and the openings `(proof of ∃, its predicate, x, hx)` to close the final proof with. -/
partial def openConj {α} (w : Expr) (items : List (Expr × Expr)) (acc : Array (Expr × Expr)) (bound : Array Expr)
    (opened : Array (Expr × Expr × Expr × Expr))
    (k : Array (Expr × Expr) → Array Expr → Array (Expr × Expr × Expr × Expr) → TermElabM α) : TermElabM α := do
  match items with
  | [] => k acc bound opened
  | (c, p) :: rest =>
    if c.isAppOfArity ``And 2 then
      openConj w ((c.appFn!.appArg!, mkProj ``And 0 p) :: (c.appArg!, mkProj ``And 1 p) :: rest) acc bound opened k
    else if c.isAppOfArity ``Exists 2 && c.appArg!.isLambda && c.containsFVar w.fvarId! &&
        !(← isProp c.appFn!.appArg!) then
      let lam := c.appArg!
      -- only an `∃` whose body is a conjunction (a record's `∃ bm, …` is a fact, not opened)
      let body0 := lam.bindingBody!
      let rec underEx (e : Expr) (fuel : Nat) : Expr :=
        match fuel with
        | 0 => e
        | f + 1 => if e.isAppOfArity ``Exists 2 && e.appArg!.isLambda then underEx e.appArg!.bindingBody! f else e
      let inner0 := underEx body0 16
      if !inner0.isAppOfArity ``And 2 ||
          (inner0.isAppOfArity ``And 2 && (inner0.appFn!.appArg!.isAppOfArity ``Eq 3 &&
            inner0.appFn!.appArg!.appFn!.appArg!.isAppOf ``Scope.declLike?)) ||
          (body0.isAppOfArity ``And 2 && (declLikeOf? w (body0.appFn!.appArg!)).isSome) ||
          (body0.isAppOfArity ``And 2 && body0.appFn!.appArg!.isAppOfArity ``Eq 3 &&
            (body0.appFn!.appArg!.appFn!.appArg!.isAppOf ``Scope.declLike?)) then
        openConj w rest (acc.push (c, p)) bound opened k
      else
        withLocalDeclD lam.bindingName! lam.bindingDomain! fun x => do
          let b := lam.bindingBody!.instantiate1 x
          withLocalDeclD `hx b fun hx => do
            openConj w ((b, hx) :: rest) acc (bound.push x) (opened.push (p, lam, x, hx)) k
    else if c.getAppFn.isConst && !c.isAppOf ``Eq && !c.isAppOf ``Exists && c.containsFVar w.fvarId! then
      -- a definition that is a conjunction (`NewProps`): its conjuncts
      match ← unfoldDefinition? c with
      | some u =>
        let u ← whnfCore u
        if u.isAppOfArity ``And 2 || u.isAppOfArity ``Exists 2 then openConj w ((u, p) :: rest) acc bound opened k
        else openConj w rest (acc.push (c, p)) bound opened k
      | none => openConj w rest (acc.push (c, p)) bound opened k
    else openConj w rest (acc.push (c, p)) bound opened k

/-- `∃ xs, t` proved from the witnesses `xs` (locals) and `pf : t`. -/
def existsIntro (xs : Array Expr) (t pf : Expr) : MetaM Expr := do
  let mut ty := t
  let mut pr := pf
  for x in xs.reverse do
    let lam ← mkLambdaFVars #[x] ty
    pr ← mkAppOptM ``Exists.intro #[← inferType x, lam, x, pr]
    ty ← mkAppM ``Exists #[lam]
  return pr

/-- Declares `T.PL`, `T.post_facts`, `T.PLex`. -/
def factsPost (n : Name) : TermElabM Unit := do
  let ci ← getConstInfo n
  forallTelescope ci.type fun xs concl => do
    unless concl.isAppOf ``Logic.WP do throwError "facts_post: {n} does not conclude WP"
    let Q := concl.appArg!
    let vars ← xs.filterM fun x => return !(← isProp (← inferType x))
    lambdaTelescope Q fun vwh body => do
      unless vwh.size == 3 do throwError "facts_post: the postcondition is not `fun v w h' => …`"
      let v := vwh[0]!; let w := vwh[1]!; let hh := vwh[2]!
      withLocalDeclD `hq body fun hq => do
      openConj w [(body, hq)] #[] #[] #[] fun items bound opened => do
      let mut facts : Array Expr := #[]
      let mut prfs : Array Expr := #[]
      let mut rest : Array (Expr × Expr) := #[]
      let optProp ← mkAppM ``Option #[mkConst ``ES.Property]
      let optBind ← mkAppM ``Option #[mkConst ``ES.Binding]
      let noneP ← mkAppOptM ``Option.none #[mkConst ``ES.Property]
      let noneB ← mkAppOptM ``Option.none #[mkConst ``ES.Binding]
      -- the objects whose existence is stated
      let mut exist : Array (Expr × Expr) := #[]
      for (c, hc) in items do
        if let some o := sizeLtOf? w c ``ES.State.heap then exist := exist.push (o, hc)
      for (c, hc) in items do
        if c.containsFVar v.fvarId! || c.containsFVar hh.fvarId! || !c.containsFVar w.fvarId! then
          rest := rest.push (c, hc); continue
        -- an existence
        if let some o := sizeLtOf? w c ``ES.State.heap then
          facts := facts.push (mkApp2 (mkConst ``Logic.Fact.kindP) o (mkLambda `K .default (mkConst ``ES.Kind) (mkConst ``True)))
          prfs := prfs.push (← mkAppM ``And.intro #[hc, mkConst ``True.intro])
          continue
        -- a property
        if let some (o, k, rd) := propRead? w c then
          if !o.containsFVar w.fvarId! && !k.containsFVar w.fvarId! then
            if let some P ← abstractOut rd c optProp #[w] then
              if let some hn ← bySimp (mkNot (P.beta #[noneP])) then
                let ex ← mkAppOptM ``Logic.lt_of_props_P #[w, o, k, P, hc, hn]
                let exact? : Option Expr := match c.eq? with
                  | some (_, l, r) => if l == rd && !r.containsFVar w.fvarId! then some r else none
                  | none => none
                match exact? with
                | some r => facts := facts.push (mkApp3 (mkConst ``Logic.Fact.prop) o k r)
                | none => facts := facts.push (mkApp3 (mkConst ``Logic.Fact.propP) o k P)
                prfs := prfs.push (← mkAppM ``And.intro #[ex, hc])
                continue
        -- an object whose existence is stated: its kind, prototype, a property read as anything, all of it
        if let some o := (c.find? fun e => (objEntryOf? w e).isSome).bind (objEntryOf? w ·) then
          if let some (_, he) := exist.find? (·.1 == o) then
            let pat := mkApp2 (mkConst ``ES.State.objEntry) w o
            let b ← kabstract c pat
            if !b.containsFVar w.fvarId! then
              let kindPat := mkApp (mkConst ``ES.Obj.kind) (.bvar 0)
              let _ := kindPat
              let P := mkLambda `ob .default (mkConst ``ES.Obj) b
              -- the whole entry (keys, kind, prototype, a read): `objP`, read through every property
              facts := facts.push (mkApp2 (mkConst ``Logic.Fact.objP) o P)
              prfs := prfs.push (← mkAppM ``And.intro #[he, hc])
              continue
        -- a record with lookups
        if c.isAppOfArity ``Exists 2 && c.appArg!.isLambda then
          let lam := c.appArg!
          let ok ← withLocalDeclD lam.bindingName! lam.bindingDomain! fun bm => do
            let b := lam.bindingBody!.instantiate1 bm
            let fl := flatConj b
            let ls := fl.map (·.1)
            let some (E, bm', oG) := declLikeOf? w ls[0]! | return none
            unless bm' == bm && !E.containsFVar w.fvarId! && !oG.containsFVar w.fvarId! && ls.size ≥ 2 do return none
            let mut bfs : Array (Expr × Expr) := #[]
            for j in [1:ls.size] do
              let some (x, lk) := lookupRead? bm ls[j]! | return none
              if x.containsFVar bm.fvarId! || x.containsFVar w.fvarId! then return none
              let some P ← abstractOut lk ls[j]! optBind #[w, bm] | return none
              bfs := bfs.push (x, P)
            let mut ex? : Option (Nat × Expr) := none
            for j in [:bfs.size] do
              if ex?.isNone then
                if let some hn ← bySimp (mkNot (bfs[j]!.2.beta #[noneB])) then ex? := some (j, hn)
            let some (j0, hn0) := ex? | return none
            let mkProof (fact : Expr) (k : Expr → Expr → MetaM Expr) : MetaM Expr := do
              let hty ← whnfR (mkApp (mkProj ``Logic.Fact 1 fact) w)
              withLocalDeclD `hb b fun hb => do
                let inner ← k bm hb
                mkAppOptM ``Exists.elim #[none, lam, hty, hc, ← mkLambdaFVars #[bm, hb] inner]
            let exOf (bm hb : Expr) : MetaM Expr := do
              let (x0, P0) := bfs[j0]!
              mkAppOptM ``Logic.lt_of_bind_P #[w, E, bm, oG, x0, P0, projPath hb fl[0]!.2, projPath hb fl[j0 + 1]!.2, hn0]
            let recF := mkApp2 (mkConst ``Logic.Fact.record) E oG
            let bsTy ← inferType bm
            let rp ← mkProof recF fun bm hb => do
              let pred ← withLocalDeclD `bs bsTy fun bs => do mkLambdaFVars #[bs] (← declLikeEq w E bs oG)
              mkAppM ``And.intro #[← exOf bm hb, ← mkAppOptM ``Exists.intro #[none, pred, bm, projPath hb fl[0]!.2]]
            let mut out : Array (Expr × Expr) := #[(recF, rp)]
            for j in [:bfs.size] do
              let (x, P) := bfs[j]!
              let f := mkApp4 (mkConst ``Logic.Fact.bind) E oG x P
              let pf ← mkProof f fun bm hb => do
                let pred ← withLocalDeclD `bs bsTy fun bs => do
                  mkLambdaFVars #[bs] (mkAnd (← declLikeEq w E bs oG) (P.beta #[← mkAppM ``GetElem?.getElem? #[bs, x]]))
                mkAppM ``And.intro #[← exOf bm hb, ← mkAppOptM ``Exists.intro #[none, pred, bm,
                  ← mkAppM ``And.intro #[projPath hb fl[0]!.2, projPath hb fl[j + 1]!.2]]]
              out := out.push (f, pf)
            return some out
          if let some out := ok then
            for (f, pf) in out do facts := facts.push f; prfs := prfs.push pf
            continue
        rest := rest.push (c, hc)
      if facts.isEmpty then
        -- no facts: only `T.Post`, over the variables the post mentions
        let mut used : Array Expr := #[]
        for x in vars.reverse do
          let inUsed ← used.anyM fun u => return (← inferType u).containsFVar x.fvarId!
          if body.containsFVar x.fvarId! || inUsed ||
              (← [v, w, hh].anyM fun u => return (← inferType u).containsFVar x.fvarId!) then
            used := #[x] ++ used
        let postV := explicitBinders (← instantiateMVars (← mkLambdaFVars (used ++ #[v, w, hh]) body)) (used.size + 3)
        let postT := explicitBinders (← instantiateMVars (← mkForallFVars (used ++ #[v, w, hh]) (mkSort .zero))) (used.size + 3)
        addDecl (Declaration.defnDecl (mkDefinitionValEx (Name.mkStr n "Post") ci.levelParams postT postV .abbrev .safe []))
        logInfo m!"{n}: no post facts; Post declared over {used.size} variables"
        return
      let L ← mkListLit (mkConst ``Logic.Fact) facts.toList
      let params := (vars ++ bound).filter fun x => L.containsFVar x.fvarId!
      let lps := ci.levelParams.map mkLevelParam
      let plName := Name.mkStr n "PL"
      let plT := explicitBinders (← instantiateMVars (← mkForallFVars params (mkApp (mkConst ``List [Level.zero]) (mkConst ``Logic.Fact)))) params.size
      let plV := explicitBinders (← instantiateMVars (← mkLambdaFVars params L)) params.size
      addDecl (Declaration.defnDecl (mkDefinitionValEx plName ci.levelParams plT plV .abbrev .safe []))
      let PLc := mkAppN (mkConst plName lps) params
      let holdsW := mkApp2 (mkConst ``Logic.Facts.holds) PLc w
      let mut hl ← mkAppOptM ``Logic.Facts.holds_nil #[w]
      let mut tl := mkApp (mkConst ``List.nil [Level.zero]) (mkConst ``Logic.Fact)
      for k in (List.range facts.size).reverse do
        hl ← mkAppOptM ``Logic.Facts.holds_cons #[facts[k]!, tl, w, prfs[k]!, hl]
        tl := mkApp3 (mkConst ``List.cons [Level.zero]) (mkConst ``Logic.Fact) facts[k]! tl
      let hlT ← mkExpectedTypeHint hl holdsW
      let restTy := if rest.isEmpty then mkConst ``True else rest.pop.foldr (fun t acc => mkAnd t.1 acc) rest.back!.1
      let mut rp : Expr := mkConst ``True.intro
      if !rest.isEmpty then
        rp := rest.back!.2
        for k in (List.range (rest.size - 1)).reverse do
          rp ← mkAppM ``And.intro #[rest[k]!.2, rp]
      let inner := mkAnd holdsW restTy
      let mut prf ← existsIntro bound inner (← mkAppM ``And.intro #[hlT, rp])
      let S ← existsFVars bound inner
      for (pe, lam, x, hx) in opened.reverse do
        prf ← mkAppOptM ``Exists.elim #[← inferType x, lam, S, pe, ← mkLambdaFVars #[x, hx] prf]
      -- the variables the post mentions (and those their types do)
      let mut used : Array Expr := #[]
      for x in vars.reverse do
        let inUsed ← used.anyM fun u => return (← inferType u).containsFVar x.fvarId!
        if body.containsFVar x.fvarId! || inUsed ||
            (← [v, w, hh].anyM fun u => return (← inferType u).containsFVar x.fvarId!) then
          used := #[x] ++ used
      let vars := used
      -- `T.Post vars v w h'`: the postcondition, over the variables it mentions
      let postV := explicitBinders (← instantiateMVars (← mkLambdaFVars (vars ++ #[v, w, hh]) body)) (vars.size + 3)
      let postT := explicitBinders (← instantiateMVars (← mkForallFVars (vars ++ #[v, w, hh]) (mkSort .zero))) (vars.size + 3)
      addDecl (Declaration.defnDecl (mkDefinitionValEx (Name.mkStr n "Post") ci.levelParams postT postV .abbrev .safe []))
      let tyI ← instantiateMVars (← mkForallImplicit (vars ++ #[v, w, hh]) (← mkForallFVars #[hq] S))
      let valI ← instantiateMVars (← mkLambdaFVars (vars ++ #[v, w, hh, hq]) prf)
      addDecl (Declaration.thmDecl { name := Name.mkStr n "post_facts", levelParams := ci.levelParams, type := tyI, value := valI })
      -- the theorem's objects, records and functions kept, the rest existential
      let keepTy (t : Expr) : Bool := t.isConstOf ``ES.ObjId || t.isConstOf ``ES.EnvId || t.isConstOf ``ES.FuncData ||
        (t.isAppOfArity ``Option 1 && t.appArg!.isConstOf ``ES.EnvId)
      let keep ← params.filterM fun x => return !bound.contains x && keepTy (← instantiateMVars (← inferType x))
      let exs := params.filter (!keep.contains ·)
      let exTy ← existsFVars exs holdsW
      let exName := Name.mkStr n "PLex"
      let exT := explicitBinders (← instantiateMVars (← mkForallFVars (keep.push w) (mkSort .zero))) (keep.size + 1)
      let exV := explicitBinders (← instantiateMVars (← mkLambdaFVars (keep.push w) exTy)) (keep.size + 1)
      addDecl (Declaration.defnDecl (mkDefinitionValEx exName ci.levelParams exT exV .abbrev .safe []))
      -- `T.post_ex : post → T.PLex keep w`
      let exApp := mkAppN (mkConst exName lps) (keep.push w)
      let mut prfE ← existsIntro exs holdsW hlT
      prfE ← mkExpectedTypeHint prfE exApp
      for (pe, lam, x, hx) in opened.reverse do
        prfE ← mkAppOptM ``Exists.elim #[← inferType x, lam, exApp, pe, ← mkLambdaFVars #[x, hx] prfE]
      let tyE ← instantiateMVars (← mkForallImplicit (vars ++ #[v, w, hh]) (← mkForallFVars #[hq] exApp))
      let valE ← instantiateMVars (← mkLambdaFVars (vars ++ #[v, w, hh, hq]) prfE)
      addDecl (Declaration.thmDecl { name := Name.mkStr n "post_ex", levelParams := ci.levelParams, type := tyE, value := valE })
      if (← getOptions).getBool `diagnostics false then
        for (c, _) in rest do logInfo m!"rest: {(← ppExpr c).pretty.take 300}"
      -- `T.PreEx keep s`: `T.Pre` with every variable but `keep` (by name) existential
      let preName := Name.mkStr n "Pre"
      let mut preNote := ""
      if let some pci := (← getEnv).find? preName then
        let keepNames ← keep.mapM fun x => x.fvarId!.getUserName
        let r ← forallTelescope pci.type fun pvs _ => do
          let some ps ← pvs.findM? (fun x => return (← x.fvarId!.getUserName) == `s) | return none
          let mut kp : Array Expr := #[]
          for kn in keepNames do
            match ← pvs.findM? (fun x => return (← x.fvarId!.getUserName) == kn) with
            | some x => kp := kp.push x
            | none => return none
          let others := pvs.filter fun x => x != ps && !kp.contains x
          let preApp := mkAppN (mkConst preName lps) pvs
          let body ← existsFVars others preApp
          let ty := explicitBinders (← instantiateMVars (← mkForallFVars (kp.push ps) (mkSort .zero))) (kp.size + 1)
          let val := explicitBinders (← instantiateMVars (← mkLambdaFVars (kp.push ps) body)) (kp.size + 1)
          addDecl (Declaration.defnDecl (mkDefinitionValEx (Name.mkStr n "PreEx") ci.levelParams ty val .abbrev .safe []))
          -- `T.pre_ex : T.Pre vars s → T.PreEx keep s`
          let exApp := mkAppN (mkConst (Name.mkStr n "PreEx") lps) (kp.push ps)
          let pr ← withLocalDeclD `hp preApp fun hp => do
            let pf ← mkExpectedTypeHint (← existsIntro others preApp hp) exApp
            let t ← instantiateMVars (← mkForallImplicit pvs (← mkForallFVars #[hp] exApp))
            let v ← instantiateMVars (← mkLambdaFVars (pvs.push hp) pf)
            return (t, v)
          return some (ty, val, pr)
        match r with
        | some (_, _, (pt, pv)) =>
          addDecl (Declaration.thmDecl { name := Name.mkStr n "pre_ex", levelParams := ci.levelParams, type := pt, value := pv })
          preNote := "; PreEx declared"
        | none => preNote := "; no PreEx (a kept variable is not Pre's)"
      logInfo m!"{n}: kept {← keep.mapM fun x => x.fvarId!.getUserName}{preNote}"
      logInfo m!"{n}: {facts.size} post facts over {params.size} variables ({keep.size} kept in PLex, {bound.size} opened), {rest.size} other conjuncts"

elab "facts_post " id:ident : command => do
  let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  liftTermElabM (factsPost n)

end Logic.FactsForm
