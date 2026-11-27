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
* `facts_top X ob as N` declares `N`: `X` with its obligation `ob` discharged — walked with `X`'s values as unknowns
  that matching assigns; the facts not found are new start facts (`hX : Facts.holds L s`, each carried to where it is
  needed), the pure conditions left new premises (`hP`), the fuel constants their least bounds, the unknowns left
  variables.
-/

open Lean Meta Elab Command
open Logic Logic.FactsForm

namespace Logic.FactsDischarge

/-- An unknown watched for diagnosis (its first assignment logged). -/
initialize watched : IO.Ref (Option MVarId) ← IO.mkRef none

/-- Logs when the watched unknown has just been assigned. -/
def checkWatch (what : String) (goal cand : Expr) : MetaM Unit := do
  let some m ← watched.get | return
  if ← m.isAssigned then
    watched.set none
    let h ← IO.FS.Handle.mk "facts_top.progress" .append
    h.putStrLn s!"WATCH {what}: assigned {((toString (← ppExpr (← instantiateMVars (mkMVar m)))).replace "\n" " ").take 200} by goal {((toString (← ppExpr (← instantiateMVars goal))).replace "\n" " ").take 500} with {((toString (← ppExpr (← instantiateMVars cand))).replace "\n" " ").take 500}"
    h.flush

initialize seenLocals : IO.Ref (Array FVarId) ← IO.mkRef #[]

/-- Each pending goal's statement when last tried, near and far, kept across fixed points (only goals that changed
are tried again). -/
initialize triedNear : IO.Ref (Std.HashMap MVarId Expr) ← IO.mkRef {}
initialize triedFarRef : IO.Ref (Std.HashMap MVarId Expr) ← IO.mkRef {}

theorem ne_none_of_eq_some {α : Type} {o : Option α} {b : α} (h : o = some b) : o ≠ none := by
  intro hn; rw [hn] at h; cases h

/-- Two property facts about one place at one state: the same read. -/
theorem prop_same {o : ES.ObjId} {k : ES.PropKey} {r1 r2 : Option ES.Property} {s : ES.State}
    (h1 : (Logic.Fact.prop o k r1).holds s) (h2 : (Logic.Fact.prop o k r2).holds s) : r1 = r2 :=
  h1.2.symm.trans h2.2

/-- Two property facts about one place (its object named twice, `he`) at one state: the same read. -/
theorem prop_same_eq {o1 o2 : ES.ObjId} {k : ES.PropKey} {r1 r2 : Option ES.Property} {s : ES.State} (he : o1 = o2)
    (h1 : (Logic.Fact.prop o1 k r1).holds s) (h2 : (Logic.Fact.prop o2 k r2).holds s) : r1 = r2 := by
  subst he; exact prop_same h1 h2

/-- Two binding facts about one binding at one state (whatever outers they name): the same binding. -/
theorem bind_same {e : ES.EnvId} {o1 o2 : Option ES.EnvId} {x : ES.JSStr} {bd1 bd2 : ES.Binding} {s : ES.State}
    (h1 : (Logic.Fact.bind e o1 x (· = some bd1)).holds s) (h2 : (Logic.Fact.bind e o2 x (· = some bd2)).holds s) :
    bd1 = bd2 := by
  obtain ⟨-, b1, d1, p1⟩ := h1
  obtain ⟨-, b2, d2, p2⟩ := h2
  rw [d1] at d2
  cases d2
  exact Option.some.inj (p1.symm.trans p2)

/-- One binding's value read twice. -/
theorem value_same {bd1 bd2 : ES.Binding} {x v : ES.Value} (he : bd1 = bd2) (h1 : bd1.value = some x)
    (h2 : bd2.value = some v) : x = v := by
  subst he; rw [h1] at h2; exact Option.some.inj h2

/-- A record's statement for any map and outer, with the record's fact: a binding fact. -/
theorem bind_of_forall_rec {e : ES.EnvId} {o : Option ES.EnvId} {x : ES.JSStr} {Q : ES.Binding → Prop} {s : ES.State}
    (hr : (Logic.Fact.record e o).holds s)
    (h : ∀ (bm : Std.HashMap ES.JSStr ES.Binding) (o' : Option ES.EnvId), Scope.declLike? (s.envEntry e) = some (bm, o') →
      ∃ bd, bm[x]? = some bd ∧ Q bd) :
    (Logic.Fact.bind e o x (fun b => ∃ bd, b = some bd ∧ Q bd)).holds s := by
  obtain ⟨hl, bs, hd⟩ := hr
  exact ⟨hl, bs, hd, h bs o hd⟩

/-- A binding fact: the record's statement for any map and outer. -/
theorem forall_of_bind {e : ES.EnvId} {o : Option ES.EnvId} {x : ES.JSStr} {Q : ES.Binding → Prop} {s : ES.State}
    (h : (Logic.Fact.bind e o x (fun b => ∃ bd, b = some bd ∧ Q bd)).holds s) :
    ∀ (bm : Std.HashMap ES.JSStr ES.Binding) (o' : Option ES.EnvId), Scope.declLike? (s.envEntry e) = some (bm, o') →
      ∃ bd, bm[x]? = some bd ∧ Q bd := by
  intro bm o' hd
  obtain ⟨-, bs, hd', hp⟩ := h
  rw [hd] at hd'
  cases hd'
  exact hp

/-- A record's map, from its fact. -/
noncomputable def recordMap {e : ES.EnvId} {o : Option ES.EnvId} {s : ES.State} (h : (Logic.Fact.record e o).holds s) :
    Std.HashMap ES.JSStr ES.Binding :=
  Classical.choose h.2

/-- A record's fact: the record with its map (`recordMap`). -/
theorem recordIs_of_record {e : ES.EnvId} {o : Option ES.EnvId} {s : ES.State} (h : (Logic.Fact.record e o).holds s) :
    (Logic.Fact.recordIs e (recordMap h) o).holds s :=
  ⟨h.1, Classical.choose_spec h.2⟩

/-- The binding a record's statement for any map and outer gives, with the record's fact. -/
noncomputable def forallBindVal {e : ES.EnvId} {o : Option ES.EnvId} {x : ES.JSStr} {Q : ES.Binding → Prop}
    {s : ES.State} (hr : (Logic.Fact.record e o).holds s)
    (h : ∀ (bm : Std.HashMap ES.JSStr ES.Binding) (o' : Option ES.EnvId), Scope.declLike? (s.envEntry e) = some (bm, o') →
      ∃ bd, bm[x]? = some bd ∧ Q bd) : ES.Binding :=
  Classical.choose (h (recordMap hr) o (recordIs_of_record hr).2)

/-- The binding `forallBindVal` chooses satisfies the statement's `Q`. -/
theorem forallBindVal_spec {e : ES.EnvId} {o : Option ES.EnvId} {x : ES.JSStr} {Q : ES.Binding → Prop}
    {s : ES.State} (hr : (Logic.Fact.record e o).holds s)
    (h : ∀ (bm : Std.HashMap ES.JSStr ES.Binding) (o' : Option ES.EnvId), Scope.declLike? (s.envEntry e) = some (bm, o') →
      ∃ bd, bm[x]? = some bd ∧ Q bd) : Q (forallBindVal hr h) :=
  (Classical.choose_spec (h (recordMap hr) o (recordIs_of_record hr).2)).2

/-- A record's statement for any map and outer, with the record's fact: the binding fact, exact. -/
theorem bind_exact_of_forall_rec {e : ES.EnvId} {o : Option ES.EnvId} {x : ES.JSStr} {Q : ES.Binding → Prop}
    {s : ES.State} (hr : (Logic.Fact.record e o).holds s)
    (h : ∀ (bm : Std.HashMap ES.JSStr ES.Binding) (o' : Option ES.EnvId), Scope.declLike? (s.envEntry e) = some (bm, o') →
      ∃ bd, bm[x]? = some bd ∧ Q bd) :
    (Logic.Fact.bind e o x (fun b => b = some (forallBindVal hr h))).holds s :=
  ⟨hr.1, recordMap hr, (recordIs_of_record hr).2,
    (Classical.choose_spec (h (recordMap hr) o (recordIs_of_record hr).2)).1⟩

/-- A record's lookup from its binding fact, whatever outer the lookup's hypothesis names (`declLike?` is a function:
the outer is the fact's). -/
theorem bind_get_any {e : ES.EnvId} {oG o : Option ES.EnvId} {x : ES.JSStr} {P : Option ES.Binding → Prop}
    {s : ES.State} {bs : Std.HashMap ES.JSStr ES.Binding} (hd : Scope.declLike? (s.envEntry e) = some (bs, o))
    (h : (Logic.Fact.bind e oG x P).holds s) : P bs[x]? := by
  obtain ⟨-, bs', hd', hp⟩ := h
  rw [hd] at hd'
  cases hd'
  exact hp

theorem bne_of_lt_size {a b : Nat} (h : a < b) : (a != b) = true := by
  simp [Nat.ne_of_lt h]

theorem all_of_forall_mem {α : Type} {xs : List α} {p : α → Bool} (h : ∀ x, x ∈ xs → p x = true) : xs.all p = true :=
  List.all_eq_true.mpr h

/-- A closed fact through the way there and more, at the start: the more, at the end of the way. -/
theorem closed_of_path {f g : Logic.Footprint} {P : ES.State → Prop} {s w : ES.State}
    (h : (Logic.Fact.closed (f.union g) P).holds s) (hF : Logic.Frame f s w) : (Logic.Fact.closed g P).holds w :=
  fun w' hw' => h w' (Logic.frame_trans hF hw')

/-- A closed fact for a larger footprint is one for a smaller (each frame inside the smaller is inside the larger). -/
theorem closed_weaken {g f : Logic.Footprint} {P : ES.State → Prop} {s : ES.State}
    (h : (Logic.Fact.closed (g.union f) P).holds s) : (Logic.Fact.closed f P).holds s := by
  intro w hw
  exact h w (Logic.frame_mono hw (fun p hp => by simp [Logic.Footprint.union, hp])
    (fun p hp => by simp [Logic.Footprint.union, hp]) (fun hj => by simp [Logic.Footprint.union] at hj; exact hj.2))

/-- The lookups `m[k]?` in `e`, each once. -/
partial def collectLookups (e : Expr) : Array Expr :=
  let rec go (e : Expr) (acc : Array Expr) : Array Expr :=
    let acc := if e.isAppOf ``GetElem?.getElem? && !acc.contains e then acc.push e else acc
    match e with
    | .app f a => go a (go f acc)
    | .lam _ d b _ | .forallE _ d b _ => go b (go d acc)
    | .mdata _ b => go b acc
    | _ => acc
  go e #[]

/-- `i < L.length` for a list `L` known to have more than `i` elements: by `decide`, checked by the kernel only (the
elaborator does not evaluate the list's length, `mkDecideProof` would). -/
def idxLt (i : Nat) (L : Expr) : MetaM Expr := do
  let len ← mkAppM ``List.length #[L]
  let prop ← mkAppM ``LT.lt #[mkNatLit i, len]
  let inst := mkApp2 (mkConst ``Nat.decLt) (mkNatLit i) len
  return mkApp3 (mkConst ``of_decide_eq_true) prop inst (← mkEqRefl (mkConst ``Bool.true))


/-- Time spent per step kind (ns, calls), for profiling the walk and the fixed point. -/
initialize stepTimes : IO.Ref (Array (String × Nat × Nat)) ← IO.mkRef #[]

/-- Runs `x`, adding its time to step kind `k`. -/
def timed {α : Type} {m : Type → Type} [Monad m] [MonadLiftT IO m] (k : String) (x : m α) : m α := do
  let t0 ← (IO.monoNanosNow : IO Nat)
  let r ← x
  let dt := (← (IO.monoNanosNow : IO Nat)) - t0
  (stepTimes.modify fun a => match a.findIdx? (·.1 == k) with
    | some i => a.modify i fun (k', t, n) => (k', t + dt, n + 1)
    | none => a.push (k, dt, 1) : IO Unit)
  return r

/-- The step times so far, longest first. -/
def stepReport : IO String := do
  let a ← stepTimes.get
  let a := a.qsort (fun x y => x.2.1 > y.2.1)
  return String.intercalate ", " (a.toList.map fun (k, t, n) => s!"{k} {t / 1000000} ms/{n}")


/-- The top's own variables (not locals of the obligation). -/
initialize topLocals : IO.Ref (Array FVarId) ← IO.mkRef #[]

/-- The start state, for steps that state facts there. -/
initialize startState : IO.Ref (Option Expr) ← IO.mkRef none


initialize firstBad : IO.Ref Bool ← IO.mkRef false

/-- Diagnosis: `isDefEq` that logs when it gives an object unknown (type `ObjId`) a record's id. -/
def defEqLog (_what : String) (a b : Expr) : MetaM Bool := withReducible (isDefEq a b)

initialize lastStep : IO.Ref String ← IO.mkRef ""

/-- Diagnosis: logs the step at which the watched unknown is first assigned (`g`'s goal before the step). -/
def checkR (what : String) (gty : String) : MetaM Unit := do
  let some m ← watched.get | return
  if ← m.isAssigned then
    let v ← instantiateMVars (mkMVar m)
    watched.set (if v.isMVar then some v.mvarId! else none)
    let h ← IO.FS.Handle.mk "facts_top.progress" .append
    h.putStrLn s!"R-ASSIGNED after {what}: {((toString (← ppExpr v)).replace "\n" " ").take 300} | step goal: {gty} | previous: {← lastStep.get}"
    h.flush
  lastStep.set gty

/-- Fact goals and pure goals left for the fixed point. -/
initialize pendingFacts : IO.Ref (Array MVarId) ← IO.mkRef #[]
/-- Fact goals stated at the start only (never matched near: `substSame`'s, whose near match would be the read it
pins down). -/
initialize startOnly : IO.Ref (Std.HashSet MVarId) ← IO.mkRef {}
/-- `substSame`'s start reads the way from the start does not keep (by fact list and index): not asked again. -/
initialize askFailed : IO.Ref (Std.HashSet (Expr × Nat)) ← IO.mkRef {}
/-- `let` outers whose hypotheses `substOuter` restated. -/
initialize restatedLets : IO.Ref (Std.HashSet FVarId) ← IO.mkRef {}
/-- Records' outers asked at the start by `substOuter` (record, its outer's unknown, the start fact's goal). -/
initialize startRecords : IO.Ref (Array (Expr × Expr × Expr)) ← IO.mkRef #[]
/-- Conjunction goals whose identifications were made (the parts of one already scanned). -/
initialize andScanned : IO.Ref (Std.HashSet MVarId) ← IO.mkRef {}
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

/-- An object fact's object (`prop`, `propP`, `kindP`, `proto`, `objP`), instantiated. -/
def factObj? (f : Expr) : MetaM (Option Expr) := do
  -- the head followed through assignments, the object taken as it is (`objsAllow` follows it shallowly too)
  let f ← if f.getAppFn.isMVar then instantiateMVars f else pure f
  let c := f.getAppFn.constName?.getD .anonymous
  if (c == ``Logic.Fact.prop || c == ``Logic.Fact.propP || c == ``Logic.Fact.kindP || c == ``Logic.Fact.proto
      || c == ``Logic.Fact.objP) && f.getAppNumArgs ≥ 1 then
    return some f.getAppArgs[0]!
  return none

/-- Whether candidate `e` may be matched with goal `f` by objects: an object that is an unknown is never guessed (it
is matched only with itself; something else, a property pointing at it, determines it). -/
partial def followMVar (e : Expr) : MetaM Expr := do
  if !e.isMVar then return e
  match ← getExprMVarAssignment? e.mvarId! with
  | some v => followMVar v
  | none => return e

def objsAllow (e f : Expr) : MetaM Bool := do
  let some oe ← factObj? e | return true
  let some of ← factObj? f | return true
  let oe ← followMVar oe
  let of ← followMVar of
  if oe == of then return true
  -- an unknown object (unassigned, followed shallowly: no instantiation) is matched only with itself
  if oe.isMVar || of.isMVar then return false
  return true

/-- Each hypothesis that is a fact list: its state, list, and elements with their kinds and keys (computed once). -/
initialize holdsCache : IO.Ref (Std.HashMap FVarId (Option (Expr × Expr × Array (Expr × Name × String)))) ←
  IO.mkRef {}

/-- Each hypothesis's `factsOf`: the fact list's proof and state (computed once). -/
initialize factsOfCache : IO.Ref (Std.HashMap FVarId (Option (Expr × Expr × Expr × Array Expr × Array (Name × String)))) ← IO.mkRef {}

/-- The fact list a hypothesis states, from the cache: its state, list, and keyed elements (keys `?` recomputed: an
object fixed since can give one). -/
def holdsOf (d : LocalDecl) : MetaM (Option (Expr × Expr × Array (Expr × Name × String))) := do
  let r ← match (← holdsCache.get).get? d.fvarId with
    | some r => pure r
    | none => do
      let ty ← whnfR (← instantiateMVars d.type)
      let r ← if !ty.isAppOfArity ``Logic.Facts.holds 2 then pure none else do
        let L := ty.appFn!.appArg!
        match ← listElems L 4096 with
        | none => pure none
        | some elems => do
          let keyed ← elems.mapM fun e => do
            let (c, k) ← factKey e
            return (e, c, k)
          pure (some (ty.appArg!, L, keyed))
      -- a list still unknown (`?LX`) is not cached
      unless ty.getAppFn.isMVar && r.isNone do holdsCache.modify (·.insert d.fvarId r)
      pure r
  -- (a key `?` passes every filter, so it need not be recomputed when its object is fixed: the trial decides)
  return r

/-- The fact lists at `w` in the context: each hypothesis, its list's elements and their keys. -/
def sourcesAt (w : Expr) : MetaM (Array (Expr × Expr × Array (Expr × Name × String))) := do
  let mut out := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let some (w', L, keyed) ← holdsOf d | continue
    unless w' == w do continue
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
  -- each goal as last tried: unchanged (nothing it unifies with was assigned since), it is not tried again
  let mut lastTried : Array (Option Expr) := goals.map fun _ => none
  let mut progress := true
  while progress do
    progress := false
    for j in [:goals.size] do
      if proofs[j]!.isSome then continue
      let f ← instantiateMVars goals[j]!
      if lastTried[j]! == some f then continue
      lastTried := lastTried.set! j (some f)
      let ground := !f.hasExprMVar
      let mut fits : Array (Expr × Expr × Nat × Expr) := #[]
      for cnd in cands[j]! do
        let (_, _, _, e) := cnd
        unless ← objsAllow e f do continue
        let saved ← saveState
        let ok ← try (defEqLog "L126" e f) catch _ => pure false
        saved.restore
        if ok then
          fits := fits.push cnd
          if ground then break
      if fits.size == 1 || (ground && fits.size ≥ 1) then
        let (h, Ls, i, e) := fits[0]!
        let _ ← defEqLog "proveFacts" e f

        let hm ← idxLt i Ls
        let gi ← factAt Ls w h i
        proofs := proofs.set! j (some gi)
        progress := true
  let mut left : Array MVarId := #[]
  let mut miss : Array String := #[]
  let mut hl ← appFacts ``Logic.Facts.holds_nil #[w]
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
    hl ← appFacts ``Logic.Facts.holds_cons #[f, tl, w, p, hl]
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
    let (wit, _) ← if (← whnfR α).isAppOfArity ``Prod 2 then tupleMVars α else do pure (← mkFreshExprMVar α (userName := if P.isLambda then P.bindingName! else .anonymous), #[])
    let body := reduceProjs (P.beta #[wit]).headBeta
    let g' ← mkFreshExprSyntheticOpaqueMVar body
    let lvl ← getLevel α
    g.assign (mkApp4 (mkConst ``Exists.intro [lvl]) α P wit g')
    g := g'.mvarId!
    n := n + 1
  Tactic.replaceMainGoal [g]
  logInfo m!"facts_exists: {n} opened"

/-- Witnesses of propositions that `openExists` made goals, for the walk to take up. -/
initialize propWitnesses : IO.Ref (Array MVarId) ← IO.mkRef #[]

/-- One `∃` opened with fresh unknowns (a tuple's components each one): the goal for the body. -/
def openExists (g : MVarId) : MetaM (Option MVarId) := g.withContext do
  let t ← whnfR (← instantiateMVars (← g.getType))
  unless t.isAppOfArity ``Exists 2 do return none
  let α := t.appFn!.appArg!
  let P := t.appArg!
  -- (a proposition's witness, `∃ (h : p), …`, is a proof to find: a goal, walked after the rest, `propWitnesses`)
  let isPropW ← isProp α
  let (wit, _) ← if isPropW then do
      let w ← mkFreshExprSyntheticOpaqueMVar α (if P.isLambda then P.bindingName! else .anonymous)
      propWitnesses.modify (·.push w.mvarId!)
      pure (w, #[])
    else if (← whnfR α).isAppOfArity ``Prod 2 then tupleMVars α else do pure (← mkFreshExprMVar α (userName := if P.isLambda then P.bindingName! else .anonymous), #[])
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

/-- A hypothesis that is a conjunction or an existential, taken apart without an eliminator (`cases` copies the
whole goal into its motive, and the walk's goals are large): a conjunction's halves `h.1`, `h.2` as new hypotheses;
an existential's witness as `x := Classical.choose h` and its property `Classical.choose_spec h`. The new
hypotheses (taken apart in turn), the goal. -/
partial def splitHyp (g : MVarId) (h : Expr) (fuel : Nat := 64) : MetaM (Array Expr × MVarId) := do
  if fuel == 0 then return (#[h], g)
  let ty ← g.withContext do whnfR (← instantiateMVars (← inferType h))
  -- a definition whose unfolding is a conjunction or an existential: unfolded
  let ty ← if ty.isAppOfArity ``And 2 || ty.isAppOfArity ``Exists 2 then pure ty else g.withContext do
      match ← unfoldDefinition? ty with
      | some u => do
        let u ← whnfR u
        pure (if u.isAppOfArity ``And 2 || u.isAppOfArity ``Exists 2 then u else ty)
      | none => pure ty
  -- a contract's own structure of statements (`ReactPerformWork.RenderDone`): its fields (the logic's and the engine's
  -- structures, `Frame` and the like, are kept whole)
  if let some c := ty.getAppFn.constName? then
    let env ← getEnv
    let ns := c.getRoot
    if isStructure env c && !(ns == `Logic || ns == `ES || ns == `Lean || ns == `Std || c == ``And || c == ``Iff)
        && (← g.withContext (isProp ty)) then
      let fields := getStructureFields env c
      -- (only one of statements about a state: a field that is an implication, such as `Hold.get`, keeps it whole)
      let ftys ← g.withContext do
        (List.range fields.size).toArray.mapM fun i => do instantiateMVars (← inferType (mkProj c i h))
      if ftys.any (·.isForall) then return (#[h], g)
      let mut ps : Array Expr := #[]
      let mut gc := g
      for i in [:fields.size] do
        let pr := mkProj c i h
        let pty ← gc.withContext do instantiateMVars (← inferType pr)
        unless ← gc.withContext (isProp pty) do continue
        let (hi, g') ← (← gc.assert fields[i]! pty pr).intro1P
        let (p, g'') ← splitHyp g' (mkFVar hi) (fuel - 1)
        ps := ps ++ p
        gc := g''
      return (ps, gc)
  if ty.isAppOfArity ``And 2 then
    let a := ty.appFn!.appArg!; let b := ty.appArg!
    let (h1, g1) ← (← g.assert `left a (mkApp3 (mkConst ``And.left) a b h)).intro1P
    let (h2, g2) ← (← g1.assert `right b (mkApp3 (mkConst ``And.right) a b h)).intro1P
    let (p1, g3) ← splitHyp g2 (mkFVar h1) (fuel - 1)
    let (p2, g4) ← splitHyp g3 (mkFVar h2) (fuel - 1)
    return (p1 ++ p2, g4)
  if ty.isAppOfArity ``Exists 2 then
    let α := ty.appFn!.appArg!; let p := ty.appArg!
    if ← g.withContext (isProp α) then return (#[h], g)
    let lvl ← g.withContext (getLevel α)
    let wit := mkApp3 (mkConst ``Classical.choose [lvl]) α p h
    let nm := if p.isLambda then p.bindingName! else `x
    let (x, g1) ← (← g.define nm α wit).intro1P
    let spec := mkApp3 (mkConst ``Classical.choose_spec [lvl]) α p h
    let specTy := (p.beta #[mkFVar x]).headBeta
    let (hs, g2) ← (← g1.assert `spec specTy spec).intro1P
    let (ps, g3) ← splitHyp g2 (mkFVar hs) (fuel - 1)
    return (ps, g3)
  return (#[h], g)

/-- A hypothesis taken apart (see `splitHyp`): the goal. -/
def destructure (g : MVarId) (h : FVarId) : MetaM MVarId := do
  let (_, g') ← splitHyp g (mkFVar h)
  return g'
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
      let hm ← idxLt i L
      let gi ← factAt L w h i
      let hty ← whnf (mkApp2 (mkConst ``Logic.Fact.holds) elems[i]! w)
      pure (← mkExpectedTypeHint gi hty, hty)
    let (fv, g1) ← (← g.assert `nf hty gi).intro1P
    let (pieces, g2) ← splitHyp g1 (mkFVar fv)
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
    let mut hl ← appFacts ``Logic.Facts.holds_nil #[w]
    let mut tl := mkApp (mkConst ``List.nil [Level.zero]) (mkConst ``Logic.Fact)
    for (f, pf) in newFacts.reverse do
      let fh ← whnf (mkApp2 (mkConst ``Logic.Fact.holds) f w)
      hl ← appFacts ``Logic.Facts.holds_cons #[f, tl, w, ← mkExpectedTypeHint pf fh, hl]
      tl := mkApp3 (mkConst ``List.cons [Level.zero]) (mkConst ``Logic.Fact) f tl
    let (_, gE) ← (← g.assert `exact (mkApp2 (mkConst ``Logic.Facts.holds) tl w) hl).intro1P
    return gE

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
  -- an object's existence at `w` in the context
  let existsAt (w o : Expr) : MetaM (Option Expr) := do
    for e in ctx do
      let et ← instantiateMVars e.type
      if let some o' := sizeLtOf? w et ``ES.State.heap then
        if o' == o then return some e.toExpr
    return none
  for d in decls do
    let t ← instantiateMVars d.type
    -- a property's absence `(w.objEntry o).props.get? k = none`, a prototype `(w.objEntry o).proto = p`
    if let some (_, lhs, rhs) := t.eq? then
      let absent := lhs.isAppOfArity ``ES.PropMap.get? 2 && rhs.isAppOfArity ``Option.none 1 &&
        lhs.appFn!.appArg!.isAppOfArity ``ES.Obj.props 1 && lhs.appFn!.appArg!.appArg!.isAppOfArity ``ES.State.objEntry 2
      let proto := lhs.isAppOfArity ``ES.Obj.proto 1 && lhs.appArg!.isAppOfArity ``ES.State.objEntry 2
      if absent || proto then
        let oe := if absent then lhs.appFn!.appArg!.appArg! else lhs.appArg!
        let w := oe.appFn!.appArg!
        let o := oe.appArg!
        if let some hl ← existsAt w o then
          let f := if absent then mkApp3 (mkConst ``Logic.Fact.prop) o lhs.appArg! rhs
            else mkApp2 (mkConst ``Logic.Fact.proto) o rhs
          let pf ← mkExpectedTypeHint (← mkAppM ``And.intro #[hl, d.toExpr]) (mkApp2 (mkConst ``Logic.Fact.holds) f w)
          byState := push byState w f pf
        continue
    -- a record's lookup `declLike? (w.envEntry e) = some (bs, o)`, the record's existence in the context
    if let some (_, lhs, rhs) := t.eq? then
      if lhs.isAppOfArity ``Scope.declLike? 1 && rhs.isAppOfArity ``Option.some 2 && lhs.appArg!.isAppOfArity ``ES.State.envEntry 2 then
        let pr := rhs.appArg!
        if pr.isAppOfArity ``Prod.mk 4 then
          let w := lhs.appArg!.appFn!.appArg!
          let e := lhs.appArg!.appArg!
          let mut hl? : Option Expr := none
          for c in ctx do
            let ct ← instantiateMVars c.type
            if let some e' := sizeLtOf? w ct ``ES.State.envs then
              if e' == e then hl? := some c.toExpr; break
          -- else its existence from a lookup in its map that is present (`lt_of_bind_ne_none`)
          if hl?.isNone then
            for c in ctx do
              let ct ← instantiateMVars c.type
              let some (_, l2, r2) := ct.eq? | continue
              unless l2.isAppOf ``GetElem?.getElem? && r2.isAppOfArity ``Option.some 2 && l2.getAppNumArgs ≥ 2 do continue
              unless l2.getAppArgs[l2.getAppNumArgs - 2]! == pr.appFn!.appArg! do continue
              let hne ← mkAppM ``ne_none_of_eq_some #[c.toExpr]
              hl? := some (← mkAppM ``Logic.lt_of_bind_ne_none #[d.toExpr, hne])
              break
          if let some hl := hl? then
            let f := mkApp3 (mkConst ``Logic.Fact.recordIs) e pr.appFn!.appArg! pr.appArg!
            let pf ← mkExpectedTypeHint (← mkAppM ``And.intro #[hl, d.toExpr]) (mkApp2 (mkConst ``Logic.Fact.holds) f w)
            byState := push byState w f pf
          -- the lookups in its map already in the context (a lookup introduced before it was not made a fact then)
          let bs := pr.appFn!.appArg!
          for e2 in ctx do
            let et ← instantiateMVars e2.type
            let some (_, l2, r2) := et.eq? | continue
            unless l2.isAppOf ``GetElem?.getElem? && r2.isAppOfArity ``Option.some 2 && l2.getAppNumArgs ≥ 2 do continue
            unless l2.getAppArgs[l2.getAppNumArgs - 2]! == bs do continue
            let x := l2.getAppArgs[l2.getAppNumArgs - 1]!
            let pred ← withLocalDeclD `b (← mkAppM ``Option #[mkConst ``ES.Binding]) fun b => do
              mkLambdaFVars #[b] (← mkEq b r2)
            let f := mkApp4 (mkConst ``Logic.Fact.bind) e pr.appArg! x pred
            let pf ← mkAppOptM ``Logic.bind_fact_of #[w, e, bs, pr.appArg!, x, r2.appArg!, d.toExpr, e2.toExpr]
            byState := push byState w f pf
    -- a predicate of a kind, `P (w.objEntry o).kind` other than `= K` (`(…).kind.isPlain = true`)
    if let some ke := t.find? (fun e => e.isAppOfArity ``ES.Obj.kind 1 && e.appArg!.isAppOfArity ``ES.State.objEntry 2) then
      let isEqK := match t.eq? with | some (_, l, _) => l == ke | none => false
      if !isEqK then
        let w := ke.appArg!.appFn!.appArg!
        let o := ke.appArg!.appArg!
        let body ← kabstract t ke
        if !body.hasLooseBVars || (body.instantiate1 (mkConst ``True)).containsFVar w.fvarId! then
          pure ()
        else if let some hl ← existsAt w o then
          let P := mkLambda `K .default (mkConst ``ES.Kind) body
          let f := mkApp2 (mkConst ``Logic.Fact.kindP) o P
          let pf ← mkExpectedTypeHint (← mkAppM ``And.intro #[hl, d.toExpr]) (mkApp2 (mkConst ``Logic.Fact.holds) f w)
          byState := push byState w f pf
          continue
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
    let mut hl ← appFacts ``Logic.Facts.holds_nil #[w]
    let mut tl := mkApp (mkConst ``List.nil [Level.zero]) (mkConst ``Logic.Fact)
    for (f, pf) in items.reverse do
      let fh ← whnf (mkApp2 (mkConst ``Logic.Fact.holds) f w)
      hl ← appFacts ``Logic.Facts.holds_cons #[f, tl, w, ← mkExpectedTypeHint pf fh, hl]
      tl := mkApp3 (mkConst ``List.cons [Level.zero]) (mkConst ``Logic.Fact) f tl
    let (_, g') ← (← g.assert `rawf (mkApp2 (mkConst ``Logic.Facts.holds) tl w) hl).intro1P
    g := g'
  return g

/-- Each hypothesis that is a frame: its from and to states (computed once). -/
initialize frameCache : IO.Ref (Std.HashMap FVarId (Option (Expr × Expr))) ← IO.mkRef {}

/-- The frames in the context: `(proof, from, to)`. -/
def framesIn : MetaM (Array (Expr × Expr × Expr)) := do
  let mut out := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let r ← match (← frameCache.get).get? d.fvarId with
      | some r => pure r
      | none => do
        let ty ← whnfR (← instantiateMVars d.type)
        let r := if ty.isAppOfArity ``Logic.Frame 3 then some (ty.appFn!.appArg!, ty.appArg!) else none
        frameCache.modify (·.insert d.fvarId r)
        pure r
    if let some (x, y) := r then out := out.push (d.toExpr, x, y)
  return out

/-- A frame from `a` to `b` composed from the context's (breadth first, the proof built for the path found only). -/
def framePath (a b : Expr) : MetaM (Option Expr) := do
  if a == b then return none
  let fs ← framesIn
  -- the states reached, each with the frame and the state it was reached from
  let mut seen : Array Expr := #[a]
  let mut via : Array (Option (Expr × Nat)) := #[none]
  let mut i := 0
  let mut found : Option Nat := none
  while i < seen.size && found.isNone do
    let st := seen[i]!
    for (p, x, y) in fs do
      if x == st && !seen.contains y then
        seen := seen.push y; via := via.push (some (p, i))
        if y == b then found := some (seen.size - 1)
    i := i + 1
  let some j := found | return none
  -- the path back from `b`, then its frames composed in order
  let mut steps : Array Expr := #[]
  let mut k := j
  let mut fuel := seen.size
  while fuel > 0 do
    fuel := fuel - 1
    match via[k]! with
    | some (p, k') => steps := steps.push p; k := k'
    | none => fuel := 0
  let path := steps.reverse
  let mut pf := path[0]!
  for q in path.extract 1 path.size do
    pf ← mkAppM ``Logic.frame_trans #[pf, q]
  return some pf

/-- The fact lists in the context with their states, lists and elements (cached by hypothesis). -/
def factListsKeyed : MetaM (Array (Expr × Expr × Expr × Array Expr × Array (Name × String))) := do
  let mut out := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    match (← factsOfCache.get).get? d.fvarId with
    | some (some r) => out := out.push r
    | some none => pure ()
    | none =>
      let r ← try
          let h ← factsOf d.toExpr
          let ty ← whnfR (← instantiateMVars (← inferType h))
          let L := ty.appFn!.appArg!
          let elems := (← listElems L 4096).getD #[]
          let keys ← elems.mapM factKey
          pure (some (h, ty.appArg!, L, elems, keys))
        catch _ => pure none
      -- (a failure is cached too, unless the type's head is still unknown: an unknown head may become a list)
      unless r.isNone && (← instantiateMVars d.type).getAppFn.isMVar do factsOfCache.modify (·.insert d.fvarId r)
      if let some x := r then out := out.push x
  return out

def factListsFull : MetaM (Array (Expr × Expr × Expr × Array Expr)) := do
  return (← factListsKeyed).map fun (h, a, L, elems, _) => (h, a, L, elems)

/-- The fact lists in the context (a spec's `Pre` too: its facts), each with its state. -/
def factLists : MetaM (Array (Expr × Expr)) := do
  return (← factListsKeyed).map fun (h, a, _, _, _) => (h, a)

/-- A record's facts fix its outer record: two at one state agree. -/
theorem record_outer_eq {e : ES.EnvId} {a b : Option ES.EnvId} {s : ES.State}
    (h1 : (Logic.Fact.record e a).holds s) (h2 : (Logic.Fact.record e b).holds s) : a = b := by
  obtain ⟨_, bs, h1⟩ := h1
  obtain ⟨_, bs', h2⟩ := h2
  rw [h1] at h2
  cases h2
  rfl

/-- A record's lookup fixes its outer record against a record fact at the same state. -/
theorem declLike_outer_eq {e : ES.EnvId} {bs : Std.HashMap ES.JSStr ES.Binding} {a b : Option ES.EnvId} {s : ES.State}
    (h1 : Scope.declLike? (s.envEntry e) = some (bs, a)) (h2 : (Logic.Fact.record e b).holds s) : a = b := by
  obtain ⟨_, bs', h2⟩ := h2
  rw [h1] at h2
  cases h2
  rfl

/-- A record's whole bindings state its outer record too. -/
theorem recordIs_record {e : ES.EnvId} {bs : Std.HashMap ES.JSStr ES.Binding} {o : Option ES.EnvId} {s : ES.State}
    (h : (Logic.Fact.recordIs e bs o).holds s) : (Logic.Fact.record e o).holds s :=
  ⟨h.1, bs, h.2⟩

/-- A fact list element `record e o`/`recordIs e bs o`, by whnf: `(e, o, isRecordIs)`. -/
def recordOf? (f : Expr) : MetaM (Option (Expr × Expr × Bool)) := do
  let f ← whnfR (← instantiateMVars f)
  if f.isAppOfArity ``Logic.Fact.record 2 then return some (f.appFn!.appArg!, f.appArg!, false)
  if f.isAppOfArity ``Logic.Fact.recordIs 3 then return some (f.appFn!.appFn!.appArg!, f.appArg!, true)
  return none

/-- The `i`th fact of list `h : Facts.holds L a`, as `(record e o).holds a`. -/
def recordFactAt (h L a : Expr) (i : Nat) (isIs : Bool) (e o : Expr) : MetaM Expr := do
  let hm ← idxLt i L
  let gi ← factAt L a h i
  let elems := (← listElems L 4096).getD #[]
  let gi ← mkExpectedTypeHint gi (mkApp2 (mkConst ``Logic.Fact.holds) elems[i]! a)
  if isIs then
    let f ← whnfR (← instantiateMVars elems[i]!)
    let bs := f.appFn!.appArg!
    let gi ← mkExpectedTypeHint gi (mkApp2 (mkConst ``Logic.Fact.holds) (mkApp3 (mkConst ``Logic.Fact.recordIs) e bs o) a)
    return mkAppN (mkConst ``recordIs_record) #[e, bs, o, a, gi]
  mkExpectedTypeHint gi (mkApp2 (mkConst ``Logic.Fact.holds) (mkApp2 (mkConst ``Logic.Fact.record) e o) a)

/-- A record's outer record that a post re-quantifies (a local `x : Option EnvId` with `record e x` at `w`): replaced
by the one a fact elsewhere states, carried to `w` (frames keep a record's outer record), by `record_outer_eq`. -/
def substOuter (g : MVarId) (top : Array FVarId) : TermElabM MVarId := do
  let mut g := g
  let mut changed := true
  let mut rounds := 0
  while changed && rounds < 16 do
    changed := false
    rounds := rounds + 1
    let r ← g.withContext do
      -- the records' facts: (list proof, list, state, index, record, outer, recordIs?), from the keyed lists (cached
      -- per hypothesis: only the elements keyed as record facts are looked at)
      let mut recs : Array (Expr × Expr × Expr × Nat × Expr × Expr × Bool) := #[]
      for (h, a, L, elems, keys) in ← factListsKeyed do
        for i in [:elems.size] do
          unless keys[i]!.1 == ``Logic.Fact.record || keys[i]!.1 == ``Logic.Fact.recordIs do continue
          if let some (e, o, isIs) ← recordOf? elems[i]! then recs := recs.push (h, L, a, i, e, o, isIs)
      -- raw lookups `declLike? (w.envEntry e) = some (bs, x)` with `x` a local
      for d in ← getLCtx do
        if d.isImplementationDetail then continue
        -- (an equation, or a type still unknown: anything else is skipped before instantiating it)
        unless d.type.isAppOfArity ``Eq 3 || d.type.getAppFn.isMVar do continue
        let ty ← instantiateMVars d.type
        let some (_, lhs, rhs) := ty.eq? | continue
        unless lhs.isAppOfArity ``Scope.declLike? 1 && rhs.isAppOfArity ``Option.some 2 do continue
        let ee := lhs.appArg!
        unless ee.isAppOfArity ``ES.State.envEntry 2 do continue
        let pr := rhs.appArg!
        unless pr.isAppOfArity ``Prod.mk 4 do continue
        let x := pr.appArg!
        let bs := pr.appFn!.appArg!
        unless x.isFVar && !top.contains x.fvarId! do continue
        if (← restatedLets.get).contains x.fvarId! then continue
        let w := ee.appFn!.appArg!
        let e := ee.appArg!
        for (h', L', a', i', e', t, isIs') in recs do
          if t == x || t.containsFVar x.fvarId! then continue
          if t.hasAnyFVar (fun y => !top.contains y) then continue
          unless ← withNewMCtxDepth (withReducible (isDefEq e e')) do continue
          let some src ← (do
              let hs ← recordFactAt h' L' a' i' isIs' e' t
              if a' == w then return some hs
              let some pf ← framePath a' w | return none
              let one ← appFacts ``Logic.Facts.holds_cons #[mkApp2 (mkConst ``Logic.Fact.record) e' t,
                mkApp (mkConst ``List.nil [Level.zero]) (mkConst ``Logic.Fact), a', hs, ← appFacts ``Logic.Facts.holds_nil #[a']]
              let (L2, prf, nkept, _) ← carry one pf
              if nkept != 1 then return none
              let hm ← idxLt 0 L2
              let g0 ← appFacts ``Logic.Facts.get #[L2, w, prf, mkNatLit 0, hm]
              return some (← mkExpectedTypeHint g0 (mkApp2 (mkConst ``Logic.Fact.holds) (mkApp2 (mkConst ``Logic.Fact.record) e' t) w)))
            | continue
          let src ← mkExpectedTypeHint src (mkApp2 (mkConst ``Logic.Fact.holds) (mkApp2 (mkConst ``Logic.Fact.record) e t) w)
          let eq := mkAppN (mkConst ``declLike_outer_eq) #[e, bs, x, t, w, d.toExpr, src]
          return some (x, t, eq)
      for (h, L, w, i, e, x, isIs) in recs do
        unless x.isFVar && !top.contains x.fvarId! do continue
        if (← restatedLets.get).contains x.fvarId! then continue
        for (h', L', a', i', e', t, isIs') in recs do
          if t == x || t.containsFVar x.fvarId! then continue
          if t.hasAnyFVar (fun y => !top.contains y) then continue
          unless ← withNewMCtxDepth (withReducible (isDefEq e e')) do continue
          -- the other fact at `w`
          let some src ← (do
              let hs ← recordFactAt h' L' a' i' isIs' e' t
              if a' == w then return some hs
              let some pf ← framePath a' w | return none
              let one ← appFacts ``Logic.Facts.holds_cons #[mkApp2 (mkConst ``Logic.Fact.record) e' t,
                mkApp (mkConst ``List.nil [Level.zero]) (mkConst ``Logic.Fact), a', hs, ← appFacts ``Logic.Facts.holds_nil #[a']]
              let (L2, prf, nkept, _) ← carry one pf
              if nkept != 1 then return none
              let hm ← idxLt 0 L2
              let g0 ← appFacts ``Logic.Facts.get #[L2, w, prf, mkNatLit 0, hm]
              return some (← mkExpectedTypeHint g0 (mkApp2 (mkConst ``Logic.Fact.holds) (mkApp2 (mkConst ``Logic.Fact.record) e' t) w)))
            | continue
          let loc ← recordFactAt h L w i isIs e x
          let src ← mkExpectedTypeHint src (mkApp2 (mkConst ``Logic.Fact.holds) (mkApp2 (mkConst ``Logic.Fact.record) e t) w)
          let eq := mkAppN (mkConst ``record_outer_eq) #[e, x, t, w, loc, src]
          return some (x, t, eq)
      -- a `let` outer no record fact names otherwise: the record's outer at the start, a start fact (one unknown per
      -- record), carried here
      if let some s0 ← startState.get then
        for (h, L, w, i, e, x, isIs) in recs do
          unless x.isFVar && !top.contains x.fvarId! do continue
          unless (← x.fvarId!.getDecl).isLet do continue
          if (← restatedLets.get).contains x.fvarId! then continue
          if e.hasAnyFVar (fun y => !top.contains y) then continue
          let some pf ← framePath s0 w | continue
          let mut found : Option (Expr × Expr) := none
          for (e', o0, F0) in ← startRecords.get do
            if ← withNewMCtxDepth (withReducible (isDefEq e e')) then found := some (o0, F0); break
          let (o0, F0) ← match found with
            | some p => pure p
            | none => do
              let lctx ← getLCtx
              let lctxTop := lctx.foldl (init := lctx) fun acc d => if top.contains d.fvarId then acc else acc.erase d.fvarId
              let insts ← getLocalInstances
              let o0 ← mkFreshExprMVarAt lctxTop insts (← x.fvarId!.getType)
              let F0 ← mkFreshExprMVarAt lctxTop insts
                (mkApp2 (mkConst ``Logic.Fact.holds) (mkApp2 (mkConst ``Logic.Fact.record) e o0) s0) .syntheticOpaque `fact
              startRecords.modify (·.push (e, o0, F0))
              pendingFacts.modify (·.push F0.mvarId!)
              pure (o0, F0)
          let rf := mkApp2 (mkConst ``Logic.Fact.record) e o0
          let one ← appFacts ``Logic.Facts.holds_cons #[rf, mkApp (mkConst ``List.nil [Level.zero]) (mkConst ``Logic.Fact),
            s0, F0, ← appFacts ``Logic.Facts.holds_nil #[s0]]
          let some src ← (try
              let (L2, prf, nkept, _) ← carry one pf
              if nkept != 1 then pure none
              else
                let g0 ← appFacts ``Logic.Facts.get #[L2, w, prf, mkNatLit 0, ← idxLt 0 L2]
                pure (some (← mkExpectedTypeHint g0 (mkApp2 (mkConst ``Logic.Fact.holds) rf w)))
            catch _ => pure none) | continue
          let loc ← recordFactAt h L w i isIs e x
          let eq := mkAppN (mkConst ``record_outer_eq) #[e, x, o0, w, loc, src]
          return some (x, o0, eq)
      return none
    if let some (x, t, eq) := r then
      if (← g.withContext x.fvarId!.getDecl).isLet then
        -- a `let` outer (opened from `∃ o bd, …`) cannot be substituted: the hypotheses naming it restated with `t`
        restatedLets.modify (·.insert x.fvarId!)
        g ← g.withContext do
          let mut gc := g
          for d in ← getLCtx do
            if d.isImplementationDetail || d.fvarId == x.fvarId! then continue
            let ty ← instantiateMVars d.type
            unless ty.containsFVar x.fvarId! do continue
            unless (← isProp ty) do continue
            let motive ← withLocalDeclD `y (← inferType x) fun y => do
              mkLambdaFVars #[y] (ty.replaceFVar x y)
            let pf ← mkEqNDRec motive d.toExpr eq
            let (_, g') ← (← gc.assert d.userName (ty.replaceFVar x t) pf).intro1P
            gc := g'
          pure gc
      else
        let (hq, g1) ← (← g.assert `houter (← g.withContext (mkEq x t)) eq).intro1P
        g ← Lean.Meta.subst g1 hq
      changed := true
  return g

/-- An equation `h` taken apart: a walk-local (not a `let`, not the top's) on one side is replaced by the other side
everywhere; constructor applications on both sides are split (`injection`) and each part taken apart in turn. -/
partial def injSubst (g : MVarId) (h : FVarId) (top : Array FVarId) (fuel : Nat := 32) : MetaM MVarId := do
  if fuel == 0 then return g
  let some (l, r) ← g.withContext do
      let ty ← instantiateMVars (← h.getType)
      pure (ty.eq?.map fun (_, l, r) => (l, r))
    | return g
  let isReg (x : Expr) : MetaM Bool := g.withContext do
    if !x.isFVar || top.contains x.fvarId! then return false
    return !(← x.fvarId!.getDecl).isLet
  -- (when the other side names locals made later, `subst` cannot: the target is rewritten, the hypotheses kept)
  let rwTarget (eq : Expr) : MetaM MVarId := g.withContext do
    let r ← g.rewrite (← g.getType) eq
    let g' ← g.replaceTargetEq r.eNew r.eqProof
    return g'
  if (← isReg l) && !r.containsFVar l.fvarId! then
    try return (← substCore g h (symm := false)).2 catch _ =>
      try return (← rwTarget (mkFVar h)) catch _ => return g
  if (← isReg r) && !l.containsFVar r.fvarId! then
    try return (← substCore g h (symm := true)).2 catch _ =>
      try return (← rwTarget (← g.withContext (mkEqSymm (mkFVar h)))) catch _ => return g
  let (l', r') ← g.withContext do pure (← whnfR l, ← whnfR r)
  unless l'.getAppFn.isConst && r'.getAppFn.isConst && l' != r' do return g
  let some (.ctorInfo _) := (← getEnv).find? l'.getAppFn.constName! | return g
  match ← (try some <$> injection g h catch _ => pure none) with
  | some (.subgoal g' eqs _) =>
    let mut g := g'
    for e in eqs do
      -- (an equation a substitution renamed is skipped)
      unless ((← g.withContext getLCtx).find? e).isSome do continue
      g ← injSubst g e top (fuel - 1)
    return g
  | _ => return g

/-- Values two facts at one state give one place (a property read, or a binding read with its value), when one of
them names walk-locals the other does not: equal, the locals replaced (`injSubst`): a value opened from a contract's
statement (`RenderDone`'s fiber `C`, its values `x1 …`) becomes the one the facts before it name. -/
def substSame (g : MVarId) (top : Array FVarId) (s0 : Expr) : TermElabM MVarId := do
  let mut g := g
  let mut tried : Std.HashSet (Nat × Nat) := {}
  for _ in [:8] do
    let r ← g.withContext do
      let isLetFV (x : FVarId) : MetaM Bool := do return (← x.getDecl).isLet
      let regs (e : Expr) : MetaM (Array FVarId) := do
        (collectFVars {} e).fvarIds.filterM fun x => do return !top.contains x && !(← isLetFV x)
      let mut props : Array (Expr × Expr × Expr × Nat × Expr × Expr × Expr) := #[]
      let mut binds : Array (Expr × Expr × Expr × Nat × Expr × Expr × Expr × Expr) := #[]
      for (h, a, L, elems, keys) in ← factListsKeyed do
        for i in [:elems.size] do
          let c := keys[i]!.1
          unless c == ``Logic.Fact.prop || c == ``Logic.Fact.bind do continue
          let f ← instantiateMVars elems[i]!
          if f.isAppOfArity ``Logic.Fact.prop 3 then
            let xs := f.getAppArgs
            props := props.push (h, a, L, i, xs[0]!, xs[1]!, xs[2]!)
          else if f.isAppOfArity ``Logic.Fact.bind 4 then
            let xs := f.getAppArgs
            let P := xs[3]!
            unless P.isLambda do continue
            let some (_, lb, rb) := P.bindingBody!.eq? | continue
            unless lb == .bvar 0 && rb.isAppOfArity ``Option.some 2 && !rb.hasLooseBVars do continue
            binds := binds.push (h, a, L, i, xs[0]!, xs[1]!, xs[2]!, rb.appArg!)
      let get (h a L : Expr) (i : Nat) (f : Expr) : MetaM Expr := do
        let gi ← factAt L a h i
        mkExpectedTypeHint gi (mkApp2 (mkConst ``Logic.Fact.holds) f a)
      -- `o1 = o2`: the same, or an equation in the context (either way round)
      let objEq (o1 o2 : Expr) : MetaM (Option Expr) := do
        if o1 == o2 then return some (← mkEqRefl o1)
        for d in ← getLCtx do
          if d.isImplementationDetail then continue
          unless d.type.isAppOfArity ``Eq 3 do continue
          let ty ← instantiateMVars d.type
          let some (_, l, r) := ty.eq? | continue
          if l == o1 && r == o2 then return some d.toExpr
          if l == o2 && r == o1 then return some (← mkEqSymm d.toExpr)
        return none
      -- a fact's proof at `a` carried to `b` (`b` itself, or along the frames from `a`)
      let carryOne (f p a b : Expr) : TermElabM (Option Expr) := do
        if a == b then return some p
        let some pf ← framePath a b | return none
        let one ← appFacts ``Logic.Facts.holds_cons #[f, mkApp (mkConst ``List.nil [Level.zero]) (mkConst ``Logic.Fact),
          a, p, ← appFacts ``Logic.Facts.holds_nil #[a]]
        let (L2, prf, nkept, _) ← carry one pf
        if nkept != 1 then return none
        let g0 ← appFacts ``Logic.Facts.get #[L2, b, prf, mkNatLit 0, ← idxLt 0 L2]
        return some (← mkExpectedTypeHint g0 (mkApp2 (mkConst ``Logic.Fact.holds) f b))
      let propLocal ← props.mapM fun x => do return !(← regs x.2.2.2.2.2.2).isEmpty
      for j1 in [:props.size] do
        unless propLocal[j1]! do continue
        let (h1, a1, L1, i1, o1, k1, r1) := props[j1]!
        for j2 in [:props.size] do
          if propLocal[j2]! || tried.contains (j1, j2) then continue
          let (h2, a2, L2, i2, o2, k2, r2) := props[j2]!
          unless k1 == k2 && r1 != r2 do continue
          -- the same object, or one an equation in the context names as it
          let some he ← objEq o1 o2 | continue
          -- the other fact at `a1`: there, or carried from an earlier state
          let f2 := mkApp3 (mkConst ``Logic.Fact.prop) o2 k2 r2
          let p2 ← get h2 a2 L2 i2 f2
          let some p2 ← carryOne f2 p2 a2 a1 | continue
          let p1 ← get h1 a1 L1 i1 (mkApp3 (mkConst ``Logic.Fact.prop) o1 k1 r1)
          let pf := mkAppN (mkConst ``prop_same_eq) #[o1, o2, k1, r1, r2, a1, he, p1, p2]
          return some ((j1, j2), pf, ← mkEq r1 r2)
      -- no other fact about the place, which the way from the start keeps: the start's read asked for (a start fact,
      -- its walk-locals unknowns of the top's), carried here, the read naming the unknowns in their place
      for j1 in [:props.size] do
        unless propLocal[j1]! do continue
        if tried.contains (200000 + j1, 0) then continue
        let (h1, a1, L1, i1, o1, k1, r1) := props[j1]!
        if (← askFailed.get).contains (h1, i1) then continue
        if o1.hasAnyFVar (fun x => !top.contains x) || k1.hasAnyFVar (fun x => !top.contains x) then continue
        if a1 == s0 then continue
        let some pf ← framePath s0 a1 | continue
        let lctx ← getLCtx
        let lctxTop := lctx.foldl (init := lctx) fun acc d => if top.contains d.fvarId then acc else acc.erase d.fvarId
        let insts ← getLocalInstances
        let mut r2 := r1
        for x in (collectFVars {} r1).fvarIds do
          unless top.contains x do
            let m ← mkFreshExprMVarAt lctxTop insts (← x.getType)
            r2 := r2.replaceFVarId x m
        let f2 := mkApp3 (mkConst ``Logic.Fact.prop) o1 k1 r2
        let saved ← saveState
        let F0 ← mkFreshExprMVarAt lctxTop insts (mkApp2 (mkConst ``Logic.Fact.holds) f2 s0) .syntheticOpaque `fact
        let one ← appFacts ``Logic.Facts.holds_cons #[f2, mkApp (mkConst ``List.nil [Level.zero]) (mkConst ``Logic.Fact),
          s0, F0, ← appFacts ``Logic.Facts.holds_nil #[s0]]
        let ok ← try
            let (L2, prf, nkept, _) ← carry one pf
            if nkept != 1 then pure none
            else
              let g0 ← appFacts ``Logic.Facts.get #[L2, a1, prf, mkNatLit 0, ← idxLt 0 L2]
              pure (some (← mkExpectedTypeHint g0 (mkApp2 (mkConst ``Logic.Fact.holds) f2 a1)))
          catch _ => pure none
        let some p2 := ok | saved.restore; askFailed.modify (·.insert (h1, i1)); continue
        pendingFacts.modify (·.push F0.mvarId!)
        let p1 ← get h1 a1 L1 i1 (mkApp3 (mkConst ``Logic.Fact.prop) o1 k1 r1)
        let pf := mkAppN (mkConst ``prop_same) #[o1, k1, r1, r2, a1, p1, p2]
        return some ((200000 + j1, 0), pf, ← mkEq r1 r2)
      -- bindings: `bd1.value = some x` (x a walk-local) and `bd2.value = some v` (v without them)
      let vals ← (← getLCtx).foldlM (init := #[]) fun acc d => do
        if d.isImplementationDetail then return acc
        unless d.type.isAppOfArity ``Eq 3 do return acc
        let ty ← instantiateMVars d.type
        let some (_, l, r) := ty.eq? | return acc
        unless l.isAppOfArity ``ES.Binding.value 1 && r.isAppOfArity ``Option.some 2 do return acc
        return acc.push (l.appArg!, r.appArg!, d.toExpr)
      for j1 in [:binds.size] do
        let (h1, a1, L1, i1, e1, o1, x1, bd1) := binds[j1]!
        let some (_, v1, hv1) := vals.find? (·.1 == bd1) | continue
        let rs1 ← regs v1
        if rs1.isEmpty then continue
        for j2 in [:binds.size] do
          if j1 == j2 || tried.contains (100000 + j1, j2) then continue
          let (h2, a2, L2, i2, e2, o2, x2, bd2) := binds[j2]!
          unless e1 == e2 && x1 == x2 && bd1 != bd2 do continue
          let some (_, v2, hv2) := vals.find? (·.1 == bd2) | continue
          unless (← regs v2).isEmpty do continue
          let optB ← mkAppM ``Option #[mkConst ``ES.Binding]
          let pred (bd : Expr) : MetaM Expr := withLocalDeclD `b optB fun b => do
            mkLambdaFVars #[b] (← mkEq b (← mkAppM ``Option.some #[bd]))
          let p1 ← get h1 a1 L1 i1 (mkApp4 (mkConst ``Logic.Fact.bind) e1 o1 x1 (← pred bd1))
          let f2 := mkApp4 (mkConst ``Logic.Fact.bind) e2 o2 x2 (← pred bd2)
          let some p2 ← carryOne f2 (← get h2 a2 L2 i2 f2) a2 a1 | continue
          let he := mkAppN (mkConst ``bind_same) #[e1, o1, o2, x1, bd1, bd2, a1, p1, p2]
          let pf := mkAppN (mkConst ``value_same) #[bd1, bd2, v1, v2, he, hv1, hv2]
          return some ((100000 + j1, j2), pf, ← mkEq v1 v2)
      return none
    let some (key, pf, ty) := r | break
    tried := tried.insert key
    let g' ← (try
        let (hEq, g1) ← (← g.assert `same ty pf).intro1P
        injSubst g1 hEq top
      catch _ => pure g)
    g := g'
  return g

/-- The goal `Facts.holds L w`: every fact list in the context carried to `w` (as hypotheses), then matched. -/
def collectFacts (g : MVarId) (top : Array FVarId) (s0 : Expr) (st : IO.Ref Collected) : TermElabM Unit := do
  let g ← g.withContext do
    let t ← whnfR (← instantiateMVars (← g.getType))
    let w := t.appArg!
    -- the goal's facts' kinds and keys: only facts that may match one are carried
    let goalKeys ← match ← listElems t.appFn!.appArg! 4096 with
      | some gs => gs.mapM fun e => (factKey e : MetaM _)
      | none => pure #[]
    let wanted (ck : Name × String) : Bool :=
      goalKeys.any fun (c, k) => c == ck.1 && (k == ck.2 || k == "?" || ck.2 == "?")
    let mut g := g
    -- the wanted facts, grouped by their state: (state, [(fact, its proof at the state)])
    let mut byState : Array (Expr × Array (Expr × Expr)) := #[]
    for (h, a, L, elems, keys) in ← timed "walk:lists" factListsKeyed do
      if a == w then continue
      for i in [:elems.size] do
        unless wanted keys[i]! do continue
        let hm ← idxLt i L
        let gi ← factAt L a h i
        let gi ← mkExpectedTypeHint gi (mkApp2 (mkConst ``Logic.Fact.holds) elems[i]! a)
        match byState.findIdx? (·.1 == a) with
        | some k => byState := byState.modify k fun (a', l) => (a', l.push (elems[i]!, gi))
        | none => byState := byState.push (a, #[(elems[i]!, gi)])
    for (a, items) in byState do
      let some pf ← timed "walk:path" (framePath a w) | continue
      -- a frame through a footprint that is a variable (`fpWL`) cannot be reflected: that source is skipped
      let saved ← saveState
      try
        let mut hl ← appFacts ``Logic.Facts.holds_nil #[a]
        let mut tl := mkApp (mkConst ``List.nil [Level.zero]) (mkConst ``Logic.Fact)
        for (f, gi) in items.reverse do
          hl ← appFacts ``Logic.Facts.holds_cons #[f, tl, a, gi, hl]
          tl := mkApp3 (mkConst ``List.cons [Level.zero]) (mkConst ``Logic.Fact) f tl
        let hSub ← mkExpectedTypeHint hl (mkApp2 (mkConst ``Logic.Facts.holds) tl a)
        let (L', prf, _, _) ← timed "walk:carry" (carry hSub pf)
        let (_, g') ← (← g.assert `carried (mkApp2 (mkConst ``Logic.Facts.holds) L' w) prf).intro1P
        g := g'
      catch _ => saved.restore
    return g
  let (left, _, n) ← timed "walk:prove" (proveFacts g)
  let _ := top; let _ := s0
  let found := n - left.length
  st.modify fun c => { c with matched := c.matched + found }
  pendingFacts.modify (· ++ left.toArray)

/-- A statement about one object's kind (`kindP`) or its whole entry (`objP`, e.g. its keys) at a state it names
nowhere else: that fact, a goal. -/
def objFactGoal? (g : MVarId) : MetaM (Option MVarId) := g.withContext do
  let goal ← instantiateMVars (← g.getType)
  let mkGoal (f w : Expr) : MetaM Expr := mkFreshExprSyntheticOpaqueMVar (mkApp2 (mkConst ``Logic.Fact.holds) f w) `fact
  if let some oe := goal.find? (fun e => e.isAppOfArity ``ES.State.objEntry 2 && e.appFn!.appArg!.isFVar && !e.hasLooseBVars) then
    let w := oe.appFn!.appArg!
    let o := oe.appArg!
    let kd := mkApp (mkConst ``ES.Obj.kind) oe
    let rest := goal.replace fun e => if e == oe then some (mkConst ``True) else none
    unless rest.containsFVar w.fvarId! || o.containsFVar w.fvarId! do
      let kOnly := !(goal.replace fun e => if e == kd then some (mkConst ``True) else none).containsFVar w.fvarId!
      if kOnly then
        let P ← withLocalDeclD `K (mkConst ``ES.Kind) fun K => do
          mkLambdaFVars #[K] (goal.replace fun e => if e == kd then some K else none)
        let F ← mkGoal (mkApp2 (mkConst ``Logic.Fact.kindP) o P) w
        g.assign (← mkExpectedTypeHint (mkProj ``And 1 F) goal)
        return some F.mvarId!
      let P ← withLocalDeclD `ob (mkConst ``ES.Obj) fun ob => do
        mkLambdaFVars #[ob] (goal.replace fun e => if e == oe then some ob else none)
      let F ← mkGoal (mkApp2 (mkConst ``Logic.Fact.objP) o P) w
      g.assign (← mkExpectedTypeHint (mkProj ``And 1 F) goal)
      return some F.mvarId!
  return none

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
      -- a record's map from its fact (`recordMap`): the record's `declLike?` that fact gives
      let bs' ← instantiateMVars bs
      if bs'.isAppOfArity ``recordMap 4 then
        let ra := bs'.getAppArgs
        let (e, o, w, R) := (ra[0]!, ra[1]!, ra[2]!, ra[3]!)
        let hd := mkProj ``And 1 (mkAppN (mkConst ``recordIs_of_record) #[e, o, w, R])
        let pred ← withLocalDeclD `b (← mkAppM ``Option #[mkConst ``ES.Binding]) fun b => do
          mkLambdaFVars #[b] (← mkEq b rhs)
        let f := mkApp4 (mkConst ``Logic.Fact.bind) e o x pred
        let F ← mkGoal f w
        let pf := mkAppN (mkConst ``Logic.Fact.bind_get) #[e, o, x, pred, w, bs', hd, F]
        g.assign (← mkExpectedTypeHint pf goal)
        return some F.mvarId!
      -- (the record's hypotheses whose outer names no walk-local first: a restated one, `substOuter`)
      let top0 ← topLocals.get
      let decls := (← getLCtx).foldl (init := #[]) fun acc d => acc.push d
      let outerLocal (d : LocalDecl) : Bool := Id.run do
        let some (_, _, r2) := d.type.eq? | return false
        unless r2.isAppOfArity ``Option.some 2 && r2.appArg!.isAppOfArity ``Prod.mk 4 do return false
        return r2.appArg!.appArg!.hasAnyFVar (fun y => !top0.contains y)
      let ordered := decls.filter (!outerLocal ·) ++ decls.filter outerLocal
      for d in ordered do
        if d.isImplementationDetail then continue
        let t ← instantiateMVars d.type
        if let some (_, l2, r2) := t.eq? then
          if l2.isAppOfArity ``Scope.declLike? 1 && r2.isAppOfArity ``Option.some 2 then
            let pr := r2.appArg!
            if pr.isAppOfArity ``Prod.mk 4 && pr.appFn!.appArg! == bs && l2.appArg!.isAppOfArity ``ES.State.envEntry 2 then
              let w := l2.appArg!.appFn!.appArg!
              let e := l2.appArg!.appArg!
              let o := pr.appArg!
              -- an outer the walk introduced (`∀ bm o, declLike? … = some (bm, o) → …`): the fact's own, unknown
              let top ← topLocals.get
              -- (only when no record fact states `e`'s outer: else `substOuter` puts that outer in place of `o`)
              let mut anyOuter := o.hasAnyFVar (fun x => !top.contains x)
              if anyOuter && false then
                for (_, _, _, elems, keys) in ← factListsKeyed do
                  for i in [:elems.size] do
                    unless keys[i]!.1 == ``Logic.Fact.record || keys[i]!.1 == ``Logic.Fact.recordIs do continue
                    if let some (e', t, _) ← recordOf? elems[i]! then
                      if !t.hasAnyFVar (fun y => !top.contains y) && (← withNewMCtxDepth (withReducible (isDefEq e e'))) then
                        anyOuter := false
              let oG ← if anyOuter then mkFreshExprMVar (← inferType o) else pure o
              let pred ← withLocalDeclD `b (← mkAppM ``Option #[mkConst ``ES.Binding]) fun b => do
                mkLambdaFVars #[b] (← mkEq b rhs)
              let f := mkApp4 (mkConst ``Logic.Fact.bind) e oG x pred
              let F ← mkGoal f w
              let pf ← if anyOuter then
                  pure (mkAppN (mkConst ``bind_get_any) #[e, oG, o, x, pred, w, bs, d.toExpr, F])
                else mkAppOptM ``Logic.Fact.bind_get #[e, oG, x, pred, w, bs, d.toExpr, F]
              g.assign (← mkExpectedTypeHint pf goal)
              return some F.mvarId!
    -- a prototype
    if lhs.isAppOfArity ``ES.Obj.proto 1 && lhs.appArg!.isAppOfArity ``ES.State.objEntry 2 then
      let w := lhs.appArg!.appFn!.appArg!
      let o := lhs.appArg!.appArg!
      let F ← mkGoal (mkApp2 (mkConst ``Logic.Fact.proto) o rhs) w
      g.assign (← mkExpectedTypeHint (mkProj ``And 1 F) goal)
      return some F.mvarId!
    -- an own property's read
    if lhs.isAppOfArity ``ES.PropMap.get? 2 then
      let pm := lhs.appFn!.appArg!
      if pm.isAppOfArity ``ES.Obj.props 1 && pm.appArg!.isAppOfArity ``ES.State.objEntry 2 then
        let w := pm.appArg!.appFn!.appArg!
        let o := pm.appArg!.appArg!
        let k := lhs.appArg!
        unless rhs.containsFVar w.fvarId! || o.containsFVar w.fvarId! || k.containsFVar w.fvarId! || !w.isFVar do
          let F ← mkGoal (mkApp3 (mkConst ``Logic.Fact.prop) o k rhs) w
          g.assign (← mkExpectedTypeHint (mkProj ``And 1 F) goal)
          return some F.mvarId!
  -- an object's existence (`kindP o (fun _ => True)`, as `facts_form` states it)
  if goal.isAppOfArity ``LT.lt 4 then
    let sz := goal.appArg!
    if sz.isAppOfArity ``Array.size 2 && sz.appArg!.isAppOfArity ``ES.State.heap 1 then
      let w := sz.appArg!.appArg!
      let o := goal.appFn!.appArg!
      if w.isFVar && !o.containsFVar w.fvarId! then
        let F ← mkGoal (mkApp2 (mkConst ``Logic.Fact.kindP) o
          (mkLambda `K .default (mkConst ``ES.Kind) (mkConst ``True))) w
        g.assign (← mkExpectedTypeHint (mkProj ``And 0 F) goal)
        return some F.mvarId!
  if let some F ← objFactGoal? g then return some F
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

/-- A goal about `w.realms`: the same about the start's realms (frames keep realms), as a new pure goal. -/
def realmGoal (g : MVarId) (s0 : Expr) : MetaM (Option MVarId) := g.withContext do
  let goal ← instantiateMVars (← g.getType)
  let some r := goal.find? fun e => e.isAppOfArity ``ES.State.realms 1 && e.appArg! != s0 | return none
  let w := r.appArg!
  let some pf ← framePath s0 w | return none
  let r0 := mkApp (mkConst ``ES.State.realms) s0
  let rTy ← inferType r
  let F ← withLocalDeclD `r rTy fun x => do mkLambdaFVars #[x] (goal.replace fun e => if e == r then some x else none)
  let G ← mkFreshExprSyntheticOpaqueMVar (F.beta #[r0]) `realm
  -- `realms_eq : w.realms = s0.realms`
  let heq ← mkAppM ``Logic.Frame.realms_eq #[pf]
  let pf' ← mkAppOptM ``Eq.mpr #[F.beta #[r], F.beta #[r0], ← mkAppM ``congrArg #[F, heq], G]
  g.assign (← mkExpectedTypeHint pf' goal)
  return some G.mvarId!

/-- A small ground equation by definitional unfolding (`{ … }.value.isSome = true`). -/
def rflOne (g : MVarId) : MetaM Bool := g.withContext do
  if ← g.isAssigned then return true
  let goal ← instantiateMVars (← g.getType)
  if goal.hasExprMVar then return false
  let some (_, l, r) := goal.eq? | return false
  if goal.approxDepth.toNat > 40 then return false
  let saved ← saveState
  if ← (try isDefEq l r catch _ => pure false) then
    g.assign (← mkEqRefl l); return true
  saved.restore; return false

/-- The hypotheses already normalized. -/
initialize normalized : IO.Ref (Std.HashSet FVarId) ← IO.mkRef {}

/-- A goal `Fact.holds f w`: matched against the fact lists at `w` in its context (one candidate fits, or `f` has no
unknowns and one does). -/
def matchOne (g : MVarId) (far : Bool := false) : TermElabM Bool := g.withContext do
  if ← g.isAssigned then return true
  if (← startOnly.get).contains g then return false
  let t ← instantiateMVars (← g.getType)
  unless t.isAppOfArity ``Logic.Fact.holds 2 do return false
  let f := t.appFn!.appArg!
  let w := t.appArg!
  let (c, k) ← factKey f
  let ground := !f.hasExprMVar
  let mut fits : Array (Expr × Expr × Nat × Expr) := #[]
  -- (a fit that would put a walk-local outer in an unknown, an `o` opened from `∃ o bd, …`, is never taken: a record's
  -- outer is the record's, found carried from earlier or left unknown, a start fact's)
  let top ← topLocals.get
  let mut clean : Array (Expr × Expr × Nat × Expr) := #[]
  for (h, Ls, keyed) in ← timed "match:sources" (sourcesAt w) do
    for i in [:keyed.size] do
      let (e, c', k') := keyed[i]!
      unless c' == c && (k == k' || k == "?" || k' == "?") do continue
      unless ← timed "match:objs" (objsAllow e f) do continue
      let saved ← saveState
      let ok ← timed "match:trial" (try (defEqLog "L590" e f) catch _ => pure false)
      let dirty ← if ok && !ground then do
          let f' ← instantiateMVars f
          let fresh := (collectFVars {} f').fvarIds.filter fun x => !top.contains x && !f.containsFVar x
          fresh.anyM fun x => do
            let ty ← whnfR (← instantiateMVars (← x.getType))
            return ty.isAppOfArity ``Option 1 && ty.appArg!.isConstOf ``ES.EnvId
        else pure false
      saved.restore
      if ok && !(← fits.anyM fun x => do pure ((← instantiateMVars x.2.2.2) == (← instantiateMVars e))) then
        fits := fits.push (h, Ls, i, e)
        unless dirty do clean := clean.push (h, Ls, i, e)
        if ground then break
    if ground && fits.size ≥ 1 then break
  let dirtyOnly := !fits.isEmpty && clean.isEmpty
  if !clean.isEmpty then fits := clean
  if (fits.isEmpty || dirtyOnly) && far then
    -- sources at earlier states with a frame to `w`: the one that fits, alone, carried to `w`
    let mut far : Array (Expr × Expr × Expr × Nat × Expr × Expr) := #[]
    for (h, a, L, elems, keys) in ← timed "match:lists" factListsKeyed do
      if a == w then continue
      unless keys.any (fun (c', k') => c' == c && (k == k' || k == "?" || k' == "?")) do continue
      let some pf ← timed "match:farpath" (framePath a w) | continue
      for i in [:elems.size] do
        let (c', k') := keys[i]!
        unless c' == c && (k == k' || k == "?" || k' == "?") do continue
        let e ← instantiateMVars elems[i]!
        unless ← timed "match:objs" (objsAllow e f) do continue
        let saved ← saveState
        let ok ← timed "match:fartrial" (try withReducible (isDefEq e f) catch _ => pure false)
        saved.restore
        if ok && !(far.any fun x => x.2.2.2.2.1 == e) then far := far.push (h, L, a, i, e, pf)
    if far.size == 1 || (ground && far.size ≥ 1) then
      let (h, L, a, i, e, pf) := far[0]!
      let hm ← idxLt i L
      let gi ← factAt L a h i
      let gi ← mkExpectedTypeHint gi (mkApp2 (mkConst ``Logic.Fact.holds) e a)
      let one ← appFacts ``Logic.Facts.holds_cons #[e, mkApp (mkConst ``List.nil [Level.zero]) (mkConst ``Logic.Fact), a, gi,
        ← appFacts ``Logic.Facts.holds_nil #[a]]
      let saved ← saveState
      try
        let (L2, prf, nkept, _) ← timed "match:farcarry" (carry one pf)
        if nkept != 1 then saved.restore; return false
        unless ← withReducible (isDefEq e f) do saved.restore; return false
        let hm1 ← idxLt 0 L2
        let g0 ← appFacts ``Logic.Facts.get #[L2, w, prf, mkNatLit 0, hm1]
        g.assign (← mkExpectedTypeHint g0 t)
        return true
      catch _ => saved.restore; return false
    else return false
  if dirtyOnly then return false
  -- fits that all read one place at `w` (one record's binding, one object's property): one binding, one read
  -- (`bind_same`, `prop_same`), whichever is taken
  let samePlace ← do
    if fits.size ≤ 1 then pure false
    else
      let place (e : Expr) : MetaM (Option (Name × Expr × Expr)) := do
        let e ← instantiateMVars e
        let some c := e.getAppFn.constName? | return none
        let xs := e.getAppArgs
        if c == ``Logic.Fact.bind && xs.size == 4 then return some (c, xs[0]!, xs[2]!)
        if c == ``Logic.Fact.prop && xs.size == 3 then return some (c, xs[0]!, xs[1]!)
        return none
      let p0 ← place fits[0]!.2.2.2
      match p0 with
      | none => pure false
      | some p0 => fits.allM fun x => do return (← place x.2.2.2) == some p0
  unless fits.size == 1 || (ground && fits.size ≥ 1) || samePlace do return false
  let (h, Ls, i, e) := fits[0]!
  let before := f.hasExprMVar
  let _ ← defEqLog "matchOne" e f

  -- diagnosis: a match that fixes flags to `false`
  if before then
    let f' ← instantiateMVars f
    if (toString (← ppExpr f')).contains "false false false" then
      logInfo m!"matched (fixing false flags): {← ppExpr f'}\n  from {← ppExpr (← instantiateMVars e)} ({fits.size} fit)"
  let hm ← idxLt i Ls
  let gi ← factAt Ls w h i
  g.assign (← mkExpectedTypeHint gi t)
  return true

/-- `?R a ?x` (an unknown relation, e.g. a host's `R2`) from the one hypothesis `?R a b`: only the goal's unknown
arguments (witnesses) are assigned. -/
def assumeRel (g : MVarId) (goal : Expr) : MetaM Bool := g.withContext do
  let hd := goal.getAppFn
  let gas := goal.getAppArgs
  let mut fit : Option (LocalDecl × Array Expr) := none
  let mut many := false
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    unless ty.getAppFn == hd && ty.getAppNumArgs == gas.size do continue
    let tas := ty.getAppArgs
    let ok := (List.range gas.size).all fun i =>
      gas[i]! == tas[i]! || (gas[i]!.isMVar && !tas[i]!.hasExprMVar)
    unless ok do continue
    if fit.isSome then many := true; break
    fit := some (d, tas)
  if !many then
    if let some (d, tas) := fit then
      for i in [:gas.size] do
        if gas[i]! != tas[i]! then
          unless ← isDefEq gas[i]! tas[i]! do return false
      g.assign d.toExpr
      return true
  return false

def assumeSame (g : MVarId) (goal : Expr) : MetaM Bool := g.withContext do
  let hd := goal.getAppFn
  let _ := hd
  -- a hypothesis that is the goal itself (assigning nothing), or `∀ y, y ∈ [a, …] → P y` with the goal `P a`
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    -- (another head, not an unknown and no `∀`: neither; skipped before instantiating)
    let h0 := d.type.getAppFn
    let memShape := match d.type with
      | .forallE _ _ (.forallE _ m _ _) _ => m.isAppOfArity ``Membership.mem 5
      | _ => false
    unless h0 == hd || h0.isMVar || memShape do continue
    let ty ← instantiateMVars d.type
    if ty == goal then g.assign d.toExpr; return true
    if let .forallE _ α (.forallE _ mem P' _) _ := ty then
      if mem.isAppOfArity ``Membership.mem 5 && mem.appArg! == .bvar 0 && !P'.hasLooseBVar 0 then
        let l := mem.appFn!.appArg!
        if l.hasLooseBVars then continue
        let some elems ← listElems l 4096 | continue
        let body := P'.lowerLooseBVars 1 1
        for i in [:elems.size] do
          if body.instantiate1 elems[i]! == goal then
            -- `elems[i] ∈ l` by `List.Mem.head`, then `List.Mem.tail` for each element before it
            let rest ← mkListLit α (elems.extract (i + 1) elems.size).toList
            let mut hm ← mkAppOptM ``List.Mem.head #[α, elems[i]!, rest]
            let mut tl ← mkListLit α (elems.extract i elems.size).toList
            for j in (List.range i).reverse do
              hm ← mkAppOptM ``List.Mem.tail #[α, elems[i]!, elems[j]!, tl, hm]
              tl ← mkListLit α (elems.extract j elems.size).toList
            let hm' ← mkExpectedTypeHint hm (mem.instantiate1 elems[i]!)
            g.assign (← mkExpectedTypeHint (mkApp2 d.toExpr elems[i]! hm') goal)
            return true
  return false

def assumeEqLeft (g : MVarId) (goal : Expr) : MetaM Bool := g.withContext do
  let hd := goal.getAppFn
  let _ := hd
  -- an equation whose left side is ground and stated by a hypothesis: the hypothesis determines the right side
  if let some (_, l, r) := goal.eq? then
    if !l.hasExprMVar then
      for d in ← getLCtx do
        if d.isImplementationDetail then continue
        unless d.type.isAppOfArity ``Eq 3 || d.type.getAppFn.isMVar do continue
        let ty ← instantiateMVars d.type
        let some (_, l', r') := ty.eq? | continue
        unless l' == l do continue
        let saved ← saveState
        if ← (try withReducible (isDefEq r r') catch _ => pure false) then
          g.assign (← mkExpectedTypeHint d.toExpr goal); return true
        saved.restore
  return false

def assumeIsSome (g : MVarId) (goal : Expr) : MetaM Bool := g.withContext do
  let hd := goal.getAppFn
  let _ := hd
  -- `x.isSome = true` from `x = some v`
  if let some (_, l, r) := goal.eq? then
    if l.isAppOfArity ``Option.isSome 2 && r.isConstOf ``Bool.true then
      let x := l.appArg!
      for d in ← getLCtx do
        if d.isImplementationDetail then continue
        unless d.type.isAppOfArity ``Eq 3 || d.type.getAppFn.isMVar do continue
        let ty ← instantiateMVars d.type
        let some (_, l', r') := ty.eq? | continue
        unless l' == x && r'.isAppOfArity ``Option.some 2 do continue
        let motive ← withLocalDeclD `y (← inferType x) fun y => do
          mkLambdaFVars #[y] (← mkEq (← mkAppM ``Option.isSome #[y]) (mkConst ``Bool.true))
        let prf ← mkAppM ``Eq.mpr #[← mkAppM ``congrArg #[motive, d.toExpr], ← mkEqRefl (mkConst ``Bool.true)]
        g.assign (← mkExpectedTypeHint prf goal); return true
  return false

/-- Diagnosis: the time since `t0` under `k`. -/
def ckT (k : String) (t0 : Nat) : MetaM Unit := do
  let dt := (← (IO.monoNanosNow : IO Nat)) - t0
  (stepTimes.modify fun a => match a.findIdx? (·.1 == k) with
    | some i => a.modify i fun (k', t, n) => (k', t + dt, n + 1)
    | none => a.push (k, dt, 1) : IO Unit)

/-- `assumeOne`'s steps, in `g`'s context. -/
def assumeBody (g : MVarId) : MetaM Bool := do
  if ← timed "assume:isAssigned" g.isAssigned then return true
  let goal ← timed "assume:inst" (instantiateMVars (← g.getType))
  let hd := goal.getAppFn
  let ground := !goal.hasExprMVar
  if ← timed "assume:same" (assumeSame g goal) then return true
  if ← timed "assume:eqLeft" (assumeEqLeft g goal) then return true
  if ← timed "assume:isSome" (assumeIsSome g goal) then return true
  -- (nested: a `←` inside `&&` would run before the test)
  if hd.isMVar then
    unless ← hd.mvarId!.isAssigned do
      if ← timed "assume:rel" (assumeRel g goal) then return true
  -- a pure goal never assigns unknowns (a hypothesis that fits may be unrelated): it waits until facts have
  unless ground do return false
  let fits ← timed "assume:ground" do
    let mut fits : Array LocalDecl := #[]
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      let h0 := d.type.getAppFn
      unless h0 == hd || h0.isMVar do continue
      let ty ← instantiateMVars d.type
      unless ty.getAppFn == hd do continue
      let saved ← saveState
      let ok ← try (defEqLog "L636" ty goal) catch _ => pure false
      saved.restore
      if ok then
        fits := fits.push d
        if ground || fits.size > 1 then break
    pure fits
  unless fits.size == 1 || (ground && fits.size ≥ 1) do return false
  let _ ← timed "assume:L642" (do defEqLog "L642" (← instantiateMVars fits[0]!.type) goal)
  timed "assume:assign" (g.assign fits[0]!.toExpr)
  return true


/-- A pure goal closed by a hypothesis with its head, matched reducibly. -/
def assumeOne (g : MVarId) : MetaM Bool := g.withContext (timed "assume:body" (assumeBody g))

/-- `∀ o, a ≠ .obj o` (a value that is no object): the value `a`. -/
def notObj? (t : Expr) : Option Expr := do
  let .forallE _ _ body _ := t | none
  guard (body.isAppOfArity ``Ne 3)
  let r := body.appArg!
  guard (r.isAppOfArity ``ES.Value.obj 1 && r.appArg! == .bvar 0)
  let a := body.appFn!.appArg!
  guard (!a.hasLooseBVars)
  return a

/-- A goal `∀ o, a ≠ .obj o` with `a` a value of another kind: by its constructor. -/
def notObjOne (g : MVarId) : TermElabM Bool := g.withContext do
  if ← g.isAssigned then return true
  let t ← instantiateMVars (← g.getType)
  let some a := notObj? t | return false
  let a ← whnfR a
  let some c := a.getAppFn.constName? | return false
  unless c.getPrefix == ``ES.Value && c != ``ES.Value.obj do return false
  let saved ← saveState
  try
    let rem ← Term.withoutErrToSorry <| Tactic.run g (Tactic.withoutRecover (Tactic.evalTactic
      (← `(tactic| (intro _ h; cases h)))))
    if rem.isEmpty then return true
    saved.restore; return false
  catch _ => saved.restore; return false

/-- `P` of each element of a list. -/
def AllL {α : Type} (P : α → Prop) : List α → Prop
  | [] => True
  | a :: l => P a ∧ AllL P l

theorem allL_mem {α : Type} {P : α → Prop} : ∀ {l : List α}, AllL P l → ∀ y, y ∈ l → P y
  | [], _, _, hy => nomatch hy
  | _ :: _, ⟨ha, hl⟩, _, hy => by
    cases hy with
    | head => exact ha
    | tail _ h => exact allL_mem hl _ h

/-- `∀ xs, body`, each `let` among `xs` a plain binder (its value dropped). -/
partial def abstractNoLets (xs : List Expr) (body : Expr) : MetaM Expr := do
  match xs with
  | [] => return body
  | x :: rest =>
    let d ← x.fvarId!.getDecl
    if d.isLet then
      withLocalDeclD d.userName d.type fun y => do
        let rest' := rest.map (·.replaceFVar x y)
        let inner ← abstractNoLets rest' (body.replaceFVar x y)
        mkForallFVars #[y] inner
    else
      let inner ← abstractNoLets rest body
      mkForallFVars #[x] inner

/-- `∀ bm o, declLike? (w.envEntry e) = some (bm, o) → ∃ bd, bm[x]? = some bd ∧ R bd`: `(w, e, x, Q)` with
`Q := fun bd => R bd`. -/
def forallBindOf? (t : Expr) : MetaM (Option (Expr × Expr × Expr × Expr)) := do
  let .forallE _ bmTy (.forallE _ _ (.forallE _ hyp body _) _) _ := t | return none
  -- binders: bm (bvar 2 in body), o (bvar 1), the hypothesis (bvar 0)
  let some (_, l, r) := hyp.eq? | return none
  unless l.isAppOfArity ``Scope.declLike? 1 && r.isAppOfArity ``Option.some 2 do return none
  let ee := l.appArg!
  unless ee.isAppOfArity ``ES.State.envEntry 2 do return none
  let w := ee.appFn!.appArg!
  let e := ee.appArg!
  if w.hasLooseBVars || e.hasLooseBVars then return none
  let pr := r.appArg!
  unless pr.isAppOfArity ``Prod.mk 4 && pr.appFn!.appArg! == .bvar 1 && pr.appArg! == .bvar 0 do return none
  unless body.isAppOfArity ``Exists 2 do return none
  let p := body.appArg!
  let .lam bdN bdTy inner _ := p | return none
  unless inner.isAppOfArity ``And 2 do return none
  let eqp := inner.appFn!.appArg!
  let R := inner.appArg!
  let some (_, gl, gr) := eqp.eq? | return none
  -- `bm[x]?` (bm: bvar 3 under the ∃'s binder), `some bd` (bd: bvar 0)
  unless gl.isAppOf ``GetElem?.getElem? && gl.getAppNumArgs ≥ 2 do return none
  unless gl.getAppArgs[gl.getAppNumArgs - 2]! == .bvar 3 do return none
  let x := gl.getAppArgs[gl.getAppNumArgs - 1]!
  if x.hasLooseBVars then return none
  unless gr.isAppOfArity ``Option.some 2 && gr.appArg! == .bvar 0 do return none
  -- `R` may name only bd
  unless R.looseBVarRange ≤ 1 do return none
  if bdTy.hasLooseBVars then return none
  let _ := bmTy
  let Q := Expr.lam bdN bdTy R .default
  return some (w, e, x, Q)

/-- The binding predicate `fun b => ∃ bd, b = some bd ∧ Q bd`. -/
def existsBindPred (Q : Expr) : MetaM Expr := do
  let optB ← mkAppM ``Option #[mkConst ``ES.Binding]
  withLocalDeclD `b optB fun b => do
    let body ← withLocalDeclD `bd (mkConst ``ES.Binding) fun bd => do
      mkLambdaFVars #[bd] (mkAnd (← mkEq b (← mkAppM ``Option.some #[bd])) (Q.beta #[bd]))
    mkLambdaFVars #[b] (← mkAppM ``Exists #[body])

/-- A goal `∀ bm o, declLike? (w.envEntry e) = some (bm, o) → ∃ bd, bm[x]? = some bd ∧ Q bd`: the binding fact
`bind e ?o x (∃ bd, · = some bd ∧ Q bd)` at `w`, a goal. -/
def forallBindGoal? (g : MVarId) (t : Expr) : MetaM (Option MVarId) := g.withContext do
  let some (w, e, x, Q) ← forallBindOf? t | return none
  let o ← mkFreshExprMVar (← mkAppM ``Option #[mkConst ``ES.EnvId])
  let P ← existsBindPred Q
  let F ← mkFreshExprSyntheticOpaqueMVar (mkApp2 (mkConst ``Logic.Fact.holds) (mkApp4 (mkConst ``Logic.Fact.bind) e o x P) w) `fact
  let pf := mkAppN (mkConst ``forall_of_bind) #[e, o, x, Q, w, F]
  g.assign (← mkExpectedTypeHint pf t)
  return some F.mvarId!

/-- A record's statement at `w'` where the context says `∀ e, e < N → w'.envEntry e = W.envEntry e` (a stability
premise's): the same at `W` (and `e < N`), new goals. -/
def envEqGoal? (g : MVarId) (t : Expr) : MetaM (Option (MVarId × MVarId)) := g.withContext do
  let some (w', e, _, _) ← forallBindOf? t | return none
  for d in ← getLCtx do
    if d.isImplementationDetail || !d.type.isForall then continue
    let ty ← instantiateMVars d.type
    let .forallE _ _ (.forallE _ lt eqn _) _ := ty | continue
    unless lt.isAppOfArity ``LT.lt 4 && lt.appFn!.appArg! == .bvar 0 do continue
    let some (_, l, r) := eqn.eq? | continue
    unless l.isAppOfArity ``ES.State.envEntry 2 && l.appFn!.appArg! == w' && l.appArg! == .bvar 1 do continue
    unless r.isAppOfArity ``ES.State.envEntry 2 && r.appArg! == .bvar 1 do continue
    let W := r.appFn!.appArg!
    if W.hasLooseBVars then continue
    let N := lt.appArg!
    if N.hasLooseBVars then continue
    let gLt ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``LT.lt #[e, N])
    let heq := mkApp2 d.toExpr e gLt
    let lhs := mkApp2 (mkConst ``ES.State.envEntry) w' e
    let rhs := mkApp2 (mkConst ``ES.State.envEntry) W e
    let motive ← withLocalDeclD `z (← inferType lhs) fun z => do
      mkLambdaFVars #[z] (t.replace fun x => if x == lhs then some z else none)
    let t' := motive.beta #[rhs]
    let gN ← mkFreshExprSyntheticOpaqueMVar t'
    let pf ← mkEqMPR (← mkCongrArg motive heq) gN
    g.assign (← mkExpectedTypeHint pf t)
    return some (gN.mvarId!, gLt.mvarId!)
  return none

/-- A list unfolded to its literal elements (`none`: not a literal list within 512 cells). -/
partial def expandList (xs : Expr) (fuel : Nat := 512) : MetaM (Option (Array Expr)) := do
  if fuel == 0 then return none
  let xs ← whnfD xs
  if xs.isAppOfArity ``List.nil 1 then return some #[]
  if xs.isAppOfArity ``List.cons 3 then
    let some rest ← expandList xs.appArg! (fuel - 1) | return none
    return some (#[xs.appFn!.appArg!] ++ rest)
  return none

/-- A goal `xs.all p = true` whose `xs` unfolds to a literal list: `∀ x, x ∈ [a, …] → p x = true`, a new goal (one per
element after `forallMem?`). -/
def allGoal? (g : MVarId) (t : Expr) : MetaM (Option MVarId) := g.withContext do
  let some (_, l, r) := t.eq? | return none
  unless r.isConstOf ``Bool.true && l.isAppOfArity ``List.all 3 do return none
  let α := l.getAppArgs[0]!
  let xs := l.getAppArgs[1]!
  let p := l.getAppArgs[2]!
  -- (only records' existence, `decide (q.1 < w.envs.size)`: other conditions wait for the context's statement of them)
  let .lam _ _ pb _ := p | return none
  -- (or that each is not the next record, `q.1 != w.envs.size`: each one there, `bne_of_lt_size`)
  let isLt := pb.isAppOfArity ``Decidable.decide 2 && pb.appFn!.appArg!.isAppOfArity ``LT.lt 4
  let isBne := pb.isAppOfArity ``bne 4 && pb.appArg!.isAppOfArity ``Array.size 2
  unless isLt || isBne do return none
  let some elems ← expandList xs | return none
  let lit ← mkListLit α elems.toList
  let goalTy ← withLocalDeclD `x α fun x => do
    let mem ← mkAppM ``Membership.mem #[lit, x]
    withLocalDeclD `hx mem fun hx => do
      mkForallFVars #[x, hx] (← mkEq (p.beta #[x]) (mkConst ``Bool.true))
  let G ← mkFreshExprSyntheticOpaqueMVar goalTy
  -- (`xs` is the literal list by definition)
  let pf := mkAppN (mkConst ``all_of_forall_mem) #[α, lit, p, G]
  g.assign (← mkExpectedTypeHint pf t)
  return some G.mvarId!

/-- A goal `decide P = true`: `P`, a new goal; `(a != b.size) = true`: `a < b.size` (`bne_of_lt_size`). -/
def decideGoal? (g : MVarId) (t : Expr) : MetaM (Option MVarId) := g.withContext do
  let some (_, l, r) := t.eq? | return none
  if r.isConstOf ``Bool.true && l.isAppOfArity ``bne 4 && l.appArg!.isAppOfArity ``Array.size 2 then
    let a := l.appFn!.appArg!
    let b := l.appArg!
    let G ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``LT.lt #[a, b])
    g.assign (← mkExpectedTypeHint (mkAppN (mkConst ``bne_of_lt_size) #[a, b, G]) t)
    return some G.mvarId!
  unless r.isConstOf ``Bool.true && l.isAppOfArity ``Decidable.decide 2 do return none
  let P := l.appFn!.appArg!
  let inst := l.appArg!
  let G ← mkFreshExprSyntheticOpaqueMVar P
  let pf := mkAppN (mkConst ``decide_eq_true) #[P, inst, G]
  g.assign (← mkExpectedTypeHint pf t)
  return some G.mvarId!

/-- A callee's contract no composite discharged, `∀ w …, Frame fp s w → … → WP … (callImpl …) …` (a host-reaching
call such as `getActiveElementDeep`, which `microtask_all` kept as a premise): the closed fact `closed fp P` at `s`,
`P w := ∀ (the other binders), body`, which becomes a premise over the way from the start. -/
def callContractGoal? (g : MVarId) (t : Expr) : MetaM (Option MVarId) := g.withContext do
  let some tu ← unfoldToForall t | return none
  forallTelescope tu fun bs body => do
    -- (the conclusion a call's `WP`, not merely one that mentions a call: an obligation is walked)
    let some c := body.getAppFn.constName? | return none
    unless c.getString! == "WP" do return none
    unless (body.find? fun e => e.isConst && e.constName!.getString! == "callImpl").isSome do return none
    let some j ← bs.findIdxM? fun b => do
        let ty ← whnfR (← inferType b)
        return ty.isAppOfArity ``Logic.Frame 3 && bs.contains ty.appArg! && !bs.contains ty.appFn!.appArg!
      | return none
    let fr ← whnfR (← inferType bs[j]!)
    let w := fr.appArg!
    let s := fr.appFn!.appArg!
    let fp := fr.appFn!.appFn!.appArg!
    let some iw := bs.findIdx? (· == w) | return none
    -- `fp` and `s` name none of the binders
    if bs.any (fun b => fp.containsFVar b.fvarId! || s.containsFVar b.fvarId!) then return none
    let others := (List.range bs.size).filter (fun k => k != j && k != iw) |>.map (bs[·]!)
    let P ← mkLambdaFVars #[w] (← mkForallFVars others.toArray body)
    let F ← mkFreshExprSyntheticOpaqueMVar (mkApp2 (mkConst ``Logic.Fact.holds) (mkApp2 (mkConst ``Logic.Fact.closed) fp P) s) `fact
    let prf ← mkLambdaFVars bs (mkAppN F (#[w, bs[j]!] ++ others.toArray))
    g.assign (← mkExpectedTypeHint prf t)
    return some F.mvarId!

/-- A goal `∀ y, y ∈ [a, b, …] → P y` as `P a ∧ P b ∧ … ∧ True` (each a goal of its own, not one about a local). -/
def forallMem?(g : MVarId) (t : Expr) : MetaM (Option MVarId) := g.withContext do
  let .forallE n α body _ := t | return none
  let .forallE _ mem P' _ := body | return none
  unless mem.isAppOfArity ``Membership.mem 5 do return none
  unless mem.appArg! == .bvar 0 do return none
  let l := mem.appFn!.appArg!
  if l.hasLooseBVars || P'.hasLooseBVarInExplicitDomain 0 false then return none
  if P'.hasLooseBVar 0 then return none
  let some elems ← listElems l 4096 | return none
  let P := mkLambda n .default α (P'.lowerLooseBVars 1 1)
  let conj ← elems.foldrM (fun a acc => mkAppM ``And #[P.beta #[a], acc]) (mkConst ``True)
  let G ← mkFreshExprSyntheticOpaqueMVar conj
  let lvl ← getLevel α
  let _ := lvl
  let hAll ← mkExpectedTypeHint G (mkApp3 (mkConst ``AllL) α P l)
  g.assign (← mkExpectedTypeHint (mkApp4 (mkConst ``allL_mem) α P l hAll) t)
  return some G.mvarId!

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
    let h ← IO.FS.Handle.mk "facts_top.progress" .append
    h.putStrLn s!"{← IO.monoMsNow} collect {c.steps} steps, head {t.getAppFn.constName?.getD `fvar}"
    if c.steps % 100 == 0 then h.putStrLn s!"  times: {← stepReport}; carry {(← carryTimes.get).toList}"
    h.flush
  if t.isForall then
    -- `∀ o, a ≠ .obj o`: one premise (`a` is decided later, or stated at the start), not a goal about a local `o`
    if (notObj? t).isSome then
      unless ← notObjOne g do pendingPures.modify (·.push g)
      return
    if let some g' ← forallMem? g t then return ← collectGoal g' top s0 st (fuel - 1)
    if let some F ← callContractGoal? g t then pendingFacts.modify (·.push F); return
    -- a record's statement for any map and outer (`∀ bm o, declLike? … = some (bm, o) → …`) the context states at the
    -- same state: that hypothesis, the one that fits (unknowns such as a contract's record assigned)
    if (t.find? fun e => e.isConstOf ``Scope.declLike?).isSome then
      let ok ← g.withContext do
        let mut fits : Array LocalDecl := #[]
        for d in ← getLCtx do
          if d.isImplementationDetail || !d.type.isForall then continue
          let ty ← instantiateMVars d.type
          unless (ty.find? fun e => e.isConstOf ``Scope.declLike?).isSome do continue
          let saved ← saveState
          let ok ← try withReducible (isDefEq ty t) catch _ => pure false
          saved.restore
          if ok then fits := fits.push d
          if fits.size > 1 then break
        if fits.size == 1 then
          if ← withReducible (isDefEq (← instantiateMVars fits[0]!.type) t) then
            g.assign fits[0]!.toExpr; return true
        return false
      if ok then st.modify fun c => { c with closed := c.closed + 1 }; return
    -- a record's statement at a state whose records a stability premise equates with another's: that state's
    if let some (gN, gLt) ← envEqGoal? g t then
      collectGoal gLt top s0 st (fuel - 1)
      return ← collectGoal gN top s0 st (fuel - 1)
    -- a record's statement for any map and outer: a binding fact (`forall_of_bind`)
    if let some F ← forallBindGoal? g t then pendingFacts.modify (·.push F); return
    -- a statement about one object's entry alone (`∀ k p, (w.objEntry o).props.get? k = some p → …`): an `objP` fact
    if (t.find? fun e => e.isAppOfArity ``ES.State.objEntry 2).isSome then
      if let some F ← objFactGoal? g then pendingFacts.modify (·.push F); return
    let (h, gI) ← g.intro1P
    let gD ← timed "walk:destructure" (destructure gI h)
    -- the fact lists among what was introduced: their existential facts made exact
    let gN ← timed "walk:normalize" <| gD.withContext do
      let mut gc := gD
      let mut fresh : Array LocalDecl := #[]
      for d in ← getLCtx do
        if d.isImplementationDetail then continue
        if d.userName.toString.startsWith "exact" || d.userName.toString.startsWith "nf" || d.userName.toString.startsWith "rawf" then continue
        unless (← normalized.get).contains d.fvarId do
          normalized.modify (·.insert d.fvarId)
          fresh := fresh.push d
          try gc ← normalizeFacts gc d.toExpr catch _ => pure ()
      -- single-fact hypotheses as fact lists
      try gc ← rawFacts gc fresh catch _ => pure ()
      pure gc
    let gN ← (try timed "walk:substOuter" (substOuter gN top) catch e => do
      let hh ← IO.FS.Handle.mk "facts_top.progress" .append
      hh.putStrLn s!"SUBSTOUTER error {((toString (← e.toMessageData.format)).replace "\n" " ").take 600}"; hh.flush
      pure gN)
    let gN ← (try timed "walk:substSame" (substSame gN top s0) catch e => do
      let hh ← IO.FS.Handle.mk "facts_top.progress" .append
      hh.putStrLn s!"SUBSTSAME error {((toString (← e.toMessageData.format)).replace "\n" " ").take 600}"; hh.flush
      pure gN)
    return ← collectGoal gN top s0 st (fuel - 1)
  if t.isAppOfArity ``Exists 2 then
    let before := (← propWitnesses.get).size
    if let some g' ← openExists g then
      let ws := (← propWitnesses.get).extract before (← propWitnesses.get).size
      collectGoal g' top s0 st (fuel - 1)
      for w in ws do collectGoal w top s0 st (fuel - 1)
      return
  if t.isAppOfArity ``And 2 then
    -- a conjunction's identifications of functions' records (`with u_d.env = d.env`, both unknown) made first: else
    -- the records are taken for different ones on the way (assumed distinct) before the identification is reached
    unless (← andScanned.get).contains g do
      g.withContext do
        let mut todo := #[t]
        let mut n := 0
        while !todo.isEmpty && n < 4096 do
          let c := todo.back!
          todo := todo.pop
          n := n + 1
          if c.isAppOfArity ``And 2 then
            todo := todo.push c.appFn!.appArg! |>.push c.appArg!
          else if let some (_, l, r) := c.eq? then
            if l.isAppOfArity ``ES.FuncData.env 1 && r.isAppOfArity ``ES.FuncData.env 1 then
              let l ← instantiateMVars l
              let r ← instantiateMVars r
              if l.appArg!.getAppFn.isMVar && r.appArg!.getAppFn.isMVar && l != r then
                let saved ← saveState
                unless ← (try isDefEq l r catch _ => pure false) do saved.restore
    let (a, b) ← g.withContext do
      let a ← mkFreshExprSyntheticOpaqueMVar t.appFn!.appArg!
      let b ← mkFreshExprSyntheticOpaqueMVar t.appArg!
      g.assign (mkApp4 (mkConst ``And.intro) t.appFn!.appArg! t.appArg! a b)
      pure (a, b)
    andScanned.modify (·.insert a.mvarId! |>.insert b.mvarId!)
    -- the right first: a spec's `Pre` puts its facts last, and they assign what its pure premises read
    collectGoal b.mvarId! top s0 st (fuel - 1)
    collectGoal a.mvarId! top s0 st (fuel - 1)
    return
  if t.isAppOfArity ``Logic.Facts.holds 2 then
    return ← timed "walk:facts" (collectFacts g top s0 st)
  -- a definition (a spec's `Pre`) whose unfolding is a conjunction, an `∃`, a `∀` or facts: unfolded
  -- (one that names no state, such as `QueueJob.QueuesJob fn fQ bQ`, a built-in's behaviour, stays one premise)
  let namesState ← g.withContext do
    (collectFVars {} t).fvarIds.anyM fun x => do return (← whnfR (← x.getType)).isConstOf ``ES.State
  if let some c := t.getAppFn.constName? then
    unless c == ``Logic.Frame || !namesState do
      if let some u ← g.withContext (unfoldDefinition? t) then
        let u ← g.withContext (whnfR u)
        if u.isForall || u.isAppOfArity ``And 2 || u.isAppOfArity ``Exists 2 || u.isAppOfArity ``Logic.Facts.holds 2 then
          return ← collectGoal (← g.replaceTargetDefEq u) top s0 st (fuel - 1)
  -- an identification a composite asks for (`with u_d.env = d.env`): two functions' records, unknown, one record
  if let some (_, l, r) := (← g.withContext (instantiateMVars t)).eq? then
    if l.isAppOfArity ``ES.FuncData.env 1 && r.isAppOfArity ``ES.FuncData.env 1 &&
        l.appArg!.getAppFn.isMVar && r.appArg!.getAppFn.isMVar then
      let ok ← g.withContext do
        let saved ← saveState
        if ← (try isDefEq l r catch _ => pure false) then
          g.assign (← mkEqRefl l); pure true
        else saved.restore; pure false
      if ok then st.modify fun c => { c with closed := c.closed + 1 }; return
  -- the rest: an assumption, or counted
  -- an assumption with the same head, matched reducibly, alone when the goal has unknowns
  let ok ← timed "walk:assume" (assumeOne g)
  if ok then st.modify fun c => { c with closed := c.closed + 1 }; return
  -- a fact in disguise: a fact goal
  if let some F ← toFactGoal g then pendingFacts.modify (·.push F); return
  if ← rflOne g then st.modify fun c => { c with closed := c.closed + 1 }; return
  -- about a later state's realms: about the start's
  if let some G ← realmGoal g s0 then
    if ← assumeOne G then st.modify fun c => { c with closed := c.closed + 1 }; return
    pendingPures.modify (·.push G); return
  -- a footprint's side condition over its entries (`fp.binds.all (fun q => decide (q.1 < w.envs.size)) = true`) no
  -- hypothesis states: one goal per entry, `decide` removed
  if let some G ← allGoal? g t then return ← collectGoal G top s0 st (fuel - 1)
  if let some G ← decideGoal? g t then return ← collectGoal G top s0 st (fuel - 1)
  pendingPures.modify (·.push g)

/-- The subterms `x.fuel` and the unknowns of `t` (every subterm visited, not only the immediate ones). -/
partial def fuelAtoms (t : Expr) : Array Expr :=
  let rec go (e : Expr) (acc : Array Expr) : Array Expr :=
    if e.isAppOfArity ``ES.State.fuel 1 || e.isMVar then (if acc.contains e then acc else acc.push e) else
    match e with
    | .app f a => go a (go f acc)
    | .mdata _ b => go b acc
    | .lam _ d b _ | .forallE _ d b _ => go b (go d acc)
    | .letE _ d v b _ => go b (go v (go d acc))
    | .proj _ _ b => go b acc
    | _ => acc
  go t #[]

/-- A fuel bound (`k ≤ w.fuel`, `s.fuel ≤ w.fuel + k`, …) by `omega` over the fuel hypotheses alone: each `x.fuel` made
a fresh number in a small context (the context's other hypotheses are not scanned), the proof put back. -/
def fuelOne (g : MVarId) : TermElabM Bool := g.withContext do
  if ← g.isAssigned then return true
  let goal ← instantiateMVars (← g.getType)
  let isArith (t : Expr) : Bool := t.isAppOfArity ``LE.le 4 || t.isAppOfArity ``LT.lt 4
  let hasFuel (t : Expr) : Bool := (t.find? fun e => e.isAppOfArity ``ES.State.fuel 1).isSome
  unless isArith goal && hasFuel goal do return false
  -- the atoms `x.fuel` of the goal and the fuel hypotheses
  let mut cand : Array (Expr × Expr) := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let t ← instantiateMVars d.type
    if isArith t && hasFuel t then cand := cand.push (d.toExpr, t)
  let mut atoms : Array Expr := #[]
  for t in #[goal] ++ cand.map (·.2) do
    -- `x.fuel`, and unknowns (constants not fixed yet, `?kC`) as numbers
    let es := fuelAtoms t
    for e in es do
      if !atoms.contains e then atoms := atoms.push e
  let abstract (t : Expr) (vals : Array Expr) : Expr :=
    t.replace fun e => match atoms.findIdx? (· == e) with
      | some i => some vals[i]!
      | none => none
  -- only what mentions nothing but the atoms
  let pure0 (t : Expr) : Bool := let u := abstract t (atoms.map fun _ => mkNatLit 0); !u.hasFVar && !u.hasExprMVar
  let dbg := (toString (← ppExpr goal)).startsWith "2400"
  if dbg then
    let hh ← IO.FS.Handle.mk "facts_top.progress" .append
    hh.putStrLn s!"FUELONE goal pure {pure0 goal}, atoms {← atoms.mapM fun a => do pure ((toString (← ppExpr a)).take 30).toString}"
    for (_, t) in cand do hh.putStrLn s!"  cand pure {pure0 t}: {((toString (← ppExpr t)).take 120).toString}"
    hh.flush
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
          let rem ← Term.withoutErrToSorry <| Tactic.run mv.mvarId! (Tactic.withoutRecover (Tactic.evalTactic (← `(tactic| omega))))
          unless rem.isEmpty do saved.restore; return none
          return some (← instantiateMVars (← mkLambdaFVars (fvs ++ hfs) (← instantiateMVars mv)))
        catch e =>
          if dbg then
            let hh ← IO.FS.Handle.mk "facts_top.progress" .append
            hh.putStrLn s!"FUELONE omega failed: {((toString (← e.toMessageData.format)).take 600).toString}"; hh.flush
          saved.restore; return none
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
        let hm ← idxLt i Ls
        let gi ← factAt Ls w h i
        let gi ← mkExpectedTypeHint gi (mkApp2 (mkConst ``Logic.Fact.holds) e w)
        let pf ← mkAppOptM ``Logic.Fact.bind_get #[none, none, none, none, w, bs, hd, gi]
        if ← (defEqLog "L788" (← whnfR (← inferType pf)) goal) then
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
      if ← (defEqLog "L810" t goal) then g.assign d.toExpr; return true
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
            if ← (defEqLog "L821" (← inferType r) goal) then g.assign r; return true
            saved.restore
          catch _ => saved.restore
  return false

/-- A fact goal `Fact.proto o p` at `w`: split into the object's existence (a fact goal) and its prototype (a pure goal,
which frames keep whatever their footprints: `protoOne`). -/
def protoSplit (g : MVarId) : MetaM Bool := g.withContext do
  if ← g.isAssigned then return false
  let t ← instantiateMVars (← g.getType)
  unless t.isAppOfArity ``Logic.Fact.holds 2 do return false
  let f ← whnfR t.appFn!.appArg!
  unless f.isAppOfArity ``Logic.Fact.proto 2 do return false
  let w := t.appArg!
  -- at the start a prototype fact is a start fact
  if (← startState.get) == some w then return false
  let o := f.appFn!.appArg!
  let p := f.appArg!
  let ex := mkApp2 (mkConst ``Logic.Fact.kindP) o (mkLambda `K .default (mkConst ``ES.Kind) (mkConst ``True))
  let gE ← mkFreshExprSyntheticOpaqueMVar (mkApp2 (mkConst ``Logic.Fact.holds) ex w)
  let gP ← mkFreshExprSyntheticOpaqueMVar (← mkEq (mkApp (mkConst ``ES.Obj.proto) (mkApp2 (mkConst ``ES.State.objEntry) w o)) p)
  let hl ← mkAppM ``And.left #[← mkExpectedTypeHint gE (← mkAppM ``And #[← mkAppM ``LT.lt #[o, ← mkAppM ``Array.size #[mkApp (mkConst ``ES.State.heap) w]], mkConst ``True])]
  g.assign (← mkExpectedTypeHint (← mkAppM ``And.intro #[hl, gP]) t)
  pendingFacts.modify (·.push gE.mvarId!)
  pendingPures.modify (·.push gP.mvarId!)
  return true

/-- A lookup `?u[k]? = r` in an existential's map (`u_…`, a callee's record map its facts do not fix): the map of
the latest record hypothesis in the context (`declLike? (w.envEntry e) = some (m, o)`, the record as the callee runs
on it). The lookups are then proved of that map, or fail (a witness, never an assumption). -/
def existsMapOne (g : MVarId) : MetaM Bool := g.withContext do
  if ← g.isAssigned then return true
  let goal ← instantiateMVars (← g.getType)
  let some (_, l, _) := goal.eq? | return false
  unless l.isAppOf ``GetElem?.getElem? && l.getAppNumArgs ≥ 2 do return false
  let M := l.getAppArgs[l.getAppNumArgs - 2]!
  unless M.isMVar do return false
  if ← M.mvarId!.isAssigned then return false
  unless (← M.mvarId!.getDecl).userName.toString.startsWith "u_" do return false
  -- a fact goal about the map (a whole record, `recordIs`) fixes it by matching: not chosen here
  for g2 in ← pendingFacts.get do
    if ← g2.isAssigned then continue
    let t2 ← instantiateMVars (← g2.getType)
    if t2.containsMVar M.mvarId! then
      let h ← IO.FS.Handle.mk "facts_top.progress" .append
      h.putStrLn s!"EXISTSMAP {(← M.mvarId!.getDecl).userName}: a fact mentions it: {((toString (← g2.withContext (ppExpr t2))).replace "\n" " ").take 400}"
      g2.withContext do
        for d in ← getLCtx do
          let ty ← instantiateMVars d.type
          if let some (_, l, _) := ty.eq? then
            if l.isAppOfArity ``Scope.declLike? 1 then
              h.putStrLn s!"  GDECL {d.userName} : {((toString (← ppExpr ty)).replace "\n" " ").take 600}"
          if ty.isAppOfArity ``Logic.Frame 3 then
            h.putStrLn s!"  GFRAME {((toString (← ppExpr ty.appFn!.appFn!.appArg!)).replace "\n" " ").take 400} : {((toString (← ppExpr ty.appFn!.appArg!)).take 20).toString} → {((toString (← ppExpr ty.appArg!)).take 20).toString}"
        let lk ← instantiateMVars (← g.getType)
        h.putStrLn s!"  LOOKUP-GOAL-CTX-STATES (goal {((toString (← ppExpr lk)).take 120).toString})"
      h.flush
      return false
  let mut last : Option Expr := none
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    let some (_, l', r') := ty.eq? | continue
    unless l'.isAppOfArity ``Scope.declLike? 1 && r'.isAppOfArity ``Option.some 2 do continue
    let pr := r'.appArg!
    unless pr.isAppOfArity ``Prod.mk 4 do continue
    let m := pr.appFn!.appArg!
    if m.hasExprMVar then continue
    last := some m
  let logE (msg : String) : MetaM Unit := do
    let h ← IO.FS.Handle.mk "facts_top.progress" .append
    h.putStrLn s!"EXISTSMAP {(← M.mvarId!.getDecl).userName}: {msg}"; h.flush
  let some m := last | logE "no record hypothesis"; return false
  let saved ← saveState
  -- the witness chosen; the goal stays pending (proved of `m`, or not)
  if ← (try isDefEq M m catch _ => pure false) then
    logE s!"chose {(toString (← ppExpr m)).take 40}"
    pendingPures.modify (·.push g); return true
  logE s!"cannot be {(toString (← ppExpr m)).take 40} (scope?)"
  saved.restore; return false

/-- A whole-record fact `Fact.recordIs e M o` at `w` from a record hypothesis there with the same map: the record's
existence from a record fact at `w` (a fact goal: record facts are kept by every frame). -/
def recordFromDecl (g : MVarId) : TermElabM Bool := g.withContext do
  if ← g.isAssigned then return true
  let t ← instantiateMVars (← g.getType)
  unless t.isAppOfArity ``Logic.Fact.holds 2 do return false
  let w := t.appArg!
  let f ← whnfR t.appFn!.appArg!
  unless f.isAppOfArity ``Logic.Fact.recordIs 3 do return false
  let e := f.getAppArgs[0]!
  let M ← instantiateMVars f.getAppArgs[1]!
  let o := f.getAppArgs[2]!
  -- an unknown map (a callee's record map): a record has one map per state, so it takes a hypothesis' map —
  -- preferring one that a lookup hypothesis relates to a pending lookup in the unknown map
  let mut prefer : Array Expr := #[]
  if M.isMVar then
    let mut keys : Array Expr := #[]
    for pg in ← pendingPures.get do
      if ← pg.isAssigned then continue
      let pt ← instantiateMVars (← pg.getType)
      for lk in collectLookups pt do
        if lk.getAppNumArgs ≥ 2 && lk.getAppArgs[lk.getAppNumArgs - 2]! == M then
          keys := keys.push lk.getAppArgs[lk.getAppNumArgs - 1]!
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      let ty ← instantiateMVars d.type
      let some (_, l, r) := ty.eq? | continue
      unless l.isAppOf ``GetElem?.getElem? && r.isAppOfArity ``Option.some 2 && l.getAppNumArgs ≥ 2 do continue
      if keys.contains l.getAppArgs[l.getAppNumArgs - 1]! then prefer := prefer.push l.getAppArgs[l.getAppNumArgs - 2]!
  let decls ← do
    let ds := (← getLCtx).decls.toArray.filterMap id
    -- preferred maps first
    let isPref (d : LocalDecl) : TermElabM Bool := do
      let ty ← instantiateMVars d.type
      match ty.eq? with
      | some (_, _, r) => pure (r.isAppOfArity ``Option.some 2 && r.appArg!.isAppOfArity ``Prod.mk 4 && prefer.contains r.appArg!.appFn!.appArg!)
      | none => pure false
    let a ← ds.filterM isPref
    let b ← ds.filterM fun d => do return !(← isPref d)
    pure (a ++ b)
  for d in decls do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    let some (_, l, r) := ty.eq? | continue
    unless l.isAppOfArity ``Scope.declLike? 1 && r.isAppOfArity ``Option.some 2 do continue
    let ee := l.appArg!
    unless ee.isAppOfArity ``ES.State.envEntry 2 do continue
    -- at `w`, or at an earlier state framed to `w` (carried: frames that leave the record keep it whole)
    let a := ee.appFn!.appArg!
    let pf? ← if a == w then pure none else framePath a w
    if a != w && pf?.isNone then continue
    let pr := r.appArg!
    unless pr.isAppOfArity ``Prod.mk 4 do continue
    unless pr.appFn!.appArg! == M || (M.isMVar && !pr.appFn!.appArg!.hasExprMVar) do continue
    let saved ← saveState
    let rlog (msg : String) : MetaM Unit := do
      if M.isMVar then
        let h ← IO.FS.Handle.mk "facts_top.progress" .append
        h.putStrLn s!"RECDECL {msg} (hyp at {(toString (← ppExpr a)).take 10}, map {(toString (← ppExpr pr.appFn!.appArg!)).take 20})"; h.flush
    unless ← withReducible (isDefEq ee.appArg! e) do rlog "env differs"; saved.restore; continue
    -- (an unknown outer is never made a walk-local's: the record's outer, found elsewhere or left a start fact's)
    let top ← topLocals.get
    if (← instantiateMVars o).isMVar && pr.appArg!.hasAnyFVar (fun x => !top.contains x) then
      saved.restore; continue
    unless ← withReducible (isDefEq pr.appArg! o) do rlog "outer differs"; saved.restore; continue
    unless ← withReducible (isDefEq pr.appFn!.appArg! M) do rlog "map differs"; saved.restore; continue
    let unknownMap := M.isMVar
    let M := pr.appFn!.appArg!
    let rf := mkApp2 (mkConst ``Logic.Fact.record) e o
    let gR ← mkFreshExprSyntheticOpaqueMVar (mkApp2 (mkConst ``Logic.Fact.holds) rf a)
    -- `(record e o).holds a` unfolds to `e < a.envs.size ∧ ∃ bs, …`
    let unf ← whnf (mkApp2 (mkConst ``Logic.Fact.holds) rf a)
    unless unf.isAppOfArity ``And 2 do saved.restore; continue
    let hl ← mkAppM ``And.left #[← mkExpectedTypeHint gR unf]
    let fIs := mkApp3 (mkConst ``Logic.Fact.recordIs) e M o
    let hA ← mkExpectedTypeHint (← mkAppM ``And.intro #[hl, d.toExpr]) (mkApp2 (mkConst ``Logic.Fact.holds) fIs a)
    match pf? with
    | none => g.assign (← mkExpectedTypeHint hA t)
    | some pf =>
      try
        -- the record existed at the start (a start premise, or proved from start facts): with frames from the
        -- start, records made since are other records (`closeNe` by sizes along frames)
        let startHyp ← match ← startState.get with
          | some s0 => do
            let lt0 ← mkAppM ``LT.lt #[e, ← mkAppM ``Array.size #[mkApp (mkConst ``ES.State.envs) s0]]
            let gS ← mkFreshExprSyntheticOpaqueMVar lt0
            pure (some (gS, lt0))
          | none => pure none
        let one ← appFacts ``Logic.Facts.holds_cons #[fIs, mkApp (mkConst ``List.nil [Level.zero]) (mkConst ``Logic.Fact), a, hA,
          ← appFacts ``Logic.Facts.holds_nil #[a]]
        carryDebug.set unknownMap
        let (L2, prf, nkept) ← match startHyp with
          | some (gS, lt0) => withLocalDeclD `hEnvStart lt0 fun hS => do
              let (L2, prf, nkept, _) ← carry one pf
              pure (L2, mkApp (← mkLambdaFVars #[hS] prf) gS, nkept)
          | none => do
              let (L2, prf, nkept, _) ← carry one pf
              pure (L2, prf, nkept)
        carryDebug.set false
        if nkept != 1 then rlog "not carried"; saved.restore; continue
        if let some (gS, _) := startHyp then pendingPures.modify (·.push gS.mvarId!)
        let hm1 ← idxLt 0 L2
        let g0 ← appFacts ``Logic.Facts.get #[L2, w, prf, mkNatLit 0, hm1]
        g.assign (← mkExpectedTypeHint g0 t)
      catch _ => saved.restore; continue
    pendingFacts.modify (·.push gR.mvarId!)
    return true
  return false

/-- A binding fact `Fact.bind e oG x (· = some v)` at `w` from a record hypothesis there, `declLike? (w.envEntry e) =
some (M, oG)`: the lookup `M[x]? = some v` a pure goal (through `modify`s: `modifyOne`). -/
def bindFromDecl (g : MVarId) : MetaM Bool := g.withContext do
  if ← g.isAssigned then return true
  let t ← instantiateMVars (← g.getType)
  unless t.isAppOfArity ``Logic.Fact.holds 2 do return false
  let w := t.appArg!
  let f ← whnfR t.appFn!.appArg!
  unless f.isAppOfArity ``Logic.Fact.bind 4 do return false
  let env := f.getAppArgs[0]!
  let oG := f.getAppArgs[1]!
  let x := f.getAppArgs[2]!
  let P := f.getAppArgs[3]!
  -- `fun b => b = some v`
  let .lam _ _ body _ := P | return false
  let some (_, lb, rb) := body.eq? | return false
  unless lb == .bvar 0 && rb.isAppOfArity ``Option.some 2 && !rb.hasLooseBVars do return false
  let v := rb.appArg!
  -- not a value still unknown, which matching a binding fact fixes (a known shape with unknown parts is fine: the
  -- record is the hypothesis's, nothing is chosen, and the lookup left is a pure goal)
  if (← instantiateMVars v).isMVar then return false
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    let some (_, l, r) := ty.eq? | continue
    unless l.isAppOfArity ``Scope.declLike? 1 && r.isAppOfArity ``Option.some 2 do continue
    let ee := l.appArg!
    unless ee.isAppOfArity ``ES.State.envEntry 2 && ee.appFn!.appArg! == w do continue
    let pr := r.appArg!
    unless pr.isAppOfArity ``Prod.mk 4 do continue
    let M := pr.appFn!.appArg!
    let saved ← saveState
    unless ← withReducible (isDefEq ee.appArg! env) do saved.restore; continue
    unless ← withReducible (isDefEq pr.appArg! oG) do saved.restore; continue
    let lookT ← mkEq (← mkAppM ``GetElem?.getElem? #[M, x]) rb
    let gL ← mkFreshExprSyntheticOpaqueMVar lookT
    let pf ← mkAppOptM ``Logic.bind_fact_of #[w, ee.appArg!, M, pr.appArg!, x, v, d.toExpr, gL]
    if ← withReducible (isDefEq (← inferType pf) t) then
      g.assign pf
      pendingPures.modify (·.push gL.mvarId!)
      return true
    saved.restore
  return false

/-- A prototype `(w.objEntry o).proto = p` of objects of the start (no locals): from a start fact `Fact.proto o p`,
carried by `proto_frame` (frames keep existing objects' prototypes). -/
def protoStart (g : MVarId) : MetaM Bool := g.withContext do
  if ← g.isAssigned then return true
  let some s0 ← startState.get | return false
  let goal ← instantiateMVars (← g.getType)
  let some (_, lhs, p) := goal.eq? | return false
  unless lhs.isAppOfArity ``ES.Obj.proto 1 && lhs.appArg!.isAppOfArity ``ES.State.objEntry 2 do return false
  let w := lhs.appArg!.appFn!.appArg!
  let o := lhs.appArg!.appArg!
  let top ← topLocals.get
  if o.hasAnyFVar (fun y => !top.contains y) || p.hasAnyFVar (fun y => !top.contains y) then return false
  -- at the start itself it stays a premise (a start fact would only be split back into it)
  if w == s0 then return false
  let pf ← framePath s0 w
  if pf.isNone then return false
  let f := mkApp2 (mkConst ``Logic.Fact.proto) o p
  let gF ← mkFreshExprSyntheticOpaqueMVar (mkApp2 (mkConst ``Logic.Fact.holds) f s0)
  let ltT ← mkAppM ``LT.lt #[o, ← mkAppM ``Array.size #[mkApp (mkConst ``ES.State.heap) s0]]
  let eqT ← mkEq (mkApp (mkConst ``ES.Obj.proto) (mkApp2 (mkConst ``ES.State.objEntry) s0 o)) p
  let hAnd ← mkExpectedTypeHint gF (← mkAppM ``And #[ltT, eqT])
  let hl ← mkAppM ``And.left #[hAnd]
  let he ← mkAppM ``And.right #[hAnd]
  let prf ← match pf with
    | none => pure he
    | some pf => mkAppOptM ``Logic.proto_frame #[none, s0, w, o, p, pf, hl, he]
  g.assign (← mkExpectedTypeHint prf goal)
  pendingFacts.modify (·.push gF.mvarId!)
  return true


/-- A pure goal with lookups `m[k]?` that hypotheses state (`m[k]? = some b`): rewritten by them, then closed by
`Option.map`/`some` simplification and `rfl`. -/
def lookupRewriteOne (g : MVarId) : TermElabM Bool := g.withContext do
  if ← g.isAssigned then return true
  let goal ← instantiateMVars (← g.getType)
  unless (goal.find? fun e => e.isAppOf ``GetElem?.getElem?).isSome do return false
  -- a plain lookup `m[k]? = r` is a fact in disguise (`toFactGoal`), not rewritten into itself
  if let some (_, l, _) := goal.eq? then
    if l.isAppOf ``GetElem?.getElem? then return false
  let mut ds : Array LocalDecl := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    let some (_, l, r) := ty.eq? | continue
    unless l.isAppOf ``GetElem?.getElem? && r.isAppOfArity ``Option.some 2 do continue
    unless (goal.find? fun e => e == l).isSome do continue
    ds := ds.push d
  -- lookups no hypothesis states: `m[k]? = some ?b` as goals of their own (a binding fact fixes `?b`)
  let mut extra : Array (Expr × Expr) := #[]
  for l in collectLookups goal do
    if ds.any (fun d => match d.type.eq? with | some (_, l', _) => l' == l | none => false) then continue
    let ty ← inferType l
    unless ty.isAppOfArity ``Option 1 do continue
    let b ← mkFreshExprMVar ty.appArg! (userName := `u_bd)
    let gL ← mkFreshExprSyntheticOpaqueMVar (← mkEq l (← mkAppM ``Option.some #[b]))
    extra := extra.push (gL, ← inferType gL)
  if ds.isEmpty && extra.isEmpty then return false
  let saved ← saveState
  try
    let mut g2 := g
    let mut ids : Array Ident := #[]
    for d in ds do
      let n ← mkFreshUserName `hlk
      let (_, g3) ← (← g2.assert n d.type d.toExpr).intro1P
      g2 := g3
      ids := ids.push (mkIdent n)
    for (gL, ty) in extra do
      let n ← mkFreshUserName `hlk
      let (_, g3) ← (← g2.assert n ty gL).intro1P
      g2 := g3
      ids := ids.push (mkIdent n)
    let lemmas : Array (TSyntax ``Lean.Parser.Tactic.simpLemma) ← ids.mapM fun i =>
      `(Lean.Parser.Tactic.simpLemma| $i:ident)
    let rem ← Term.withoutErrToSorry <| Tactic.run g2 (Tactic.withoutRecover (Tactic.evalTactic
      (← `(tactic| (simp only [$lemmas,*, Option.map_some, Option.some.injEq]) <;> try rfl))))
    if rem.isEmpty then
      for (gL, _) in extra do pendingPures.modify (·.push gL.mvarId!)
      return true
    saved.restore; return false
  catch _ => saved.restore; return false

/-- A lookup through `HashMap.modify`s (`(m.modify k f)[k']? = r`): simplified by `getElem?_modify`, the keys'
comparisons decided; what is left (a lookup in the map below) is a pure goal again. -/
def modifyOne (g : MVarId) : TermElabM Bool := g.withContext do
  if ← g.isAssigned then return true
  let goal ← instantiateMVars (← g.getType)
  let some (_, lhs, _) := goal.eq? | return false
  unless lhs.isAppOf ``GetElem?.getElem? do return false
  unless (lhs.find? fun e => e.isAppOf ``Std.HashMap.modify).isSome do return false
  let saved ← saveState
  try
    let rem ← Term.withoutErrToSorry <| Tactic.run g (Tactic.withoutRecover (Tactic.evalTactic
      (← `(tactic| simp (config := { decide := true }) only [Std.HashMap.getElem?_modify, ↓reduceIte, beq_self_eq_true, ite_true, ite_false]))))
    match rem with
    | [] => return true
    | [g'] =>
      let t' ← instantiateMVars (← g'.getType)
      if (t'.find? fun e => e.isAppOf ``Std.HashMap.modify).isSome then saved.restore; return false
      -- lookups left in the map below: rewritten by the hypotheses that state them (`m[k]? = some b`)
      do
        -- the hypotheses named so the tactic can use them
        let saved2 ← saveState
        try
          let mut g2 := g'
          let mut ids : Array Ident := #[]
          let ds ← g'.withContext do
            let mut ds : Array LocalDecl := #[]
            for d in ← getLCtx do
              if d.isImplementationDetail then continue
              let ty ← instantiateMVars d.type
              let some (_, l, r) := ty.eq? | continue
              unless l.isAppOf ``GetElem?.getElem? && r.isAppOfArity ``Option.some 2 do continue
              unless (t'.find? fun e => e == l).isSome do continue
              ds := ds.push d
            pure ds
          for d in ds do
            let n ← mkFreshUserName `hlk
            let (_, g3) ← (← g2.assert n d.type d.toExpr).intro1P
            g2 := g3
            ids := ids.push (mkIdent n)
          if !ids.isEmpty then
            let lemmas : Array (TSyntax ``Lean.Parser.Tactic.simpLemma) ← ids.mapM fun i =>
              `(Lean.Parser.Tactic.simpLemma| $i:ident)
            let rem2 ← Term.withoutErrToSorry <| Tactic.run g2 (Tactic.withoutRecover (Tactic.evalTactic
              (← `(tactic| simp only [$lemmas,*, Option.map_some, Option.some.injEq]))))
            if rem2.isEmpty then return true
          saved2.restore
        catch _ => saved2.restore
      pendingPures.modify (·.push g'); return true
    | _ => saved.restore; return false
  catch _ => saved.restore; return false

/-- `a ≠ b` with one side fresh (`x.heap.size ≤ f` in the context) and the other an object of the start (no local):
its existence at the start is a fact goal there, frames make heaps only grow (`Frame.heap_le`). -/
def freshOne (g : MVarId) : MetaM Bool := g.withContext do
  if ← g.isAssigned then return true
  let some s0 ← startState.get | return false
  let goal ← instantiateMVars (← g.getType)
  unless goal.isAppOfArity ``Ne 3 do return false
  let a := goal.appFn!.appArg!
  let b := goal.appArg!
  unless (← whnfR (← inferType a)).isConstOf ``Nat do return false
  let top ← topLocals.get
  for (f, o, fFirst) in #[(a, b, true), (b, a, false)] do
    if o.hasAnyFVar (fun y => !top.contains y) then continue
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      let t ← instantiateMVars d.type
      unless t.isAppOfArity ``LE.le 4 && t.appArg! == f do continue
      let sz := t.appFn!.appArg!
      unless sz.isAppOfArity ``Array.size 2 && sz.appArg!.isAppOfArity ``ES.State.heap 1 do continue
      let x := sz.appArg!.appArg!
      let hle ← if x == s0 then mkAppM ``Nat.le_refl #[sz] else
        match ← framePath s0 x with
        | some pf => mkAppM ``Logic.Frame.heap_le #[pf]
        | none => continue
      let ex := mkApp2 (mkConst ``Logic.Fact.kindP) o (mkLambda `K .default (mkConst ``ES.Kind) (mkConst ``True))
      let gE ← mkFreshExprSyntheticOpaqueMVar (mkApp2 (mkConst ``Logic.Fact.holds) ex s0)
      let ho ← mkAppM ``And.left #[← mkExpectedTypeHint gE (← mkAppM ``And #[← mkAppM ``LT.lt #[o, ← mkAppM ``Array.size #[mkApp (mkConst ``ES.State.heap) s0]], mkConst ``True])]
      let lt ← mkAppM ``Nat.lt_of_lt_of_le #[ho, ← mkAppM ``Nat.le_trans #[hle, d.toExpr]]
      let ne ← mkAppM ``Nat.ne_of_lt #[lt]
      let pf ← if fFirst then mkAppM ``Ne.symm #[ne] else pure ne
      g.assign (← mkExpectedTypeHint pf goal)
      pendingFacts.modify (·.push gE.mvarId!)
      return true
  return false

/-- A binding goal `bind e o x (∃ bd, · = some bd ∧ Q bd)` at `w` from a record's statement for any map and outer at
`w` or before (`bind_of_forall_rec`: the record's fact there asked for, a goal), carried to `w`. -/
def forallBindOne (g : MVarId) : TermElabM Bool := g.withContext do
  if ← g.isAssigned then return true
  let t ← instantiateMVars (← g.getType)
  unless t.isAppOfArity ``Logic.Fact.holds 2 do return false
  let f := t.appFn!.appArg!
  let w := t.appArg!
  unless f.isAppOfArity ``Logic.Fact.bind 4 do return false
  let e := f.getAppArgs[0]!
  let x := f.getAppArgs[2]!
  for d in ← getLCtx do
    if d.isImplementationDetail || !d.type.isForall then continue
    let ty ← instantiateMVars d.type
    let some (a, e', x', Q) ← forallBindOf? ty | continue
    unless x' == x do continue
    let hh ← IO.FS.Handle.mk "facts_top.progress" .append
    let pf? ← if a == w then pure none else framePath a w
    if a != w && pf?.isNone then
      hh.putStrLn s!"FBIND {d.userName} at {← ppExpr a}: no path to {← ppExpr w}"
      for d2 in ← getLCtx do
        if d2.isImplementationDetail then continue
        let ty2 ← instantiateMVars d2.type
        if ty2.containsFVar w.fvarId! && (toString (← ppExpr ty2)).length < 600 then
          hh.putStrLn s!"   W' {d2.userName} : {((toString (← ppExpr ty2)).replace "\n" " ").take 300}"
      hh.flush; continue
    -- an exact goal `(· = some ?v)`, its value unknown: the binding the statement gives (`forallBindVal`)
    if true then
      let P := f.getAppArgs[3]!
      if let .lam _ _ body _ := P then
        if let some (_, lb, rb) := body.eq? then
          if lb == .bvar 0 && rb.isAppOfArity ``Option.some 2 && rb.appArg!.isMVar then
            let V := rb.appArg!
            let vd ← V.mvarId!.getDecl
            if !(← V.mvarId!.isAssigned) && vd.lctx.contains d.fvarId && (!a.isFVar || vd.lctx.contains a.fvarId!) then
              let saved ← saveState
              let o2 := f.getAppArgs[1]!
              let Rg ← mkFreshExprMVarAt vd.lctx vd.localInstances
                (mkApp2 (mkConst ``Logic.Fact.holds) (mkApp2 (mkConst ``Logic.Fact.record) e' o2) a) .syntheticOpaque `fact
              let val := mkAppN (mkConst ``forallBindVal) #[e', o2, x, Q, a, Rg, d.toExpr]
              if (← isDefEq e e') && (← isDefEq V val) then
                let pa := mkAppN (mkConst ``bind_exact_of_forall_rec) #[e', o2, x, Q, a, Rg, d.toExpr]
                let pa ← mkExpectedTypeHint pa (mkApp2 (mkConst ``Logic.Fact.holds) f a)
                -- at `w`: there, or carried along the frames from `a`
                let pw ← match pf? with
                  | none => pure (some pa)
                  | some pf => do
                    let one ← appFacts ``Logic.Facts.holds_cons #[f, mkApp (mkConst ``List.nil [Level.zero]) (mkConst ``Logic.Fact),
                      a, pa, ← appFacts ``Logic.Facts.holds_nil #[a]]
                    try
                      let (L2, prf, nkept, _) ← carry one pf
                      if nkept != 1 then pure none
                      else
                        let g0 ← appFacts ``Logic.Facts.get #[L2, w, prf, mkNatLit 0, ← idxLt 0 L2]
                        pure (some (← mkExpectedTypeHint g0 t))
                    catch _ => pure none
                if let some pw := pw then
                  pendingFacts.modify (·.push Rg.mvarId!)
                  g.assign (← mkExpectedTypeHint pw t)
                  return true
              saved.restore
    let saved ← saveState
    let o2 ← mkFreshExprMVar (← mkAppM ``Option #[mkConst ``ES.EnvId])
    let f2 := mkApp4 (mkConst ``Logic.Fact.bind) e' o2 x (← existsBindPred Q)
    unless ← (try withReducible (isDefEq f f2) catch _ => pure false) do
      hh.putStrLn s!"FBIND {d.userName}: no fit {← ppExpr f} vs {← ppExpr f2}"; hh.flush
      saved.restore; continue
    let Rg ← mkFreshExprSyntheticOpaqueMVar (mkApp2 (mkConst ``Logic.Fact.holds) (mkApp2 (mkConst ``Logic.Fact.record) e' o2) a) `fact
    let p2 := mkAppN (mkConst ``bind_of_forall_rec) #[e', o2, x, Q, a, Rg, d.toExpr]
    let p2 ← mkExpectedTypeHint p2 (mkApp2 (mkConst ``Logic.Fact.holds) f2 a)
    let pw ← match pf? with
      | none => pure (some p2)
      | some pf => do
        let one ← appFacts ``Logic.Facts.holds_cons #[f2, mkApp (mkConst ``List.nil [Level.zero]) (mkConst ``Logic.Fact),
          a, p2, ← appFacts ``Logic.Facts.holds_nil #[a]]
        try
          let (L2, prf, nkept, _) ← carry one pf
          if nkept != 1 then pure none
          else
            let g0 ← appFacts ``Logic.Facts.get #[L2, w, prf, mkNatLit 0, ← idxLt 0 L2]
            pure (some (← mkExpectedTypeHint g0 (mkApp2 (mkConst ``Logic.Fact.holds) f2 w)))
        catch _ => pure none
    let some pw := pw | hh.putStrLn s!"FBIND {d.userName}: not carried"; hh.flush; saved.restore; continue
    pendingFacts.modify (·.push Rg.mvarId!)
    g.assign (← mkExpectedTypeHint pw t)
    return true
  return false

/-- A goal `recordIs e ?M o` at `w`, its map unknown: from the record's fact at `w` (a goal), its map that fact's
(`recordMap`). -/
def recordIsFromRecord (g : MVarId) : TermElabM Bool := g.withContext do
  if ← g.isAssigned then return true
  let t ← instantiateMVars (← g.getType)
  unless t.isAppOfArity ``Logic.Fact.holds 2 do return false
  let f := t.appFn!.appArg!
  let w := t.appArg!
  unless f.isAppOfArity ``Logic.Fact.recordIs 3 do return false
  -- (at the start, the record with its map is a start fact as it is)
  if (← startState.get) == some w then return false
  let xs := f.getAppArgs
  let M := xs[1]!
  -- a map already taken from the record's fact at `w`: that fact's
  let M' ← instantiateMVars M
  if M'.isAppOfArity ``recordMap 4 && M'.getAppArgs[2]! == w then
    let ra := M'.getAppArgs
    let saved ← saveState
    if ← isDefEq xs[2]! ra[1]! then
      g.assign (← mkExpectedTypeHint (mkAppN (mkConst ``recordIs_of_record) #[ra[0]!, ra[1]!, w, ra[3]!]) t)
      return true
    saved.restore; return false
  unless M.isMVar do return false
  if ← M.mvarId!.isAssigned then return false
  let hh0 ← IO.FS.Handle.mk "facts_top.progress" .append
  hh0.putStrLn s!"RECMAP try at {← ppExpr w}"; hh0.flush
  let e := xs[0]!
  let o := xs[2]!
  -- (the record's fact goal in the map's own context: the map is assigned a term naming it)
  let md ← M.mvarId!.getDecl
  let Rg ← mkFreshExprMVarAt md.lctx md.localInstances
    (mkApp2 (mkConst ``Logic.Fact.holds) (mkApp2 (mkConst ``Logic.Fact.record) e o) w) .syntheticOpaque `fact
  let saved ← saveState
  unless ← isDefEq M (mkAppN (mkConst ``recordMap) #[e, o, w, Rg]) do
    let hh ← IO.FS.Handle.mk "facts_top.progress" .append
    let md ← M.mvarId!.getDecl
    hh.putStrLn s!"RECMAP no fit: map's context has w {md.lctx.contains w.fvarId!}, depth {md.depth}"; hh.flush
    saved.restore; return false
  pendingFacts.modify (·.push Rg.mvarId!)
  g.assign (← mkExpectedTypeHint (mkAppN (mkConst ``recordIs_of_record) #[e, o, w, Rg]) t)
  return true

/-- A pure goal about the binding `forallBindVal hr h` chose: a conjunct of its `Q` (`forallBindVal_spec`). -/
def forallValOne (g : MVarId) : MetaM Bool := g.withContext do
  if ← g.isAssigned then return true
  let t ← instantiateMVars (← g.getType)
  let some V := t.find? (·.isAppOfArity ``forallBindVal 7) | return false
  let xs := V.getAppArgs
  let Q := xs[3]!
  let spec := mkAppN (mkConst ``forallBindVal_spec) xs
  -- the conjuncts, each with its proof (a right-nested `∧`, as `Q` states them)
  let mut parts : Array (Expr × Expr) := #[]
  let mut p := spec
  let mut ty := (Q.beta #[V]).headBeta
  for _ in [:8] do
    let ty' ← whnfR ty
    if ty'.isAppOfArity ``And 2 then
      let a := ty'.appFn!.appArg!; let b := ty'.appArg!
      parts := parts.push (mkApp3 (mkConst ``And.left) a b p, a)
      p := mkApp3 (mkConst ``And.right) a b p
      ty := b
    else break
  parts := parts.push (p, ty)
  for (pc, tc) in parts do
    let saved ← saveState
    if ← (try withReducible (isDefEq tc t) catch _ => pure false) then
      g.assign (← mkExpectedTypeHint pc t); return true
    saved.restore
  return false

/-- `x = some ?v` from `x.isSome = true` (a binding's value only known to be there): `?v := x.get h`
(`Option.some_get`). -/
def someGetOne (g : MVarId) : MetaM Bool := g.withContext do
  if ← g.isAssigned then return true
  let goal ← instantiateMVars (← g.getType)
  if let some (_, l, r) := goal.eq? then
    -- (nested: a `←` inside `&&` would run before the tests)
    if r.isAppOfArity ``Option.some 2 && r.appArg!.isMVar then
     if !(← r.appArg!.mvarId!.isAssigned) then
      let V := r.appArg!
      let vd ← V.mvarId!.getDecl
      for d in ← getLCtx do
        if d.isImplementationDetail then continue
        unless d.type.isAppOfArity ``Eq 3 do continue
        let ty ← instantiateMVars d.type
        let some (_, l2, r2) := ty.eq? | continue
        unless l2.isAppOfArity ``Option.isSome 2 && l2.appArg! == l && r2.isConstOf ``Bool.true do continue
        unless vd.lctx.contains d.fvarId do continue
        unless (collectFVars {} l).fvarIds.all vd.lctx.contains do continue
        let saved ← saveState
        let val ← mkAppOptM ``Option.get #[none, l, d.toExpr]
        if ← isDefEq V val then
          let pf ← mkEqSymm (← mkAppOptM ``Option.some_get #[none, l, d.toExpr])
          g.assign (← mkExpectedTypeHint pf goal); return true
        saved.restore
  return false

/-- Pure goals and fact goals retried in turn (the pure ones assign what the facts' objects are) until nothing
changes: the rounds taken. -/
def fixedPoint (st : IO.Ref Collected) (rounds : Nat := 64) : TermElabM Nat := do
  -- facts at earlier states (carried) are searched only in a round after one that found nothing nearer
  let mut far := false
  -- each goal's statement when last tried (nothing else a step reads changes here): unchanged, it is not retried
  let mut tried ← triedNear.get
  let mut triedFar ← triedFarRef.get
  for r in [:rounds] do
    let mut progress := false
    let ps ← pendingPures.get
    let mut ps' := #[]
    for g in ps do
      let ty ← instantiateMVars (← g.getType)
      if (if far then triedFar.get? g else tried.get? g) == some ty then ps' := ps'.push g; continue
      if far then triedFar := triedFar.insert g ty else tried := tried.insert g ty
      let a1 ← timed "assume" (assumeOne g)
      let a1 ← if a1 then pure true else timed "forallVal" (forallValOne g)
      let a2 ← if a1 then pure true else timed "fuel" (fuelOne g)
      let a3 ← if a2 then pure true else timed "lookup" (lookupOne g)
      let a4 ← if a3 then pure true else timed "proto" (protoOne g)
      let a4 ← if a4 then pure true else timed "fresh" (freshOne g)
      let a4 ← if a4 then pure true else timed "protoStart" (protoStart g)
      let a4 ← if a4 then pure true else timed "modify" (modifyOne g)
      let a4 ← if a4 then pure true else timed "notObj" (notObjOne g)
      let a4 ← if a4 then pure true else timed "lookupRw" (lookupRewriteOne g)
      -- a lookup or prototype that became a fact in disguise (a witness chosen since): a fact goal
      let a4 ← if a4 then pure true else timed "toFact" (do
        match ← toFactGoal g with
        | some F => pendingFacts.modify (·.push F); pure true
        | none => pure false)
      let a4 ← if a4 || !far then pure a4 else timed "existsMap" (existsMapOne g)
      let a4 ← if a4 || !far then pure a4 else timed "someGet" (someGetOne g)
      if a4 then
        progress := true; st.modify fun c => { c with closed := c.closed + 1 }
      else ps' := ps'.push g
    -- goals the steps added during the round (after the snapshot) are kept
    pendingPures.modify fun cur => ps' ++ cur.extract ps.size cur.size
    let fs ← pendingFacts.get
    let mut fs' := #[]
    for g in fs do
      let ty ← instantiateMVars (← g.getType)
      if (if far then triedFar.get? g else tried.get? g) == some ty then fs' := fs'.push g; continue
      if far then triedFar := triedFar.insert g ty else tried := tried.insert g ty
      let mo ← timed (if far then "match far" else "match") (matchOne g far)
      let mo ← if mo then pure true else timed "protoSplit" (protoSplit g)
      let mo ← if mo then pure true else timed "bindDecl" (bindFromDecl g)
      let mo ← if mo then pure true else timed "recordDecl" (recordFromDecl g)
      let mo ← if mo then pure true else timed "forallBind" (forallBindOne g)
      let mo ← if mo || !far then pure mo else timed "recordIsMap" (recordIsFromRecord g)
      if mo then
        progress := true; st.modify fun c => { c with matched := c.matched + 1 }
      else fs' := fs'.push g
    pendingFacts.modify fun cur => fs' ++ cur.extract fs.size cur.size
    if !progress then
      if far then triedNear.set tried; triedFarRef.set triedFar; return r + 1
      far := true
    else far := false
  triedNear.set tried; triedFarRef.set triedFar
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

/-- Each `?k : Nat` with lower bounds among the pure goals (`n ≤ ?k`, `n` a closed numeral expression) fixed to the
largest: the fuel constants. -/
def fixFuelConstants : MetaM Nat := do
  let mut bounds : Array (MVarId × Nat) := #[]
  for g in ← pendingPures.get do
    let t ← instantiateMVars (← g.getType)
    unless t.isAppOfArity ``LE.le 4 do continue
    let rhs := t.appArg!
    unless rhs.isMVar do continue
    let lhs ← instantiateMVars t.appFn!.appArg!
    if lhs.hasExprMVar || lhs.hasFVar then continue
    let v ← whnfD lhs
    let some n := v.rawNatLit? <|> v.nat? | continue
    let m := rhs.mvarId!
    match bounds.findIdx? (·.1 == m) with
    | some i => bounds := bounds.modify i fun (m', k) => (m', max k n)
    | none => bounds := bounds.push (m, n)
  for (m, n) in bounds do
    unless ← m.isAssigned do m.assign (mkNatLit n)
  return bounds.size

/-- The value split for the kernel: each subterm of it over `bs` alone (no loose bound variable), a proof bigger than
`limit` objects (counted with sharing ignored, capped), made a theorem of its own over the variables of `bs` it names
(with those their types name), applied in its place: the kernel checks each with caches of its own (one 8M-object
proof needs ~48 GB, its parts far less). -/
partial def splitBig (base : Name) (lps : List Name) (bs : Array Expr) (val : Expr) (limit : Nat := 50000) : MetaM Expr := do
  let counter ← IO.mkRef 0
  let cache ← IO.mkRef (Std.HashMap.emptyWithCapacity (α := Expr) (β := Expr × Nat) 1024)
  let bset : Std.HashSet FVarId := bs.foldl (fun acc b => acc.insert b.fvarId!) {}
  let rec visit (e : Expr) : MetaM (Expr × Nat) := do
    if e.isAtomic then return (e, 1)
    -- (shared subterms: once)
    if let some r := (← cache.get).get? e then return r
    let (e', n) ← match e with
      | .app f a => do
        let (f', nf) ← visit f
        let (a', na) ← visit a
        pure (e.updateApp! f' a', nf + na + 1)
      | .lam _ t b _ => do
        let (t', nt) ← visit t
        let (b', nb) ← visit b
        pure (e.updateLambdaE! t' b', nt + nb + 1)
      | .forallE _ t b _ => do
        let (t', nt) ← visit t
        let (b', nb) ← visit b
        pure (e.updateForallE! t' b', nt + nb + 1)
      | .letE _ t v b _ => do
        let (t', nt) ← visit t
        let (v', nv) ← visit v
        let (b', nb) ← visit b
        pure (e.updateLetE! t' v' b', nt + nv + nb + 1)
      | .mdata _ b => do
        let (b', nb) ← visit b
        pure (e.updateMData! b', nb + 1)
      | .proj _ _ b => do
        let (b', nb) ← visit b
        pure (e.updateProj! b', nb + 1)
      | _ => pure (e, 1)
    let n := min n (10 * limit)
    let (e', n) ← do
      if n > limit && !e'.hasLooseBVars && !e'.hasMVar then
        if ← (try isProof e' catch _ => pure false) then
          let ty ← instantiateMVars (← inferType e')
          -- the variables it names, with those their types name, in `bs`'s order
          let mut need : Std.HashSet FVarId := {}
          let mut todo := ((collectFVars {} e').fvarIds ++ (collectFVars {} ty).fvarIds)
          while !todo.isEmpty do
            let x := todo.back!
            todo := todo.pop
            if need.contains x then continue
            need := need.insert x
            for y in (collectFVars {} (← instantiateMVars (← x.getType))).fvarIds do
              unless need.contains y do todo := todo.push y
          if need.toArray.all bset.contains then
            let xs := bs.filter (need.contains ·.fvarId!)
            let i ← counter.modifyGet fun i => (i, i + 1)
            let nm := base ++ Name.mkSimple s!"part_{i}"
            let auxTy ← mkForallFVars xs ty
            let auxVal ← mkLambdaFVars xs e'
            addDecl (.thmDecl { name := nm, levelParams := lps, type := auxTy, value := auxVal })
            pure (mkAppN (mkConst nm (lps.map mkLevelParam)) xs, xs.size + 1)
          else pure (e', n)
        else pure (e', n)
      else pure (e', n)
    cache.modify fun c => c.insert e (e', n)
    return (e', n)
  let (v, _) ← visit val
  return v

/-- `X`'s statement opened: the kept parameters and the premises as locals, the values as unknowns, the obligation
`obn` a placeholder; `k` gets the conclusion, the arguments for `X`, the kept locals, the premises, and the
obligation's position and type. -/
def openForTop (ty : Expr) (obn : Name) (args kept hyps : Array Expr) (ob : Option (Nat × Expr))
    (k : Expr → Array Expr → Array Expr → Array Expr → Option (Nat × Expr) → TermElabM Unit) : TermElabM Unit := do
  let keepNames : List Name := [`eng, `σ, `answer, `HI, `s, `h]
  -- one pass over the binders without instantiating the rest at each (that re-traverses the deep obligations):
  -- each binder's type instantiated once, the conclusion once; the locals made in one local context
  let mut lctx ← getLCtx
  let mut body := ty
  let mut args := args
  let mut kept := kept
  let mut hyps := hyps
  let mut ob := ob
  let mut fuel := 100000
  while fuel > 0 do
    fuel := fuel - 1
    match body with
    | .forallE n d b bi =>
      let d' := d.instantiateRev args
      let isP ← withLCtx lctx (← getLocalInstances) (isProp d')
      if isP && n == obn then
        let m ← withLCtx lctx (← getLocalInstances) (mkFreshExprMVar d')
        ob := some (args.size, d')
        args := args.push m
      else if isP || keepNames.contains n then
        let fid ← mkFreshFVarId
        lctx := lctx.mkLocalDecl fid n d' bi
        let x := mkFVar fid
        args := args.push x
        if isP then hyps := hyps.push x else kept := kept.push x
      else
        let m ← withLCtx lctx (← getLocalInstances) (mkFreshExprMVar d' (userName := n))
        args := args.push m
      body := b
    | _ => break
  let concl := body.instantiateRev args
  withLCtx lctx (← getLocalInstances) (k concl args kept hyps ob)


/-- The unassigned unknowns a term depends on, without instantiating it: assignments and delayed assignments' pending
values followed, each unknown and each subterm looked at once (instantiating a proof whose delayed assignments still
wait on unknowns re-walks their values again and again). Unknowns' types are followed too. -/
def unknownsOf (roots : Array Expr) : MetaM (Array MVarId) := do
  let mut seenE : Std.HashSet Expr := {}
  let mut seenM : Std.HashSet MVarId := {}
  let mut out : Array MVarId := #[]
  let mut stack : Array Expr := roots
  while !stack.isEmpty do
    let e := stack.back!
    stack := stack.pop
    if !e.hasMVar || seenE.contains e then continue
    seenE := seenE.insert e
    match e with
    | .mvar m =>
      if seenM.contains m then continue
      seenM := seenM.insert m
      stack := stack.push (← m.getType)
      match ← getExprMVarAssignment? m with
      | some v => stack := stack.push v
      | none =>
        match ← getDelayedMVarAssignment? m with
        | some da => stack := stack.push (mkMVar da.mvarIdPending)
        | none => out := out.push m
    | .app f a => stack := (stack.push f).push a
    | .lam _ t b _ => stack := (stack.push t).push b
    | .forallE _ t b _ => stack := (stack.push t).push b
    | .letE _ t v b _ => stack := ((stack.push t).push v).push b
    | .mdata _ b => stack := stack.push b
    | .proj _ _ b => stack := stack.push b
    | _ => pure ()
  return out

/-- The unknowns left in `ty`/`val` made leading variables (in an order their types allow). -/
def generalizeMVars (ty val : Expr) : MetaM (Expr × Expr) := do
  let mut ms := (← getMVars ty) ++ (← getMVars val)
  ms := ms.foldl (fun acc m => if acc.contains m then acc else acc.push m) #[]
  -- those whose types mention no other unknown first
  let mut order : Array MVarId := #[]
  let mut left := ms
  for _ in [:ms.size + 1] do
    let mut next := #[]
    for m in left do
      let tm ← instantiateMVars (← m.getType)
      let deps := (← getMVars tm).filter (fun d => left.contains d && d != m)
      if deps.isEmpty then order := order.push m else next := next.push m
    left := next
    if left.isEmpty then break
  order := order ++ left
  -- the locals made in one go (nesting one continuation per unknown overflows the stack)
  let mut lctx ← getLCtx
  let mut xs : Array Expr := #[]
  for m in order do
    if ← m.isAssigned then continue
    let tm ← instantiateMVars (← m.getType)
    let nm := (← m.getDecl).userName
    let nm := if nm.isAnonymous then Name.mkSimple s!"v{xs.size}" else nm
    let fid ← mkFreshFVarId
    lctx := lctx.mkLocalDecl fid nm tm
    m.assign (mkFVar fid)
    xs := xs.push (mkFVar fid)
  withLCtx lctx (← getLocalInstances) do
    let ty ← instantiateMVars ty
    let val ← instantiateMVars val
    return (← mkForallFVars xs ty, ← mkLambdaFVars xs val)

/-- `facts_top X ob as N`: see the module docstring. -/
syntax (name := factsTop) "facts_top " ident ident " as " ident : command

@[command_elab factsTop] def elabFactsTop : CommandElab := fun stx => do
  let Xn ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo stx[1]
  let obn := stx[2].getId
  let N := (← getCurrNamespace) ++ stx[4].getId
  -- no info trees: every tactic run would keep a snapshot of the (huge) metavariable context, processed at the end
  withEnableInfoTree false <| liftTermElabM do
    let ci ← getConstInfo Xn
    -- progress to a file (a command's own output is captured, and lost if Lean aborts)
    let mark (m : String) : IO Unit := do
      -- (with the resident memory, from /proc on Linux)
      let rss ← (try
          let st ← IO.FS.readFile "/proc/self/status"
          pure ((st.splitOn "\n").find? (·.startsWith "VmRSS:") |>.getD "")
        catch _ => pure "")
      let rss := (rss.drop 6).trim
      let h ← IO.FS.Handle.mk "facts_top.progress" .append
      h.putStrLn s!"{← IO.monoMsNow} [{rss}] {m}"; h.flush
    mark "start"
    openForTop ci.type obn #[] #[] #[] none fun concl args kept hyps ob => do
      mark s!"opened: {args.size} binders, {hyps.size} premises; kept {kept.map (·.fvarId!.name)}, premises {hyps.map (·.fvarId!.name)}"
      let some (oi, obT) := ob | throwError "facts_top: {Xn} has no premise {obn}"
      let some s0 ← kept.findM? (fun x => return (← x.fvarId!.getUserName) == `s)
        | throwError "facts_top: no start state s"
      -- the new start facts and pure premises: hypotheses whose types are filled in at the end
      let LX ← mkFreshExprMVar (mkApp (mkConst ``List [Level.zero]) (mkConst ``Logic.Fact))
      let PX ← mkFreshExprMVar (mkSort .zero)
      withLocalDeclD `hX (mkApp2 (mkConst ``Logic.Facts.holds) LX s0) fun hX => do
      withLocalDeclD `hP PX fun hP => do
        let top := (← getLCtx).getFVarIds
        let st ← IO.mkRef ({} : Collected)
        pendingFacts.set #[]; pendingPures.set #[]
        let g ← mkFreshExprSyntheticOpaqueMVar obT
        mark "walking"
        topLocals.set top
        startOnly.set {}
        askFailed.set {}
        restatedLets.set {}
        startRecords.set #[]
        andScanned.set {}
        -- start objects that must be distinct to carry a fact: premises (`topNe?`), stated at the end
        topNes.set #[]
        topNeAllow.set (some top)
        topNeStrict.set true
        -- key tables: reflected checks compare keys by index (filled at the end)
        do
          let tb ← mkFreshExprMVar (mkApp (mkConst ``List [0]) (mkConst ``ES.JSStr))
          let tp ← mkFreshExprMVar (mkApp (mkConst ``List [0]) (mkConst ``ES.PropKey))
          let hnb ← mkFreshExprMVar (← mkAppM ``List.Nodup #[tb])
          let hnp ← mkFreshExprMVar (← mkAppM ``List.Nodup #[tp])
          keyTables.set (some { tb, tp, hnb, hnp })
          keyListB.set #[]
          factChains.set {}
          keyListP.set #[]
        topUnknowns.set (some (args.foldl (init := {}) fun acc a => if a.isMVar then acc.insert a.mvarId! else acc))
        carryTimes.set {}
        startState.set (some s0)
        holdsCache.set {}
        factsOfCache.set {}
        frameCache.set {}
        triedNear.set {}
        triedFarRef.set {}
        stepTimes.set #[]
        collectGoal g.mvarId! top s0 st
        mark "walked"
        mark s!"  times: {← stepReport}"
        let _ ← fixedPoint st
        mark "fixed point"
        mark s!"  times: {← stepReport}"
        let nk ← fixFuelConstants
        -- constants fixed change hypotheses, not only goals: every goal is tried near again
        if nk > 0 then triedNear.set {}
        mark s!"{nk} fuel constants fixed"
        let _ ← fixedPoint st
        mark "fixed point again"
        mark s!"  times: {← stepReport}"
        -- the facts left: new start facts (proved by carrying them from `s`)
        let mut facts : Array Expr := #[]
        let mut factGoals : Array (MVarId × Nat) := #[]
        let mut closedGoals : Array MVarId := #[]
        let mut localFacts : Array Format := #[]
        for fg in ← pendingFacts.get do
          let t ← instantiateMVars (← fg.getType)
          let f := t.appFn!.appArg!
          -- a closed fact needed after the start: a premise over the whole way there (`closedGoals`, below; its locals generalized)
          if (← whnfR f).isAppOfArity ``Logic.Fact.closed 2 && t.appArg! != s0 then
            closedGoals := closedGoals.push fg
            continue
          -- a fact on a local (a value opened inside the obligation) cannot be stated at the start
          if f.hasAnyFVar (fun x => !top.contains x) then
            localFacts := localFacts.push (← fg.withContext (ppExpr f))
            if localFacts.size ≤ 18 then
              fg.withContext do
                let w := t.appArg!
                let (c, k) ← factKey f
                let hh ← IO.FS.Handle.mk "facts_top.progress" .append
                let one (e : Expr) : MetaM String := do pure (((toString (← ppExpr e)).replace "\n" " ").take 260).toString
                let fvs := (collectFVars {} f).fvarIds.filter (fun x => !top.contains x)
                let mut ls : Array String := #[]
                for x in fvs do
                  let d ← x.getDecl
                  ls := ls.push s!"{d.userName} : {← one d.type}{if d.isLet then " (let)" else ""}"
                hh.putStrLn s!"LOCAL {← one f} at {← one w} key {c} {k}; locals {ls}"
                if c == ``Logic.Fact.recordIs then
                  hh.putStrLn s!"  RFULL {((toString (← ppExpr f)).replace "\n" " ").take 3000} AT {← one w}"
                  for d in ← getLCtx do
                    let ty ← instantiateMVars d.type
                    if let some (_, l, _) := ty.eq? then
                      if l.isAppOfArity ``Scope.declLike? 1 then
                        hh.putStrLn s!"  RDECL {d.userName} : {((toString (← ppExpr ty)).replace "\n" " ").take 3000}"
                if k == "workInProgress" then
                  for d in ← getLCtx do
                    let ty ← instantiateMVars d.type
                    if let some (_, l, _) := ty.eq? then
                      if l.isAppOfArity ``Scope.declLike? 1 then
                        hh.putStrLn s!"  DECL {d.userName} : {((toString (← ppExpr ty)).replace "\n" " ").take 4000}"
                if k == "didReceiveUpdate" || k == "workInProgress" then
                  hh.putStrLn s!"  FULL {((toString (← ppExpr f)).replace "\n" " ").take 1500}"
                  for (h, a) in ← factLists do
                    let ty ← instantiateMVars (← inferType h)
                    let some elems ← listElems (← whnfR ty).appFn!.appArg! 4096 | continue
                    for e in elems do
                      let (c', k') ← factKey e
                      if k' == k then
                        let fpth ← framePath a w
                        let saved ← saveState
                        let ok ← try withReducible (isDefEq (← instantiateMVars e) f) catch _ => pure false
                        saved.restore
                        hh.putStrLn s!"  SRC at {← one a} path {a == w || fpth.isSome} defeq {ok} head {c'}: {((toString (← ppExpr e)).replace "\n" " ").take 1500}"
                        if let some pf := fpth then
                          let ty ← instantiateMVars (← inferType pf)
                          hh.putStrLn s!"  PATH TYPE {((toString (← ppExpr ty)).replace "\n" " ").take 2500}"
                          let one1 ← appFacts ``Logic.Facts.holds_cons #[e, mkApp (mkConst ``List.nil [Level.zero]) (mkConst ``Logic.Fact), a,
                            ← mkFreshExprMVar (mkApp2 (mkConst ``Logic.Fact.holds) e a), ← appFacts ``Logic.Facts.holds_nil #[a]]
                          try
                            let (_, _, nk, _) ← carry one1 pf
                            hh.putStrLn s!"  CARRY kept {nk}"
                          catch ex => hh.putStrLn s!"  CARRY error {((toString (← ex.toMessageData.format)).replace "\n" " ").take 800}"
                if true then
                  for x in fvs do
                    if (← seenLocals.get).contains x then continue
                    seenLocals.modify (·.push x)
                    for d in ← getLCtx do
                      if d.isImplementationDetail then continue
                      let ty ← instantiateMVars d.type
                      if ty.containsFVar x then
                        hh.putStrLn s!"    MENTIONS {d.userName} : {(((toString (← ppExpr ty)).replace "\n" " ").take 700).toString}"
                  let decls := (← getLCtx).decls.toArray.filterMap id
                  for x in fvs do
                    let some i := decls.findIdx? (·.fvarId == x) | continue
                    for j in [i - min i 8 : i + 4] do
                      if h : j < decls.size then
                        let d := decls[j]
                        hh.putStrLn s!"    ctx[{j}] {d.userName} : {← one d.type}"
                let o ← whnfR (← whnfR f).getAppArgs[0]!
                for (h, a) in ← factLists do
                  let ty ← instantiateMVars (← inferType h)
                  let some elems ← listElems (← whnfR ty).appFn!.appArg! 4096 | continue
                  for e in elems do
                    let e ← instantiateMVars e
                    let (c', k') ← factKey e
                    if c' == c && (k' == k || k' == "?" || k == "?") && (← whnfR (← whnfR e).getAppArgs[0]!) == o then
                      let fpth ← framePath a w
                      let path := if a == w then "same state" else if fpth.isSome then "frame path" else "NO frame path"
                      hh.putStrLn s!"  cand at {← one a} ({path}): {← one e}"
                hh.flush
            continue
          factGoals := factGoals.push (fg, facts.size)
          facts := facts.push f
        -- the pure goals left: premises (those on a local are stuck)
        let mut pures : Array (MVarId × Expr) := #[]
        let mut stuck : Array Format := #[]
        for pg in ← pendingPures.get do
          let t ← instantiateMVars (← pg.getType)
          if t.hasAnyFVar (fun f => !top.contains f) then
            stuck := stuck.push (← pg.withContext (ppExpr t))
            if (t.find? fun e => e.isAppOfArity ``ES.State.fuel 1).isSome then
              pg.withContext do
                let hh ← IO.FS.Handle.mk "facts_top.progress" .append
                hh.putStrLn s!"FUEL {((toString (← ppExpr t)).replace "\n" " ").take 200}"
                for d in ← getLCtx do
                  if d.isImplementationDetail then continue
                  let ty ← instantiateMVars d.type
                  if (ty.find? fun e => e.isAppOfArity ``ES.State.fuel 1).isSome && (toString (← ppExpr ty)).length < 300 then
                    hh.putStrLn s!"    {d.userName} : {((toString (← ppExpr ty)).replace "\n" " ").take 250}"
                  else if ty.isAppOfArity ``Logic.Frame 3 then
                    hh.putStrLn s!"    FRAME {((toString (← ppExpr ty.appFn!.appArg!)).take 30).toString} → {((toString (← ppExpr ty.appArg!)).take 30).toString}"
                hh.flush
            if (toString (← pg.withContext (ppExpr t))).contains "isHydrating" then
              pg.withContext do
                let hh ← IO.FS.Handle.mk "facts_top.progress" .append
                hh.putStrLn s!"HYD {((toString (← ppExpr t)).replace "\n" " ").take 300}"
                let ms ← getMVars t
                for m in ms do
                  hh.putStrLn s!"  unknown {(← m.getDecl).userName} : {((toString (← ppExpr (← m.getType))).take 80).toString} kind {repr (← m.getDecl).kind}"
                for d in ← getLCtx do
                  if d.isImplementationDetail then continue
                  let ty ← instantiateMVars d.type
                  if ms.any (fun m => ty.containsMVar m) then
                    hh.putStrLn s!"    {d.userName} : {((toString (← ppExpr ty)).replace "\n" " ").take 300}"
                -- other pending goals mentioning it
                for g2 in ← pendingFacts.get do
                  let t2 ← instantiateMVars (← g2.getType)
                  if ms.any (fun m => t2.containsMVar m) then
                    hh.putStrLn s!"    PENDING-FACT {((toString (← ppExpr t2)).replace "\n" " ").take 300}"
                hh.flush
            if !t.isAppOfArity ``Ne 3 && stuck.size ≤ 40 then
              pg.withContext do
                let hh ← IO.FS.Handle.mk "facts_top.progress" .append
                hh.putStrLn s!"STUCKCTX {((toString (← ppExpr t)).replace "\n" " ").take 200}"
                for x in (collectFVars {} t).fvarIds.filter (fun f => !top.contains f) do
                  let xd ← x.getDecl
                  let vs ← match xd.value? with
                    | some v => do pure s!" := {((toString (← ppExpr v)).replace "\n" " ").take 300}"
                    | none => pure ""
                  hh.putStrLn s!"  local {xd.userName} : {(toString (← ppExpr xd.type)).take 60}{vs}"
                  let mut n := 0
                  for d in ← getLCtx do
                    if d.isImplementationDetail || n ≥ 10 then continue
                    let ty ← instantiateMVars d.type
                    if ty.containsFVar x && (toString (← ppExpr ty)).length < 500 then
                      n := n + 1
                      hh.putStrLn s!"    {d.userName} : {((toString (← ppExpr ty)).replace "\n" " ").take 300}"
                hh.flush
            if t.isAppOfArity ``Ne 3 && stuck.size ≤ 60 then
              pg.withContext do
                let hh ← IO.FS.Handle.mk "facts_top.progress" .append
                hh.putStrLn s!"NE {((toString (← ppExpr t)).replace "\n" " ").take 200}"
                -- diagnosis: everything stated at a state named `w2`
                for d in ← getLCtx do
                  if d.isImplementationDetail then continue
                  let ty ← instantiateMVars d.type
                  let names ← (collectFVars {} ty).fvarIds.mapM fun x => do return (← x.getDecl).userName.toString
                  if names.contains "w2" then
                    hh.putStrLn s!"    W2 {d.userName} : {((toString (← ppExpr ty)).replace "\n" " ").take 400}"
                for x in (collectFVars {} t).fvarIds.filter (fun f => !top.contains f) do
                  let xd ← x.getDecl
                  let vs ← match xd.value? with
                    | some v => do pure s!" := {((toString (← ppExpr v)).replace "\n" " ").take 200}"
                    | none => pure ""
                  hh.putStrLn s!"  local {xd.userName} : {(toString (← ppExpr xd.type)).take 60}{vs}"
                  let mut n := 0
                  for d in ← getLCtx do
                    if d.isImplementationDetail || n ≥ 8 then continue
                    let ty ← instantiateMVars d.type
                    if ty.containsFVar x && (toString (← ppExpr ty)).length < 400 then
                      n := n + 1
                      hh.putStrLn s!"    {d.userName} : {((toString (← ppExpr ty)).replace "\n" " ").take 300}"
                  for d in ← getLCtx do
                    let ty ← instantiateMVars d.type
                    if ty.containsFVar x && (ty.isAppOfArity ``Ne 3 || (ty.isForall && (toString (← ppExpr ty)).contains '≠')) then
                      hh.putStrLn s!"    NE-HYP {d.userName} : {((toString (← ppExpr ty)).replace "\n" " ").take 300}"
                hh.flush
          else pures := pures.push (pg, t)
        mark s!"classified: {facts.size} facts, {pures.size} pures, {stuck.size} stuck, {localFacts.size} on locals"
        -- the unknowns are what they will be: records may be assumed distinct (`topNe?`)
        topNeStrict.set false
        -- what cannot be stated at the start: reported before anything is carried
        unless stuck.isEmpty && localFacts.isEmpty do
          for x in stuck.extract 0 40 do
            let str := (toString x).replace "\n" " "
            mark s!"stuck: {(str.take 1500).toString} … {(str.drop (str.length - 800)).toString}"
          for x in localFacts.extract 0 40 do mark s!"fact on locals: {(((toString x).replace "\n" " ").take 300).toString}"
          mark "reporting"
          logError m!"facts_top: {stuck.size} goals stuck, {localFacts.size} facts on locals"
          mark "reported; returning"
          topNeAllow.set none; keyTables.set none
          return
        LX.mvarId!.assign (← mkListLit (mkConst ``Logic.Fact) facts.toList)
        mark "start facts assigned"
        let mut notLifted : Array Format := #[]
        let LXv ← instantiateMVars LX
        let carryOne (fg : MVarId) (i : Nat) : TermElabM (Option Format) := fg.withContext do
          let t ← instantiateMVars (← fg.getType)
          let w := t.appArg!
          let f := t.appFn!.appArg!
          let hm ← idxLt i LXv
          let gi ← factAt LXv s0 hX i
          if w == s0 then fg.assign (← mkExpectedTypeHint gi t); return none
          let some pf ← framePath s0 w | return some (← ppExpr t)
          -- (diagnosis) the path's frames: their states and footprints' parts
          let rec leaves (e : Expr) (fuel : Nat) : Array Expr :=
            match fuel with
            | 0 => #[e]
            | n + 1 => if e.isAppOf ``Logic.frame_trans then leaves e.appFn!.appArg! n ++ leaves e.appArg! n else #[e]
          let mut desc := ""
          for q in leaves pf 64 do
            let qt ← whnfR (← instantiateMVars (← inferType q))
            if qt.isAppOfArity ``Logic.Frame 3 then
              let fp := qt.appFn!.appFn!.appArg!
              let cs := fp.getUsedConstants.filter fun c => !(c.toString.startsWith "Logic.Footprint") && !(c.toString.startsWith "List") && !(c.toString.startsWith "Prod") && !(c.toString.startsWith "ES.JSStr") && !(c.toString.startsWith "String") && !(c.toString.startsWith "Char") && !(c.toString.startsWith "OfNat") && !(c.toString.startsWith "instOfNat") && c.toString.length > 4
              desc := desc ++ s!" | {← ppExpr qt.appFn!.appArg!} → {← ppExpr qt.appArg!} [{q.getAppFn}] {(cs.toList.take 8)}"
          mark s!"PATH {((toString (← ppExpr t)).replace "\n" " ").take 120} :: {desc.take 2500}"
          let one ← appFacts ``Logic.Facts.holds_cons #[f, mkApp (mkConst ``List.nil [Level.zero]) (mkConst ``Logic.Fact), s0,
            ← mkExpectedTypeHint gi (mkApp2 (mkConst ``Logic.Fact.holds) f s0), ← appFacts ``Logic.Facts.holds_nil #[s0]]
          carryDebug.set true
          let (L', prf, nkept, _) ← carry one pf
          carryDebug.set false
          if nkept != 1 then return some (← ppExpr t)
          let hm1 ← idxLt 0 L'
          fg.assign (← mkExpectedTypeHint (← appFacts ``Logic.Facts.get #[L', w, prf, mkNatLit 0, hm1]) t)
          return none
        -- the start facts grouped by the state they are needed at: one path and one carry per state
        let mut groups : Array (Expr × Array (MVarId × Nat)) := #[]
        for (fg, i) in factGoals do
          let t ← instantiateMVars (← fg.getType)
          let w := t.appArg!
          match groups.findIdx? (·.1 == w) with
          | some k => groups := groups.modify k fun (w', l) => (w', l.push (fg, i))
          | none => groups := groups.push (w, #[(fg, i)])
        mark s!"start facts at {groups.size} states"
        let mut nDone := 0
        let mut nShared := 0
        for (w, items) in groups do
          let (fg0, _) := items[0]!
          let shared ← (try fg0.withContext do
              if w == s0 then pure none else
              let some pf ← carryTimed "group:path" (framePath s0 w) | pure none
              -- the group's facts as one list at the start, carried to `w`
              -- (built as they are, not type-checked step by step: checking `LXv[i]` against each fact walks the
              -- start list in the elaborator; the kernel's check of the whole is cheap)
              let mut hl := mkApp (mkConst ``Logic.Facts.holds_nil) s0
              let mut tl := mkApp (mkConst ``List.nil [Level.zero]) (mkConst ``Logic.Fact)
              for (fg, i) in items.reverse do
                let t ← instantiateMVars (← fg.getType)
                let f := t.appFn!.appArg!
                let gi ← factAt LXv s0 hX i
                let gi ← mkExpectedTypeHint gi (mkApp2 (mkConst ``Logic.Fact.holds) f s0)
                hl := mkAppN (mkConst ``Logic.Facts.holds_cons) #[f, tl, s0, gi, hl]
                tl := mkApp3 (mkConst ``List.cons [Level.zero]) (mkConst ``Logic.Fact) f tl
              let hSub ← mkExpectedTypeHint hl (mkApp2 (mkConst ``Logic.Facts.holds) tl s0)
              let (L', prf, _, _) ← carryTimed "group:carry" (carry hSub pf)
              let some elems ← listElems L' 4096 | pure none
              -- (the shared proof's locals, collected once: each goal of the group checks them against its context)
              let fvs := (collectFVars {} (← instantiateMVars prf)).fvarIds
              pure (some (L', prf, elems, fvs))
            catch _ => pure none)
          for (fg, i) in items do
            nDone := nDone + 1
            if nDone % 100 == 0 then mark s!"carried {nDone}"
            let done ← (try fg.withContext do
                let t ← instantiateMVars (← fg.getType)
                let f := t.appFn!.appArg!
                if w == s0 then
                  let gi ← factAt LXv s0 hX i
                  fg.assign (← mkExpectedTypeHint gi t); return true
                let some (L', prf, elems, fvs) := shared | return false
                let some k := elems.findIdx? (· == f) | return false
                -- the shared proof's locals are this goal's too
                let lctx ← getLCtx
                unless fvs.all lctx.contains do return false
                -- (`Facts.get {l s} h i hi`, applied as it is: inferring the shared proof's type per goal is costly)
                let pf ← factAt L' w prf k
                fg.assign (← mkExpectedTypeHint pf t); return true
              catch _ => pure false)
            if done then nShared := nShared + 1
            unless done do
              let r ← (try carryOne fg i catch e => do pure (some (← e.toMessageData.format)))
              if let some x := r then
                notLifted := notLifted.push x
                mark s!"NOTLIFTED {((toString x).replace "\n" " ").take 1500}"
                -- diagnosis: the goal's hypotheses about its binding or property (by key)
                fg.withContext do
                  let t ← instantiateMVars (← fg.getType)
                  let (_, k) ← factKey t.appFn!.appArg!
                  let hh ← IO.FS.Handle.mk "facts_top.progress" .append
                  let mut n := 0
                  for d in ← getLCtx do
                    if d.isImplementationDetail || n ≥ 12 then continue
                    let ty ← instantiateMVars d.type
                    let str := toString (← ppExpr ty)
                    let isRec := (toString (← ppExpr t)).startsWith "(Fact.recordIs"
                    if isRec then
                      if ty.isAppOfArity ``Eq 3 && (ty.find? fun e => e.isConstOf ``Scope.declLike?).isSome &&
                          ty.containsFVar t.appArg!.fvarId! then
                        n := n + 1
                        hh.putStrLn s!"    DECL {d.userName} : {(str.replace "\n" " ").take 300}"
                    else if (str.splitOn k).length > 1 && str.length < 2000 then
                      n := n + 1
                      hh.putStrLn s!"    HYP {d.userName} : {(str.replace "\n" " ").take 400}"
                  -- the frames into its state, and what is assumed there
                  for d in ← getLCtx do
                    if d.isImplementationDetail then continue
                    let ty ← instantiateMVars d.type
                    if ty.isAppOfArity ``Logic.Frame 3 && ty.appArg! == t.appArg! then
                      hh.putStrLn s!"    INTO {d.userName} : {((toString (← ppExpr ty)).replace "\n" " ").take 250}"
                    else if ty.containsFVar t.appArg!.fvarId! && (toString (← ppExpr ty)).length < 300 then
                      hh.putStrLn s!"    AT {d.userName} : {((toString (← ppExpr ty)).replace "\n" " ").take 250}"
                  -- the facts with its key at its state, and whether each fits
                  let f := t.appFn!.appArg!
                  let w := t.appArg!
                  for (_, a, _, elems, keys) in ← factListsKeyed do
                    for i in [:elems.size] do
                      unless keys[i]!.2 == k do continue
                      let e ← instantiateMVars elems[i]!
                      let saved ← saveState
                      let ok ← try withReducible (isDefEq e f) catch _ => pure false
                      saved.restore
                      hh.putStrLn s!"    CAND at {← ppExpr a} (same state {a == w}, fits {ok}): {((toString (← ppExpr e)).replace "\n" " ").take 250}"
                  hh.flush
        -- closed facts needed at `w`: `∀ locals, (closed (fpPath ∪ g) P).holds s0` a premise (the footprint of the whole
        -- way from the start added, its locals generalized, as the host's reads are stated for any footprint that
        -- misses their objects), carried along the way and weakened to `g`
        for fg in closedGoals do
          let r : Except Format (MVarId × Expr) ← (try fg.withContext do
              let t ← instantiateMVars (← fg.getType)
              let w := t.appArg!
              let f ← whnfR t.appFn!.appArg!
              let g := f.appFn!.appArg!
              let P := f.appArg!
              let some pf ← framePath s0 w | return .error (← (m!"no frame path: " ++ (← ppExpr t)).format)
              let pfTy ← whnfR (← instantiateMVars (← inferType pf))
              let fpPath := pfTy.appFn!.appFn!.appArg!
              let enl := mkApp2 (mkConst ``Logic.Fact.closed) (mkApp2 (mkConst ``Logic.Footprint.union) fpPath g) P
              let body := mkApp2 (mkConst ``Logic.Fact.holds) enl s0
              -- unknowns made inside the obligation whose types name no local: moved to the top's context (else
              -- generalizing the locals would apply them to the locals)
              let topDecl ← LX.mvarId!.getDecl
              for m in ← getMVars (← instantiateMVars body) do
                if ← m.isAssigned <||> m.isDelayedAssigned then continue
                let d ← m.getDecl
                unless d.lctx.any (fun x => !x.isImplementationDetail && !top.contains x.fvarId) do continue
                let ty ← instantiateMVars d.type
                if ty.hasAnyFVar (fun x => !top.contains x) then continue
                let m' ← mkFreshExprMVarAt topDecl.lctx topDecl.localInstances ty d.kind d.userName
                m.assign m'
              let body ← instantiateMVars body
              let enl ← instantiateMVars enl
              let P ← instantiateMVars P
              let g ← instantiateMVars g
              -- the locals it names, with the locals their types name, in context order
              let lctx ← getLCtx
              let mut need : Std.HashSet FVarId := {}
              let mut todo := (collectFVars {} (← instantiateMVars body)).fvarIds.filter (fun x => !top.contains x)
              while !todo.isEmpty do
                let x := todo.back!
                todo := todo.pop
                if need.contains x then continue
                need := need.insert x
                let ty ← instantiateMVars (← x.getType)
                for y in (collectFVars {} ty).fvarIds do
                  unless top.contains y || need.contains y do todo := todo.push y
              let xs := (lctx.foldl (fun acc d => if need.contains d.fvarId then acc.push d.toExpr else acc) #[])
              -- (a `let` among them, a witness opened from an `∃`, generalized as any value: its definition names the
              -- states it was opened at)
              let premTy ← abstractNoLets xs.toList body
              if premTy.hasAnyFVar (fun x => !top.contains x) then
                let ls ← ((collectFVars {} premTy).fvarIds.filter (fun x => !top.contains x)).mapM fun x => do return (← x.getDecl).userName
                return .error (← (m!"locals {ls}: " ++ (← ppExpr t)).format)
              let pm ← mkFreshExprMVar premTy
              let inst := mkAppN pm xs
              -- (along the way itself, `closed_of_path`: no carrying, whose reflection decides the footprints' keys)
              let inst ← mkExpectedTypeHint inst body
              let got := mkAppN (mkConst ``closed_of_path) #[fpPath, g, P, s0, w, inst, pf]
              fg.assign (← mkExpectedTypeHint got t)
              return .ok (pm.mvarId!, premTy)
            catch e => pure (.error (← e.toMessageData.format)))
          match r with
          | .ok pr =>
            pures := pures.push pr
            let str := (toString (← ppExpr pr.2)).replace "\n" " "
            mark s!"CLOSED premise: … {(str.drop (str.length - 400)).toString}"
          | .error x =>
            notLifted := notLifted.push x
            mark s!"NOTLIFTED closed {((toString x).replace "\n" " ").take 600}"
        mark s!"{closedGoals.size} closed facts as premises over the way from the start"
        mark s!"start facts: {nShared} by shared carries, {facts.size - nShared} one by one, {notLifted.size} not carried"
        topNeAllow.set none
        mark s!"carry times: {(← carryTimes.get).toList}"
        let nes ← topNes.get
        mark s!"{nes.size} start objects assumed distinct"
        for (a, b, _) in nes do
          let a ← instantiateMVars a
          let b ← instantiateMVars b
          mark s!"DISTINCT {← ppExpr a} ≠ {← ppExpr b}"
          if a == b then
            logError m!"facts_top: an object assumed distinct from itself: {a}"
            return
        for (_, _, g) in nes do
          pures := pures.push (g.mvarId!, ← instantiateMVars (← g.mvarId!.getType))
        PX.mvarId!.assign (pures.foldr (fun (_, t) acc => mkAnd t acc) (mkConst ``True))
        for (pg, _) in pures, i in [:pures.size] do
          let mut pr := hP
          for _ in [:i] do pr := mkProj ``And 1 pr
          pg.assign (mkProj ``And 0 pr)
        mark "premises assigned"
        logInfo m!"facts_top: {facts.size} start facts, {pures.size} pure premises, {nk} fuel constants fixed, {stuck.size} stuck, {notLifted.size} not carried from the start, {localFacts.size} facts on locals"
        mark s!"{localFacts.size} facts on locals: {(localFacts.extract 0 8).map fun x => ((toString x).take 200).toString}"
        unless stuck.isEmpty && notLifted.isEmpty && localFacts.isEmpty do
          for x in stuck.extract 0 12 do logInfo m!"stuck: {x}"
          for x in notLifted.extract 0 12 do logInfo m!"not carried: {x}"
          throwError "facts_top: obligations left"
        -- the theorem: `X` with the obligation proved; the unknowns left as variables
        -- the key tables, literal lists now, each duplicate-free once (a theorem of its own, decided)
        if let some kt ← keyTables.get then
          keyTables.set none
          let fill (tbl hn : Expr) (α : Expr) (l : Array (String × Expr)) (suffix : String) : TermElabM Unit := do
            let lit ← mkListLit α (l.toList.map (·.2))
            unless ← isDefEq tbl lit do throwError "facts_top: key table"
            let ty ← mkAppM ``List.Nodup #[lit]
            let inst ← synthInstance (← mkAppM ``Decidable #[ty])
            let prf := mkApp3 (mkConst ``of_decide_eq_true) ty inst (← mkEqRefl (mkConst ``Bool.true))
            let nm := N ++ Name.mkSimple suffix
            addDecl (.thmDecl { name := nm, levelParams := [], type := ty, value := prf })
            unless ← isDefEq hn (mkConst nm) do throwError "facts_top: key table proof"
          fill kt.tb kt.hnb (mkConst ``ES.JSStr) (← keyListB.get) "keysB_nodup"
          fill kt.tp kt.hnp (mkConst ``ES.PropKey) (← keyListP.get) "keysP_nodup"
          mark s!"key tables: {(← keyListB.get).size} binding keys, {(← keyListP.get).size} property keys"
        mark "closing"
        let proofOb ← instantiateMVars g
        mark s!"proof instantiated: {← proofOb.numObjs} objects"
        args[oi]!.mvarId!.assign proofOb
        -- the unknowns left made variables first (abstracting the premises over open unknowns rebuilds each
        -- unknown's context: with thousands of them that does not fit in memory); then everything instantiated
        let val0 := mkAppN (mkConst Xn (ci.levelParams.map mkLevelParam)) args
        let hypTys ← (hyps ++ #[hX, hP]).mapM fun x => do instantiateMVars (← inferType x)
        let ms ← unknownsOf (#[val0, concl] ++ hypTys)
        let seen : Std.HashSet MVarId := ms.foldl (·.insert ·) {}
        mark s!"closing: {ms.size} unknowns and goals"
        -- in an order their types allow: depth first, each unknown after the ones its type mentions
        let mut deps : Std.HashMap MVarId (Array MVarId) := {}
        for m in ms do
          let tm ← instantiateMVars (← m.getType)
          deps := deps.insert m ((← getMVars tm).filter (fun d => seen.contains d && d != m))
        let mut order : Array MVarId := #[]
        let mut placed : Std.HashSet MVarId := {}
        let mut entered : Std.HashSet MVarId := {}
        for root in ms do
          if placed.contains root then continue
          -- (an explicit stack: an unknown is placed when the ones it depends on are)
          let mut stack : Array (MVarId × Bool) := #[(root, false)]
          while !stack.isEmpty do
            let (m, ready) := stack.back!
            stack := stack.pop
            if placed.contains m then continue
            if ready then
              placed := placed.insert m; order := order.push m
            else if entered.contains m then
              continue  -- (a cycle: placed when its first visit finishes)
            else
              entered := entered.insert m
              stack := stack.push (m, true)
              for d in (deps.getD m #[]) do
                unless placed.contains d do stack := stack.push (d, false)
        mark "closing: ordered"
        -- a goal left unproved (a proposition, or a goal the walk made) is an error, never a variable
        let mut open_ : Array Format := #[]
        for m in order do
          if (← m.isAssigned) || (← m.isDelayedAssigned) then continue
          let d ← m.getDecl
          let tm ← instantiateMVars d.type
          if d.kind.isSyntheticOpaque || (← isProp tm) then
            open_ := open_.push (f!"[{d.userName} {repr d.kind} depth {d.depth}] " ++ (← m.withContext (ppExpr tm)))
        unless open_.isEmpty do
          for x in open_.extract 0 12 do
            mark s!"unproved: {(((toString x).replace "\n" " ").take 300).toString}"
          throwError "facts_top: {open_.size} goals unproved"
        let mut lctx ← getLCtx
        let mut xs : Array Expr := #[]
        for m in order do
          if (← m.isAssigned) || (← m.isDelayedAssigned) then continue
          let tm ← instantiateMVars (← m.getType)
          let nm := (← m.getDecl).userName
          let nm := if nm.isAnonymous then Name.mkSimple s!"v{xs.size}" else nm
          let fid ← mkFreshFVarId
          lctx := lctx.mkLocalDecl fid nm tm
          m.assign (mkFVar fid)
          xs := xs.push (mkFVar fid)
        mark s!"{xs.size} variables"
        withLCtx lctx (← getLocalInstances) do
          let val ← instantiateMVars val0
          mark s!"value instantiated: {← val.numObjs} objects"
          -- (equal subterms one object: instantiating copies them, ~16 times over)
          let val := ShareCommon.shareCommon' val
          mark s!"value shared: {← val.numObjs} objects"
          -- diagnosis: the value's head constants, counted over its shared nodes
          if (← IO.getEnv "FACTS_HIST") == some "1" then
            let mut seen : Std.HashSet UInt64 := {}
            let mut counts : Std.HashMap Name Nat := {}
            let mut todo : Array Expr := #[val]
            let mut n := 0
            while !todo.isEmpty do
              let e := todo.back!
              todo := todo.pop
              let h := hash e
              if seen.contains h then continue
              seen := seen.insert h
              n := n + 1
              match e with
              | .app .. =>
                let f := e.getAppFn
                let nm := f.constName?.getD (if f.isFVar then `fvar else if f.isMVar then `mvar else `other)
                counts := counts.insert nm (counts.getD nm 0 + 1)
                todo := todo.push e.appFn! |>.push e.appArg!
              | .lam _ t b _ | .forallE _ t b _ => todo := todo.push t |>.push b
              | .letE _ t v b _ => todo := todo.push t |>.push v |>.push b
              | .mdata _ b | .proj _ _ b => todo := todo.push b
              | _ => pure ()
            let top := (counts.toArray.qsort (fun a b => a.2 > b.2)).extract 0 40
            mark s!"HIST {n} nodes: {top.map fun (k, v) => s!"{k} {v}"}"
          let bs := kept ++ xs ++ hyps ++ #[hX, hP]
          -- (split for the kernel: its big proofs theorems of their own)
          -- (split for the kernel only when asked: `FACTS_SPLIT=1`)
          let val ← if (← IO.getEnv "FACTS_SPLIT") == some "1" then splitBig N ci.levelParams bs val else pure val
          let ty ← instantiateMVars (← mkForallFVars bs (← instantiateMVars concl))
          let val ← instantiateMVars (← mkLambdaFVars bs val)
          mark s!"abstracted: type {← ty.numObjs}, value {← val.numObjs} objects"
          if ty.hasMVar || val.hasMVar then throwError "facts_top: unknowns left"
          -- diagnosis: free variables left
          let fvsV := (collectFVars {} val).fvarIds
          let fvsT := (collectFVars {} ty).fvarIds
          let lc ← getLCtx
          let mut desc : Array String := #[]
          for f in fvsV ++ fvsT do
            match lc.find? f with
            | some d => desc := desc.push s!"{d.userName} : {((toString (← ppExpr d.type)).take 120).toString}"
            | none => desc := desc.push s!"{f.name} (not in context)"
          unless desc.isEmpty do
            let mut inXs := 0
            for x in xs do
              if (collectFVars {} (← inferType x)).fvarIds.any (fun f => fvsV.contains f || fvsT.contains f) then inXs := inXs + 1
            mark s!"free variables: {desc.size} (in the value {fvsV.size}, in the type {fvsT.size}, in {inXs} variables' types): {desc.extract 0 12}"
            throwError "facts_top: free variables left: {desc.extract 0 12}"
          addDecl (.thmDecl { name := N, levelParams := ci.levelParams, type := ty, value := val })
          mark "added"
        logInfo m!"facts_top: {N} declared"

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
