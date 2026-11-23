import JSProofs.Loops2

/-!
# `for (x in o) body` (zippy docs/react-proofs.md)

The interpreter's for-in (`evalForIn`) is not built from `Sem` combinators, so the compiled denotations keep it as an
interpreter call. Its loop is EnumerateObjectProperties as `%ForInIteratorPrototype%.next` does it: each object's own
string keys captured when the object is entered, each key (not yet visited) looked up again, enumerable ones bound to
the loop variable and the body run, then the prototype. `forInStep` is that loop's step, named; `ForInWP` the loop
from a state; the step lemmas below each take one step.
-/

open ES ES.M HostRuns
open Std (HashMap HashSet)

namespace Logic

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ}

/-- The for-in loop's state: the current object, the keys visited, the current object's keys, the index, whether the
current object was entered, the last value. -/
abbrev ForInSt := Value × HashSet PropKey × Array PropKey × Nat × Bool × Value

/-- One step of the for-in loop (`evalForIn`'s, verbatim). -/
def forInStep (n : Nat) (ctx : Ctx) (lhs : ForLhs) (body : Stmt) (labels : Array JSStr) :
    ForInSt → M (ForInSt ⊕ Compl) := fun (cur, visited, keys, i, wasVisited, v) => do
  M.tick
  let .obj co := cur | return .inr (.normal (some v))
  if !wasVisited then
    let ks ← Obj'.ownPropertyKeys co
    let ks := ks.filter fun k => match k with | .str _ => true | _ => false
    return .inl (cur, visited, ks, 0, true, v)
  if h : i < keys.size then
    let k := keys[i]
    if visited.contains k then return .inl (cur, visited, keys, i + 1, true, v)
    match ← Obj'.getOwnProperty co k with
    | none => return .inl (cur, visited, keys, i + 1, true, v)
    | some p =>
      let visited := visited.insert k
      if !p.enumerable then return .inl (cur, visited, keys, i + 1, true, v)
      let .str ks := k | return .inl (cur, visited, keys, i + 1, true, v)
      let ictx ← bindForLhs n ctx lhs (.str ks)
      let r ← evalStmt n ictx body
      if !loopContinues r labels then return .inr (r.updateEmpty (some v))
      return .inl (cur, visited, keys, i + 1, true, (r.value?).getD v)
  else
    let p ← Obj'.getPrototypeOf co
    return .inl (p, visited, #[], 0, false, v)

/-- `evalForIn` for a loop variable that is not `var x = init`: the head, then the loop. -/
theorem evalForIn_eq (n : Nat) (ctx : Ctx) (lhs : ForLhs) (rhs : Expr) (body : Stmt) (labels : Array JSStr)
    (hl : ∀ x ie, lhs ≠ .decl .var (.ident x) (some ie)) :
    evalForIn (n + 1) ctx lhs rhs body labels = (do
      let ov ← evalForHead n ctx lhs rhs
      if ov.isNullish then return .brk none none
      let o ← toObject ov
      M.repeatFrom ((.obj o, {}, #[], 0, false, .undefined) : ForInSt) (forInStep n ctx lhs body labels)) := by
  cases lhs with
  | pattern p => rfl
  | decl k p ie =>
    cases k <;> cases p <;> cases ie <;> first | rfl | (exfalso; exact hl _ _ rfl)

/-- The for-in loop from state `st` with `b` iterations allowed. -/
def ForInWP (eng : Engine) (answer : HostAnswer σ) (N n : Nat) (ctx : Ctx) (lhs : ForLhs) (body : Stmt)
    (labels : Array JSStr) (b : Nat) (st : ForInSt) (h : σ) (s : State) (Q : Compl → State → σ → Prop) : Prop :=
  WPR eng answer N h (M.loop (forInStep n ctx lhs body labels) b st s) Q

theorem forIn_step {N n : Nat} {ctx : Ctx} {lhs : ForLhs} {body : Stmt} {labels : Array JSStr} {b : Nat} {st : ForInSt}
    {h : σ} {s : State} {Q : Compl → State → σ → Prop} (hb : 1 ≤ b)
    (hw : WP eng answer N h (forInStep n ctx lhs body labels st) s fun r w h1 =>
      match r with
      | .inl st' => ForInWP eng answer N n ctx lhs body labels (b - 1) st' h1 w Q
      | .inr c => Q c w h1) :
    ForInWP eng answer N n ctx lhs body labels b st h s Q := by
  obtain ⟨k, rfl⟩ : ∃ k, b = k + 1 := ⟨b - 1, by omega⟩
  unfold ForInWP
  simp only [M.loop]
  apply wpr_loopRes
  exact wp_mono hw fun r w h1 q => by cases r <;> exact q

/-- **The end**: the prototype chain ran out. -/
theorem forIn_end {N n : Nat} {ctx : Ctx} {lhs : ForLhs} {body : Stmt} {labels : Array JSStr} {b : Nat}
    {cur : Value} {visited : HashSet PropKey} {keys : Array PropKey} {i : Nat} {wv : Bool} {v : Value}
    {h : σ} {s : State} {Q : Compl → State → σ → Prop} (hb : 1 ≤ b) (hf : 1 ≤ s.fuel)
    (hcur : ∀ o, cur ≠ .obj o) (hq : Q (.normal (some v)) (s.withFuel (s.fuel - 1)) h) :
    ForInWP eng answer N n ctx lhs body labels b (cur, visited, keys, i, wv, v) h s Q := by
  refine forIn_step hb ?_
  have hfz : (s.fuel == 0) = false := by simp; omega
  cases cur with
  | obj o => exact absurd rfl (hcur o)
  | _ =>
    refine wp_of_eq (a := Sum.inr (Compl.normal (some v))) (w := s.withFuel (s.fuel - 1)) ?_ hq
    simp [forInStep, M.bind_eq, M.bind_apply, M.tick, hfz, M.bindRes_ok, Pure.pure, M.pure]; rfl

/-- The step after its tick. -/
def forInStep' (n : Nat) (ctx : Ctx) (lhs : ForLhs) (body : Stmt) (labels : Array JSStr) :
    ForInSt → M (ForInSt ⊕ Compl) := fun (cur, visited, keys, i, wasVisited, v) => do
  let .obj co := cur | return .inr (.normal (some v))
  if !wasVisited then
    let ks ← Obj'.ownPropertyKeys co
    let ks := ks.filter fun k => match k with | .str _ => true | _ => false
    return .inl (cur, visited, ks, 0, true, v)
  if h : i < keys.size then
    let k := keys[i]
    if visited.contains k then return .inl (cur, visited, keys, i + 1, true, v)
    match ← Obj'.getOwnProperty co k with
    | none => return .inl (cur, visited, keys, i + 1, true, v)
    | some p =>
      let visited := visited.insert k
      if !p.enumerable then return .inl (cur, visited, keys, i + 1, true, v)
      let .str ks := k | return .inl (cur, visited, keys, i + 1, true, v)
      let ictx ← bindForLhs n ctx lhs (.str ks)
      let r ← evalStmt n ictx body
      if !loopContinues r labels then return .inr (r.updateEmpty (some v))
      return .inl (cur, visited, keys, i + 1, true, (r.value?).getD v)
  else
    let p ← Obj'.getPrototypeOf co
    return .inl (p, visited, #[], 0, false, v)

theorem forInStep_tick {n : Nat} {ctx : Ctx} {lhs : ForLhs} {body : Stmt} {labels : Array JSStr} {st : ForInSt}
    {s : State} (hf : 1 ≤ s.fuel) :
    forInStep n ctx lhs body labels st s = forInStep' n ctx lhs body labels st (s.withFuel (s.fuel - 1)) := by
  have hfz : (s.fuel == 0) = false := by simp; omega
  obtain ⟨cur, visited, keys, i, wv, v⟩ := st
  simp only [forInStep, forInStep', M.bind_eq, M.bind_apply, M.tick, hfz, Bool.false_eq_true, ↓reduceIte, M.bindRes_ok]
  rfl

/-- A step, after its tick. -/
theorem forIn_step' {N n : Nat} {ctx : Ctx} {lhs : ForLhs} {body : Stmt} {labels : Array JSStr} {b : Nat} {st : ForInSt}
    {h : σ} {s : State} {Q : Compl → State → σ → Prop} (hb : 1 ≤ b) (hf : 1 ≤ s.fuel)
    (hw : WP eng answer N h (forInStep' n ctx lhs body labels st) (s.withFuel (s.fuel - 1)) fun r w h1 =>
      match r with
      | .inl st' => ForInWP eng answer N n ctx lhs body labels (b - 1) st' h1 w Q
      | .inr c => Q c w h1) :
    ForInWP eng answer N n ctx lhs body labels b st h s Q := by
  refine forIn_step hb ?_
  rw [wp_iff_wpr, forInStep_tick hf]
  exact hw

/-- **Entering an object**: its own string keys. -/
theorem forIn_enter {N n : Nat} {ctx : Ctx} {lhs : ForLhs} {body : Stmt} {labels : Array JSStr} {b : Nat}
    {co : ObjId} {visited : HashSet PropKey} {keys : Array PropKey} {i : Nat} {v : Value}
    {h : σ} {s : State} {Q : Compl → State → σ → Prop} (hb : 1 ≤ b) (hf : 1 ≤ s.fuel)
    (hw : WP eng answer N h (Obj'.ownPropertyKeys co) (s.withFuel (s.fuel - 1)) fun ks w h1 =>
      ForInWP eng answer N n ctx lhs body labels (b - 1)
        (.obj co, visited, ks.filter (fun k => match k with | .str _ => true | _ => false), 0, true, v) h1 w Q) :
    ForInWP eng answer N n ctx lhs body labels b (.obj co, visited, keys, i, false, v) h s Q := by
  refine forIn_step' hb hf ?_
  simp only [forInStep', Bool.not_false, ↓reduceIte]
  exact wp_bind (wp_mono hw fun ks w h1 q => wp_pure q)

/-- **The next object**: the current one's keys done, its prototype. -/
theorem forIn_proto {N n : Nat} {ctx : Ctx} {lhs : ForLhs} {body : Stmt} {labels : Array JSStr} {b : Nat}
    {co : ObjId} {visited : HashSet PropKey} {keys : Array PropKey} {i : Nat} {v : Value}
    {h : σ} {s : State} {Q : Compl → State → σ → Prop} (hb : 1 ≤ b) (hf : 1 ≤ s.fuel) (hi : keys.size ≤ i)
    (hw : WP eng answer N h (Obj'.getPrototypeOf co) (s.withFuel (s.fuel - 1)) fun p w h1 =>
      ForInWP eng answer N n ctx lhs body labels (b - 1) (p, visited, #[], 0, false, v) h1 w Q) :
    ForInWP eng answer N n ctx lhs body labels b (.obj co, visited, keys, i, true, v) h s Q := by
  refine forIn_step' hb hf ?_
  have hi' : ¬ i < keys.size := by omega
  simp only [forInStep', Bool.not_true, Bool.false_eq_true, ↓reduceIte, hi', ↓reduceDIte]
  exact wp_bind (wp_mono hw fun p w h1 q => wp_pure q)

/-- **A key**: looked up again; a key visited before, a missing or non-enumerable property, or a symbol skipped. -/
theorem forIn_skip {N n : Nat} {ctx : Ctx} {lhs : ForLhs} {body : Stmt} {labels : Array JSStr} {b : Nat}
    {co : ObjId} {visited : HashSet PropKey} {keys : Array PropKey} {i : Nat} {v : Value}
    {h : σ} {s : State} {Q : Compl → State → σ → Prop} (hb : 1 ≤ b) (hf : 1 ≤ s.fuel) (hi : i < keys.size)
    (hvis : visited.contains keys[i] = false)
    (hw : WP eng answer N h (Obj'.getOwnProperty co keys[i]) (s.withFuel (s.fuel - 1)) fun p w h1 =>
      match p with
      | none => ForInWP eng answer N n ctx lhs body labels (b - 1) (.obj co, visited, keys, i + 1, true, v) h1 w Q
      | some p => p.enumerable = false ∧
          ForInWP eng answer N n ctx lhs body labels (b - 1) (.obj co, visited.insert keys[i], keys, i + 1, true, v) h1 w Q) :
    ForInWP eng answer N n ctx lhs body labels b (.obj co, visited, keys, i, true, v) h s Q := by
  refine forIn_step' hb hf ?_
  simp only [forInStep', Bool.not_true, Bool.false_eq_true, ↓reduceIte, hi, ↓reduceDIte, hvis]
  refine wp_bind (wp_mono hw fun p w h1 q => ?_)
  cases p with
  | none => exact wp_pure q
  | some p => obtain ⟨hne, q⟩ := q; simp only [hne, Bool.not_false, ↓reduceIte]; exact wp_pure q

/-- **An enumerable string key**: bound to the loop variable, the body run; on unless it broke out. -/
theorem forIn_key {N n : Nat} {ctx : Ctx} {lhs : ForLhs} {body : Stmt} {labels : Array JSStr} {b : Nat}
    {co : ObjId} {visited : HashSet PropKey} {keys : Array PropKey} {i : Nat} {v : Value} {k : JSStr}
    {h : σ} {s : State} {Q : Compl → State → σ → Prop} (hb : 1 ≤ b) (hf : 1 ≤ s.fuel) (hi : i < keys.size)
    (hk : keys[i] = .str k) (hvis : visited.contains (.str k) = false)
    (hw : WP eng answer N h (Obj'.getOwnProperty co (.str k)) (s.withFuel (s.fuel - 1)) fun p w h1 =>
      ∃ pr, p = some pr ∧ pr.enumerable = true ∧
      WP eng answer N h1 (bindForLhs n ctx lhs (.str k)) w fun ictx w2 h2 =>
      WP eng answer N h2 (evalStmt n ictx body) w2 fun r w3 h3 =>
        if loopContinues r labels then
          ForInWP eng answer N n ctx lhs body labels (b - 1)
            (.obj co, visited.insert (.str k), keys, i + 1, true, (r.value?).getD v) h3 w3 Q
        else Q (r.updateEmpty (some v)) w3 h3) :
    ForInWP eng answer N n ctx lhs body labels b (.obj co, visited, keys, i, true, v) h s Q := by
  refine forIn_step' hb hf ?_
  simp only [forInStep', Bool.not_true, Bool.false_eq_true, ↓reduceIte, hi, ↓reduceDIte, hk, hvis]
  refine wp_bind (wp_mono hw fun p w h1 q => ?_)
  obtain ⟨pr, rfl, hen, q⟩ := q
  simp only [hen, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  refine wp_bind (wp_mono q fun ictx w2 h2 q2 => ?_)
  refine wp_bind (wp_mono q2 fun r w3 h3 q3 => ?_)
  cases hl : loopContinues r labels
  · simp only [hl, Bool.not_false, ↓reduceIte] at q3 ⊢; exact wp_pure q3
  · simp only [hl, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at q3 ⊢; exact wp_pure q3

/-- **`for (x in o) body`** over an object: its head evaluated, then the loop from the object, bounded by the fuel
left; a `break` without a label ends it normally. -/
theorem wp_forInStmt {N n : Nat} {h : σ} {ctx : Ctx} {lhs : ForLhs} {rhs : Expr} {body : Stmt} {s : State}
    {Q : Compl → State → σ → Prop} (hl : ∀ x ie, lhs ≠ .decl .var (.ident x) (some ie))
    (hw : WP eng answer N h (evalForHead n (Sem.inner ctx) lhs rhs) s fun ov w h1 =>
      ∃ o, ov = .obj o ∧ ForInWP eng answer N n (Sem.inner ctx) lhs body ctx.labels w.fuel
        (.obj o, {}, #[], 0, false, .undefined) h1 w fun r w2 h2 => Q (Sem.breakToNormal r) w2 h2) :
    WP eng answer N h (evalStmt (n + 2) ctx (.forIn lhs rhs body)) s Q := by
  show WP eng answer N h (do
    let r ← evalForIn (n + 1) (Sem.inner ctx) lhs rhs body ctx.labels
    Pure.pure (Sem.breakToNormal r)) s Q
  rw [evalForIn_eq n _ lhs rhs body _ hl]
  refine wp_bind ?_
  refine wp_bind (wp_mono hw fun ov w h1 q => ?_)
  obtain ⟨o, rfl, q⟩ := q
  simp only [Value.isNullish, Bool.false_eq_true, ↓reduceIte]
  show WP eng answer N h1 (toObject (.obj o) >>= fun o => M.repeatFrom _ _) w _
  refine wp_bind (wp_of_eq (a := o) (w := w) rfl ?_)
  exact wp_mono q fun r w2 h2 q2 => wp_pure q2

end

end Logic
