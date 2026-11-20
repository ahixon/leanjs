import Proofs.While
import Proofs.Env

/-!
# `for` loops with invariants

`Sem.forS` with a `let` declaration: a loop environment for the declared names, the declaration,
then each iteration (`forIter`) runs in a copy of the previous iteration's environment
(`perIterationEnv`, CreatePerIterationEnvironment): tick, test, body, copy, update.
-/

namespace ES

open Sem

/-- CreatePerIterationEnvironment: a new declarative environment (same outer) with copies of the
bindings `perIter` of `cur`. -/
def perIterationEnv (perIter : Array JSStr) (cur : EnvId) : M EnvId := do
  if perIter.isEmpty then return cur
  let outer ← readEnv cur Env.outer
  let env ← newDeclEnv outer
  M.forArr perIter fun bn => do
    createMutableBinding env bn false
    let v ← getBindingValue cur bn true
    initializeBinding env bn v
  pure env

/-- One iteration of a `for` loop, as `Sem.forS` runs it (the current environment and the completion
value so far). -/
def forIter (test update : Option CExpr) (body : CStmt) (labels : Array JSStr) (ctx : Ctx)
    (perIter : Array JSStr) : EnvId × Value → M ((EnvId × Value) ⊕ Compl) :=
  fun (lex, v) => do
    M.tick
    let ictx := { ctx with lex }
    if let some t := test then
      if !toBoolean (← t ictx) then return .inr (.normal (some v))
    let r ← body ictx
    if !loopContinues r labels then return .inr (r.updateEmpty (some v))
    let v := (r.value?).getD v
    let lex ← perIterationEnv perIter lex
    if let some u := update then let _ ← u { ctx with lex }
    return .inl (lex, v)

/-- CreatePerIterationEnvironment for one name `x`: a fresh declarative environment with the same
outer, holding a copy of `x`'s value. -/
theorem perIterationEnv_one (x : JSStr) (cur o : EnvId) (s : State) (b : Std.HashMap JSStr Binding)
    (bd : Binding) (v : Value) (h : cur < s.envs.size) (hE : s.envEntry cur = .decl b (some o))
    (hb : b[x]? = some bd) (hv : bd.value = some v) :
    perIterationEnv #[x] cur s =
      .ok s.envs.size ((s.pushEnv (.decl {} (some o))).setEnv s.envs.size
        (.decl (((∅ : Std.HashMap JSStr Binding).insert x { deletable := false }).modify x
          fun bd => { bd with value := some v }) (some o))) := by
  obtain ⟨bv, bm, bs, bdl⟩ := bd
  simp only at hv
  subst hv
  have h1 : cur < s.envs.size + 1 := Nat.lt_succ_of_lt h
  have hne : s.envs.size ≠ cur := Nat.ne_of_gt h
  simp [perIterationEnv, M.bind_eq, M.bind_apply, readEnv_entry, h, h1, hE, newDeclEnv_eq, pure, M.pure,
    createMutableBinding_declLike, getBindingValue, State.setEnv_envEntry_ne _ _ _ _ hne, State.pushEnv_entry_lt,
    State.pushEnv_entry_at, hb, initializeBinding_declLike, State.setEnv_envEntry_self]

/-- `perIterationEnv` as `Sem.forS` inlines it (to fold it back with `simp only [← perIterationEnv_def]`). -/
theorem perIterationEnv_def (perIter : Array JSStr) (cur : EnvId) :
    perIterationEnv perIter cur =
      if perIter.isEmpty = true then pure cur
      else (readEnv cur Env.outer).bind fun outer => (newDeclEnv outer).bind fun env =>
        (M.forArr perIter fun bn => (createMutableBinding env bn false).bind fun _ =>
          (getBindingValue cur bn true).bind fun v => initializeBinding env bn v).bind fun _ => pure env := rfl

end ES
