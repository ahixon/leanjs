import JSProofs.Loops

/-!
# `while` loops with invariants

`Sem.whileS` runs `whileIter` (tick, test, body) in a loop bounded by the fuel at the start. The
rule: an invariant on the completion value so far and the state, preserved by each iteration that
continues, with a measure that decreases and stays below the starting fuel.
-/

namespace ES

open Sem

/-- One iteration of a `while` loop, as `Sem.whileS` runs it (`v`: the completion value so far). -/
def whileIter (t : CExpr) (body : CStmt) (labels : Array JSStr) (ctx : Ctx) : Value → M (Value ⊕ Compl) :=
  fun v => do
    M.tick
    if !toBoolean (← t ctx) then return .inr (Compl.normal (some v))
    let r ← body ctx
    if !loopContinues r labels then return .inr (r.updateEmpty (some v))
    return .inl ((r.value?).getD v)

theorem whileS_eq (t : CExpr) (body : CStmt) (ctx : Ctx) :
    Sem.whileS t body ctx = (do
      let r ← M.repeatFrom Value.undefined (whileIter t body ctx.labels (Sem.inner ctx))
      pure (breakToNormal r)) := rfl

/-- **The `while` rule.** -/
theorem whileS_inv (t : CExpr) (body : CStmt) (ctx : Ctx) (I : Value → State → Prop) (Q : Compl → State → Prop)
    (V : Value → State → Nat)
    (hstep : ∀ v s, I v s →
      (∃ v' s', whileIter t body ctx.labels (Sem.inner ctx) v s = .ok (.inl v') s' ∧ I v' s' ∧ V v' s' < V v s) ∨
      (∃ c s', whileIter t body ctx.labels (Sem.inner ctx) v s = .ok (.inr c) s' ∧ Q c s'))
    (s : State) (hI : I .undefined s) (hV : V .undefined s < s.fuel) :
    ∃ c s', Sem.whileS t body ctx s = .ok (breakToNormal c) s' ∧ Q c s' := by
  obtain ⟨c, s', hl, hQ⟩ := M.loop_inv _ I Q V hstep s.fuel .undefined s hI hV
  refine ⟨c, s', ?_, hQ⟩
  rw [whileS_eq]
  simp only [M.bind_eq, M.bind_apply, M.repeatFrom, hl, M.bindRes_ok]
  rfl

end ES
