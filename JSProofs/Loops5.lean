import JSProofs.Loops4

/-!
# `for (; test; ) body` (zippy docs/react-proofs.md)

React's child reconciler: `for (; null !== currentFirstChild; ) …` — no initializer; the iterations as for `var`
(`ForWP`).
-/

open ES ES.M HostRuns

namespace Logic

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ}

theorem forS_none_eq (test : Sem.CExpr) (body : Sem.CStmt) (ctx : Ctx) :
    Sem.forS .none (some test) none body ctx = (do
      let r ← M.repeatFrom ((Sem.inner ctx).lex, Value.undefined) (forStep (Sem.inner ctx) ctx.labels test body)
      Pure.pure (Sem.breakToNormal r)) := by
  funext s
  simp only [Sem.forS, withDisposeScope, Bool.not_false, ↓reduceIte, M.bind_eq, M.bind_apply,
    M.bindRes_ok, Array.isEmpty_empty, Sem.inner, pure_bind', forStep]
  rfl

/-- **`for (; test; ) body`**: the iterations from the fuel left (`ForWP`); a `break` without a label ends it
normally. -/
theorem wp_forNone {n : Nat} {h : σ} {test : Sem.CExpr} {body : Sem.CStmt} {ctx : Ctx} {s : State}
    {Q : Compl → State → σ → Prop}
    (hw : ForWP eng answer n (Sem.inner ctx) ctx.labels test body s.fuel .undefined h s
      fun r w2 h2 => Q (Sem.breakToNormal r) w2 h2) :
    WP eng answer n h (Sem.forS .none (some test) none body ctx) s Q := by
  rw [forS_none_eq]
  apply wp_bind
  exact wp_mono (x := fun w => M.loop _ w.fuel _ w) (s := s) hw fun r w2 h2 qq => wp_of_eq rfl qq

end

end Logic
