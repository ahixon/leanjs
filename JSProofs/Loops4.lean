import JSProofs.Loops2

/-!
# `for (expr; test; ) body` (zippy docs/react-proofs.md)

React's `bailoutOnAlreadyFinishedWork` clones a fiber's children with
`for (renderLanes.return = workInProgress; null !== current.sibling; ) …`: the initializer is an expression, evaluated
once, its value dropped; then the iterations as for `var` (`ForWP`).
-/

open ES ES.M HostRuns

namespace Logic

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ}

theorem forS_expr_eq (e : Sem.CExpr) (test : Sem.CExpr) (body : Sem.CStmt) (ctx : Ctx) :
    Sem.forS (.expr e) (some test) none body ctx = (do
      let r ← (do
        let _ ← e (Sem.inner ctx)
        M.repeatFrom ((Sem.inner ctx).lex, Value.undefined) (forStep (Sem.inner ctx) ctx.labels test body))
      Pure.pure (Sem.breakToNormal r)) := by
  funext s
  simp only [Sem.forS, withDisposeScope, Bool.not_false, ↓reduceIte, M.bind_eq, M.bind_apply,
    M.bindRes_ok, Array.isEmpty_empty, Sem.inner, pure_bind', forStep]
  rfl

/-- **`for (expr; test; ) body`**: the initializer, then the iterations from the fuel left (`ForWP`). -/
theorem wp_forExpr {n : Nat} {h : σ} {e : Sem.CExpr} {test : Sem.CExpr} {body : Sem.CStmt} {ctx : Ctx} {s : State}
    {Q : Compl → State → σ → Prop}
    (hw : WP eng answer n h (e (Sem.inner ctx)) s fun _ w h1 =>
      ForWP eng answer n (Sem.inner ctx) ctx.labels test body w.fuel .undefined h1 w
        fun r w2 h2 => Q (Sem.breakToNormal r) w2 h2) :
    WP eng answer n h (Sem.forS (.expr e) (some test) none body ctx) s Q := by
  rw [forS_expr_eq]
  apply wp_bind
  apply wp_bind
  refine wp_mono hw fun _ w h1 q => ?_
  have q' : WPR eng answer n h1 (M.loop (forStep (Sem.inner ctx) ctx.labels test body) w.fuel
      ((Sem.inner ctx).lex, .undefined) w) fun r w2 h2 => WP eng answer n h2 (Pure.pure (Sem.breakToNormal r)) w2 Q :=
    wp_mono (x := fun w => M.loop _ w.fuel _ w) (s := w) q fun r w2 h2 qq => wp_of_eq rfl qq
  exact q'

end

end Logic
