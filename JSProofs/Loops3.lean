import JSProofs.FuncExpr

/-!
# `do … while` loops, one iteration at a time (zippy docs/react-proofs.md)

`do body while (test)` (React's `flushSyncWorkAcrossRoots_impl` runs its roots again while one did work): like `for`
(`Loops2`), the loop runs under the fuel when it starts; each iteration takes a step of fuel, runs the body, then the
test. `DoWP` is "the loop from here"; `do_iter` unfolds one iteration.
-/

open ES ES.M HostRuns
open Std (HashMap)

namespace Logic

/-- One iteration of `do body while (test)`. -/
def doStep (ctx : Ctx) (labels : Array JSStr) (body : Sem.CStmt) (test : Sem.CExpr) :
    Value → M (Value ⊕ Compl) := fun v => do
  M.tick
  let r ← body ctx
  if !loopContinues r labels then return .inr (r.updateEmpty (some v))
  let v := (r.value?).getD v
  if !toBoolean (← test ctx) then return .inr (Compl.normal (some v))
  return .inl v

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ}

/-- The loop from value `v` with `b` iterations allowed. -/
def DoWP (eng : Engine) (answer : HostAnswer σ) (n : Nat) (ctx : Ctx) (labels : Array JSStr) (body : Sem.CStmt)
    (test : Sem.CExpr) (b : Nat) (v : Value) (h : σ) (s : State) (Q : Compl → State → σ → Prop) : Prop :=
  WPR eng answer n h (M.loop (doStep ctx labels body test) b v s) Q

/-- **One iteration**: a step of fuel, the body, then (if it went on) the test: again or done. -/
theorem do_iter {n : Nat} {ctx : Ctx} {labels : Array JSStr} {body : Sem.CStmt} {test : Sem.CExpr} {b : Nat}
    {v : Value} {h : σ} {s : State} {Q : Compl → State → σ → Prop} (hb : 1 ≤ b) (hf : 1 ≤ s.fuel)
    (hw : WP eng answer n h (body ctx) (s.withFuel (s.fuel - 1)) fun r w h1 =>
      if loopContinues r labels then
        WP eng answer n h1 (test ctx) w fun tv w2 h2 =>
          if toBoolean tv then DoWP eng answer n ctx labels body test (b - 1) ((r.value?).getD v) h2 w2 Q
          else Q (.normal (some ((r.value?).getD v))) w2 h2
      else Q (r.updateEmpty (some v)) w h1) :
    DoWP eng answer n ctx labels body test b v h s Q := by
  obtain ⟨k, rfl⟩ : ∃ k, b = k + 1 := ⟨b - 1, by omega⟩
  have hfz : (s.fuel == 0) = false := by simp; omega
  unfold DoWP
  simp only [M.loop]
  apply wpr_loopRes
  simp only [doStep, M.bind_eq, M.bind_apply, M.tick, hfz, Bool.false_eq_true, ↓reduceIte, M.bindRes_ok]
  apply wpr_bind
  refine wp_mono hw fun r w h1 q => ?_
  cases hl : loopContinues r labels
  · simp only [hl, Bool.false_eq_true, ↓reduceIte, Bool.not_false] at q ⊢
    exact wp_of_eq rfl q
  · simp only [hl, ↓reduceIte, Bool.not_true, Bool.false_eq_true] at q ⊢
    rw [wp_iff_wpr]
    apply wpr_bind
    refine wp_mono q fun tv w2 h2 q' => ?_
    cases ht : toBoolean tv
    · simp only [ht, Bool.false_eq_true, ↓reduceIte, Bool.not_false] at q' ⊢
      exact wp_of_eq rfl q'
    · simp only [ht, ↓reduceIte, Bool.not_true, Bool.false_eq_true] at q' ⊢
      exact wp_of_eq rfl q'

/-- **`do body while (test)`**: the iterations from the fuel left; a `break` without a label ends it normally. -/
theorem wp_doWhile {n : Nat} {h : σ} {body : Sem.CStmt} {test : Sem.CExpr} {ctx : Ctx} {s : State}
    {Q : Compl → State → σ → Prop}
    (hw : DoWP eng answer n (Sem.inner ctx) ctx.labels body test s.fuel .undefined h s
      fun r w2 h2 => Q (Sem.breakToNormal r) w2 h2) :
    WP eng answer n h (Sem.doWhile body test ctx) s Q := by
  rw [wp_iff_wpr]
  simp only [Sem.doWhile, M.bind_eq, M.bind_apply]
  apply wpr_bind
  exact wp_mono (x := fun w => M.loop _ w.fuel _ w) (s := s) hw fun r w2 h2 q => wp_of_eq rfl q

end

end Logic
