import JSProofs.ArrayRules

/-!
# `for` loops, one iteration at a time (zippy docs/react-proofs.md)

`for (var x = …; test; ) body` (React's `getRootForUpdatedFiber` walks `.return` up the fiber tree this way). The loop
runs under a bound fixed when it starts (the fuel then); each iteration takes a step of fuel (`State.withFuel`).
`ForWP` is "the loop from here"; `for_iter` unfolds one iteration, so for a tree of fixed shape the `js` tactic
follows the iterations like straight-line code.
-/

open ES ES.M HostRuns
open Std (HashMap)

namespace Logic

/-- The state with its fuel replaced (a loop iteration's step). -/
def _root_.ES.State.withFuel (s : State) (f : Nat) : State := { s with fuel := f }

@[js_simp] theorem withFuel_envEntry (s : State) (f : Nat) (e : EnvId) : (s.withFuel f).envEntry e = s.envEntry e := rfl
@[js_simp] theorem withFuel_objEntry (s : State) (f : Nat) (o : ObjId) : (s.withFuel f).objEntry o = s.objEntry o := rfl
@[js_simp] theorem withFuel_envs (s : State) (f : Nat) : (s.withFuel f).envs = s.envs := rfl
@[js_simp] theorem withFuel_heap (s : State) (f : Nat) : (s.withFuel f).heap = s.heap := rfl
@[js_simp] theorem withFuel_fuel (s : State) (f : Nat) : (s.withFuel f).fuel = f := rfl

theorem frame_withFuel {fp : Footprint} {s u : State} (hF : Frame fp s u) (f : Nat) : Frame fp s (u.withFuel f) :=
  ⟨hF.envs_le, hF.heap_le, hF.env_agree, hF.obj_agree, hF.env_eq, hF.obj_eq, hF.realms_eq, hF.jobs_prefix,
    hF.jobs_eq⟩

/-- One iteration of `for (…; test; ) body` whose declarations are `var`s (no per-iteration copies). -/
def forStep (ctx : Ctx) (labels : Array JSStr) (test : Sem.CExpr) (body : Sem.CStmt) :
    EnvId × Value → M ((EnvId × Value) ⊕ Compl) := fun (lex, v) => do
  M.tick
  let ictx := { ctx with lex }
  if !toBoolean (← test ictx) then return .inr (.normal (some v))
  let r ← body ictx
  if !loopContinues r labels then return .inr (r.updateEmpty (some v))
  return .inl (lex, (r.value?).getD v)

/-! ## `<` on Numbers -/

/-- `a < b` on two Numbers. -/
def ltNum (a b : F64) : Bool := (if a == .nan || b == .nan then none else some (Conv.ltF a b)) == some true

theorem toPrim_num (a : F64) (hint : Option Bool) (s : State) : toPrim (.num a) hint s = .ok (.num a) s := by
  unfold toPrim; rw [show maxDepth = 19999 + 1 from rfl]; simp only [ES.toPrimitive]; rfl

theorem binaryOp_lt_num (a b : F64) (s : State) :
    Sem.binaryOp .lt (.num a) (.num b) s = .ok (.bool (ltNum a b)) s := by
  simp only [Sem.binaryOp, isLessThan, M.bind_eq, M.bind_apply, ↓reduceIte, toPrim_num, M.bindRes_ok,
    FDI.pure_app, toNumeric_num, ltNum]

simproc [js_simp] ltNumEval (ltNum _ _) := reduceClosed

/-! ## Strict equality of non-Numbers, by their kinds (React's `null !== x`, `fiber === other`) -/

@[js_simp] theorem seq_null_null : isStrictlyEqual .null .null = true := rfl
@[js_simp] theorem seq_null_obj (o : ObjId) : isStrictlyEqual .null (.obj o) = false := rfl
@[js_simp] theorem seq_obj_null (o : ObjId) : isStrictlyEqual (.obj o) .null = false := rfl
@[js_simp] theorem seq_undef_undef : isStrictlyEqual .undefined .undefined = true := rfl
@[js_simp] theorem seq_undef_obj (o : ObjId) : isStrictlyEqual .undefined (.obj o) = false := rfl
@[js_simp] theorem seq_obj_undef (o : ObjId) : isStrictlyEqual (.obj o) .undefined = false := rfl
@[js_simp] theorem seq_null_undef : isStrictlyEqual .null .undefined = false := rfl
@[js_simp] theorem seq_undef_null : isStrictlyEqual .undefined .null = false := rfl
@[js_simp] theorem seq_obj_obj (a b : ObjId) : isStrictlyEqual (.obj a) (.obj b) = (a == b) := rfl
@[js_simp] theorem seq_null_num (x : F64) : isStrictlyEqual .null (.num x) = false := rfl
@[js_simp] theorem seq_num_null (x : F64) : isStrictlyEqual (.num x) .null = false := rfl
@[js_simp] theorem seq_obj_num (o : ObjId) (x : F64) : isStrictlyEqual (.obj o) (.num x) = false := rfl
@[js_simp] theorem seq_num_obj (o : ObjId) (x : F64) : isStrictlyEqual (.num x) (.obj o) = false := rfl

attribute [js_simp] ArgsWP Sem.breakToNormal Compl.value? Option.getD_some Option.getD_none loopContinues

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ}

/-- The loop from iteration state `(ctx.lex, v)` with `b` iterations allowed. -/
def ForWP (eng : Engine) (answer : HostAnswer σ) (n : Nat) (ctx : Ctx) (labels : Array JSStr) (test : Sem.CExpr)
    (body : Sem.CStmt) (b : Nat) (v : Value) (h : σ) (s : State) (Q : Compl → State → σ → Prop) : Prop :=
  WPR eng answer n h (M.loop (forStep ctx labels test body) b (ctx.lex, v) s) Q

/-- **One iteration**: a step of fuel, the test, and either the end (the last value) or the body and the rest. -/
theorem for_iter {n : Nat} {ctx : Ctx} {labels : Array JSStr} {test : Sem.CExpr} {body : Sem.CStmt} {b : Nat}
    {v : Value} {h : σ} {s : State} {Q : Compl → State → σ → Prop} (hb : 1 ≤ b) (hf : 1 ≤ s.fuel)
    (hw : WP eng answer n h (test ctx) (s.withFuel (s.fuel - 1)) fun tv w h1 =>
      if toBoolean tv then
        WP eng answer n h1 (body ctx) w fun r w2 h2 =>
          if loopContinues r labels then ForWP eng answer n ctx labels test body (b - 1) ((r.value?).getD v) h2 w2 Q
          else Q (r.updateEmpty (some v)) w2 h2
      else Q (.normal (some v)) w h1) :
    ForWP eng answer n ctx labels test body b v h s Q := by
  obtain ⟨k, rfl⟩ : ∃ k, b = k + 1 := ⟨b - 1, by omega⟩
  have hfz : (s.fuel == 0) = false := by simp; omega
  unfold ForWP
  simp only [M.loop]
  apply wpr_loopRes
  simp only [forStep, M.bind_eq, M.bind_apply, M.tick, hfz, Bool.false_eq_true, ↓reduceIte, M.bindRes_ok]
  have hctx : ({ ctx with lex := ctx.lex } : Ctx) = ctx := rfl
  rw [hctx]
  apply wpr_bind
  refine wp_mono hw fun tv w h1 q => ?_
  cases htb : toBoolean tv
  · simp only [htb, Bool.false_eq_true, ↓reduceIte, Bool.not_false] at q ⊢
    exact wp_of_eq rfl q
  · simp only [htb, ↓reduceIte, Bool.not_true, Bool.false_eq_true] at q ⊢
    rw [wp_iff_wpr]
    apply wpr_bind
    refine wp_mono q fun r w2 h2 q' => ?_
    cases hl : loopContinues r labels
    · simp only [hl, Bool.false_eq_true, ↓reduceIte, Bool.not_false] at q' ⊢
      exact wp_of_eq rfl q'
    · simp only [hl, ↓reduceIte, Bool.not_true, Bool.false_eq_true] at q' ⊢
      exact wp_of_eq rfl q'

theorem pure_bind' {α β : Type} (a : α) (f : α → M β) : (Pure.pure a : M α).bind f = f a := by
  funext s; rfl

theorem forS_var_eq (decl : Sem.CStmt) (test : Sem.CExpr) (body : Sem.CStmt) (ctx : Ctx) :
    Sem.forS (.var decl) (some test) none body ctx = (do
      let r ← (do
        let _ ← decl (Sem.inner ctx)
        M.repeatFrom ((Sem.inner ctx).lex, Value.undefined) (forStep (Sem.inner ctx) ctx.labels test body))
      Pure.pure (Sem.breakToNormal r)) := by
  funext s
  simp only [Sem.forS, withDisposeScope, Bool.not_false, ↓reduceIte, M.bind_eq, M.bind_apply,
    M.bindRes_ok, Array.isEmpty_empty, Sem.inner, pure_bind', forStep]
  rfl

/-- **`for (var …; test; ) body`**: the declarations, then the iterations from the fuel left (`ForWP`); a `break`
without a label ends it normally. -/
theorem wp_forVar {n : Nat} {h : σ} {decl : Sem.CStmt} {test : Sem.CExpr} {body : Sem.CStmt} {ctx : Ctx} {s : State}
    {Q : Compl → State → σ → Prop}
    (hw : WP eng answer n h (decl (Sem.inner ctx)) s fun _ w h1 =>
      ForWP eng answer n (Sem.inner ctx) ctx.labels test body w.fuel .undefined h1 w
        fun r w2 h2 => Q (Sem.breakToNormal r) w2 h2) :
    WP eng answer n h (Sem.forS (.var decl) (some test) none body ctx) s Q := by
  rw [forS_var_eq]
  apply wp_bind
  apply wp_bind
  refine wp_mono hw fun _ w h1 q => ?_
  have q' : WPR eng answer n h1 (M.loop (forStep (Sem.inner ctx) ctx.labels test body) w.fuel
      ((Sem.inner ctx).lex, .undefined) w) fun r w2 h2 => WP eng answer n h2 (Pure.pure (Sem.breakToNormal r)) w2 Q :=
    wp_mono (x := fun w => M.loop _ w.fuel _ w) (s := w) q fun r w2 h2 qq => wp_of_eq rfl qq
  exact q'

/-- **`a < b`** of two Numbers. -/
theorem wp_ltNum {n : Nat} {h : σ} {a b : F64} {s : State} {Q : Value → State → σ → Prop}
    (hq : Q (.bool (ltNum a b)) s h) : WP eng answer n h (Sem.binaryOp .lt (.num a) (.num b)) s Q :=
  wp_of_eq (binaryOp_lt_num a b s) hq

end

end Logic
