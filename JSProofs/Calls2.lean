import JSProofs.Auto

/-!
# Calls inside a body (zippy docs/react-proofs.md)

`f(a₁, …)` where `f` is a variable: the reference (`Scope.resolve`), its value (`Scope.lookup`: the same record),
`this` undefined (a declarative or function record), the arguments left to right (`ArgsWP`), then the callee's
[[Call]] one level of calls down (`wp_call`), whose spec is the callee's own theorem. `wp_callGen` enters a
compiled function: its generated statements in `FDI.fdiCtx`, from `bodyState`.
-/

open ES ES.M HostRuns
open Std (HashMap)

namespace Logic

/-- Where `resolve` and `lookup` both succeed, they stop at the same record, which binds the name to the value. -/
theorem resolve_lookup (s : State) (x : JSStr) (v : Value) :
    ∀ (k : Nat) (e0 e : EnvId), Scope.resolve s k e0 x = some e → Scope.lookup s k e0 x = some v →
      ∃ bm o bd, e < s.envs.size ∧ Scope.declLike? (s.envEntry e) = some (bm, o) ∧ bm[x]? = some bd ∧
        bd.value = some v := by
  intro k
  induction k with
  | zero => intro e0 e hr; simp [Scope.resolve] at hr
  | succ k ih =>
    intro e0 e hr hl
    simp only [Scope.resolve] at hr
    rw [Scope.lookup_succ] at hl
    by_cases he : e0 < s.envs.size
    · simp only [he, ↓reduceIte] at hr hl
      cases hd : Scope.declLike? (s.envEntry e0) with
      | none => rw [hd] at hr; simp at hr
      | some p =>
        obtain ⟨bm, o⟩ := p
        rw [hd] at hr hl
        simp only at hr hl
        cases hb : bm[x]? with
        | some bd =>
          have hc : bm.contains x = true := by simp [Std.HashMap.contains_iff_mem, Std.HashMap.mem_iff_isSome_getElem?, hb]
          simp only [hc, ↓reduceIte, Option.some.injEq] at hr
          subst hr
          rw [hb] at hl
          exact ⟨bm, o, bd, he, hd, hb, hl⟩
        | none =>
          have hc : bm.contains x = false := by
            simp [Std.HashMap.contains_eq_isSome_getElem?, hb]
          simp only [hc, Bool.false_eq_true, ↓reduceIte] at hr
          rw [hb] at hl
          cases o with
          | none => simp at hr
          | some o => exact ih o e hr hl
    · simp [he] at hr

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ}

/-- An argument list from `acc` on: each plain argument evaluated in turn (spread arguments are not covered). -/
def ArgsWP (eng : Engine) (answer : HostAnswer σ) (n : Nat) (ctx : Ctx) :
    List Sem.ArgD → Array Value → σ → State → (Array Value → State → σ → Prop) → Prop
  | [], acc, h, s, Q => Q acc s h
  | .expr e :: as, acc, h, s, Q => WP eng answer n h (e ctx) s fun v w h1 => ArgsWP eng answer n ctx as (acc.push v) h1 w Q
  | .spread _ :: _, _, _, _, _ => False

theorem wp_foldArgs {n : Nat} (ctx : Ctx) {Q : Array Value → State → σ → Prop} :
    ∀ (as : List Sem.ArgD) (acc : Array Value) (h : σ) (s : State), ArgsWP eng answer n ctx as acc h s Q →
      WP eng answer n h (M.foldList as acc fun acc a => match a with
        | .expr e => do Pure.pure (acc.push (← e ctx))
        | .spread e => do
          let v ← e ctx
          let xs ← iterableToList v
          Pure.pure (acc ++ xs)) s Q := by
  intro as
  induction as with
  | nil => intro acc h s hw; exact wp_of_eq rfl hw
  | cons a as ih =>
    intro acc h s hw
    cases a with
    | spread e => exact hw.elim
    | expr e =>
      rw [wp_iff_wpr, M.foldList_cons]
      apply wpr_bind
      rw [← wp_iff_wpr]
      apply wp_bind
      exact wp_mono hw fun v w h1 q => wp_of_eq rfl (ih _ h1 w q)

/-- **An argument list.** -/
theorem wp_args {n : Nat} {h : σ} {as : Array Sem.ArgD} {ctx : Ctx} {s : State}
    {Q : Array Value → State → σ → Prop} (hw : ArgsWP eng answer n ctx as.toList #[] h s Q) :
    WP eng answer n h (Sem.args as ctx) s Q := by
  show WP eng answer n h (M.foldArr as #[] _) s Q
  rw [M.foldArr_eq]
  exact wp_foldArgs ctx as.toList #[] h s hw

/-- The callee's value is a function object (`IsCallable`). -/
def CallableC (s : State) (fv : Value) : Prop :=
  match fv with
  | .obj o => o < s.heap.size ∧ match (s.objEntry o).kind with
    | .func _ | .builtin _ | .bound .. => True
    | _ => False
  | _ => False

theorem isCallable_of {s : State} {fv : Value} (h : CallableC s fv) : isCallable fv s = .ok true s := by
  cases fv with
  | obj o =>
    obtain ⟨hlt, hk⟩ := h
    simp only [isCallable, readObj_entry o _ s hlt]
    cases hkd : (s.objEntry o).kind <;> rw [hkd] at hk <;> first | exact hk.elim | rfl
  | _ => exact h.elim

/-- **`f(args)`** of a variable's function: its value read through the scope chain, `this` undefined, the
arguments, then the callee one level of calls down (its own spec, through `wp_call`). -/
theorem wp_callIdentC {n : Nat} {h : σ} {f : JSStr} {as : Array Sem.ArgD} {name : CalleeDesc} {ctx : Ctx}
    {s : State} {Q : Value → State → σ → Prop} (hk : depth ≤ s.fuel)
    (hw : match Scope.resolve s depth ctx.lex f, Scope.lookup s depth ctx.lex f with
      | some _, some fv => ArgsWP eng answer (n + 1) ctx as.toList #[] h s fun args w h1 =>
          CallableC w fv ∧ WP eng answer n h1 (callImpl eng fv .undefined args) w Q
      | _, _ => False) :
    WP eng answer (n + 1) h (Sem.call (Sem.identRef f) (Sem.args as) false name ctx) s Q := by
  cases hr : Scope.resolve s depth ctx.lex f with
  | none => rw [hr] at hw; exact hw.elim
  | some e =>
    cases hl : Scope.lookup s depth ctx.lex f with
    | none => rw [hr, hl] at hw; exact hw.elim
    | some fv =>
      rw [hr, hl] at hw
      obtain ⟨bm, o, bd, he, hd, hb, hv⟩ := resolve_lookup s f fv depth ctx.lex e hr hl
      have h1 : Sem.identRef f ctx s = .ok (.env (some e) f ctx.strict) s :=
        Scope.resolveBinding_of_resolve s depth ctx.lex f ctx.strict e hr hk
      have h2 := Scope.getRefValue_env s e f ctx.strict he bm o hd bd fv hb hv
      have h3 : refThisValue (.env (some e) f ctx.strict) s = .ok .undefined s := by
        simp only [refThisValue, readEnv_entry e _ s he]
        cases hen : s.envEntry e <;> rw [hen] at hd <;> simp [Scope.declLike?] at hd <;> rfl
      rw [wp_iff_wpr]
      simp only [Sem.call, M.bind_eq, M.bind_apply, h1, M.bindRes_ok, h2, Bool.false_and, Bool.false_eq_true,
        ↓reduceIte, h3]
      apply wpr_bind
      refine wp_mono (wp_args hw) fun args w h' ⟨hc, hq⟩ => ?_
      rw [wp_iff_wpr]
      simp only [M.bind_apply, isCallable_of hc, M.bindRes_ok, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      rw [← wp_iff_wpr]
      exact wp_call hq

/-- **`if (t) c else a`**: the test, then the branch `toBoolean` picks (an empty `else`: a normal, empty completion);
the completion's empty value becomes `undefined`. -/
theorem wp_ifS {n : Nat} {h : σ} {t : Sem.CExpr} {c : Sem.CStmt} {a : Option Sem.CStmt} {ctx : Ctx} {s : State}
    {Q : Compl → State → σ → Prop}
    (hw : WP eng answer n h (t (Sem.inner ctx)) s fun tv w h1 =>
      WP eng answer n h1 (if toBoolean tv then c (Sem.inner ctx) else match a with
        | some a => a (Sem.inner ctx)
        | none => Pure.pure (.normal none)) w fun r w2 h2 => Q (r.updateEmpty (some .undefined)) w2 h2) :
    WP eng answer n h (Sem.ifS t c a ctx) s Q := by
  rw [wp_iff_wpr]
  simp only [Sem.ifS, M.bind_eq, M.bind_apply]
  apply wpr_bind
  refine wp_mono hw fun tv w h1 q => ?_
  cases hb : toBoolean tv
  · cases a with
    | none =>
      simp only [hb, Bool.false_eq_true, ↓reduceIte] at q ⊢
      obtain ⟨r, w2, h2, k, hr, q'⟩ := q
      cases hr
      exact wp_of_eq rfl q'
    | some a =>
      simp only [hb, Bool.false_eq_true, ↓reduceIte] at q ⊢
      rw [wp_iff_wpr, M.bind_apply]
      exact wpr_bind (wp_mono q fun r w2 h2 q' => wp_of_eq rfl q')
  · simp only [hb, ↓reduceIte] at q ⊢
    rw [wp_iff_wpr, M.bind_apply]
    exact wpr_bind (wp_mono q fun r w2 h2 q' => wp_of_eq rfl q')

/-- **Entering a compiled function**: its generated statements (`f`, equal to the interpreter's by `heq`) in
`FDI.fdiCtx`, from `bodyState`. -/
theorem wp_callGen {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t : Value} {args : Array Value}
    {s : State} {Q : Value → State → σ → Prop} {f : Nat → Sem.CStmt} {stmts : Array Stmt} {H : Nat}
    (heq : ∀ m, f m = (evalStmts (m + H) · stmts)) (hH : H ≤ 999999)
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : 2 ≤ s.fuel)
    (hcls : d.isClassCtor = false) (hmode : d.thisMode = .strict)
    (hasync : d.code.isAsync = false) (hgen : d.code.isGenerator = false) (hs : FDI.Simple d)
    (hbody : d.code.body = .stmts stmts) (hdisp : d.code.info.fdi.usesDispose = false)
    (hb : WP eng answer n h (f (999999 - H) (FDI.fdiCtx fo d s.envs.size)) (bodyState s fo d t args)
      fun c w h' => Q (retVal c) { w with realm := s.realm, script := s.script } h') :
    WP eng answer n h (callImpl eng (.obj fo) t args) s Q := by
  apply wp_call_simple hlt hk hf hcls hmode hasync hgen hs hbody hdisp
  rw [heq, Nat.sub_add_cancel hH] at hb
  exact hb

/-- **`a op b`** of two Numbers, a numeric operator. -/
theorem wp_numOp {n : Nat} {h : σ} {op : BinOp} {a b : F64} {s : State} {Q : Value → State → σ → Prop}
    (hop : isNumOp op = true) (hq : Q (.num (numberBinOp op a b)) s h) :
    WP eng answer n h (Sem.binaryOp op (.num a) (.num b)) s Q :=
  wp_of_eq (binaryOp_num op a b s hop) hq

end

/-- `js_step` with the rules for calls, `if`, and numeric operators. -/
macro_rules
  | `(tactic| js_step) => `(tactic| first
      | apply wp_ifS
      | apply wp_callIdentC (by simp [depth]; omega)
      | apply wp_numOp (by decide)
      | (simp only [ArgsWP]; done)
      | simp only [ArgsWP])

end Logic
