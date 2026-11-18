/-
  End-to-end correctness: composing the four simulation theorems, and
  connecting them to the executable translators in `LeanJS.Trans.Core`.

  All theorems assume the *source* program evaluates without a runtime error
  (`NoErr`), as is standard for compiler correctness (cf. CompCert). For
  closed programs whose result is a primitive (number, string, boolean) we
  derive the simplest possible statement: the translated program evaluates
  to exactly the same value.
-/
import LeanJS.Semantics.SimIRToLean
import LeanJS.Semantics.SimLeanToIR
import LeanJS.Trans.Core

set_option autoImplicit true

namespace LeanJS.Semantics

open LeanJS.JS
open LeanJS.Lean
open LeanJS.IR

/-! ## Primitive values are preserved exactly -/

theorem VCorr.prim_eq (h : VCorr S v v') (hp : IsPrim v) : v' = v := by
  cases h with
  | number | string | bool => rfl
  | unit => cases hp
  | undefined => cases hp
  | clo hc _ => have := S.clo_src hc; cases hp <;> cases this
  | record => cases hp
  | array => cases hp

theorem ResultCorr.prim_val (h : ResultCorr S (.val v s) r') (hp : IsPrim v) : r' = .val v s := by
  cases h with
  | val hv => rw [hv.prim_eq hp]

theorem ModeCorr.discard_val (h : ModeCorr S .discard (.val v s) r') : ∃ v', r' = .val v' s := by
  cases h with
  | discard => exact ⟨_, rfl⟩
  | sig _ hs => simp [isSignal] at hs

theorem StmtCorr.val_inv (h : StmtCorr S (.val v s) r') : ∃ v', r' = .val v' s := by
  cases h with
  | val => exact ⟨_, rfl⟩
  | sig _ hs => simp [isSignal] at hs

/-! ## JS round trip: JS → IR → JS -/

/-- JS expressions survive the round trip, up to value correspondence. -/
theorem js_roundtrip_expr
    (h1 : JSToIRExpr e ir) (h2 : IRToJSExpr ir e')
    (heval : JSEvalExpr env st e r) (hok : NoErr r)
    (hc1 : EnvCorr SJI env ienv) (hc2 : EnvCorr SIJ ienv env') :
    ∃ fuel r_ir r', Eval ienv st fuel ir r_ir ∧ ResultCorr SJI r r_ir ∧
      JSEvalExpr env' st e' r' ∧ ResultCorr SIJ r_ir r' := by
  obtain ⟨n, r_ir, e1, c1⟩ := sim_js_to_ir_expr h1 heval hok hc1
  obtain ⟨r', e2, c2⟩ := sim_ir_to_js_expr h2 e1 c1.noErr_right hc2
  exact ⟨n, r_ir, r', e1, c1, e2, c2⟩

/-- A closed JS expression that evaluates to a primitive value still
    evaluates to that exact value after the round trip. -/
theorem js_roundtrip_expr_prim
    (h1 : JSToIRExpr e ir) (h2 : IRToJSExpr ir e')
    (heval : JSEvalExpr .nil st e (.val v s)) (hp : IsPrim v) :
    JSEvalExpr .nil st e' (.val v s) := by
  obtain ⟨_, r_ir, r', _, c1, e2, c2⟩ := js_roundtrip_expr h1 h2 heval trivial .nil .nil
  rw [c1.prim_val hp] at c2
  rw [c2.prim_val hp] at e2
  exact e2

/-- JS programs (statement lists) survive the round trip: normal completion
    stays normal completion with the same final store, and `return`/`throw`
    signals carry corresponding values. -/
theorem js_roundtrip_program
    (h1 : JSToIRStmts p ir) (h2 : IRToJSStmts .discard ir p')
    (heval : JSEvalStmts env st p r) (hok : NoErr r)
    (hc1 : EnvCorr SJI env ienv) (hc2 : EnvCorr SIJ ienv env') :
    ∃ fuel r_ir r', Eval ienv st fuel ir r_ir ∧ StmtCorr SJI r r_ir ∧
      JSEvalStmts env' st p' r' ∧ ModeCorr SIJ .discard r_ir r' := by
  obtain ⟨n, r_ir, e1, c1⟩ := sim_js_to_ir_program h1 heval hok hc1
  obtain ⟨r', e2, c2⟩ := sim_ir_to_js_stmts h2 e1 c1.noErr_right hc2
  exact ⟨n, r_ir, r', e1, c1, e2, c2⟩

/-- A closed JS program that completes normally still completes normally,
    with the same final store, after the round trip. -/
theorem js_roundtrip_program_completes
    (h1 : JSToIRStmts p ir) (h2 : IRToJSStmts .discard ir p')
    (heval : JSEvalStmts .nil st p (.val v s)) :
    ∃ v', JSEvalStmts .nil st p' (.val v' s) := by
  obtain ⟨_, r_ir, r', _, c1, e2, c2⟩ := js_roundtrip_program h1 h2 heval trivial .nil .nil
  obtain ⟨_, rfl⟩ := c1.val_inv
  obtain ⟨v', rfl⟩ := c2.discard_val
  exact ⟨v', e2⟩

/-! ## Lean round trip: Lean → IR → Lean -/

theorem lean_roundtrip_expr
    (h1 : LeanToIRExpr e ir) (h2 : IRToLeanExpr ir e')
    (heval : LeanEvalExpr env st e r) (hok : NoErr r)
    (hc1 : EnvCorr SLI env ienv) (hc2 : EnvCorr SIL ienv env') :
    ∃ fuel r_ir r', Eval ienv st fuel ir r_ir ∧ ResultCorr SLI r r_ir ∧
      LeanEvalExpr env' st e' r' ∧ ResultCorr SIL r_ir r' := by
  obtain ⟨n, r_ir, e1, c1⟩ := sim_lean_to_ir_expr h1 heval hok hc1
  obtain ⟨r', e2, c2⟩ := sim_ir_to_lean_expr h2 e1 c1.noErr_right hc2
  exact ⟨n, r_ir, r', e1, c1, e2, c2⟩

theorem lean_roundtrip_expr_prim
    (h1 : LeanToIRExpr e ir) (h2 : IRToLeanExpr ir e')
    (heval : LeanEvalExpr .nil st e (.val v s)) (hp : IsPrim v) :
    LeanEvalExpr .nil st e' (.val v s) := by
  obtain ⟨_, r_ir, r', _, c1, e2, c2⟩ := lean_roundtrip_expr h1 h2 heval trivial .nil .nil
  rw [c1.prim_val hp] at c2
  rw [c2.prim_val hp] at e2
  exact e2

/-! ## Cross-language -/

/-- JS → IR → Lean, for expressions -/
theorem js_to_lean_expr
    (h1 : JSToIRExpr e ir) (h2 : IRToLeanExpr ir le)
    (heval : JSEvalExpr env st e r) (hok : NoErr r)
    (hc1 : EnvCorr SJI env ienv) (hc2 : EnvCorr SIL ienv lenv) :
    ∃ fuel r_ir r', Eval ienv st fuel ir r_ir ∧ ResultCorr SJI r r_ir ∧
      LeanEvalExpr lenv st le r' ∧ ResultCorr SIL r_ir r' := by
  obtain ⟨n, r_ir, e1, c1⟩ := sim_js_to_ir_expr h1 heval hok hc1
  obtain ⟨r', e2, c2⟩ := sim_ir_to_lean_expr h2 e1 c1.noErr_right hc2
  exact ⟨n, r_ir, r', e1, c1, e2, c2⟩

/-- JS → IR → Lean, for programs: a JS program becomes a Lean expression -/
theorem js_to_lean_program
    (h1 : JSToIRStmts p ir) (h2 : IRToLeanExpr ir le)
    (heval : JSEvalStmts env st p r) (hok : NoErr r)
    (hc1 : EnvCorr SJI env ienv) (hc2 : EnvCorr SIL ienv lenv) :
    ∃ fuel r_ir r', Eval ienv st fuel ir r_ir ∧ StmtCorr SJI r r_ir ∧
      LeanEvalExpr lenv st le r' ∧ ResultCorr SIL r_ir r' := by
  obtain ⟨n, r_ir, e1, c1⟩ := sim_js_to_ir_program h1 heval hok hc1
  obtain ⟨r', e2, c2⟩ := sim_ir_to_lean_expr h2 e1 c1.noErr_right hc2
  exact ⟨n, r_ir, r', e1, c1, e2, c2⟩

theorem js_to_lean_expr_prim
    (h1 : JSToIRExpr e ir) (h2 : IRToLeanExpr ir le)
    (heval : JSEvalExpr .nil st e (.val v s)) (hp : IsPrim v) :
    LeanEvalExpr .nil st le (.val v s) := by
  obtain ⟨_, r_ir, r', _, c1, e2, c2⟩ := js_to_lean_expr h1 h2 heval trivial .nil .nil
  rw [c1.prim_val hp] at c2
  rw [c2.prim_val hp] at e2
  exact e2

/-- Lean → IR → JS, for expressions -/
theorem lean_to_js_expr
    (h1 : LeanToIRExpr e ir) (h2 : IRToJSExpr ir je)
    (heval : LeanEvalExpr env st e r) (hok : NoErr r)
    (hc1 : EnvCorr SLI env ienv) (hc2 : EnvCorr SIJ ienv jenv) :
    ∃ fuel r_ir r', Eval ienv st fuel ir r_ir ∧ ResultCorr SLI r r_ir ∧
      JSEvalExpr jenv st je r' ∧ ResultCorr SIJ r_ir r' := by
  obtain ⟨n, r_ir, e1, c1⟩ := sim_lean_to_ir_expr h1 heval hok hc1
  obtain ⟨r', e2, c2⟩ := sim_ir_to_js_expr h2 e1 c1.noErr_right hc2
  exact ⟨n, r_ir, r', e1, c1, e2, c2⟩

/-- Lean → IR → JS, where the Lean expression becomes a JS program -/
theorem lean_to_js_program
    (h1 : LeanToIRExpr e ir) (h2 : IRToJSStmts .discard ir p)
    (heval : LeanEvalExpr env st e r) (hok : NoErr r)
    (hc1 : EnvCorr SLI env ienv) (hc2 : EnvCorr SIJ ienv jenv) :
    ∃ fuel r_ir r', Eval ienv st fuel ir r_ir ∧ ResultCorr SLI r r_ir ∧
      JSEvalStmts jenv st p r' ∧ ModeCorr SIJ .discard r_ir r' := by
  obtain ⟨n, r_ir, e1, c1⟩ := sim_lean_to_ir_expr h1 heval hok hc1
  obtain ⟨r', e2, c2⟩ := sim_ir_to_js_stmts h2 e1 c1.noErr_right hc2
  exact ⟨n, r_ir, r', e1, c1, e2, c2⟩

theorem lean_to_js_expr_prim
    (h1 : LeanToIRExpr e ir) (h2 : IRToJSExpr ir je)
    (heval : LeanEvalExpr .nil st e (.val v s)) (hp : IsPrim v) :
    JSEvalExpr .nil st je (.val v s) := by
  obtain ⟨_, r_ir, r', _, c1, e2, c2⟩ := lean_to_js_expr h1 h2 heval trivial .nil .nil
  rw [c1.prim_val hp] at c2
  rw [c2.prim_val hp] at e2
  exact e2

end LeanJS.Semantics

/-! ## The executable translators are covered by these theorems -/

namespace LeanJS.Trans.Core

open LeanJS.Semantics
open LeanJS.IR

/-- Forget the certificate of a certified translation -/
def Res.out {P : α → Prop} (x : Res {a // P a}) : Except String α := x.map Subtype.val

theorem Res.sound {P : α → Prop} {x : Res {a // P a}} (h : Res.out x = .ok a) : P a := by
  unfold Res.out at h
  cases x with
  | error _ => simp [Except.map] at h
  | ok p => simp [Except.map] at h; exact h ▸ p.property

/-- JS program → JS program, through IR -/
def jsRoundtrip (p : JS.Program) : Except String JS.Program := do
  let ⟨ir, _⟩ ← jsStmts p
  let ⟨p', _⟩ ← irStmts .discard ir
  pure p'

/-- JS program → Lean expression, through IR -/
def jsToLean (p : JS.Program) : Except String LeanJS.Lean.LeanExpr := do
  let ⟨ir, _⟩ ← jsStmts p
  let ⟨e, _⟩ ← irLean ir
  pure e

/-- Lean expression → JS program, through IR -/
def leanToJS (e : LeanJS.Lean.LeanExpr) : Except String JS.Program := do
  let ⟨ir, _⟩ ← leanExpr e
  let ⟨p, _⟩ ← irStmts .discard ir
  pure p

/-- Lean expression → Lean expression, through IR -/
def leanRoundtrip (e : LeanJS.Lean.LeanExpr) : Except String LeanJS.Lean.LeanExpr := do
  let ⟨ir, _⟩ ← leanExpr e
  let ⟨e', _⟩ ← irLean ir
  pure e'

theorem jsRoundtrip_spec (h : jsRoundtrip p = .ok p') :
    ∃ ir, JSToIRStmts p ir ∧ IRToJSStmts .discard ir p' := by
  unfold jsRoundtrip at h
  cases h1 : jsStmts p with
  | error _ => simp [h1, bind, Except.bind] at h
  | ok r1 =>
    cases h2 : irStmts .discard r1.val with
    | error _ => simp [h1, h2, bind, Except.bind] at h
    | ok r2 =>
      simp [h1, h2, bind, Except.bind, pure, Except.pure] at h
      exact ⟨r1.val, r1.property, h ▸ r2.property⟩

theorem jsToLean_spec (h : jsToLean p = .ok e) :
    ∃ ir, JSToIRStmts p ir ∧ IRToLeanExpr ir e := by
  unfold jsToLean at h
  cases h1 : jsStmts p with
  | error _ => simp [h1, bind, Except.bind] at h
  | ok r1 =>
    cases h2 : irLean r1.val with
    | error _ => simp [h1, h2, bind, Except.bind] at h
    | ok r2 =>
      simp [h1, h2, bind, Except.bind, pure, Except.pure] at h
      exact ⟨r1.val, r1.property, h ▸ r2.property⟩

theorem leanToJS_spec (h : leanToJS e = .ok p) :
    ∃ ir, LeanToIRExpr e ir ∧ IRToJSStmts .discard ir p := by
  unfold leanToJS at h
  cases h1 : leanExpr e with
  | error _ => simp [h1, bind, Except.bind] at h
  | ok r1 =>
    cases h2 : irStmts .discard r1.val with
    | error _ => simp [h1, h2, bind, Except.bind] at h
    | ok r2 =>
      simp [h1, h2, bind, Except.bind, pure, Except.pure] at h
      exact ⟨r1.val, r1.property, h ▸ r2.property⟩

theorem leanRoundtrip_spec (h : leanRoundtrip e = .ok e') :
    ∃ ir, LeanToIRExpr e ir ∧ IRToLeanExpr ir e' := by
  unfold leanRoundtrip at h
  cases h1 : leanExpr e with
  | error _ => simp [h1, bind, Except.bind] at h
  | ok r1 =>
    cases h2 : irLean r1.val with
    | error _ => simp [h1, h2, bind, Except.bind] at h
    | ok r2 =>
      simp [h1, h2, bind, Except.bind, pure, Except.pure] at h
      exact ⟨r1.val, r1.property, h ▸ r2.property⟩

/-- **The CLI's verified JS round trip is correct**: if `jsRoundtrip` accepts
    a closed program that completes normally, the output program also
    completes normally with the same final store. -/
theorem jsRoundtrip_correct (h : jsRoundtrip p = .ok p')
    (heval : JSEvalStmts .nil st p (.val v s)) :
    ∃ v', JSEvalStmts .nil st p' (.val v' s) := by
  obtain ⟨ir, h1, h2⟩ := jsRoundtrip_spec h
  exact js_roundtrip_program_completes h1 h2 heval

/-- **The CLI's verified JS → Lean translation is correct.** -/
theorem jsToLean_correct (h : jsToLean p = .ok le)
    (heval : JSEvalStmts env st p r) (hok : NoErr r)
    (hc1 : EnvCorr SJI env ienv) (hc2 : EnvCorr SIL ienv lenv) :
    ∃ fuel ir r_ir r', Eval ienv st fuel ir r_ir ∧ StmtCorr SJI r r_ir ∧
      LeanEvalExpr lenv st le r' ∧ ResultCorr SIL r_ir r' := by
  obtain ⟨ir, h1, h2⟩ := jsToLean_spec h
  obtain ⟨n, r_ir, r', e1, c1, e2, c2⟩ := js_to_lean_program h1 h2 heval hok hc1 hc2
  exact ⟨n, ir, r_ir, r', e1, c1, e2, c2⟩

/-- **The CLI's verified Lean → JS translation is correct.** -/
theorem leanToJS_correct (h : leanToJS e = .ok p)
    (heval : LeanEvalExpr env st e r) (hok : NoErr r)
    (hc1 : EnvCorr SLI env ienv) (hc2 : EnvCorr SIJ ienv jenv) :
    ∃ fuel ir r_ir r', Eval ienv st fuel ir r_ir ∧ ResultCorr SLI r r_ir ∧
      JSEvalStmts jenv st p r' ∧ ModeCorr SIJ .discard r_ir r' := by
  obtain ⟨ir, h1, h2⟩ := leanToJS_spec h
  obtain ⟨n, r_ir, r', e1, c1, e2, c2⟩ := lean_to_js_program h1 h2 heval hok hc1 hc2
  exact ⟨n, ir, r_ir, r', e1, c1, e2, c2⟩

/-- **The CLI's verified Lean round trip is correct.** -/
theorem leanRoundtrip_correct (h : leanRoundtrip e = .ok e')
    (heval : LeanEvalExpr .nil st e (.val v s)) (hp : IsPrim v) :
    LeanEvalExpr .nil st e' (.val v s) := by
  obtain ⟨ir, h1, h2⟩ := leanRoundtrip_spec h
  exact lean_roundtrip_expr_prim h1 h2 heval hp

end LeanJS.Trans.Core
