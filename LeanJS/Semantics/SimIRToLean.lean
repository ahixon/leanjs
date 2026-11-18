/-
  Forward simulation: IR → Lean preserves semantics (verified core).

  If an IR expression evaluates (with any fuel) to a non-error result, and it
  translates to Lean, then under corresponding environments the Lean
  expression evaluates to a corresponding result. IR `unit` and `undefined`
  both become Lean `()`.
-/
import LeanJS.Semantics.SimIRToJS

set_option autoImplicit true

namespace LeanJS.Semantics

open LeanJS.Lean
open LeanJS.IR

def IRLeanClo (v v' : IRValue) (e e' : Env) : Prop :=
  ∃ p body body', v = .closure e none [p] body ∧
    v' = .leanClosure e' none p body' ∧ IRToLeanExpr body body'

def SIL : CorrSpec where
  uUnit := .unit
  uUndef := .unit
  hUnit := .unit
  hUndef := .unit
  Clo := IRLeanClo
  clo_src := by rintro _ _ _ _ ⟨_, _, _, rfl, _, _⟩; exact .closure
  clo_tgt := by rintro _ _ _ _ ⟨_, _, _, _, rfl, _⟩; exact .lean

theorem irBinOpToLean_spec (h : irBinOpToLean op = some lop) : leanBinOpToIR lop = some op := by
  cases op <;> simp [irBinOpToLean] at h <;> subst h <;> rfl

theorem irUnaryOpToLean_spec (h : irUnaryOpToLean op = some lop) : leanUnaryOpToIR lop = some op := by
  cases op <;> simp [irUnaryOpToLean] at h <;> subst h <;> rfl

/-- A one-argument `EvalArgs` derivation that produced a value -/
theorem EvalArgs.inv_single_val (h : EvalArgs env st n [a] [] (.val (.array vs) s)) :
    ∃ v, Eval env st n a (.val v s) ∧ vs = [v] := by
  cases h with
  | cons_ok ha hrest =>
    cases hrest with
    | nil => exact ⟨_, ha, rfl⟩
  | cons_signal _ hs => simp [isSignal] at hs

theorem EvalArgs.inv_single_signal (h : EvalArgs env st n [a] [] r) (hs : isSignal r) :
    Eval env st n a r := by
  cases h with
  | cons_ok ha hrest =>
    cases hrest with
    | nil => simp [isSignal] at hs
  | cons_signal ha _ => exact ha

set_option maxHeartbeats 6400000 in
mutual

theorem sim_ir_lean_expr {n : Nat} (h : Eval ienv st n e r) (hne : NoErr r)
    (ht : IRToLeanExpr e e') (hc : EnvCorr SIL ienv lenv) :
    ∃ r', LeanEvalExpr lenv st e' r' ∧ ResultCorr SIL r r' := by
  cases h with
  | fuel_zero => exact absurd hne id
  | lit =>
    cases ht with
    | num => exact ⟨_, .lit, .val .number⟩
    | str => exact ⟨_, .lit, .val .string⟩
    | bool => exact ⟨_, .lit, .val .bool⟩
    | unit => exact ⟨_, .unit, .val .unit⟩
  | var_ok hl =>
    cases ht
    obtain ⟨v', hl', hv⟩ := hc.lookup hl
    exact ⟨_, .ident hl', .val hv⟩
  | var_unbound => exact absurd hne id
  | undefined =>
    cases ht
    exact ⟨_, .unit, .val .undefined⟩
  | let_ok hv hb =>
    cases ht with
    | let_ htv htb =>
      obtain ⟨r1, e1, c1⟩ := sim_ir_lean_expr hv trivial htv hc
      obtain ⟨vv', rfl, hvv⟩ := c1.inv_val
      obtain ⟨r2, e2, c2⟩ := sim_ir_lean_expr hb hne htb (.cons hvv hc)
      exact ⟨_, .let_ok e1 e2, c2⟩
  | let_signal hv hs =>
    cases ht with
    | let_ htv _ =>
      obtain ⟨r1, e1, c1⟩ := sim_ir_lean_expr hv hne htv hc
      exact ⟨_, .let_signal e1 (c1.signal hs), c1⟩
  | lam hp =>
    subst hp
    cases ht with
    | lam hb => exact ⟨_, .lam_one, .val (.clo ⟨_, _, _, rfl, rfl, hb⟩ hc)⟩
  | app_ok hf ha hap =>
    cases ht with
    | app htf hta =>
      obtain ⟨r1, e1, c1⟩ := sim_ir_lean_expr hf trivial htf hc
      obtain ⟨fv', rfl, hfv⟩ := c1.inv_val
      obtain ⟨v, hav, rfl⟩ := ha.inv_single_val
      obtain ⟨r2, e2, c2⟩ := sim_ir_lean_expr hav trivial hta hc
      obtain ⟨v', rfl, hv⟩ := c2.inv_val
      obtain ⟨r3, e3, c3⟩ := sim_ir_lean_apply hap hne hfv hv
      exact ⟨_, .app_ok e1 e2 e3, c3⟩
  | app_func_signal hf hs =>
    cases ht with
    | app htf _ =>
      obtain ⟨r1, e1, c1⟩ := sim_ir_lean_expr hf hne htf hc
      exact ⟨_, .app_fn_signal e1 (c1.signal hs), c1⟩
  | app_args_signal hf ha hs =>
    cases ht with
    | app htf hta =>
      obtain ⟨r1, e1, c1⟩ := sim_ir_lean_expr hf trivial htf hc
      obtain ⟨fv', rfl, hfv⟩ := c1.inv_val
      obtain ⟨r2, e2, c2⟩ := sim_ir_lean_expr (ha.inv_single_signal hs) hne hta hc
      exact ⟨_, .app_arg_signal e1 e2 (c2.signal hs), c2⟩
  | binOp_ok hl hr hres =>
    subst hres
    cases ht with
    | binOp htl htr hop =>
      obtain ⟨r1, e1, c1⟩ := sim_ir_lean_expr hl trivial htl hc
      obtain ⟨lv', rfl, hlv⟩ := c1.inv_val
      obtain ⟨r2, e2, c2⟩ := sim_ir_lean_expr hr trivial htr hc
      obtain ⟨rv', rfl, hrv⟩ := c2.inv_val
      exact ⟨_, .binOp_ok e1 e2 (irBinOpToLean_spec hop), evalBinOp_corr (.inl rfl) hlv hrv _ hne⟩
  | binOp_left_signal hl hs =>
    cases ht with
    | binOp htl _ _ =>
      obtain ⟨r1, e1, c1⟩ := sim_ir_lean_expr hl hne htl hc
      exact ⟨_, .binOp_left_signal e1 (c1.signal hs), c1⟩
  | binOp_right_signal hl hr hs =>
    cases ht with
    | binOp htl htr _ =>
      obtain ⟨r1, e1, c1⟩ := sim_ir_lean_expr hl trivial htl hc
      obtain ⟨lv', rfl, hlv⟩ := c1.inv_val
      obtain ⟨r2, e2, c2⟩ := sim_ir_lean_expr hr hne htr hc
      exact ⟨_, .binOp_right_signal e1 e2 (c2.signal hs), c2⟩
  | unaryOp_ok ha hres =>
    subst hres
    cases ht with
    | unaryOp hta hop =>
      obtain ⟨r1, e1, c1⟩ := sim_ir_lean_expr ha trivial hta hc
      obtain ⟨v', rfl, hv⟩ := c1.inv_val
      exact ⟨_, .unaryOp_ok e1 (irUnaryOpToLean_spec hop), evalUnaryOp_corr _ hv _ hne⟩
  | unaryOp_signal ha hs =>
    cases ht with
    | unaryOp hta _ =>
      obtain ⟨r1, e1, c1⟩ := sim_ir_lean_expr ha hne hta hc
      exact ⟨_, .unaryOp_signal e1 (c1.signal hs), c1⟩
  | record hf =>
    cases ht with
    | record htf =>
      obtain ⟨r1, e1, c1⟩ := sim_ir_lean_fields hf hne htf hc .nil
      exact ⟨_, .structLit e1, c1⟩
  | project_record_ok he hl =>
    cases ht with
    | project hte =>
      obtain ⟨r1, e1, c1⟩ := sim_ir_lean_expr he trivial hte hc
      obtain ⟨rv', rfl, hrv⟩ := c1.inv_val
      obtain ⟨fs', rfl, hfs⟩ := hrv.inv_record
      rcases hfs.lookup _ with ⟨hn, _⟩ | ⟨v, v', hv, hv', hvv⟩
      · rw [hn] at hl; cases hl
      · rw [hv] at hl; cases hl
        exact ⟨_, .proj_ok e1 hv', .val hvv⟩
  | project_record_missing => exact absurd hne id
  | project_constructed_tag he _ =>
    cases ht with
    | project hte =>
      obtain ⟨r1, e1, c1⟩ := sim_ir_lean_expr he trivial hte hc
      obtain ⟨v', rfl, hv⟩ := c1.inv_val
      cases hv with
      | clo hc' _ => cases SIL.clo_src hc'
  | project_constructed_other => exact absurd hne id
  | project_non_record => exact absurd hne id
  | project_signal he hs =>
    cases ht with
    | project hte =>
      obtain ⟨r1, e1, c1⟩ := sim_ir_lean_expr he hne hte hc
      exact ⟨_, .proj_signal e1 (c1.signal hs), c1⟩
  | array he =>
    cases ht with
    | array hte =>
      obtain ⟨r1, e1, c1⟩ := sim_ir_lean_elems he hne hte hc .nil
      exact ⟨_, .arrayLit e1, c1⟩
  | if_true hcnd htr hbr =>
    cases ht with
    | if_ htc htt _ =>
      obtain ⟨r1, e1, c1⟩ := sim_ir_lean_expr hcnd trivial htc hc
      obtain ⟨cv', rfl, hcv⟩ := c1.inv_val
      obtain ⟨r2, e2, c2⟩ := sim_ir_lean_expr hbr hne htt hc
      exact ⟨_, .if_true e1 (hcv.truthy ▸ htr) e2, c2⟩
  | if_false hcnd htr hbr =>
    cases ht with
    | if_ htc _ hte =>
      obtain ⟨r1, e1, c1⟩ := sim_ir_lean_expr hcnd trivial htc hc
      obtain ⟨cv', rfl, hcv⟩ := c1.inv_val
      obtain ⟨r2, e2, c2⟩ := sim_ir_lean_expr hbr hne hte hc
      exact ⟨_, .if_false e1 (hcv.truthy ▸ htr) e2, c2⟩
  | if_signal hcnd hs =>
    cases ht with
    | if_ htc _ _ =>
      obtain ⟨r1, e1, c1⟩ := sim_ir_lean_expr hcnd hne htc hc
      exact ⟨_, .if_signal e1 (c1.signal hs), c1⟩
  | throw_ok he =>
    cases ht with
    | throw hte =>
      obtain ⟨r1, e1, c1⟩ := sim_ir_lean_expr he trivial hte hc
      obtain ⟨v', rfl, hv⟩ := c1.inv_val
      exact ⟨_, .throw_ok e1, .throw hv⟩
  | throw_signal he hs =>
    cases ht with
    | throw hte =>
      obtain ⟨r1, e1, c1⟩ := sim_ir_lean_expr he hne hte hc
      exact ⟨_, .throw_signal e1 (c1.signal hs), c1⟩
  | _ => cases ht
  termination_by (n, 0)
  decreasing_by
    all_goals simp_wf
    all_goals subst_vars
    all_goals first
      | (apply Prod.Lex.left; omega)
      | (apply Prod.Lex.right; first | omega | (simp [List.length_cons]; done) | (simp [List.length_cons]; omega))

theorem sim_ir_lean_fields {n : Nat} (h : EvalFields ienv st n fs acc r) (hne : NoErr r)
    (ht : IRToLeanFields fs fs') (hc : EnvCorr SIL ienv lenv) (ha : FieldsCorr SIL acc acc') :
    ∃ r', LeanEvalFields lenv st fs' acc' r' ∧ ResultCorr SIL r r' := by
  cases h with
  | nil =>
    cases ht
    exact ⟨_, .fields_nil, .val (.record ha.reverse)⟩
  | cons_ok he hrest =>
    cases ht with
    | cons hte htr =>
      obtain ⟨r1, e1, c1⟩ := sim_ir_lean_expr he trivial hte hc
      obtain ⟨v', rfl, hv⟩ := c1.inv_val
      obtain ⟨r2, e2, c2⟩ := sim_ir_lean_fields hrest hne htr hc (.cons hv ha)
      exact ⟨_, .fields_cons_ok e1 e2, c2⟩
  | cons_signal he hs =>
    cases ht with
    | cons hte _ =>
      obtain ⟨r1, e1, c1⟩ := sim_ir_lean_expr he hne hte hc
      exact ⟨_, .fields_cons_signal e1 (c1.signal hs), c1⟩
  termination_by (n, fs.length)
  decreasing_by
    all_goals simp_wf
    all_goals subst_vars
    all_goals first
      | (apply Prod.Lex.left; omega)
      | (apply Prod.Lex.right; first | omega | (simp [List.length_cons]; done) | (simp [List.length_cons]; omega))

theorem sim_ir_lean_elems {n : Nat} (h : EvalElems ienv st n es acc r) (hne : NoErr r)
    (ht : IRToLeanExprs es es') (hc : EnvCorr SIL ienv lenv) (ha : ListCorr SIL acc acc') :
    ∃ r', LeanEvalElems lenv st es' acc' r' ∧ ResultCorr SIL r r' := by
  cases h with
  | nil =>
    cases ht
    exact ⟨_, .elems_nil, .val (.array ha.reverse)⟩
  | cons_ok he hrest =>
    cases ht with
    | cons hte htr =>
      obtain ⟨r1, e1, c1⟩ := sim_ir_lean_expr he trivial hte hc
      obtain ⟨v', rfl, hv⟩ := c1.inv_val
      obtain ⟨r2, e2, c2⟩ := sim_ir_lean_elems hrest hne htr hc (.cons hv ha)
      exact ⟨_, .elems_cons_ok e1 e2, c2⟩
  | cons_signal he hs =>
    cases ht with
    | cons hte _ =>
      obtain ⟨r1, e1, c1⟩ := sim_ir_lean_expr he hne hte hc
      exact ⟨_, .elems_cons_signal e1 (c1.signal hs), c1⟩
  termination_by (n, es.length)
  decreasing_by
    all_goals simp_wf
    all_goals subst_vars
    all_goals first
      | (apply Prod.Lex.left; omega)
      | (apply Prod.Lex.right; first | omega | (simp [List.length_cons]; done) | (simp [List.length_cons]; omega))

theorem sim_ir_lean_apply {n : Nat} (h : ApplyFunc fv [av] st n r) (hne : NoErr r)
    (hf : VCorr SIL fv fv') (hv : VCorr SIL av av') :
    ∃ r', LeanApply fv' av' st r' ∧ ResultCorr SIL r r' := by
  cases hf with
  | clo hclo hce =>
    obtain ⟨p, body, body', rfl, rfl, hb⟩ := hclo
    obtain ⟨bodyRes, heb, rfl⟩ := h.inv_closure
    have hfv : VCorr SIL (.closure _ none [p] body) (.leanClosure _ none p body') :=
      .clo ⟨_, _, _, rfl, rfl, hb⟩ hce
    obtain ⟨r1, e1, c1⟩ :=
      sim_ir_lean_expr heb (unwrapReturn_noErr hne) hb (hce.ofCall (.cons hv .nil) hfv [p] none)
    exact ⟨_, .apply_closure e1, c1.unwrapReturn⟩
  | _ => cases h <;> exact absurd hne id
  termination_by (n, 1)
  decreasing_by
    all_goals simp_wf
    all_goals subst_vars
    all_goals first
      | (apply Prod.Lex.left; omega)
      | (apply Prod.Lex.right; omega)

end

/-- **Forward simulation, IR → Lean.** -/
theorem sim_ir_to_lean_expr
    (htrans : IRToLeanExpr ir_e lean_e)
    (heval : Eval irenv store fuel ir_e result_ir)
    (hok : NoErr result_ir)
    (hcorr : EnvCorr SIL irenv leanenv) :
    ∃ result_lean, LeanEvalExpr leanenv store lean_e result_lean ∧
      ResultCorr SIL result_ir result_lean :=
  sim_ir_lean_expr heval hok htrans hcorr

end LeanJS.Semantics
