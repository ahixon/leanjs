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

/-- An IR closure with parameters `p :: qs` corresponds to the curried Lean
    closure for `p` whose body takes the remaining parameters. -/
def IRLeanClo (v v' : IRValue) (e e' : Env) : Prop :=
  ∃ p qs body body', v = .closure e none (p :: qs) body ∧
    v' = .leanClosure e' none p (leanTail qs body') ∧ IRToLeanExpr body body'

def SIL : CorrSpec where
  uUnit := .unit
  uUndef := .unit
  hUnit := .unit
  hUndef := .unit
  Clo := IRLeanClo
  clo_src := by rintro _ _ _ _ ⟨_, _, _, _, rfl, _, _⟩; exact .closure
  clo_tgt := by rintro _ _ _ _ ⟨_, _, _, _, _, rfl, _⟩; exact .lean

/-! ## Curried application in Lean -/

/-- Applying a Lean function value to several arguments, one at a time.
    Every application but the last returns a function value. -/
inductive LeanApplyMany : IRValue → List IRValue → Store → EvalResult → Prop where
  | one : LeanApply g v st r → LeanApplyMany g [v] st r
  | cons : LeanApply g v st (.val g' st') → LeanApplyMany g' (w :: ws) st' r →
      LeanApplyMany g (v :: w :: ws) st r

theorem lean_lam_eval (p : String) (qs : List String) (b : LeanExpr) :
    LeanEvalExpr env st (.lam (leanParamsOf (p :: qs)) b)
      (.val (.leanClosure env none p (leanTail qs b)) st) := by
  cases qs with
  | nil => exact .lam_one
  | cons q qs => exact .lam_cons (by simp [leanParamsOf])

/-- Applying a curried closure to its parameters one by one evaluates the
    body in the environment extended with all of them. -/
theorem lean_apply_curried (b : LeanExpr) :
    ∀ (p : String) (qs : List String) (cenv : Env) (vs : List IRValue) (st : Store) (r : EvalResult),
      vs.length = qs.length + 1 →
      LeanEvalExpr (cenv.extendMany ((p :: qs).zip vs)) st b r →
      LeanApplyMany (.leanClosure cenv none p (leanTail qs b)) vs st (unwrapReturn r)
  | p, [], cenv, [v], st, r, _, h => .one (.apply_closure h)
  | p, q :: qs, cenv, v :: w :: ws, st, r, hlen, h => by
    have hlam : LeanApply (.leanClosure cenv none p (leanTail (q :: qs) b)) v st
        (.val (.leanClosure (cenv.extend p v) none q (leanTail qs b)) st) :=
      .apply_closure (lean_lam_eval q qs b)
    refine .cons hlam ?_
    exact lean_apply_curried b q qs (cenv.extend p v) (w :: ws) st r
      (by simp at hlen ⊢; omega) h
  | _, [], _, [], _, _, hlen, _ => by simp at hlen
  | _, [], _, _ :: _ :: _, _, _, hlen, _ => by simp at hlen
  | _, _ :: _, _, [], _, _, hlen, _ => by simp at hlen
  | _, _ :: _, _, [_], _, _, hlen, _ => by simp at hlen

/-- Lean values of atoms: they evaluate in any store, without changing it -/
inductive LeanAtomVals (env : Env) : List LeanExpr → List IRValue → Prop where
  | nil : LeanAtomVals env [] []
  | cons : (∀ st, LeanEvalExpr env st e (.val v st)) → LeanAtomVals env es vs →
      LeanAtomVals env (e :: es) (v :: vs)

/-- The Lean application spine `((h a) e₁) … eₙ` with atoms `eᵢ` -/
theorem lean_spine (hat : LeanAtomVals lenv as' vs') :
    ∀ {H a g v s1 s2 r}, LeanEvalExpr lenv st H (.val g s1) →
      LeanEvalExpr lenv s1 a (.val v s2) →
      LeanApplyMany g (v :: vs') s2 r →
      LeanEvalExpr lenv st (as'.foldl .app (.app H a)) r := by
  induction hat with
  | nil =>
    intro H a g v s1 s2 r hH ha hap
    cases hap with
    | one hap => exact .app_ok hH ha hap
  | cons he _ ih =>
    intro H a g v s1 s2 r hH ha hap
    cases hap with
    | cons hap1 hrest => exact ih (.app_ok hH ha hap1) (he _) hrest

theorem lean_spine_signal (hs : isSignal r) :
    ∀ (es : List LeanExpr) {H : LeanExpr}, LeanEvalExpr lenv st H r →
      LeanEvalExpr lenv st (es.foldl .app H) r
  | [], _, h => h
  | _ :: es, _, h => lean_spine_signal hs es (.app_fn_signal h hs)

theorem irBinOpToLean_spec (h : irBinOpToLean op = some lop) : leanBinOpToIR lop = some op := by
  cases op <;> simp [irBinOpToLean] at h <;> subst h <;> rfl

theorem irUnaryOpToLean_spec (h : irUnaryOpToLean op = some lop) : leanUnaryOpToIR lop = some op := by
  cases op <;> simp [irUnaryOpToLean] at h <;> subst h <;> rfl

/-! ## Atoms -/

theorem atom_eval (ha : IsAtom e) (ht : IRToLeanExpr e e') (h : Eval ienv st n e (.val v s))
    (hc : EnvCorr SIL ienv lenv) :
    ∃ v', VCorr SIL v v' ∧ (∀ st', LeanEvalExpr lenv st' e' (.val v' st')) ∧ s = st := by
  cases ha with
  | var =>
    cases h with
    | var_ok hl =>
      cases ht
      obtain ⟨v', hl', hv⟩ := hc.lookup hl
      exact ⟨v', hv, fun _ => .ident hl', rfl⟩
  | lit =>
    cases h with
    | lit =>
      cases ht with
      | num => exact ⟨_, .number, fun _ => .lit, rfl⟩
      | str => exact ⟨_, .string, fun _ => .lit, rfl⟩
      | bool => exact ⟨_, .bool, fun _ => .lit, rfl⟩
      | unit => exact ⟨_, .unit, fun _ => .unit, rfl⟩
  | undef =>
    cases h with
    | undefined => cases ht; exact ⟨_, .undefined, fun _ => .unit, rfl⟩

theorem atom_no_signal (ha : IsAtom e) (h : Eval ienv st n e r) (hs : isSignal r) : ¬ NoErr r := by
  cases ha <;> cases h <;> simp_all [isSignal, NoErr]

/-- Evaluating atomic arguments: values, store unchanged, and the Lean
    atoms evaluate to corresponding values. -/
theorem EvalArgs.atoms (hc : EnvCorr SIL ienv lenv) :
    ∀ (as : List IRExpr) {as' st acc r}, IRToLeanAtoms as as' →
      EvalArgs ienv st n as acc r → NoErr r →
      ∃ vs vs', r = .val (.array (acc.reverse ++ vs)) st ∧ ListCorr SIL vs vs' ∧
        LeanAtomVals lenv as' vs' := by
  intro as
  induction as with
  | nil =>
    intro as' st acc r ht h _
    cases ht; cases h; exact ⟨[], [], by simp, .nil, .nil⟩
  | cons e es ih =>
    intro as' st acc r ht h hne
    cases ht with
    | cons hat hte hts =>
      cases h with
      | cons_ok he hrest =>
        obtain ⟨v', hv, hl, rfl⟩ := atom_eval hat hte he hc
        obtain ⟨vs, vs', rfl, hvs, hlv⟩ := ih hts hrest hne
        exact ⟨_ :: vs, v' :: vs', by simp, .cons hv hvs, .cons hl hlv⟩
      | cons_signal he hs => exact absurd hne (atom_no_signal hat he hs)

set_option maxHeartbeats 6400000 in
set_option maxRecDepth 8192 in
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
    | lam hb hps =>
      obtain ⟨⟨p, ty⟩, qs, rfl⟩ := List.exists_cons_of_ne_nil hps
      exact ⟨_, lean_lam_eval p (qs.map Prod.fst) _,
        .val (.clo ⟨p, _, _, _, rfl, rfl, hb⟩ hc)⟩
  | app_ok hf ha hap =>
    cases ht with
    | app htf hta hts =>
      obtain ⟨r1, e1, c1⟩ := sim_ir_lean_expr hf trivial htf hc
      obtain ⟨fv', rfl, hfv⟩ := c1.inv_val
      cases ha with
      | cons_ok ha1 hrest =>
        obtain ⟨r2, e2, c2⟩ := sim_ir_lean_expr ha1 trivial hta hc
        obtain ⟨v', rfl, hv⟩ := c2.inv_val
        obtain ⟨vs, vs', heq, hvs, hat⟩ := EvalArgs.atoms hc _ hts hrest trivial
        simp at heq
        obtain ⟨rfl, rfl⟩ := heq
        obtain ⟨r3, e3, c3⟩ := sim_ir_lean_apply hap hne hfv (.cons hv hvs)
        exact ⟨_, lean_spine hat e1 e2 e3, c3⟩
      | cons_signal _ hs => simp [isSignal] at hs
  | app_func_signal hf hs =>
    cases ht with
    | app htf _ _ =>
      obtain ⟨r1, e1, c1⟩ := sim_ir_lean_expr hf hne htf hc
      exact ⟨_, lean_spine_signal (c1.signal hs) _ (.app_fn_signal e1 (c1.signal hs)), c1⟩
  | app_args_signal hf ha hs =>
    cases ht with
    | app htf hta hts =>
      obtain ⟨r1, e1, c1⟩ := sim_ir_lean_expr hf trivial htf hc
      obtain ⟨fv', rfl, hfv⟩ := c1.inv_val
      cases ha with
      | cons_ok _ hrest =>
        obtain ⟨vs, vs', rfl, _, _⟩ := EvalArgs.atoms hc _ hts hrest hne
        simp [isSignal] at hs
      | cons_signal ha1 _ =>
        obtain ⟨r2, e2, c2⟩ := sim_ir_lean_expr ha1 hne hta hc
        exact ⟨_, lean_spine_signal (c2.signal hs) _ (.app_arg_signal e1 e2 (c2.signal hs)), c2⟩
  | binOp_ok hl hn hr hres =>
    subst hres
    cases ht with
    | binOp htl htr hop =>
      obtain ⟨r1, e1, c1⟩ := sim_ir_lean_expr hl trivial htl hc
      obtain ⟨lv', rfl, hlv⟩ := c1.inv_val
      obtain ⟨r2, e2, c2⟩ := sim_ir_lean_expr hr trivial htr hc
      obtain ⟨rv', rfl, hrv⟩ := c2.inv_val
      exact ⟨_, .binOp_ok e1 (irBinOpToLean_spec hop) (hlv.needsRight_tgt (.inl rfl) hn) e2,
        evalBinOp_corr (.inl rfl) hlv hrv _ hne⟩
  | binOp_short hl hn =>
    cases ht with
    | binOp htl htr hop =>
      obtain ⟨r1, e1, c1⟩ := sim_ir_lean_expr hl trivial htl hc
      obtain ⟨lv', rfl, hlv⟩ := c1.inv_val
      exact ⟨_, .binOp_short e1 (irBinOpToLean_spec hop) (hlv.needsRight_tgt (.inl rfl) hn),
        .val hlv⟩
  | binOp_left_signal hl hs =>
    cases ht with
    | binOp htl _ _ =>
      obtain ⟨r1, e1, c1⟩ := sim_ir_lean_expr hl hne htl hc
      exact ⟨_, .binOp_left_signal e1 (c1.signal hs), c1⟩
  | binOp_right_signal hl hn hr hs =>
    cases ht with
    | @binOp _ _ _ _ _ lop htl htr hop =>
      obtain ⟨r1, e1, c1⟩ := sim_ir_lean_expr hl trivial htl hc
      obtain ⟨lv', rfl, hlv⟩ := c1.inv_val
      obtain ⟨r2, e2, c2⟩ := sim_ir_lean_expr hr hne htr hc
      have hn' : optNeedsRight (leanBinOpToIR lop) lv' = true := by
        rw [irBinOpToLean_spec hop]; exact hlv.needsRight_tgt (.inl rfl) hn
      exact ⟨_, .binOp_right_signal e1 hn' e2 (c2.signal hs), c2⟩
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

theorem sim_ir_lean_apply {n : Nat} (h : ApplyFunc fv vs st n r) (hne : NoErr r)
    (hf : VCorr SIL fv fv') (hv : ListCorr SIL vs vs') :
    ∃ r', LeanApplyMany fv' vs' st r' ∧ ResultCorr SIL r r' := by
  cases hf with
  | clo hclo hce =>
    obtain ⟨p, qs, body, body', rfl, rfl, hb⟩ := hclo
    obtain ⟨hlen, bodyRes, heb, rfl⟩ := h.inv_closure hne
    have hfv : VCorr SIL (.closure _ none (p :: qs) body)
        (.leanClosure _ none p (leanTail qs body')) :=
      .clo ⟨_, _, _, _, rfl, rfl, hb⟩ hce
    obtain ⟨r1, e1, c1⟩ :=
      sim_ir_lean_expr heb (unwrapReturn_noErr hne) hb (hce.ofCall hv hfv (p :: qs) none)
    have hlen' : vs'.length = qs.length + 1 := by
      have := hv.length_eq; simp at hlen; omega
    exact ⟨_, lean_apply_curried body' p qs _ vs' st r1 hlen' e1, c1.unwrapReturn⟩
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
