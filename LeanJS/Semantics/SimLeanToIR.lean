/-
  Forward simulation: Lean → IR preserves semantics (verified core).

  If a Lean expression evaluates to a non-error result, and it translates to
  IR, then under corresponding environments the IR expression evaluates
  (for some fuel) to a corresponding result.
-/
import LeanJS.Semantics.SimJSToIR

set_option autoImplicit true

namespace LeanJS.Semantics

open LeanJS.Lean
open LeanJS.IR

/-- A Lean closure corresponds to the one-parameter IR closure of its
    translated body -/
def LeanIRClo (v v' : IRValue) (e e' : Env) : Prop :=
  ∃ name p body body', v = .leanClosure e name p body ∧
    v' = .closure e' name [p] body' ∧ LeanToIRExpr body body'

def SLI : CorrSpec where
  uUnit := .unit
  uUndef := .undefined
  hUnit := .unit
  hUndef := .undefined
  Clo := LeanIRClo
  clo_src := by rintro _ _ _ _ ⟨_, _, _, _, rfl, _, _⟩; exact .lean
  clo_tgt := by rintro _ _ _ _ ⟨_, _, _, _, _, rfl, _⟩; exact .closure

theorem leanLit_vcorr (l : LeanLit) : VCorr S (leanLitToValue l) (irLitToValue (leanLitToIRLit l)) := by
  cases l <;> constructor

def LeanIRGoal : LeanJ → EvalResult → Prop
  | .expr env st e, r => ∀ e' ienv, LeanToIRExpr e e' → EnvCorr SLI env ienv →
      ∃ n r', Eval ienv st n e' r' ∧ ResultCorr SLI r r'
  | .fields env st fs acc, r => ∀ fs' ienv acc', LeanToIRFields fs fs' → EnvCorr SLI env ienv →
      FieldsCorr SLI acc acc' → ∃ n r', EvalFields ienv st n fs' acc' r' ∧ ResultCorr SLI r r'
  | .elems env st es acc, r => ∀ es' ienv acc', LeanToIRExprs es es' → EnvCorr SLI env ienv →
      ListCorr SLI acc acc' → ∃ n r', EvalElems ienv st n es' acc' r' ∧ ResultCorr SLI r r'
  | .apply fv av st, r => ∀ fv' av', VCorr SLI fv fv' → VCorr SLI av av' →
      ∃ n r', ApplyFunc fv' [av'] st n r' ∧ ResultCorr SLI r r'

set_option maxHeartbeats 3200000 in
theorem sim_lean_all (h : LeanSem j r) : NoErr r → LeanIRGoal j r := by
  induction h with
  | ident hl =>
    intro _ e' ienv ht hc
    cases ht
    obtain ⟨v', hl', hv⟩ := hc.lookup hl
    exact ⟨1, _, .var_ok hl', .val hv⟩
  | lit =>
    intro _ e' ienv ht hc
    cases ht
    exact ⟨1, _, .lit, .val (leanLit_vcorr _)⟩
  | unit =>
    intro _ e' ienv ht hc
    cases ht
    exact ⟨1, _, .lit, .val .unit⟩
  | paren _ ih =>
    intro hne e' ienv ht hc
    cases ht with
    | paren ht => exact ih hne _ _ ht hc
  | lam_one =>
    intro _ e' ienv ht hc
    cases ht with
    | lam_one hb => exact ⟨1, _, .lam rfl, .val (.clo ⟨_, _, _, _, rfl, rfl, hb⟩ hc)⟩
    | lam_cons hne _ => exact absurd rfl hne
  | lam_cons hps =>
    intro _ e' ienv ht hc
    cases ht with
    | lam_one hb => exact absurd rfl hps
    | lam_cons _ hb => exact ⟨1, _, .lam rfl, .val (.clo ⟨_, _, _, _, rfl, rfl, hb⟩ hc)⟩
  | app_ok _ _ _ ihf iha ihap =>
    intro hne e' ienv ht hc
    cases ht with
    | app htf hta =>
      obtain ⟨n1, r1, e1, c1⟩ := ihf trivial _ _ htf hc
      obtain ⟨fv', rfl, hfv⟩ := c1.inv_val
      obtain ⟨n2, r2, e2, c2⟩ := iha trivial _ _ hta hc
      obtain ⟨av', rfl, hav⟩ := c2.inv_val
      obtain ⟨n3, r3, e3, c3⟩ := ihap hne _ _ hfv hav
      exact ⟨max n1 (max n2 n3) + 1, _,
        .app_ok (e1.lift (.val hfv) (by omega))
          (.cons_ok (e2.lift (.val hav) (by omega)) .nil)
          (ApplyFunc.fuel_mono e3 (by omega) c3.noErr_right.nf), c3⟩
  | app_fn_signal _ hs ihf =>
    intro hne e' ienv ht hc
    cases ht with
    | app htf _ =>
      obtain ⟨n1, r1, e1, c1⟩ := ihf hne _ _ htf hc
      exact ⟨n1 + 1, _, .app_func_signal e1 (c1.signal hs), c1⟩
  | app_arg_signal _ _ hs ihf iha =>
    intro hne e' ienv ht hc
    cases ht with
    | app htf hta =>
      obtain ⟨n1, r1, e1, c1⟩ := ihf trivial _ _ htf hc
      obtain ⟨fv', rfl, hfv⟩ := c1.inv_val
      obtain ⟨n2, r2, e2, c2⟩ := iha hne _ _ hta hc
      exact ⟨max n1 n2 + 1, _,
        .app_args_signal (e1.lift (.val hfv) (by omega))
          (.cons_signal (e2.lift c2 (by omega)) (c2.signal hs)) (c2.signal hs), c2⟩
  | let_ok _ _ ihv ihb =>
    intro hne e' ienv ht hc
    cases ht with
    | let_ htv htb =>
      obtain ⟨n1, r1, e1, c1⟩ := ihv trivial _ _ htv hc
      obtain ⟨v', rfl, hv⟩ := c1.inv_val
      obtain ⟨n2, r2, e2, c2⟩ := ihb hne _ _ htb (.cons hv hc)
      exact ⟨max n1 n2 + 1, _, .let_ok (e1.lift (.val hv) (by omega)) (e2.lift c2 (by omega)), c2⟩
  | let_signal _ hs ihv =>
    intro hne e' ienv ht hc
    cases ht with
    | let_ htv _ =>
      obtain ⟨n1, r1, e1, c1⟩ := ihv hne _ _ htv hc
      exact ⟨n1 + 1, _, .let_signal e1 (c1.signal hs), c1⟩
  | if_true _ htr _ ihc ihb =>
    intro hne e' ienv ht hc
    cases ht with
    | if_ htc htt _ =>
      obtain ⟨n1, r1, e1, c1⟩ := ihc trivial _ _ htc hc
      obtain ⟨cv', rfl, hcv⟩ := c1.inv_val
      obtain ⟨n2, r2, e2, c2⟩ := ihb hne _ _ htt hc
      exact ⟨max n1 n2 + 1, _,
        .if_true (e1.lift (.val hcv) (by omega)) (hcv.truthy ▸ htr) (e2.lift c2 (by omega)), c2⟩
  | if_false _ htr _ ihc ihb =>
    intro hne e' ienv ht hc
    cases ht with
    | if_ htc _ hte =>
      obtain ⟨n1, r1, e1, c1⟩ := ihc trivial _ _ htc hc
      obtain ⟨cv', rfl, hcv⟩ := c1.inv_val
      obtain ⟨n2, r2, e2, c2⟩ := ihb hne _ _ hte hc
      exact ⟨max n1 n2 + 1, _,
        .if_false (e1.lift (.val hcv) (by omega)) (hcv.truthy ▸ htr) (e2.lift c2 (by omega)), c2⟩
  | if_signal _ hs ihc =>
    intro hne e' ienv ht hc
    cases ht with
    | if_ htc _ _ =>
      obtain ⟨n1, r1, e1, c1⟩ := ihc hne _ _ htc hc
      exact ⟨n1 + 1, _, .if_signal e1 (c1.signal hs), c1⟩
  | binOp_ok _ _ hop ihl ihr =>
    intro hne e' ienv ht hc
    cases ht with
    | binOp htl htr hop' =>
      rw [hop] at hop'; cases hop'
      obtain ⟨n1, r1, e1, c1⟩ := ihl trivial _ _ htl hc
      obtain ⟨lv', rfl, hlv⟩ := c1.inv_val
      obtain ⟨n2, r2, e2, c2⟩ := ihr trivial _ _ htr hc
      obtain ⟨rv', rfl, hrv⟩ := c2.inv_val
      exact ⟨max n1 n2 + 1, _,
        .binOp_ok (e1.lift (.val hlv) (by omega)) (e2.lift (.val hrv) (by omega)) rfl,
        evalBinOp_corr (.inl rfl) hlv hrv _ hne⟩
  | binOp_left_signal _ hs ihl =>
    intro hne e' ienv ht hc
    cases ht with
    | binOp htl _ _ =>
      obtain ⟨n1, r1, e1, c1⟩ := ihl hne _ _ htl hc
      exact ⟨n1 + 1, _, .binOp_left_signal e1 (c1.signal hs), c1⟩
  | binOp_right_signal _ _ hs ihl ihr =>
    intro hne e' ienv ht hc
    cases ht with
    | binOp htl htr _ =>
      obtain ⟨n1, r1, e1, c1⟩ := ihl trivial _ _ htl hc
      obtain ⟨lv', rfl, hlv⟩ := c1.inv_val
      obtain ⟨n2, r2, e2, c2⟩ := ihr hne _ _ htr hc
      exact ⟨max n1 n2 + 1, _,
        .binOp_right_signal (e1.lift (.val hlv) (by omega)) (e2.lift c2 (by omega))
          (c2.signal hs), c2⟩
  | unaryOp_ok _ hop iha =>
    intro hne e' ienv ht hc
    cases ht with
    | unaryOp hta hop' =>
      rw [hop] at hop'; cases hop'
      obtain ⟨n1, r1, e1, c1⟩ := iha trivial _ _ hta hc
      obtain ⟨v', rfl, hv⟩ := c1.inv_val
      exact ⟨n1 + 1, _, .unaryOp_ok e1 rfl, evalUnaryOp_corr _ hv _ hne⟩
  | unaryOp_signal _ hs iha =>
    intro hne e' ienv ht hc
    cases ht with
    | unaryOp hta _ =>
      obtain ⟨n1, r1, e1, c1⟩ := iha hne _ _ hta hc
      exact ⟨n1 + 1, _, .unaryOp_signal e1 (c1.signal hs), c1⟩
  | structLit _ ih =>
    intro hne e' ienv ht hc
    cases ht with
    | structLit htf =>
      obtain ⟨n1, r1, e1, c1⟩ := ih hne _ _ _ htf hc .nil
      exact ⟨n1 + 1, _, .record e1, c1⟩
  | arrayLit _ ih =>
    intro hne e' ienv ht hc
    cases ht with
    | arrayLit hte =>
      obtain ⟨n1, r1, e1, c1⟩ := ih hne _ _ _ hte hc .nil
      exact ⟨n1 + 1, _, .array e1, c1⟩
  | proj_ok _ hl ihe =>
    intro _ e' ienv ht hc
    cases ht with
    | proj hte =>
      obtain ⟨n1, r1, e1, c1⟩ := ihe trivial _ _ hte hc
      obtain ⟨rv', rfl, hrv⟩ := c1.inv_val
      obtain ⟨fs', rfl, hfs⟩ := hrv.inv_record
      rcases hfs.lookup _ with ⟨hn, _⟩ | ⟨v, v', hv, hv', hvv⟩
      · rw [hn] at hl; cases hl
      · rw [hv] at hl; cases hl
        exact ⟨n1 + 1, _, .project_record_ok e1 hv', .val hvv⟩
  | proj_signal _ hs ihe =>
    intro hne e' ienv ht hc
    cases ht with
    | proj hte =>
      obtain ⟨n1, r1, e1, c1⟩ := ihe hne _ _ hte hc
      exact ⟨n1 + 1, _, .project_signal e1 (c1.signal hs), c1⟩
  | throw_ok _ ihe =>
    intro _ e' ienv ht hc
    cases ht with
    | throw hte =>
      obtain ⟨n1, r1, e1, c1⟩ := ihe trivial _ _ hte hc
      obtain ⟨v', rfl, hv⟩ := c1.inv_val
      exact ⟨n1 + 1, _, .throw_ok e1, .throw hv⟩
  | throw_signal _ hs ihe =>
    intro hne e' ienv ht hc
    cases ht with
    | throw hte =>
      obtain ⟨n1, r1, e1, c1⟩ := ihe hne _ _ hte hc
      exact ⟨n1 + 1, _, .throw_signal e1 (c1.signal hs), c1⟩
  | fields_nil =>
    intro _ fs' ienv acc' ht hc ha
    cases ht
    exact ⟨0, _, .nil, .val (.record ha.reverse)⟩
  | fields_cons_ok _ _ ihe ihr =>
    intro hne fs' ienv acc' ht hc ha
    cases ht with
    | cons hte htr =>
      obtain ⟨n1, r1, e1, c1⟩ := ihe trivial _ _ hte hc
      obtain ⟨v', rfl, hv⟩ := c1.inv_val
      obtain ⟨n2, r2, e2, c2⟩ := ihr hne _ _ _ htr hc (.cons hv ha)
      exact ⟨max n1 n2, _,
        .cons_ok (e1.lift (.val hv) (by omega))
          (EvalFields.fuel_mono e2 (by omega) c2.noErr_right.nf), c2⟩
  | fields_cons_signal _ hs ihe =>
    intro hne fs' ienv acc' ht hc ha
    cases ht with
    | cons hte _ =>
      obtain ⟨n1, r1, e1, c1⟩ := ihe hne _ _ hte hc
      exact ⟨n1, _, .cons_signal e1 (c1.signal hs), c1⟩
  | elems_nil =>
    intro _ es' ienv acc' ht hc ha
    cases ht
    exact ⟨0, _, .nil, .val (.array ha.reverse)⟩
  | elems_cons_ok _ _ ihe ihr =>
    intro hne es' ienv acc' ht hc ha
    cases ht with
    | cons hte htr =>
      obtain ⟨n1, r1, e1, c1⟩ := ihe trivial _ _ hte hc
      obtain ⟨v', rfl, hv⟩ := c1.inv_val
      obtain ⟨n2, r2, e2, c2⟩ := ihr hne _ _ _ htr hc (.cons hv ha)
      exact ⟨max n1 n2, _,
        .cons_ok (e1.lift (.val hv) (by omega))
          (EvalElems.fuel_mono e2 (by omega) c2.noErr_right.nf), c2⟩
  | elems_cons_signal _ hs ihe =>
    intro hne es' ienv acc' ht hc ha
    cases ht with
    | cons hte _ =>
      obtain ⟨n1, r1, e1, c1⟩ := ihe hne _ _ hte hc
      exact ⟨n1, _, .cons_signal e1 (c1.signal hs), c1⟩
  | @apply_closure cenv name p av body st res _ ih =>
    intro hne fv' av' hf hav
    cases hf with
    | clo hclo hce =>
      obtain ⟨_, _, _, body', heq, rfl, hb⟩ := hclo
      cases heq
      have hfv : VCorr SLI _ (.closure _ name [p] body') := .clo ⟨_, _, _, _, rfl, rfl, hb⟩ hce
      obtain ⟨n1, r1, e1, c1⟩ :=
        ih (unwrapReturn_noErr hne) _ _ hb (hce.ofCall (.cons hav .nil) hfv [p] name)
      exact ⟨n1, _, .ofBody e1, c1.unwrapReturn⟩

/-- **Forward simulation, Lean → IR.** -/
theorem sim_lean_to_ir_expr
    (htrans : LeanToIRExpr lean_e ir_e)
    (heval : LeanEvalExpr leanenv store lean_e result_lean)
    (hok : NoErr result_lean)
    (hcorr : EnvCorr SLI leanenv irenv) :
    ∃ fuel result_ir, Eval irenv store fuel ir_e result_ir ∧
      ResultCorr SLI result_lean result_ir :=
  sim_lean_all heval hok _ _ htrans hcorr

end LeanJS.Semantics
