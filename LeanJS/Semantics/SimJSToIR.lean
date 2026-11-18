/-
  Forward simulation: JS → IR preserves semantics (verified core).

  If a JS expression (statement list) evaluates to a result `r` that is not a
  runtime error, and it translates to IR, then for any IR environment that
  corresponds to the JS environment, the IR program evaluates (for some fuel)
  to a corresponding result. Expressions produce `ResultCorr` results;
  statement lists produce `StmtCorr` results (statement completion values
  are not observable in JS, so only signals and the store must agree).
-/
import LeanJS.Semantics.EnvCorr
import LeanJS.Semantics.TransRel
import LeanJS.Semantics.FuelMono

set_option autoImplicit true

namespace LeanJS.Semantics

open LeanJS.JS
open LeanJS.IR

/-! ## Shared helpers for all simulation proofs -/

theorem NoErr.nf {r : EvalResult} (h : NoErr r) : notFuelError r := by
  cases r <;> simp_all [NoErr, notFuelError]

theorem isSignal_noErr_val : ¬ isSignal (.val v s) := by simp [isSignal]

theorem VCorr.inv_array (h : VCorr S (.array vs) v') : ∃ vs', v' = .array vs' ∧ ListCorr S vs vs' := by
  cases h with
  | array h => exact ⟨_, rfl, h⟩
  | clo hc _ => cases S.clo_src hc

theorem VCorr.inv_record (h : VCorr S (.record fs) v') :
    ∃ fs', v' = .record fs' ∧ FieldsCorr S fs fs' := by
  cases h with
  | record h => exact ⟨_, rfl, h⟩
  | clo hc _ => cases S.clo_src hc

theorem ResultCorr.inv_val (h : ResultCorr S (.val v s) r') : ∃ v', r' = .val v' s ∧ VCorr S v v' := by
  cases h with
  | val h => exact ⟨_, rfl, h⟩

theorem anyParams_fst (names : List String) : (anyParams names).map Prod.fst = names := by
  induction names <;> simp_all [anyParams]

/-- IR's closure-call environment is our `callEnv` -/
theorem irCallEnv_eq (cenv : Env) (name : Option String) (ps : List String)
    (args : List IRValue) (body : IRExpr) :
    (match name with
      | some n => (cenv.extendMany (ps.zip args)).extend n (.closure cenv name ps body)
      | none => cenv.extendMany (ps.zip args)) =
    callEnv cenv name ps args (.closure cenv name ps body) := by
  cases name <;> rfl

theorem unwrapReturn_eq_match (r : EvalResult) :
    (match r with | .return_ v s => .val v s | other => other) = unwrapReturn r := by
  cases r <;> rfl

/-- Build an IR closure application from a body derivation in `callEnv` -/
theorem ApplyFunc.ofBody (h : Eval (callEnv cenv name ps args (.closure cenv name ps body)) st n body r) :
    ApplyFunc (.closure cenv name ps body) args st n (unwrapReturn r) := by
  refine .closure_ok rfl rfl ?_ (unwrapReturn_eq_match r).symm
  cases name <;> exact h

theorem unwrapBlockResult_signal (h : isSignal r) : unwrapBlockResult r = unwrapReturn r := by
  cases r <;> simp_all [isSignal, unwrapBlockResult, unwrapReturn]

/-- Lift an IR derivation to more fuel (results here never are fuel errors) -/
theorem Eval.lift (h : Eval env st n e r) (hc : ResultCorr S r0 r) (hle : n ≤ m) :
    Eval env st m e r := Eval.fuel_mono h hle hc.noErr_right.nf

/-! ## Statement-level result correspondence -/

/-- Statement results: normal completions correspond regardless of value;
    signals correspond as results. -/
inductive StmtCorr (S : CorrSpec) : EvalResult → EvalResult → Prop where
  | val : StmtCorr S (.val v s) (.val v' s)
  | sig : ResultCorr S r r' → isSignal r → StmtCorr S r r'

theorem StmtCorr.noErr_right (h : StmtCorr S r r') : NoErr r' := by
  cases h with
  | val => trivial
  | sig h _ => exact h.noErr_right

theorem StmtCorr.signal (h : StmtCorr S r r') (hs : isSignal r) : isSignal r' := by
  cases h with
  | val => simp [isSignal] at hs
  | sig h _ => exact h.signal hs

/-! ## The JS → IR correspondence -/

/-- JS function bodies and their IR translations -/
inductive JSToIRFun : ExprOrBlock → IRExpr → Prop where
  | expr : JSToIRExpr e e' → JSToIRFun (.expr e) e'
  | block : JSToIRFunBody ss b → JSToIRFun (.block ss) b

/-- A JS closure corresponds to the IR closure of its translated body -/
def JSIRClo (v v' : IRValue) (e e' : Env) : Prop :=
  ∃ name names body body', v = .jsClosure e name names body ∧
    v' = .closure e' name names body' ∧ JSToIRFun body body'

def SJI : CorrSpec where
  uUnit := .unit
  uUndef := .undefined
  hUnit := .unit
  hUndef := .undefined
  Clo := JSIRClo
  clo_src := by rintro _ _ _ _ ⟨_, _, _, _, rfl, _, _⟩; exact .js
  clo_tgt := by rintro _ _ _ _ ⟨_, _, _, _, _, rfl, _⟩; exact .closure

theorem StmtCorr.lift (h : Eval env st n e r) (hc : StmtCorr S r0 r) (hle : n ≤ m) :
    Eval env st m e r := Eval.fuel_mono h hle hc.noErr_right.nf

/-! ## Simulation -/

/-- What the simulation guarantees for each JS judgment form -/
def JSIRGoal : JSJ → EvalResult → Prop
  | .expr env st e, r => ∀ e' ienv, JSToIRExpr e e' → EnvCorr SJI env ienv →
      ∃ n r', Eval ienv st n e' r' ∧ ResultCorr SJI r r'
  | .args env st es acc, r => ∀ es' ienv acc', JSToIRExprs es es' → EnvCorr SJI env ienv →
      ListCorr SJI acc acc' → ∃ n r', EvalArgs ienv st n es' acc' r' ∧ ResultCorr SJI r r'
  | .elems env st es acc, r => ∀ es' ienv acc', JSToIRElems es es' → EnvCorr SJI env ienv →
      ListCorr SJI acc acc' → ∃ n r', EvalElems ienv st n es' acc' r' ∧ ResultCorr SJI r r'
  | .props env st ps acc, r => ∀ fs ienv acc', JSToIRProps ps fs → EnvCorr SJI env ienv →
      FieldsCorr SJI acc acc' → ∃ n r', EvalFields ienv st n fs acc' r' ∧ ResultCorr SJI r r'
  | .apply fv vs st, r => ∀ fv' vs', VCorr SJI fv fv' → ListCorr SJI vs vs' →
      ∃ n r', ApplyFunc fv' vs' st n r' ∧ ResultCorr SJI r r'
  | .stmt env st s, r => ∀ s' ienv, JSToIRStmt s s' → EnvCorr SJI env ienv →
      ∃ n r', Eval ienv st n s' r' ∧ StmtCorr SJI r r'
  | .stmts env st ss, r => ∀ ir ienv, JSToIRStmts ss ir → EnvCorr SJI env ienv →
      ∃ n r', Eval ienv st n ir r' ∧ StmtCorr SJI r r'

set_option maxHeartbeats 3200000 in
theorem sim_js_all (h : JSSem j r) : NoErr r → JSIRGoal j r := by
  induction h with
  | ident hl =>
    intro _ e' ienv ht hc
    cases ht
    obtain ⟨v', hl', hv⟩ := hc.lookup hl
    exact ⟨1, _, .var_ok hl', .val hv⟩
  | literal hl =>
    intro _ e' ienv ht hc
    cases ht <;> simp [jsLitToValue] at hl <;> subst hl
    · exact ⟨1, _, .lit, .val .string⟩
    · exact ⟨1, _, .lit, .val .number⟩
    · exact ⟨1, _, .lit, .val .bool⟩
    · exact ⟨1, _, .undefined, .val .undefined⟩
    · exact ⟨1, _, .undefined, .val .undefined⟩
  | paren _ ih =>
    intro hne e' ienv ht hc
    cases ht with
    | paren ht => exact ih hne _ _ ht hc
  | binary_ok _ _ hop ihl ihr =>
    intro hne e' ienv ht hc
    cases ht with
    | binary htl htr hop' =>
      rw [hop] at hop'; cases hop'
      obtain ⟨n1, r1, e1, c1⟩ := ihl trivial _ _ htl hc
      obtain ⟨lv', rfl, hlv⟩ := c1.inv_val
      obtain ⟨n2, r2, e2, c2⟩ := ihr trivial _ _ htr hc
      obtain ⟨rv', rfl, hrv⟩ := c2.inv_val
      exact ⟨max n1 n2 + 1, _,
        .binOp_ok (e1.lift (.val hlv) (by omega)) (e2.lift (.val hrv) (by omega)) rfl,
        evalBinOp_corr (.inl rfl) hlv hrv _ hne⟩
  | binary_left_signal _ hs ihl =>
    intro hne e' ienv ht hc
    cases ht with
    | binary htl htr hop' =>
      obtain ⟨n1, r1, e1, c1⟩ := ihl hne _ _ htl hc
      exact ⟨n1 + 1, _, .binOp_left_signal e1 (c1.signal hs), c1⟩
  | binary_right_signal _ _ hs ihl ihr =>
    intro hne e' ienv ht hc
    cases ht with
    | binary htl htr hop' =>
      obtain ⟨n1, r1, e1, c1⟩ := ihl trivial _ _ htl hc
      obtain ⟨lv', rfl, hlv⟩ := c1.inv_val
      obtain ⟨n2, r2, e2, c2⟩ := ihr hne _ _ htr hc
      exact ⟨max n1 n2 + 1, _,
        .binOp_right_signal (e1.lift (.val hlv) (by omega)) (e2.lift c2 (by omega))
          (c2.signal hs), c2⟩
  | unary_ok _ hop iha =>
    intro hne e' ienv ht hc
    cases ht with
    | unary hta hop' =>
      rw [hop] at hop'; cases hop'
      obtain ⟨n1, r1, e1, c1⟩ := iha trivial _ _ hta hc
      obtain ⟨v', rfl, hv⟩ := c1.inv_val
      exact ⟨n1 + 1, _, .unaryOp_ok e1 rfl, evalUnaryOp_corr _ hv _ hne⟩
  | unary_signal _ hs iha =>
    intro hne e' ienv ht hc
    cases ht with
    | unary hta _ =>
      obtain ⟨n1, r1, e1, c1⟩ := iha hne _ _ hta hc
      exact ⟨n1 + 1, _, .unaryOp_signal e1 (c1.signal hs), c1⟩
  | cond_true _ htr _ ihc ihb =>
    intro hne e' ienv ht hc
    cases ht with
    | cond htc htt hte =>
      obtain ⟨n1, r1, e1, c1⟩ := ihc trivial _ _ htc hc
      obtain ⟨cv', rfl, hcv⟩ := c1.inv_val
      obtain ⟨n2, r2, e2, c2⟩ := ihb hne _ _ htt hc
      exact ⟨max n1 n2 + 1, _,
        .if_true (e1.lift (.val hcv) (by omega)) (hcv.truthy ▸ htr) (e2.lift c2 (by omega)), c2⟩
  | cond_false _ htr _ ihc ihb =>
    intro hne e' ienv ht hc
    cases ht with
    | cond htc htt hte =>
      obtain ⟨n1, r1, e1, c1⟩ := ihc trivial _ _ htc hc
      obtain ⟨cv', rfl, hcv⟩ := c1.inv_val
      obtain ⟨n2, r2, e2, c2⟩ := ihb hne _ _ hte hc
      exact ⟨max n1 n2 + 1, _,
        .if_false (e1.lift (.val hcv) (by omega)) (hcv.truthy ▸ htr) (e2.lift c2 (by omega)), c2⟩
  | cond_signal _ hs ihc =>
    intro hne e' ienv ht hc
    cases ht with
    | cond htc _ _ =>
      obtain ⟨n1, r1, e1, c1⟩ := ihc hne _ _ htc hc
      exact ⟨n1 + 1, _, .if_signal e1 (c1.signal hs), c1⟩
  | call_ok _ _ _ ihf iha ihap =>
    intro hne e' ienv ht hc
    cases ht with
    | call htf hta =>
      obtain ⟨n1, r1, e1, c1⟩ := ihf trivial _ _ htf hc
      obtain ⟨fv', rfl, hfv⟩ := c1.inv_val
      obtain ⟨n2, r2, e2, c2⟩ := iha trivial _ _ _ hta hc .nil
      obtain ⟨av', rfl, hav⟩ := c2.inv_val
      obtain ⟨vs', rfl, hvs⟩ := hav.inv_array
      obtain ⟨n3, r3, e3, c3⟩ := ihap hne _ _ hfv hvs
      exact ⟨max n1 (max n2 n3) + 1, _,
        .app_ok (e1.lift (.val hfv) (by omega))
          (EvalArgs.fuel_mono e2 (by omega) trivial)
          (ApplyFunc.fuel_mono e3 (by omega) c3.noErr_right.nf), c3⟩
  | call_callee_signal _ hs ihf =>
    intro hne e' ienv ht hc
    cases ht with
    | call htf _ =>
      obtain ⟨n1, r1, e1, c1⟩ := ihf hne _ _ htf hc
      exact ⟨n1 + 1, _, .app_func_signal e1 (c1.signal hs), c1⟩
  | call_args_signal _ _ hs ihf iha =>
    intro hne e' ienv ht hc
    cases ht with
    | call htf hta =>
      obtain ⟨n1, r1, e1, c1⟩ := ihf trivial _ _ htf hc
      obtain ⟨fv', rfl, hfv⟩ := c1.inv_val
      obtain ⟨n2, r2, e2, c2⟩ := iha hne _ _ _ hta hc .nil
      exact ⟨max n1 n2 + 1, _,
        .app_args_signal (e1.lift (.val hfv) (by omega))
          (EvalArgs.fuel_mono e2 (by omega) c2.noErr_right.nf) (c2.signal hs), c2⟩
  | function hp =>
    intro _ e' ienv ht hc
    cases ht with
    | function hp' hb =>
      rw [hp] at hp'; cases hp'
      exact ⟨1, _, .lam (anyParams_fst _).symm,
        .val (.clo ⟨_, _, _, _, rfl, rfl, .block hb⟩ hc)⟩
  | arrow hp =>
    intro _ e' ienv ht hc
    cases ht with
    | arrow_expr hp' hb =>
      rw [hp] at hp'; cases hp'
      exact ⟨1, _, .lam (anyParams_fst _).symm,
        .val (.clo ⟨_, _, _, _, rfl, rfl, .expr hb⟩ hc)⟩
    | arrow_block hp' hb =>
      rw [hp] at hp'; cases hp'
      exact ⟨1, _, .lam (anyParams_fst _).symm,
        .val (.clo ⟨_, _, _, _, rfl, rfl, .block hb⟩ hc)⟩
  | array _ ih =>
    intro hne e' ienv ht hc
    cases ht with
    | array hte =>
      obtain ⟨n1, r1, e1, c1⟩ := ih hne _ _ _ hte hc .nil
      exact ⟨n1 + 1, _, .array e1, c1⟩
  | object _ ih =>
    intro hne e' ienv ht hc
    cases ht with
    | object htp =>
      obtain ⟨n1, r1, e1, c1⟩ := ih hne _ _ _ htp hc .nil
      exact ⟨n1 + 1, _, .record e1, c1⟩
  | member_ok => intro _ e' ienv ht; cases ht
  | member_missing => intro _ e' ienv ht; cases ht
  | member_signal => intro _ e' ienv ht; cases ht
  -- arguments
  | args_nil =>
    intro _ es' ienv acc' ht hc ha
    cases ht
    exact ⟨0, _, .nil, .val (.array ha.reverse)⟩
  | args_cons_ok _ _ ihe ihr =>
    intro hne es' ienv acc' ht hc ha
    cases ht with
    | cons hte htr =>
      obtain ⟨n1, r1, e1, c1⟩ := ihe trivial _ _ hte hc
      obtain ⟨v', rfl, hv⟩ := c1.inv_val
      obtain ⟨n2, r2, e2, c2⟩ := ihr hne _ _ _ htr hc (.cons hv ha)
      exact ⟨max n1 n2, _,
        .cons_ok (e1.lift (.val hv) (by omega))
          (EvalArgs.fuel_mono e2 (by omega) c2.noErr_right.nf), c2⟩
  | args_cons_signal _ hs ihe =>
    intro hne es' ienv acc' ht hc ha
    cases ht with
    | cons hte _ =>
      obtain ⟨n1, r1, e1, c1⟩ := ihe hne _ _ hte hc
      exact ⟨n1, _, .cons_signal e1 (c1.signal hs), c1⟩
  -- array elements
  | elems_nil =>
    intro _ es' ienv acc' ht hc ha
    cases ht
    exact ⟨0, _, .nil, .val (.array ha.reverse)⟩
  | elems_some_ok _ _ ihe ihr =>
    intro hne es' ienv acc' ht hc ha
    cases ht with
    | some hte htr =>
      obtain ⟨n1, r1, e1, c1⟩ := ihe trivial _ _ hte hc
      obtain ⟨v', rfl, hv⟩ := c1.inv_val
      obtain ⟨n2, r2, e2, c2⟩ := ihr hne _ _ _ htr hc (.cons hv ha)
      exact ⟨max n1 n2, _,
        .cons_ok (e1.lift (.val hv) (by omega))
          (EvalElems.fuel_mono e2 (by omega) c2.noErr_right.nf), c2⟩
  | elems_some_signal _ hs ihe =>
    intro hne es' ienv acc' ht hc ha
    cases ht with
    | some hte _ =>
      obtain ⟨n1, r1, e1, c1⟩ := ihe hne _ _ hte hc
      exact ⟨n1, _, .cons_signal e1 (c1.signal hs), c1⟩
  | elems_hole _ ihr =>
    intro hne es' ienv acc' ht hc ha
    cases ht with
    | hole htr =>
      obtain ⟨n2, r2, e2, c2⟩ := ihr hne _ _ _ htr hc (.cons (S := SJI) .undefined ha)
      exact ⟨n2 + 1, _,
        .cons_ok .undefined (EvalElems.fuel_mono e2 (by omega) c2.noErr_right.nf), c2⟩
  -- object properties
  | props_nil =>
    intro _ fs ienv acc' ht hc ha
    cases ht
    exact ⟨0, _, .nil, .val (.record ha.reverse)⟩
  | props_cons_ok _ _ ihe ihr =>
    intro hne fs ienv acc' ht hc ha
    cases ht with
    | cons hte htr =>
      obtain ⟨n1, r1, e1, c1⟩ := ihe trivial _ _ hte hc
      obtain ⟨v', rfl, hv⟩ := c1.inv_val
      obtain ⟨n2, r2, e2, c2⟩ := ihr hne _ _ _ htr hc (.cons hv ha)
      exact ⟨max n1 n2, _,
        .cons_ok (e1.lift (.val hv) (by omega))
          (EvalFields.fuel_mono e2 (by omega) c2.noErr_right.nf), c2⟩
  | props_cons_signal _ hs ihe =>
    intro hne fs ienv acc' ht hc ha
    cases ht with
    | cons hte _ =>
      obtain ⟨n1, r1, e1, c1⟩ := ihe hne _ _ hte hc
      exact ⟨n1, _, .cons_signal e1 (c1.signal hs), c1⟩
  -- function application
  | @apply_expr_body cenv name params args e st res _ ih =>
    intro hne fv' vs' hf hv
    cases hf with
    | clo hclo hce =>
      obtain ⟨_, _, _, body', heq, rfl, hfun⟩ := hclo
      cases heq
      cases hfun with
      | expr hte =>
        have hfv : VCorr SJI _ (.closure _ name params body') :=
          .clo ⟨_, _, _, _, rfl, rfl, .expr hte⟩ hce
        obtain ⟨n1, r1, e1, c1⟩ :=
          ih (unwrapReturn_noErr hne) _ _ hte (hce.ofCall hv hfv params name)
        exact ⟨n1, _, .ofBody e1, c1.unwrapReturn⟩
  | @apply_block_body cenv name params args ss st res hb ih =>
    intro hne fv' vs' hf hv
    cases hf with
    | clo hclo hce =>
      obtain ⟨_, _, _, body', heq, rfl, hfun⟩ := hclo
      cases heq
      cases hfun with
      | block hfb =>
        have hfv : VCorr SJI _ (.closure _ name params body') :=
          .clo ⟨_, _, _, _, rfl, rfl, .block hfb⟩ hce
        have hce' := hce.ofCall hv hfv params name
        cases hfb with
        | ret hte =>
          -- the body is `[return e]`; view it as a statement list
          have hts : JSToIRStmts [.return_ (some _)] (.«return» _) := .last rfl (.return_some hte)
          obtain ⟨n1, r1, e1, c1⟩ := ih (unwrapBlockResult_noErr hne) _ _ hts hce'
          cases e1 with
          | fuel_zero => exact absurd c1.noErr_right id
          | return_ok he' =>
            cases c1 with
            | sig c1 _ =>
              cases c1 with
              | ret hv' => exact ⟨_, _, .ofBody he', .val hv'⟩
          | return_signal he' hs' =>
            cases c1 with
            | val => simp [isSignal] at hs'
            | sig c1 hs =>
              refine ⟨_, _, .ofBody he', ?_⟩
              rw [unwrapBlockResult_signal hs]; exact c1.unwrapReturn
        | general hts =>
          obtain ⟨n1, r1, e1, c1⟩ := ih (unwrapBlockResult_noErr hne) _ _ hts hce'
          cases c1 with
          | val =>
            exact ⟨n1 + 2, _, .ofBody (.seq (.cons_ok (Eval.fuel_mono e1 (by omega) trivial)
                (.singleton .undefined) (by simp))), .val .undefined⟩
          | sig c1 hs =>
            refine ⟨n1 + 1, _, .ofBody (.seq (.cons_signal e1 (c1.signal hs) (by simp))), ?_⟩
            rw [unwrapBlockResult_signal hs]; exact c1.unwrapReturn
  -- single statements
  | stmt_expr _ ih =>
    intro hne s' ienv ht hc
    cases ht with
    | expr hte =>
      obtain ⟨n1, r1, e1, c1⟩ := ih hne _ _ hte hc
      refine ⟨n1, _, e1, ?_⟩
      cases c1 with
      | val => exact .val
      | ret h => exact .sig (.ret h) trivial
      | throw h => exact .sig (.throw h) trivial
      | brk => exact .sig .brk trivial
      | cont => exact .sig .cont trivial
  | stmt_block _ ih =>
    intro hne s' ienv ht hc
    cases ht with
    | block htb => exact ih hne _ _ htb hc
  | stmt_empty =>
    intro _ s' ienv ht hc
    cases ht
    exact ⟨1, _, .undefined, .val⟩
  | stmt_return_some _ ih =>
    intro _ s' ienv ht hc
    cases ht with
    | return_some hte =>
      obtain ⟨n1, r1, e1, c1⟩ := ih trivial _ _ hte hc
      obtain ⟨v', rfl, hv⟩ := c1.inv_val
      exact ⟨n1 + 1, _, .return_ok e1, .sig (.ret hv) trivial⟩
  | stmt_return_some_signal _ hs ih =>
    intro hne s' ienv ht hc
    cases ht with
    | return_some hte =>
      obtain ⟨n1, r1, e1, c1⟩ := ih hne _ _ hte hc
      exact ⟨n1 + 1, _, .return_signal e1 (c1.signal hs), .sig c1 hs⟩
  | stmt_return_none =>
    intro _ s' ienv ht hc
    cases ht
    exact ⟨2, _, .return_ok .undefined, .sig (.ret .undefined) trivial⟩
  | stmt_throw_ok _ ih =>
    intro _ s' ienv ht hc
    cases ht with
    | throw hte =>
      obtain ⟨n1, r1, e1, c1⟩ := ih trivial _ _ hte hc
      obtain ⟨v', rfl, hv⟩ := c1.inv_val
      exact ⟨n1 + 1, _, .throw_ok e1, .sig (.throw hv) trivial⟩
  | stmt_throw_signal _ hs ih =>
    intro hne s' ienv ht hc
    cases ht with
    | throw hte =>
      obtain ⟨n1, r1, e1, c1⟩ := ih hne _ _ hte hc
      exact ⟨n1 + 1, _, .throw_signal e1 (c1.signal hs), .sig c1 hs⟩
  | stmt_if_true _ htr _ ihc ihb =>
    intro hne s' ienv ht hc
    cases ht with
    | if_else htc htt _ =>
      obtain ⟨n1, r1, e1, c1⟩ := ihc trivial _ _ htc hc
      obtain ⟨cv', rfl, hcv⟩ := c1.inv_val
      obtain ⟨n2, r2, e2, c2⟩ := ihb hne _ _ htt hc
      exact ⟨max n1 n2 + 1, _,
        .if_true (e1.lift (.val hcv) (by omega)) (hcv.truthy ▸ htr) (c2.lift e2 (by omega)), c2⟩
    | if_noelse htc htt =>
      obtain ⟨n1, r1, e1, c1⟩ := ihc trivial _ _ htc hc
      obtain ⟨cv', rfl, hcv⟩ := c1.inv_val
      obtain ⟨n2, r2, e2, c2⟩ := ihb hne _ _ htt hc
      exact ⟨max n1 n2 + 1, _,
        .if_true (e1.lift (.val hcv) (by omega)) (hcv.truthy ▸ htr) (c2.lift e2 (by omega)), c2⟩
  | stmt_if_false _ htr _ ihc ihb =>
    intro hne s' ienv ht hc
    cases ht with
    | if_else htc _ hte =>
      obtain ⟨n1, r1, e1, c1⟩ := ihc trivial _ _ htc hc
      obtain ⟨cv', rfl, hcv⟩ := c1.inv_val
      obtain ⟨n2, r2, e2, c2⟩ := ihb hne _ _ hte hc
      exact ⟨max n1 n2 + 1, _,
        .if_false (e1.lift (.val hcv) (by omega)) (hcv.truthy ▸ htr) (c2.lift e2 (by omega)), c2⟩
  | stmt_if_false_none _ htr ihc =>
    intro _ s' ienv ht hc
    cases ht with
    | if_noelse htc _ =>
      obtain ⟨n1, r1, e1, c1⟩ := ihc trivial _ _ htc hc
      obtain ⟨cv', rfl, hcv⟩ := c1.inv_val
      exact ⟨n1 + 2, _,
        .if_false (e1.lift (.val hcv) (by omega)) (hcv.truthy ▸ htr) .undefined, .val⟩
  | stmt_if_signal _ hs ihc =>
    intro hne s' ienv ht hc
    cases ht with
    | if_else htc _ _ =>
      obtain ⟨n1, r1, e1, c1⟩ := ihc hne _ _ htc hc
      exact ⟨n1 + 1, _, .if_signal e1 (c1.signal hs), .sig c1 hs⟩
    | if_noelse htc _ =>
      obtain ⟨n1, r1, e1, c1⟩ := ihc hne _ _ htc hc
      exact ⟨n1 + 1, _, .if_signal e1 (c1.signal hs), .sig c1 hs⟩
  -- statement lists
  | stmts_nil =>
    intro _ ir ienv ht hc
    cases ht with
    | nil => exact ⟨1, _, .undefined, .val⟩
  | stmts_decl_ok _ _ _ ihi ihr =>
    intro hne ir ienv ht hc
    cases ht with
    | decl _ hti htr =>
      obtain ⟨n1, r1, e1, c1⟩ := ihi trivial _ _ hti hc
      obtain ⟨v', rfl, hv⟩ := c1.inv_val
      obtain ⟨n2, r2, e2, c2⟩ := ihr hne _ _ htr (.cons hv hc)
      exact ⟨max n1 n2 + 1, _, .let_ok (e1.lift (.val hv) (by omega)) (c2.lift e2 (by omega)), c2⟩
    | last hd _ => simp [Stmt.isDecl] at hd
    | cons hd _ _ _ => simp [Stmt.isDecl] at hd
  | stmts_decl_signal _ _ hs ihi =>
    intro hne ir ienv ht hc
    cases ht with
    | decl _ hti _ =>
      obtain ⟨n1, r1, e1, c1⟩ := ihi hne _ _ hti hc
      exact ⟨n1 + 1, _, .let_signal e1 (c1.signal hs), .sig c1 hs⟩
    | last hd _ => simp [Stmt.isDecl] at hd
    | cons hd _ _ _ => simp [Stmt.isDecl] at hd
  | stmts_funcDecl hp _ ihr =>
    intro hne ir ienv ht hc
    cases ht with
    | funcDecl hp' hb htr =>
      rw [hp] at hp'; cases hp'
      obtain ⟨n2, r2, e2, c2⟩ := ihr hne _ _ htr
        (.cons (.clo ⟨_, _, _, _, rfl, rfl, .block hb⟩ hc) hc)
      exact ⟨n2 + 2, _, .let_ok (.lam (anyParams_fst _).symm) (c2.lift e2 (by omega)), c2⟩
    | last hd _ => simp [Stmt.isDecl] at hd
    | cons hd _ _ _ => simp [Stmt.isDecl] at hd
  | stmts_stmt_ok hd _ hrest ihs ihr =>
    intro hne ir ienv ht hc
    cases ht with
    | decl => simp [Stmt.isDecl] at hd
    | funcDecl => simp [Stmt.isDecl] at hd
    | last _ hts =>
      cases hrest with
      | stmts_nil =>
        obtain ⟨n1, r1, e1, c1⟩ := ihs trivial _ _ hts hc
        cases c1 with
        | val => exact ⟨n1, _, e1, .val⟩
        | sig _ hsig => simp [isSignal] at hsig
    | cons _ hts htr _ =>
      obtain ⟨n1, r1, e1, c1⟩ := ihs trivial _ _ hts hc
      cases c1 with
      | val =>
        obtain ⟨n2, r2, e2, c2⟩ := ihr hne _ _ htr hc
        exact ⟨max n1 n2 + 1, _, .seq (.cons_ok (Eval.fuel_mono e1 (by omega) trivial)
          (.singleton (c2.lift e2 (by omega))) (by simp)), c2⟩
      | sig _ hsig => simp [isSignal] at hsig
  | stmts_stmt_signal hd _ hsig ihs =>
    intro hne ir ienv ht hc
    cases ht with
    | decl => simp [Stmt.isDecl] at hd
    | funcDecl => simp [Stmt.isDecl] at hd
    | last _ hts =>
      exact ihs hne _ _ hts hc
    | cons _ hts _ _ =>
      obtain ⟨n1, r1, e1, c1⟩ := ihs hne _ _ hts hc
      exact ⟨n1 + 1, _, .seq (.cons_signal e1 (c1.signal hsig) (by simp)), c1⟩

/-! ## Main theorems -/

/-- **Forward simulation, JS → IR, expressions.** -/
theorem sim_js_to_ir_expr
    (htrans : JSToIRExpr js_e ir_e)
    (heval : JSEvalExpr jsenv store js_e result_js)
    (hok : NoErr result_js)
    (hcorr : EnvCorr SJI jsenv irenv) :
    ∃ fuel result_ir, Eval irenv store fuel ir_e result_ir ∧
      ResultCorr SJI result_js result_ir :=
  sim_js_all heval hok _ _ htrans hcorr

/-- **Forward simulation, JS → IR, programs (statement lists).** -/
theorem sim_js_to_ir_program
    (htrans : JSToIRStmts prog ir)
    (heval : JSEvalStmts jsenv store prog result_js)
    (hok : NoErr result_js)
    (hcorr : EnvCorr SJI jsenv irenv) :
    ∃ fuel result_ir, Eval irenv store fuel ir result_ir ∧
      StmtCorr SJI result_js result_ir :=
  sim_js_all heval hok _ _ htrans hcorr

end LeanJS.Semantics
