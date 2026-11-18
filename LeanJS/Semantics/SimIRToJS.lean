/-
  Forward simulation: IR → JS preserves semantics (verified core).

  If an IR expression evaluates (with any fuel) to a non-error result, and it
  translates to JS, then under corresponding environments the JS program
  evaluates to a corresponding result.

  * Expression mode (`IRToJSExpr`): results correspond (`ResultCorr`).
  * Statement mode (`IRToJSStmts m`): results correspond per `ModeCorr m`:
    in `.tail` mode the IR value is what the JS statements *return* (or the
    JS falls off the end and the IR value is `undefined`-like); in
    `.discard` mode values are dropped.

  IR `unit` and `undefined` both become JS `undefined`.
-/
import LeanJS.Semantics.SimJSToIR

set_option autoImplicit true

namespace LeanJS.Semantics

open LeanJS.JS
open LeanJS.IR

/-! ## The IR → JS correspondence -/

/-- An IR closure body and the JS function body it becomes -/
inductive IRJSFun : Option String → IRExpr → ExprOrBlock → Prop where
  | expr : IRToJSExpr body b' → IRJSFun none body (.expr b')
  | block : IRToJSStmts .tail body ss → IRJSFun name body (.block ss)

def IRJSClo (v v' : IRValue) (e e' : Env) : Prop :=
  ∃ name ps body jb, v = .closure e name ps body ∧
    v' = .jsClosure e' name ps jb ∧ IRJSFun name body jb

def SIJ : CorrSpec where
  uUnit := .undefined
  uUndef := .undefined
  hUnit := .undefined
  hUndef := .undefined
  Clo := IRJSClo
  clo_src := by rintro _ _ _ _ ⟨_, _, _, _, rfl, _, _⟩; exact .closure
  clo_tgt := by rintro _ _ _ _ ⟨_, _, _, _, _, rfl, _⟩; exact .js

/-- Statement-mode result correspondence -/
inductive ModeCorr (S : CorrSpec) : StmtMode → EvalResult → EvalResult → Prop where
  | tail_ret : VCorr S v v' → ModeCorr S .tail (.val v s) (.return_ v' s)
  | tail_fall : VCorr S v .undefined → ModeCorr S .tail (.val v s) (.val v' s)
  | discard : ModeCorr S .discard (.val v s) (.val v' s)
  | sig : ResultCorr S r r' → isSignal r → ModeCorr S m r r'

theorem ModeCorr.noErr_right (h : ModeCorr S m r r') : NoErr r' := by
  cases h with
  | sig h _ => exact h.noErr_right
  | _ => trivial

/-- In a closure call, a tail-mode body yields corresponding call results -/
theorem ModeCorr.apply (h : ModeCorr S .tail r r') :
    ResultCorr S (unwrapReturn r) (unwrapBlockResult r') := by
  cases h with
  | tail_ret hv => exact .val hv
  | tail_fall hv => exact .val hv
  | sig h hs => rw [unwrapBlockResult_signal (h.signal hs)]; exact h.unwrapReturn

/-! ## Helper lemmas -/

theorem irBinOpToJS_spec (h : irBinOpToJS op = some jop) :
    ∃ op', jsBinOpToIR jop = some op' ∧ (op' = op ∨ (op = .strConcat ∧ op' = .add)) := by
  cases op <;> simp [irBinOpToJS] at h <;> subst h <;> simp [jsBinOpToIR]

theorem irUnaryOpToJS_spec (h : irUnaryOpToJS op = some jop) : jsUnaryOpToIR jop = some op := by
  cases op <;> simp [irUnaryOpToJS] at h <;> subst h <;> rfl

set_option maxHeartbeats 4000000 in
theorem evalBinOp_not_return (op : IRBinOp) (l r : IRValue) (s : Store) :
    ∀ v s', evalBinOp op l r s ≠ .return_ v s' := by
  intro v s' h
  unfold evalBinOp at h
  split at h <;> (try split at h) <;> simp_all

theorem evalUnaryOp_not_return (op : IRUnaryOp) (v : IRValue) (s : Store) :
    ∀ v' s', evalUnaryOp op v s ≠ .return_ v' s' := by
  intro v' s' h
  unfold evalUnaryOp at h
  split at h <;> simp_all

@[simp] theorem unwrapReturn_ne_return : unwrapReturn r ≠ .return_ v s := by
  cases r <;> simp [unwrapReturn]

@[simp] theorem unwrapBlockResult_ne_return : unwrapBlockResult r ≠ .return_ v s := by
  cases r <;> simp [unwrapBlockResult]

/-- JS expressions (and calls) never complete with a `return` signal -/
def JSNoRet : JSJ → EvalResult → Prop
  | .stmt .., _ => True
  | .stmts .., _ => True
  | _, r => ∀ v s, r ≠ .return_ v s

theorem js_no_return (h : JSSem j r) : JSNoRet j r := by
  induction h
  all_goals (try simp only [JSNoRet] at *)
  all_goals first
    | trivial
    | (intro v s heq
       first
       | (subst heq; simp_all)
       | simp_all [evalBinOp_not_return, evalUnaryOp_not_return])

theorem jsExpr_no_return (h : JSEvalExpr env st e r) : ∀ v s, r ≠ .return_ v s :=
  js_no_return h

theorem unwrapReturn_of_not_return (h : ∀ v s, r ≠ .return_ v s) : unwrapReturn r = r := by
  cases r <;> simp_all [unwrapReturn]

theorem noDecls_cons (h : noDecls (s :: ss) = true) : s.isDecl = false ∧ noDecls ss = true := by
  simp [noDecls] at h ⊢; exact ⟨h.1, h.2⟩

/-- Running a declaration-free statement list and then `rs` -/
theorem jsStmts_append_val (ss : List Stmt) (hnd : noDecls ss = true)
    (h1 : JSEvalStmts env st ss (.val v s1)) (h2 : JSEvalStmts env s1 rs r) :
    JSEvalStmts env st (ss ++ rs) r := by
  induction ss generalizing st with
  | nil => cases h1; exact h2
  | cons s ss ih =>
    obtain ⟨hd, hnd'⟩ := noDecls_cons hnd
    cases h1 with
    | stmts_stmt_ok _ hs hrest => exact .stmts_stmt_ok hd hs (ih hnd' hrest)
    | stmts_stmt_signal _ _ hsig => simp [isSignal] at hsig
    | stmts_decl_ok => simp [Stmt.isDecl] at hd
    | stmts_decl_signal => simp [Stmt.isDecl] at hd
    | stmts_funcDecl => simp [Stmt.isDecl] at hd

theorem jsStmts_append_signal (ss : List Stmt) (hnd : noDecls ss = true)
    (h1 : JSEvalStmts env st ss r) (hs : isSignal r) :
    JSEvalStmts env st (ss ++ rs) r := by
  induction ss generalizing st with
  | nil => cases h1; simp [isSignal] at hs
  | cons s ss ih =>
    obtain ⟨hd, hnd'⟩ := noDecls_cons hnd
    cases h1 with
    | stmts_stmt_ok _ hs' hrest => exact .stmts_stmt_ok hd hs' (ih hnd' hrest)
    | stmts_stmt_signal _ hs' hsig => exact .stmts_stmt_signal hd hs' hsig
    | stmts_decl_ok => simp [Stmt.isDecl] at hd
    | stmts_decl_signal => simp [Stmt.isDecl] at hd
    | stmts_funcDecl => simp [Stmt.isDecl] at hd

/-- A one-statement list behaves like the statement, except that normal
    completion yields `undefined`. -/
theorem jsStmts_single (hd : s.isDecl = false) (h : JSEvalStmt env st s r) :
    ∃ r', JSEvalStmts env st [s] r' ∧
      ((∃ v s1, r = .val v s1 ∧ r' = .val .undefined s1) ∨ (isSignal r ∧ r' = r)) := by
  cases r with
  | val v s1 => exact ⟨_, .stmts_stmt_ok hd h .stmts_nil, .inl ⟨v, s1, rfl, rfl⟩⟩
  | _ => exact ⟨_, .stmts_stmt_signal hd h trivial, .inr ⟨trivial, rfl⟩⟩

theorem ModeCorr.single (hc : ModeCorr S m r r0) (hd : s.isDecl = false)
    (h : JSEvalStmt env st s r0) : ∃ r', JSEvalStmts env st [s] r' ∧ ModeCorr S m r r' := by
  obtain ⟨r', hr', hk⟩ := jsStmts_single hd h
  refine ⟨r', hr', ?_⟩
  rcases hk with ⟨v, s1, rfl, rfl⟩ | ⟨hs, rfl⟩
  · cases hc with
    | tail_fall hv => exact .tail_fall hv
    | discard => exact .discard
    | sig hrc hs' => cases hrc <;> simp [isSignal] at hs'
  · exact hc

theorem ModeCorr.val_any (h : ModeCorr S m r (.val v' s)) : ModeCorr S m r (.val v'' s) := by
  cases h with
  | tail_fall hv => exact .tail_fall hv
  | discard => exact .discard
  | sig hc hs => cases hc; simp [isSignal] at hs

theorem ModeCorr.discard_inv (h : ModeCorr S .discard (.val v s) r') : ∃ v', r' = .val v' s := by
  cases h with
  | discard => exact ⟨_, rfl⟩
  | sig _ hs => simp [isSignal] at hs

/-- Invert a one-statement list -/
theorem jsStmts_single_inv (h : JSEvalStmts env st [s] r') (hd : s.isDecl = false) :
    ∃ r0, JSEvalStmt env st s r0 ∧
      ((∃ v s1, r0 = .val v s1 ∧ r' = .val .undefined s1) ∨ (isSignal r0 ∧ r' = r0)) := by
  cases h with
  | stmts_stmt_ok _ hs hrest => cases hrest; exact ⟨_, hs, .inl ⟨_, _, rfl, rfl⟩⟩
  | stmts_stmt_signal _ hs hsig => exact ⟨_, hs, .inr ⟨hsig, rfl⟩⟩
  | stmts_decl_ok => simp [Stmt.isDecl] at hd
  | stmts_decl_signal => simp [Stmt.isDecl] at hd
  | stmts_funcDecl => simp [Stmt.isDecl] at hd

theorem ModeCorr.of_single (hc : ModeCorr S m r r')
    (hk : (∃ v s1, r0 = .val v s1 ∧ r' = .val .undefined s1) ∨ (isSignal r0 ∧ r' = r0)) :
    ModeCorr S m r r0 := by
  rcases hk with ⟨v, s1, rfl, rfl⟩ | ⟨_, rfl⟩
  · exact hc.val_any
  · exact hc

theorem simpleParamNames_fst_pid (ps : List (String × IRType)) :
    simpleParamNames ((ps.map Prod.fst).map pid) = some (ps.map Prod.fst) :=
  simpleParamNames_map_pid _

theorem ApplyFunc.inv_closure (h : ApplyFunc (.closure cenv name ps body) args st n r) :
    ∃ bodyRes, Eval (callEnv cenv name ps args (.closure cenv name ps body)) st n body bodyRes ∧
      r = unwrapReturn bodyRes := by
  cases h with
  | closure_ok henv henv' hb hres =>
    subst henv henv'
    exact ⟨_, by cases name <;> exact hb, hres.trans (unwrapReturn_eq_match _)⟩
  | non_function hne => exact absurd rfl (hne _ _ _ _)

theorem jsEvalStmts_nil_inv (h : JSEvalStmts env st [] r) : r = .val .undefined st := by
  cases h; rfl

/-! ## Simulation -/

set_option maxHeartbeats 6400000 in
set_option maxRecDepth 8192 in
mutual

theorem sim_ir_js_expr {n : Nat} (h : Eval ienv st n e r) (hne : NoErr r)
    (ht : IRToJSExpr e e') (hc : EnvCorr SIJ ienv jenv) :
    ∃ r', JSEvalExpr jenv st e' r' ∧ ResultCorr SIJ r r' := by
  cases h with
  | fuel_zero => exact absurd hne id
  | lit =>
    cases ht with
    | num => exact ⟨_, .literal rfl, .val .number⟩
    | str => exact ⟨_, .literal rfl, .val .string⟩
    | bool => exact ⟨_, .literal rfl, .val .bool⟩
    | unit => exact ⟨_, .literal rfl, .val .unit⟩
  | var_ok hl =>
    cases ht
    obtain ⟨v', hl', hv⟩ := hc.lookup hl
    exact ⟨_, .ident hl', .val hv⟩
  | var_unbound => exact absurd hne id
  | undefined =>
    cases ht
    exact ⟨_, .literal rfl, .val .undefined⟩
  | let_ok hv hb =>
    cases ht with
    | let_ htv htb =>
      obtain ⟨r1, e1, c1⟩ := sim_ir_js_expr hv trivial htv hc
      obtain ⟨vv', rfl, hvv⟩ := c1.inv_val
      obtain ⟨r2, e2, c2⟩ := sim_ir_js_expr hb hne htb (.cons hvv hc)
      refine ⟨_, .call_ok (.arrow (simpleParamNames_map_pid [_]))
        (.args_cons_ok e1 .args_nil) (.apply_expr_body e2), ?_⟩
      rw [unwrapReturn_of_not_return (jsExpr_no_return e2)]; exact c2
  | let_signal hv hs =>
    cases ht with
    | let_ htv htb =>
      obtain ⟨r1, e1, c1⟩ := sim_ir_js_expr hv hne htv hc
      exact ⟨_, .call_args_signal (.arrow (simpleParamNames_map_pid [_]))
        (.args_cons_signal e1 (c1.signal hs)) (c1.signal hs), c1⟩
  | lam hp =>
    subst hp
    cases ht with
    | lam_expr hb =>
      exact ⟨_, .arrow (simpleParamNames_fst_pid _),
        .val (.clo ⟨_, _, _, _, rfl, rfl, .expr hb⟩ hc)⟩
    | lam_block hb =>
      exact ⟨_, .arrow (simpleParamNames_fst_pid _),
        .val (.clo ⟨_, _, _, _, rfl, rfl, .block hb⟩ hc)⟩
    | lam_named hb =>
      exact ⟨_, .function (simpleParamNames_fst_pid _),
        .val (.clo ⟨_, _, _, _, rfl, rfl, .block hb⟩ hc)⟩
  | app_ok hf ha hap =>
    cases ht with
    | app htf hta =>
      obtain ⟨r1, e1, c1⟩ := sim_ir_js_expr hf trivial htf hc
      obtain ⟨fv', rfl, hfv⟩ := c1.inv_val
      obtain ⟨r2, e2, c2⟩ := sim_ir_js_args ha trivial hta hc .nil
      obtain ⟨av', rfl, hav⟩ := c2.inv_val
      obtain ⟨vs', rfl, hvs⟩ := hav.inv_array
      obtain ⟨r3, e3, c3⟩ := sim_ir_js_apply hap hne hfv hvs
      exact ⟨_, .call_ok e1 e2 e3, c3⟩
  | app_func_signal hf hs =>
    cases ht with
    | app htf _ =>
      obtain ⟨r1, e1, c1⟩ := sim_ir_js_expr hf hne htf hc
      exact ⟨_, .call_callee_signal e1 (c1.signal hs), c1⟩
  | app_args_signal hf ha hs =>
    cases ht with
    | app htf hta =>
      obtain ⟨r1, e1, c1⟩ := sim_ir_js_expr hf trivial htf hc
      obtain ⟨fv', rfl, hfv⟩ := c1.inv_val
      obtain ⟨r2, e2, c2⟩ := sim_ir_js_args ha hne hta hc .nil
      exact ⟨_, .call_args_signal e1 e2 (c2.signal hs), c2⟩
  | binOp_ok hl hr hres =>
    subst hres
    cases ht with
    | binOp htl htr hop =>
      obtain ⟨op', hop', hrel⟩ := irBinOpToJS_spec hop
      obtain ⟨r1, e1, c1⟩ := sim_ir_js_expr hl trivial htl hc
      obtain ⟨lv', rfl, hlv⟩ := c1.inv_val
      obtain ⟨r2, e2, c2⟩ := sim_ir_js_expr hr trivial htr hc
      obtain ⟨rv', rfl, hrv⟩ := c2.inv_val
      exact ⟨_, .binary_ok e1 e2 hop', evalBinOp_corr hrel hlv hrv _ hne⟩
  | binOp_left_signal hl hs =>
    cases ht with
    | binOp htl _ _ =>
      obtain ⟨r1, e1, c1⟩ := sim_ir_js_expr hl hne htl hc
      exact ⟨_, .binary_left_signal e1 (c1.signal hs), c1⟩
  | binOp_right_signal hl hr hs =>
    cases ht with
    | binOp htl htr _ =>
      obtain ⟨r1, e1, c1⟩ := sim_ir_js_expr hl trivial htl hc
      obtain ⟨lv', rfl, hlv⟩ := c1.inv_val
      obtain ⟨r2, e2, c2⟩ := sim_ir_js_expr hr hne htr hc
      exact ⟨_, .binary_right_signal e1 e2 (c2.signal hs), c2⟩
  | unaryOp_ok ha hres =>
    subst hres
    cases ht with
    | unaryOp hta hop =>
      obtain ⟨r1, e1, c1⟩ := sim_ir_js_expr ha trivial hta hc
      obtain ⟨v', rfl, hv⟩ := c1.inv_val
      exact ⟨_, .unary_ok e1 (irUnaryOpToJS_spec hop), evalUnaryOp_corr _ hv _ hne⟩
  | unaryOp_signal ha hs =>
    cases ht with
    | unaryOp hta _ =>
      obtain ⟨r1, e1, c1⟩ := sim_ir_js_expr ha hne hta hc
      exact ⟨_, .unary_signal e1 (c1.signal hs), c1⟩
  | record hf =>
    cases ht with
    | record htf =>
      obtain ⟨r1, e1, c1⟩ := sim_ir_js_fields hf hne htf hc .nil
      exact ⟨_, .object e1, c1⟩
  | project_record_ok he hl =>
    cases ht with
    | project hte =>
      obtain ⟨r1, e1, c1⟩ := sim_ir_js_expr he trivial hte hc
      obtain ⟨rv', rfl, hrv⟩ := c1.inv_val
      obtain ⟨fs', rfl, hfs⟩ := hrv.inv_record
      rcases hfs.lookup _ with ⟨hn, _⟩ | ⟨v, v', hv, hv', hvv⟩
      · rw [hn] at hl; cases hl
      · rw [hv] at hl; cases hl
        exact ⟨_, .member_ok e1 hv', .val hvv⟩
  | project_record_missing => exact absurd hne id
  | project_constructed_tag he _ =>
    cases ht with
    | project hte =>
      obtain ⟨r1, e1, c1⟩ := sim_ir_js_expr he trivial hte hc
      obtain ⟨v', rfl, hv⟩ := c1.inv_val
      cases hv with
      | clo hc' _ => cases SIJ.clo_src hc'
  | project_constructed_other => exact absurd hne id
  | project_non_record => exact absurd hne id
  | project_signal he hs =>
    cases ht with
    | project hte =>
      obtain ⟨r1, e1, c1⟩ := sim_ir_js_expr he hne hte hc
      exact ⟨_, .member_signal e1 (c1.signal hs), c1⟩
  | array he =>
    cases ht with
    | array hte =>
      obtain ⟨r1, e1, c1⟩ := sim_ir_js_elems he hne hte hc .nil
      exact ⟨_, .array e1, c1⟩
  | if_true hcnd htr hbr =>
    cases ht with
    | if_ htc htt _ =>
      obtain ⟨r1, e1, c1⟩ := sim_ir_js_expr hcnd trivial htc hc
      obtain ⟨cv', rfl, hcv⟩ := c1.inv_val
      obtain ⟨r2, e2, c2⟩ := sim_ir_js_expr hbr hne htt hc
      exact ⟨_, .cond_true e1 (hcv.truthy ▸ htr) e2, c2⟩
  | if_false hcnd htr hbr =>
    cases ht with
    | if_ htc _ hte =>
      obtain ⟨r1, e1, c1⟩ := sim_ir_js_expr hcnd trivial htc hc
      obtain ⟨cv', rfl, hcv⟩ := c1.inv_val
      obtain ⟨r2, e2, c2⟩ := sim_ir_js_expr hbr hne hte hc
      exact ⟨_, .cond_false e1 (hcv.truthy ▸ htr) e2, c2⟩
  | if_signal hcnd hs =>
    cases ht with
    | if_ htc _ _ =>
      obtain ⟨r1, e1, c1⟩ := sim_ir_js_expr hcnd hne htc hc
      exact ⟨_, .cond_signal e1 (c1.signal hs), c1⟩
  | _ => cases ht
  termination_by (n, 0)
  decreasing_by
    all_goals simp_wf
    all_goals subst_vars
    all_goals first
      | (apply Prod.Lex.left; omega)
      | (apply Prod.Lex.right; first | omega | (simp [List.length_cons]; done) | (simp [List.length_cons]; omega))

theorem sim_ir_js_args {n : Nat} (h : EvalArgs ienv st n es acc r) (hne : NoErr r)
    (ht : IRToJSExprs es es') (hc : EnvCorr SIJ ienv jenv) (ha : ListCorr SIJ acc acc') :
    ∃ r', JSEvalArgs jenv st es' acc' r' ∧ ResultCorr SIJ r r' := by
  cases h with
  | nil =>
    cases ht
    exact ⟨_, .args_nil, .val (.array ha.reverse)⟩
  | cons_ok he hrest =>
    cases ht with
    | cons hte htr =>
      obtain ⟨r1, e1, c1⟩ := sim_ir_js_expr he trivial hte hc
      obtain ⟨v', rfl, hv⟩ := c1.inv_val
      obtain ⟨r2, e2, c2⟩ := sim_ir_js_args hrest hne htr hc (.cons hv ha)
      exact ⟨_, .args_cons_ok e1 e2, c2⟩
  | cons_signal he hs =>
    cases ht with
    | cons hte _ =>
      obtain ⟨r1, e1, c1⟩ := sim_ir_js_expr he hne hte hc
      exact ⟨_, .args_cons_signal e1 (c1.signal hs), c1⟩
  termination_by (n, es.length)
  decreasing_by
    all_goals simp_wf
    all_goals subst_vars
    all_goals first
      | (apply Prod.Lex.left; omega)
      | (apply Prod.Lex.right; first | omega | (simp [List.length_cons]; done) | (simp [List.length_cons]; omega))

theorem sim_ir_js_elems {n : Nat} (h : EvalElems ienv st n es acc r) (hne : NoErr r)
    (ht : IRToJSExprs es es') (hc : EnvCorr SIJ ienv jenv) (ha : ListCorr SIJ acc acc') :
    ∃ r', JSEvalElems jenv st (es'.map some) acc' r' ∧ ResultCorr SIJ r r' := by
  cases h with
  | nil =>
    cases ht
    exact ⟨_, .elems_nil, .val (.array ha.reverse)⟩
  | cons_ok he hrest =>
    cases ht with
    | cons hte htr =>
      obtain ⟨r1, e1, c1⟩ := sim_ir_js_expr he trivial hte hc
      obtain ⟨v', rfl, hv⟩ := c1.inv_val
      obtain ⟨r2, e2, c2⟩ := sim_ir_js_elems hrest hne htr hc (.cons hv ha)
      exact ⟨_, .elems_some_ok e1 e2, c2⟩
  | cons_signal he hs =>
    cases ht with
    | cons hte _ =>
      obtain ⟨r1, e1, c1⟩ := sim_ir_js_expr he hne hte hc
      exact ⟨_, .elems_some_signal e1 (c1.signal hs), c1⟩
  termination_by (n, es.length)
  decreasing_by
    all_goals simp_wf
    all_goals subst_vars
    all_goals first
      | (apply Prod.Lex.left; omega)
      | (apply Prod.Lex.right; first | omega | (simp [List.length_cons]; done) | (simp [List.length_cons]; omega))

theorem sim_ir_js_fields {n : Nat} (h : EvalFields ienv st n fs acc r) (hne : NoErr r)
    (ht : IRToJSFields fs ps) (hc : EnvCorr SIJ ienv jenv) (ha : FieldsCorr SIJ acc acc') :
    ∃ r', JSEvalProps jenv st ps acc' r' ∧ ResultCorr SIJ r r' := by
  cases h with
  | nil =>
    cases ht
    exact ⟨_, .props_nil, .val (.record ha.reverse)⟩
  | cons_ok he hrest =>
    cases ht with
    | cons hte htr =>
      obtain ⟨r1, e1, c1⟩ := sim_ir_js_expr he trivial hte hc
      obtain ⟨v', rfl, hv⟩ := c1.inv_val
      obtain ⟨r2, e2, c2⟩ := sim_ir_js_fields hrest hne htr hc (.cons hv ha)
      exact ⟨_, .props_cons_ok e1 e2, c2⟩
  | cons_signal he hs =>
    cases ht with
    | cons hte _ =>
      obtain ⟨r1, e1, c1⟩ := sim_ir_js_expr he hne hte hc
      exact ⟨_, .props_cons_signal e1 (c1.signal hs), c1⟩
  termination_by (n, fs.length)
  decreasing_by
    all_goals simp_wf
    all_goals subst_vars
    all_goals first
      | (apply Prod.Lex.left; omega)
      | (apply Prod.Lex.right; first | omega | (simp [List.length_cons]; done) | (simp [List.length_cons]; omega))

theorem sim_ir_js_apply {n : Nat} (h : ApplyFunc fv vs st n r) (hne : NoErr r)
    (hf : VCorr SIJ fv fv') (hv : ListCorr SIJ vs vs') :
    ∃ r', JSApply fv' vs' st r' ∧ ResultCorr SIJ r r' := by
  cases hf with
  | clo hclo hce =>
    obtain ⟨name, ps, body, jb, rfl, rfl, hfun⟩ := hclo
    obtain ⟨bodyRes, hb, rfl⟩ := h.inv_closure
    cases hfun with
    | expr hte =>
      have hfv : VCorr SIJ (.closure _ none ps body) (.jsClosure _ none ps (.expr _)) :=
        .clo ⟨_, _, _, _, rfl, rfl, .expr hte⟩ hce
      obtain ⟨r1, e1, c1⟩ :=
        sim_ir_js_expr hb (unwrapReturn_noErr hne) hte (hce.ofCall hv hfv ps none)
      exact ⟨_, .apply_expr_body e1, c1.unwrapReturn⟩
    | block hts =>
      have hfv : VCorr SIJ (.closure _ name ps body) (.jsClosure _ name ps (.block _)) :=
        .clo ⟨_, _, _, _, rfl, rfl, .block hts⟩ hce
      obtain ⟨r1, e1, c1⟩ :=
        sim_ir_js_stmts hb (unwrapReturn_noErr hne) hts (hce.ofCall hv hfv ps name)
      exact ⟨_, .apply_block_body e1, c1.apply⟩
  | _ => cases h <;> exact absurd hne id
  termination_by (n, 2)
  decreasing_by
    all_goals simp_wf
    all_goals subst_vars
    all_goals first
      | (apply Prod.Lex.left; omega)
      | (apply Prod.Lex.right; first | omega | (simp [List.length_cons]; done) | (simp [List.length_cons]; omega))

theorem sim_ir_js_stmts {n : Nat} (h : Eval ienv st n e r) (hne : NoErr r)
    (ht : IRToJSStmts m e ss) (hc : EnvCorr SIJ ienv jenv) :
    ∃ r', JSEvalStmts jenv st ss r' ∧ ModeCorr SIJ m r r' := by
  cases ht with
  | let_ htv htb =>
    cases h with
    | fuel_zero => exact absurd hne id
    | let_ok hv hb =>
      obtain ⟨r1, e1, c1⟩ := sim_ir_js_expr hv trivial htv hc
      obtain ⟨vv', rfl, hvv⟩ := c1.inv_val
      obtain ⟨r2, e2, c2⟩ := sim_ir_js_stmts hb hne htb (.cons hvv hc)
      exact ⟨_, .stmts_decl_ok (.inl rfl) e1 e2, c2⟩
    | let_signal hv hs =>
      obtain ⟨r1, e1, c1⟩ := sim_ir_js_expr hv hne htv hc
      exact ⟨_, .stmts_decl_signal (.inl rfl) e1 (c1.signal hs), .sig c1 hs⟩
  | if_ htc htt hte =>
    cases h with
    | fuel_zero => exact absurd hne id
    | if_true hcnd htr hbr =>
      obtain ⟨r1, e1, c1⟩ := sim_ir_js_expr hcnd trivial htc hc
      obtain ⟨cv', rfl, hcv⟩ := c1.inv_val
      obtain ⟨r2, e2, c2⟩ := sim_ir_js_stmts hbr hne htt hc
      exact c2.single rfl (.stmt_if_true e1 (hcv.truthy ▸ htr) (.stmt_block e2))
    | if_false hcnd htr hbr =>
      obtain ⟨r1, e1, c1⟩ := sim_ir_js_expr hcnd trivial htc hc
      obtain ⟨cv', rfl, hcv⟩ := c1.inv_val
      obtain ⟨r2, e2, c2⟩ := sim_ir_js_stmts hbr hne hte hc
      exact c2.single rfl (.stmt_if_false e1 (hcv.truthy ▸ htr) (.stmt_block e2))
    | if_signal hcnd hs =>
      obtain ⟨r1, e1, c1⟩ := sim_ir_js_expr hcnd hne htc hc
      exact (ModeCorr.sig c1 hs).single rfl (.stmt_if_signal e1 (c1.signal hs))
  | if_noelse htc htt hte =>
    cases h with
    | fuel_zero => exact absurd hne id
    | if_true hcnd htr hbr =>
      obtain ⟨r1, e1, c1⟩ := sim_ir_js_expr hcnd trivial htc hc
      obtain ⟨cv', rfl, hcv⟩ := c1.inv_val
      obtain ⟨r2, e2, c2⟩ := sim_ir_js_stmts hbr hne htt hc
      exact c2.single rfl (.stmt_if_true e1 (hcv.truthy ▸ htr) (.stmt_block e2))
    | if_false hcnd htr hbr =>
      obtain ⟨r1, e1, c1⟩ := sim_ir_js_expr hcnd trivial htc hc
      obtain ⟨cv', rfl, hcv⟩ := c1.inv_val
      obtain ⟨r2, e2, c2⟩ := sim_ir_js_stmts hbr hne hte hc
      rw [jsEvalStmts_nil_inv e2] at c2
      exact c2.single rfl (.stmt_if_false_none e1 (hcv.truthy ▸ htr))
    | if_signal hcnd hs =>
      obtain ⟨r1, e1, c1⟩ := sim_ir_js_expr hcnd hne htc hc
      exact (ModeCorr.sig c1 hs).single rfl (.stmt_if_signal e1 (c1.signal hs))
  | funcDecl hts htb =>
    cases h with
    | fuel_zero => exact absurd hne id
    | let_ok hv hb =>
      cases hv with
      | lam hp =>
        subst hp
        obtain ⟨r2, e2, c2⟩ := sim_ir_js_stmts hb hne htb
          (.cons (.clo ⟨_, _, _, _, rfl, rfl, .block hts⟩ hc) hc)
        exact ⟨_, .stmts_funcDecl (simpleParamNames_fst_pid _) e2, c2⟩
    | let_signal hv hs =>
      cases hv with
      | fuel_zero => exact absurd hne id
      | lam => simp [isSignal] at hs
  | if_elseif htc htt hte hd =>
    cases h with
    | fuel_zero => exact absurd hne id
    | if_true hcnd htr hbr =>
      obtain ⟨r1, e1, c1⟩ := sim_ir_js_expr hcnd trivial htc hc
      obtain ⟨cv', rfl, hcv⟩ := c1.inv_val
      obtain ⟨r2, e2, c2⟩ := sim_ir_js_stmts hbr hne htt hc
      exact c2.single rfl (.stmt_if_true e1 (hcv.truthy ▸ htr) (.stmt_block e2))
    | if_false hcnd htr hbr =>
      obtain ⟨r1, e1, c1⟩ := sim_ir_js_expr hcnd trivial htc hc
      obtain ⟨cv', rfl, hcv⟩ := c1.inv_val
      obtain ⟨r2, e2, c2⟩ := sim_ir_js_stmts hbr hne hte hc
      obtain ⟨r0, e0, hk⟩ := jsStmts_single_inv e2 hd
      exact (c2.of_single hk).single rfl (.stmt_if_false e1 (hcv.truthy ▸ htr) e0)
    | if_signal hcnd hs =>
      obtain ⟨r1, e1, c1⟩ := sim_ir_js_expr hcnd hne htc hc
      exact (ModeCorr.sig c1 hs).single rfl (.stmt_if_signal e1 (c1.signal hs))
  | seq_last hte htr hrest =>
    cases h with
    | fuel_zero => exact absurd hne id
    | seq hs => exact sim_ir_js_seq_last hs hne hte htr hrest hc
  | seq_one hte =>
    cases h with
    | fuel_zero => exact absurd hne id
    | seq hs =>
      cases hs with
      | singleton he => exact sim_ir_js_stmts he hne hte hc
      | cons_ok _ _ hne' => exact absurd rfl hne'
      | cons_signal _ _ hne' => exact absurd rfl hne'
  | seq_block hte htr hrest =>
    cases h with
    | fuel_zero => exact absurd hne id
    | seq hs => exact sim_ir_js_seq_block hs hne hte htr hrest hc
  | seq_flat hte hnd htr hrest =>
    cases h with
    | fuel_zero => exact absurd hne id
    | seq hs => exact sim_ir_js_seq_flat hs hne hte hnd htr hrest hc
  | ret hte =>
    cases h with
    | fuel_zero => exact absurd hne id
    | return_ok he =>
      obtain ⟨r1, e1, c1⟩ := sim_ir_js_expr he trivial hte hc
      obtain ⟨v', rfl, hv⟩ := c1.inv_val
      exact ⟨_, .stmts_stmt_signal rfl (.stmt_return_some e1) trivial, .sig (.ret hv) trivial⟩
    | return_signal he hs =>
      obtain ⟨r1, e1, c1⟩ := sim_ir_js_expr he hne hte hc
      exact ⟨_, .stmts_stmt_signal rfl (.stmt_return_some_signal e1 (c1.signal hs))
        (c1.signal hs), .sig c1 hs⟩
  | throw hte =>
    cases h with
    | fuel_zero => exact absurd hne id
    | throw_ok he =>
      obtain ⟨r1, e1, c1⟩ := sim_ir_js_expr he trivial hte hc
      obtain ⟨v', rfl, hv⟩ := c1.inv_val
      exact ⟨_, .stmts_stmt_signal rfl (.stmt_throw_ok e1) trivial, .sig (.throw hv) trivial⟩
    | throw_signal he hs =>
      obtain ⟨r1, e1, c1⟩ := sim_ir_js_expr he hne hte hc
      exact ⟨_, .stmts_stmt_signal rfl (.stmt_throw_signal e1 (c1.signal hs))
        (c1.signal hs), .sig c1 hs⟩
  | expr_tail hte =>
    obtain ⟨r1, e1, c1⟩ := sim_ir_js_expr h hne hte hc
    cases c1 with
    | val hv =>
      exact ⟨_, .stmts_stmt_signal rfl (.stmt_return_some e1) trivial, .tail_ret hv⟩
    | ret hv => exact absurd rfl (jsExpr_no_return e1 _ _)
    | throw hv =>
      exact ⟨_, .stmts_stmt_signal rfl (.stmt_return_some_signal e1 trivial) trivial,
        .sig (.throw hv) trivial⟩
    | brk =>
      exact ⟨_, .stmts_stmt_signal rfl (.stmt_return_some_signal e1 trivial) trivial,
        .sig .brk trivial⟩
    | cont =>
      exact ⟨_, .stmts_stmt_signal rfl (.stmt_return_some_signal e1 trivial) trivial,
        .sig .cont trivial⟩
  | expr_discard hte =>
    obtain ⟨r1, e1, c1⟩ := sim_ir_js_expr h hne hte hc
    cases c1 with
    | val hv => exact ⟨_, .stmts_stmt_ok rfl (.stmt_expr e1) .stmts_nil, .discard⟩
    | ret hv => exact ⟨_, .stmts_stmt_signal rfl (.stmt_expr e1) trivial, .sig (.ret hv) trivial⟩
    | throw hv =>
      exact ⟨_, .stmts_stmt_signal rfl (.stmt_expr e1) trivial, .sig (.throw hv) trivial⟩
    | brk => exact ⟨_, .stmts_stmt_signal rfl (.stmt_expr e1) trivial, .sig .brk trivial⟩
    | cont => exact ⟨_, .stmts_stmt_signal rfl (.stmt_expr e1) trivial, .sig .cont trivial⟩
  | undef =>
    cases h with
    | fuel_zero => exact absurd hne id
    | undefined =>
      cases m
      · exact ⟨_, .stmts_nil, .tail_fall .undefined⟩
      · exact ⟨_, .stmts_nil, .discard⟩
  | unit =>
    cases h with
    | fuel_zero => exact absurd hne id
    | lit =>
      cases m
      · exact ⟨_, .stmts_nil, .tail_fall .unit⟩
      · exact ⟨_, .stmts_nil, .discard⟩
  termination_by (n, 1)
  decreasing_by
    all_goals simp_wf
    all_goals subst_vars
    all_goals first
      | (apply Prod.Lex.left; omega)
      | (apply Prod.Lex.right; first | omega | (simp [List.length_cons]; done) | (simp [List.length_cons]; omega))

/-- `seq (e :: rest)` translated as `{ ss } rs` -/
theorem sim_ir_js_seq_block {n : Nat} (h : EvalSeq ienv st n (e :: rest) r) (hne : NoErr r)
    (hte : IRToJSStmts .discard e ss) (htr : IRToJSStmts m (.seq rest) rs) (hrest : rest ≠ [])
    (hc : EnvCorr SIJ ienv jenv) :
    ∃ r', JSEvalStmts jenv st (.block ss :: rs) r' ∧ ModeCorr SIJ m r r' := by
  cases h with
  | singleton _ => exact absurd rfl hrest
  | cons_ok he hs _ =>
    obtain ⟨r1, e1, c1⟩ := sim_ir_js_stmts he trivial hte hc
    cases c1 with
    | discard =>
      obtain ⟨r2, e2, c2⟩ := sim_ir_js_seq hs hne htr hc
      exact ⟨_, .stmts_stmt_ok rfl (.stmt_block e1) e2, c2⟩
    | sig _ hsig => simp [isSignal] at hsig
  | cons_signal he hs _ =>
    obtain ⟨r1, e1, c1⟩ := sim_ir_js_stmts he hne hte hc
    cases c1 with
    | discard => simp [isSignal] at hs
    | sig c1 hs' => exact ⟨_, .stmts_stmt_signal rfl (.stmt_block e1) (c1.signal hs'), .sig c1 hs'⟩
  termination_by (n, 2 * rest.length + 5)
  decreasing_by
    all_goals simp_wf
    all_goals subst_vars
    all_goals first
      | (apply Prod.Lex.left; omega)
      | (apply Prod.Lex.right; first | omega | (simp [List.length_cons]; done) | (simp [List.length_cons]; omega))

/-- `seq (e :: rest)` translated as `ss ++ rs` (no declarations in `ss`) -/
theorem sim_ir_js_seq_flat {n : Nat} (h : EvalSeq ienv st n (e :: rest) r) (hne : NoErr r)
    (hte : IRToJSStmts .discard e ss) (hnd : noDecls ss = true)
    (htr : IRToJSStmts m (.seq rest) rs) (hrest : rest ≠ [])
    (hc : EnvCorr SIJ ienv jenv) :
    ∃ r', JSEvalStmts jenv st (ss ++ rs) r' ∧ ModeCorr SIJ m r r' := by
  cases h with
  | singleton _ => exact absurd rfl hrest
  | cons_ok he hs _ =>
    obtain ⟨r1, e1, c1⟩ := sim_ir_js_stmts he trivial hte hc
    cases c1 with
    | discard =>
      obtain ⟨r2, e2, c2⟩ := sim_ir_js_seq hs hne htr hc
      exact ⟨_, jsStmts_append_val ss hnd e1 e2, c2⟩
    | sig _ hsig => simp [isSignal] at hsig
  | cons_signal he hs _ =>
    obtain ⟨r1, e1, c1⟩ := sim_ir_js_stmts he hne hte hc
    cases c1 with
    | discard => simp [isSignal] at hs
    | sig c1 hs' => exact ⟨_, jsStmts_append_signal ss hnd e1 (c1.signal hs'), .sig c1 hs'⟩
  termination_by (n, 2 * rest.length + 5)
  decreasing_by
    all_goals simp_wf
    all_goals subst_vars
    all_goals first
      | (apply Prod.Lex.left; omega)
      | (apply Prod.Lex.right; first | omega | (simp [List.length_cons]; done) | (simp [List.length_cons]; omega))

/-- `seq (e :: rest)` where `rest` contributes no statements -/
theorem sim_ir_js_seq_last {n : Nat} (h : EvalSeq ienv st n (e :: rest) r) (hne : NoErr r)
    (hte : IRToJSStmts .discard e ss) (htr : IRToJSStmts m (.seq rest) []) (hrest : rest ≠ [])
    (hc : EnvCorr SIJ ienv jenv) :
    ∃ r', JSEvalStmts jenv st ss r' ∧ ModeCorr SIJ m r r' := by
  cases h with
  | singleton _ => exact absurd rfl hrest
  | cons_ok he hs _ =>
    obtain ⟨r1, e1, c1⟩ := sim_ir_js_stmts he trivial hte hc
    obtain ⟨v1, rfl⟩ := c1.discard_inv
    obtain ⟨r2, e2, c2⟩ := sim_ir_js_seq hs hne htr hc
    rw [jsEvalStmts_nil_inv e2] at c2
    exact ⟨_, e1, c2.val_any⟩
  | cons_signal he hs _ =>
    obtain ⟨r1, e1, c1⟩ := sim_ir_js_stmts he hne hte hc
    cases c1 with
    | discard => simp [isSignal] at hs
    | sig c1 hs' => exact ⟨_, e1, .sig c1 hs'⟩
  termination_by (n, 2 * rest.length + 5)
  decreasing_by
    all_goals simp_wf
    all_goals subst_vars
    all_goals first
      | (apply Prod.Lex.left; omega)
      | (apply Prod.Lex.right; first | omega | (simp [List.length_cons]; done) | (simp [List.length_cons]; omega))

/-- Statement-mode translation of `seq es`, from an `EvalSeq` derivation -/
theorem sim_ir_js_seq {n : Nat} (h : EvalSeq ienv st n es r) (hne : NoErr r)
    (ht : IRToJSStmts m (.seq es) ss) (hc : EnvCorr SIJ ienv jenv) :
    ∃ r', JSEvalStmts jenv st ss r' ∧ ModeCorr SIJ m r r' := by
  cases ht with
  | seq_one hte =>
    cases h with
    | singleton he => exact sim_ir_js_stmts he hne hte hc
    | cons_ok _ _ hne' => exact absurd rfl hne'
    | cons_signal _ _ hne' => exact absurd rfl hne'
  | seq_block hte htr hrest => exact sim_ir_js_seq_block h hne hte htr hrest hc
  | seq_flat hte hnd htr hrest => exact sim_ir_js_seq_flat h hne hte hnd htr hrest hc
  | seq_last hte htr hrest => exact sim_ir_js_seq_last h hne hte htr hrest hc
  | expr_tail hte => cases hte
  | expr_discard hte => cases hte
  termination_by (n, 2 * es.length + 4)
  decreasing_by
    all_goals simp_wf
    all_goals subst_vars
    all_goals first
      | (apply Prod.Lex.left; omega)
      | (apply Prod.Lex.right; first | omega | (simp [List.length_cons]; done) | (simp [List.length_cons]; omega))

end

/-! ## Main theorems -/

/-- **Forward simulation, IR → JS, expressions.** -/
theorem sim_ir_to_js_expr
    (htrans : IRToJSExpr ir_e js_e)
    (heval : Eval irenv store fuel ir_e result_ir)
    (hok : NoErr result_ir)
    (hcorr : EnvCorr SIJ irenv jsenv) :
    ∃ result_js, JSEvalExpr jsenv store js_e result_js ∧ ResultCorr SIJ result_ir result_js :=
  sim_ir_js_expr heval hok htrans hcorr

/-- **Forward simulation, IR → JS, statement mode** (`.discard` for programs,
    `.tail` for function bodies). -/
theorem sim_ir_to_js_stmts
    (htrans : IRToJSStmts m ir_e prog)
    (heval : Eval irenv store fuel ir_e result_ir)
    (hok : NoErr result_ir)
    (hcorr : EnvCorr SIJ irenv jsenv) :
    ∃ result_js, JSEvalStmts jsenv store prog result_js ∧ ModeCorr SIJ m result_ir result_js :=
  sim_ir_js_stmts heval hok htrans hcorr

end LeanJS.Semantics
