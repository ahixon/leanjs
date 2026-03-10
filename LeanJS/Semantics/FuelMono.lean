/-
  Fuel monotonicity: if evaluation succeeds (non-fuel-error) with fuel n,
  it produces the same result with any m ≥ n.
-/
import LeanJS.Semantics.Relation

set_option autoImplicit true

namespace LeanJS.Semantics

open LeanJS.IR

private theorem succ_le_succ {n m : Nat} (h : n + 1 ≤ m) : ∃ m', m = m' + 1 :=
  ⟨m - 1, by omega⟩

private theorem notFuelError_of_tryCatch_match
    {result : EvalResult} {ac : EvalResult} {fs : Store}
    (hres : result = match ac with
      | .val v _ => .val v fs | .return_ v _ => .return_ v fs
      | .break_ _ => .break_ fs | .continue_ _ => .continue_ fs
      | .throw_ v _ => .throw_ v fs | .error msg => .error msg)
    (hnf : notFuelError result) : notFuelError ac := by
  subst hres; cases ac <;> first | trivial | exact hnf

private theorem notFuelError_of_return_match
    {result bodyResult : EvalResult}
    (hres : result = match bodyResult with | .return_ v s => .val v s | other => other)
    (hnf : notFuelError result) : notFuelError bodyResult := by
  subst hres; cases bodyResult <;> first | trivial | exact hnf

set_option maxHeartbeats 12800000 in
set_option maxRecDepth 2048 in
mutual

def Eval.fuel_mono
    (h : Eval env store n e r) (hle : n ≤ m) (hnf : notFuelError r) :
    Eval env store m e r := by
  cases h with
  | fuel_zero => exact absurd hnf id
  | lit => obtain ⟨m', rfl⟩ := succ_le_succ hle; exact .lit
  | var_ok h => obtain ⟨m', rfl⟩ := succ_le_succ hle; exact .var_ok h
  | var_unbound h => obtain ⟨m', rfl⟩ := succ_le_succ hle; exact .var_unbound h
  | undefined => obtain ⟨m', rfl⟩ := succ_le_succ hle; exact .undefined
  | this_ok h => obtain ⟨m', rfl⟩ := succ_le_succ hle; exact .this_ok h
  | this_none h => obtain ⟨m', rfl⟩ := succ_le_succ hle; exact .this_none h
  | let_ok hv hb =>
    obtain ⟨m', rfl⟩ := succ_le_succ hle
    exact .let_ok (Eval.fuel_mono hv (by omega) trivial) (Eval.fuel_mono hb (by omega) hnf)
  | let_signal hv hs =>
    obtain ⟨m', rfl⟩ := succ_le_succ hle
    exact .let_signal (Eval.fuel_mono hv (by omega) hnf) hs
  | lam heq => obtain ⟨m', rfl⟩ := succ_le_succ hle; exact .lam heq
  | app_ok hf ha hap =>
    obtain ⟨m', rfl⟩ := succ_le_succ hle
    exact .app_ok (Eval.fuel_mono hf (by omega) trivial)
      (EvalArgs.fuel_mono ha (by omega) trivial) (ApplyFunc.fuel_mono hap (by omega) hnf)
  | app_func_signal hf hs =>
    obtain ⟨m', rfl⟩ := succ_le_succ hle
    exact .app_func_signal (Eval.fuel_mono hf (by omega) hnf) hs
  | app_args_signal hf ha hs =>
    obtain ⟨m', rfl⟩ := succ_le_succ hle
    exact .app_args_signal (Eval.fuel_mono hf (by omega) trivial)
      (EvalArgs.fuel_mono ha (by omega) hnf) hs
  | binOp_ok hl hr heq =>
    obtain ⟨m', rfl⟩ := succ_le_succ hle
    exact .binOp_ok (Eval.fuel_mono hl (by omega) trivial)
      (Eval.fuel_mono hr (by omega) trivial) heq
  | binOp_left_signal hl hs =>
    obtain ⟨m', rfl⟩ := succ_le_succ hle
    exact .binOp_left_signal (Eval.fuel_mono hl (by omega) hnf) hs
  | binOp_right_signal hl hr hs =>
    obtain ⟨m', rfl⟩ := succ_le_succ hle
    exact .binOp_right_signal (Eval.fuel_mono hl (by omega) trivial)
      (Eval.fuel_mono hr (by omega) hnf) hs
  | unaryOp_ok ha heq =>
    obtain ⟨m', rfl⟩ := succ_le_succ hle
    exact .unaryOp_ok (Eval.fuel_mono ha (by omega) trivial) heq
  | unaryOp_signal ha hs =>
    obtain ⟨m', rfl⟩ := succ_le_succ hle
    exact .unaryOp_signal (Eval.fuel_mono ha (by omega) hnf) hs
  | mkRef_ok hv halloc =>
    obtain ⟨m', rfl⟩ := succ_le_succ hle
    exact .mkRef_ok (Eval.fuel_mono hv (by omega) trivial) halloc
  | mkRef_signal hv hs =>
    obtain ⟨m', rfl⟩ := succ_le_succ hle
    exact .mkRef_signal (Eval.fuel_mono hv (by omega) hnf) hs
  | deref_ok hr hread =>
    obtain ⟨m', rfl⟩ := succ_le_succ hle
    exact .deref_ok (Eval.fuel_mono hr (by omega) trivial) hread
  | deref_dangling hr hread =>
    obtain ⟨m', rfl⟩ := succ_le_succ hle
    exact .deref_dangling (Eval.fuel_mono hr (by omega) trivial) hread
  | deref_non_ref hr hne =>
    obtain ⟨m', rfl⟩ := succ_le_succ hle
    exact .deref_non_ref (Eval.fuel_mono hr (by omega) trivial) hne
  | deref_signal hr hs =>
    obtain ⟨m', rfl⟩ := succ_le_succ hle
    exact .deref_signal (Eval.fuel_mono hr (by omega) hnf) hs
  | assign_ok hr hv hw =>
    obtain ⟨m', rfl⟩ := succ_le_succ hle
    exact .assign_ok (Eval.fuel_mono hr (by omega) trivial)
      (Eval.fuel_mono hv (by omega) trivial) hw
  | assign_dangling hr hv hw =>
    obtain ⟨m', rfl⟩ := succ_le_succ hle
    exact .assign_dangling (Eval.fuel_mono hr (by omega) trivial)
      (Eval.fuel_mono hv (by omega) trivial) hw
  | assign_val_signal hr hv hs =>
    obtain ⟨m', rfl⟩ := succ_le_succ hle
    exact .assign_val_signal (Eval.fuel_mono hr (by omega) trivial)
      (Eval.fuel_mono hv (by omega) hnf) hs
  | assign_non_ref hr hne =>
    obtain ⟨m', rfl⟩ := succ_le_succ hle
    exact .assign_non_ref (Eval.fuel_mono hr (by omega) trivial) hne
  | assign_ref_signal hr hs =>
    obtain ⟨m', rfl⟩ := succ_le_succ hle
    exact .assign_ref_signal (Eval.fuel_mono hr (by omega) hnf) hs
  | record hf =>
    obtain ⟨m', rfl⟩ := succ_le_succ hle
    exact .record (EvalFields.fuel_mono hf (by omega) hnf)
  | project_record_ok he hl =>
    obtain ⟨m', rfl⟩ := succ_le_succ hle
    exact .project_record_ok (Eval.fuel_mono he (by omega) trivial) hl
  | project_record_missing he hn =>
    obtain ⟨m', rfl⟩ := succ_le_succ hle
    exact .project_record_missing (Eval.fuel_mono he (by omega) trivial) hn
  | project_constructed_tag he ht =>
    obtain ⟨m', rfl⟩ := succ_le_succ hle
    exact .project_constructed_tag (Eval.fuel_mono he (by omega) trivial) ht
  | project_constructed_other he hne =>
    obtain ⟨m', rfl⟩ := succ_le_succ hle
    exact .project_constructed_other (Eval.fuel_mono he (by omega) trivial) hne
  | project_non_record he hne hnc =>
    obtain ⟨m', rfl⟩ := succ_le_succ hle
    exact .project_non_record (Eval.fuel_mono he (by omega) trivial) hne hnc
  | project_signal he hs =>
    obtain ⟨m', rfl⟩ := succ_le_succ hle
    exact .project_signal (Eval.fuel_mono he (by omega) hnf) hs
  | projectIdx_string_record_ok he hi hrv hl =>
    obtain ⟨m', rfl⟩ := succ_le_succ hle
    exact .projectIdx_string_record_ok (Eval.fuel_mono he (by omega) trivial)
      (Eval.fuel_mono hi (by omega) trivial) hrv hl
  | projectIdx_string_record_missing he hi hrv hn =>
    obtain ⟨m', rfl⟩ := succ_le_succ hle
    exact .projectIdx_string_record_missing (Eval.fuel_mono he (by omega) trivial)
      (Eval.fuel_mono hi (by omega) trivial) hrv hn
  | projectIdx_string_non_record he hi hne =>
    obtain ⟨m', rfl⟩ := succ_le_succ hle
    exact .projectIdx_string_non_record (Eval.fuel_mono he (by omega) trivial)
      (Eval.fuel_mono hi (by omega) trivial) hne
  | projectIdx_number_array_ok he hi hrv hidx hlt =>
    obtain ⟨m', rfl⟩ := succ_le_succ hle
    exact .projectIdx_number_array_ok (Eval.fuel_mono he (by omega) trivial)
      (Eval.fuel_mono hi (by omega) trivial) hrv hidx hlt
  | projectIdx_number_array_oob he hi hrv hge =>
    obtain ⟨m', rfl⟩ := succ_le_succ hle
    exact .projectIdx_number_array_oob (Eval.fuel_mono he (by omega) trivial)
      (Eval.fuel_mono hi (by omega) trivial) hrv hge
  | projectIdx_number_non_array he hi hne =>
    obtain ⟨m', rfl⟩ := succ_le_succ hle
    exact .projectIdx_number_non_array (Eval.fuel_mono he (by omega) trivial)
      (Eval.fuel_mono hi (by omega) trivial) hne
  | projectIdx_bad_index he hi hns hnn =>
    obtain ⟨m', rfl⟩ := succ_le_succ hle
    exact .projectIdx_bad_index (Eval.fuel_mono he (by omega) trivial)
      (Eval.fuel_mono hi (by omega) trivial) hns hnn
  | projectIdx_idx_signal he hi hs =>
    obtain ⟨m', rfl⟩ := succ_le_succ hle
    exact .projectIdx_idx_signal (Eval.fuel_mono he (by omega) trivial)
      (Eval.fuel_mono hi (by omega) hnf) hs
  | projectIdx_expr_signal he hs =>
    obtain ⟨m', rfl⟩ := succ_le_succ hle
    exact .projectIdx_expr_signal (Eval.fuel_mono he (by omega) hnf) hs
  | array hf =>
    obtain ⟨m', rfl⟩ := succ_le_succ hle
    exact .array (EvalElems.fuel_mono hf (by omega) hnf)
  | index_ok ha hi hidx hlt =>
    obtain ⟨m', rfl⟩ := succ_le_succ hle
    exact .index_ok (Eval.fuel_mono ha (by omega) trivial)
      (Eval.fuel_mono hi (by omega) trivial) hidx hlt
  | index_oob ha hi hge =>
    obtain ⟨m', rfl⟩ := succ_le_succ hle
    exact .index_oob (Eval.fuel_mono ha (by omega) trivial)
      (Eval.fuel_mono hi (by omega) trivial) hge
  | index_bad_idx ha hi hne =>
    obtain ⟨m', rfl⟩ := succ_le_succ hle
    exact .index_bad_idx (Eval.fuel_mono ha (by omega) trivial)
      (Eval.fuel_mono hi (by omega) trivial) hne
  | index_idx_signal ha hi hs =>
    obtain ⟨m', rfl⟩ := succ_le_succ hle
    exact .index_idx_signal (Eval.fuel_mono ha (by omega) trivial)
      (Eval.fuel_mono hi (by omega) hnf) hs
  | index_non_array ha hne =>
    obtain ⟨m', rfl⟩ := succ_le_succ hle
    exact .index_non_array (Eval.fuel_mono ha (by omega) trivial) hne
  | index_arr_signal ha hs =>
    obtain ⟨m', rfl⟩ := succ_le_succ hle
    exact .index_arr_signal (Eval.fuel_mono ha (by omega) hnf) hs
  | if_true hc ht he =>
    obtain ⟨m', rfl⟩ := succ_le_succ hle
    exact .if_true (Eval.fuel_mono hc (by omega) trivial) ht
      (Eval.fuel_mono he (by omega) hnf)
  | if_false hc ht he =>
    obtain ⟨m', rfl⟩ := succ_le_succ hle
    exact .if_false (Eval.fuel_mono hc (by omega) trivial) ht
      (Eval.fuel_mono he (by omega) hnf)
  | if_signal hc hs =>
    obtain ⟨m', rfl⟩ := succ_le_succ hle
    exact .if_signal (Eval.fuel_mono hc (by omega) hnf) hs
  | ternary_true hc ht he =>
    obtain ⟨m', rfl⟩ := succ_le_succ hle
    exact .ternary_true (Eval.fuel_mono hc (by omega) trivial) ht
      (Eval.fuel_mono he (by omega) hnf)
  | ternary_false hc ht he =>
    obtain ⟨m', rfl⟩ := succ_le_succ hle
    exact .ternary_false (Eval.fuel_mono hc (by omega) trivial) ht
      (Eval.fuel_mono he (by omega) hnf)
  | ternary_signal hc hs =>
    obtain ⟨m', rfl⟩ := succ_le_succ hle
    exact .ternary_signal (Eval.fuel_mono hc (by omega) hnf) hs
  | loop hl =>
    obtain ⟨m', rfl⟩ := succ_le_succ hle
    exact .loop (EvalLoop.fuel_mono hl (by omega) hnf)
  | seq hs =>
    obtain ⟨m', rfl⟩ := succ_le_succ hle
    exact .seq (EvalSeq.fuel_mono hs (by omega) hnf)
  | return_ok he =>
    obtain ⟨m', rfl⟩ := succ_le_succ hle
    exact .return_ok (Eval.fuel_mono he (by omega) trivial)
  | return_signal he hs =>
    obtain ⟨m', rfl⟩ := succ_le_succ hle
    exact .return_signal (Eval.fuel_mono he (by omega) hnf) hs
  | «break» => obtain ⟨m', rfl⟩ := succ_le_succ hle; exact .break
  | «continue» => obtain ⟨m', rfl⟩ := succ_le_succ hle; exact .continue
  | throw_ok he =>
    obtain ⟨m', rfl⟩ := succ_le_succ hle
    exact .throw_ok (Eval.fuel_mono he (by omega) trivial)
  | throw_signal he hs =>
    obtain ⟨m', rfl⟩ := succ_le_succ hle
    exact .throw_signal (Eval.fuel_mono he (by omega) hnf) hs
  | tryCatch_ok_no_fin hb hnt =>
    obtain ⟨m', rfl⟩ := succ_le_succ hle
    exact .tryCatch_ok_no_fin (Eval.fuel_mono hb (by omega) hnf) hnt
  | tryCatch_throw_no_fin hb hce hh =>
    obtain ⟨m', rfl⟩ := succ_le_succ hle
    exact .tryCatch_throw_no_fin (Eval.fuel_mono hb (by omega) trivial) hce
      (Eval.fuel_mono hh (by omega) hnf)
  | tryCatch_ok_fin_ok hb hnt hac hfs hfin hres =>
    obtain ⟨m', rfl⟩ := succ_le_succ hle
    exact .tryCatch_ok_fin_ok
      (Eval.fuel_mono hb (by omega) (hac ▸ notFuelError_of_tryCatch_match hres hnf))
      hnt hac hfs (Eval.fuel_mono hfin (by omega) trivial) hres
  | tryCatch_throw_fin_ok hb hce hh hfs hfin hres =>
    obtain ⟨m', rfl⟩ := succ_le_succ hle
    exact .tryCatch_throw_fin_ok (Eval.fuel_mono hb (by omega) trivial) hce
      (Eval.fuel_mono hh (by omega) (notFuelError_of_tryCatch_match hres hnf))
      hfs (Eval.fuel_mono hfin (by omega) trivial) hres
  | tryCatch_ok_fin_signal hb hnt hnfe hfs hfin hs =>
    obtain ⟨m', rfl⟩ := succ_le_succ hle
    exact .tryCatch_ok_fin_signal (Eval.fuel_mono hb (by omega) hnfe) hnt hnfe hfs
      (Eval.fuel_mono hfin (by omega) hnf) hs
  | tryCatch_throw_fin_signal hb hce hh hnfe hfs hfin hs =>
    obtain ⟨m', rfl⟩ := succ_le_succ hle
    exact .tryCatch_throw_fin_signal (Eval.fuel_mono hb (by omega) trivial) hce
      (Eval.fuel_mono hh (by omega) hnfe) hnfe hfs
      (Eval.fuel_mono hfin (by omega) hnf) hs
  | «match» hs hm =>
    obtain ⟨m', rfl⟩ := succ_le_succ hle
    exact .match (Eval.fuel_mono hs (by omega) trivial)
      (EvalMatch.fuel_mono hm (by omega) hnf)
  | match_signal hs hsig =>
    obtain ⟨m', rfl⟩ := succ_le_succ hle
    exact .match_signal (Eval.fuel_mono hs (by omega) hnf) hsig
  | construct_ok ha =>
    obtain ⟨m', rfl⟩ := succ_le_succ hle
    exact .construct_ok (EvalArgs.fuel_mono ha (by omega) trivial)
  | construct_signal ha hs =>
    obtain ⟨m', rfl⟩ := succ_le_succ hle
    exact .construct_signal (EvalArgs.fuel_mono ha (by omega) hnf) hs
  | newObj_ok hf ha hap =>
    obtain ⟨m', rfl⟩ := succ_le_succ hle
    exact .newObj_ok (Eval.fuel_mono hf (by omega) trivial)
      (EvalArgs.fuel_mono ha (by omega) trivial) (ApplyFunc.fuel_mono hap (by omega) hnf)
  | newObj_callee_signal hf hs =>
    obtain ⟨m', rfl⟩ := succ_le_succ hle
    exact .newObj_callee_signal (Eval.fuel_mono hf (by omega) hnf) hs
  | newObj_args_signal hf ha hs =>
    obtain ⟨m', rfl⟩ := succ_le_succ hle
    exact .newObj_args_signal (Eval.fuel_mono hf (by omega) trivial)
      (EvalArgs.fuel_mono ha (by omega) hnf) hs
  | «await» he =>
    obtain ⟨m', rfl⟩ := succ_le_succ hle
    exact .await (Eval.fuel_mono he (by omega) hnf)
  | yield_some he =>
    obtain ⟨m', rfl⟩ := succ_le_succ hle
    exact .yield_some (Eval.fuel_mono he (by omega) hnf)
  | yield_none => obtain ⟨m', rfl⟩ := succ_le_succ hle; exact .yield_none
  | spread he =>
    obtain ⟨m', rfl⟩ := succ_le_succ hle
    exact .spread (Eval.fuel_mono he (by omega) hnf)
  termination_by (n, 0)
  decreasing_by
    all_goals simp_wf
    all_goals first
      | apply Prod.Lex.left; omega
      | (apply Prod.Lex.right; subst_vars; simp [List.length_cons]; try omega)

def EvalArgs.fuel_mono
    (h : EvalArgs env store n args acc r) (hle : n ≤ m) (hnf : notFuelError r) :
    EvalArgs env store m args acc r := by
  cases h with
  | nil => exact .nil
  | cons_ok ha hr =>
    exact .cons_ok (Eval.fuel_mono ha hle trivial) (EvalArgs.fuel_mono hr hle hnf)
  | cons_signal ha hs =>
    exact .cons_signal (Eval.fuel_mono ha hle hnf) hs
  termination_by (n, args.length)
  decreasing_by
    all_goals simp_wf
    all_goals first
      | apply Prod.Lex.left; omega
      | (apply Prod.Lex.right; subst_vars; simp [List.length_cons]; try omega)

def ApplyFunc.fuel_mono
    (h : ApplyFunc fv args store n r) (hle : n ≤ m) (hnf : notFuelError r) :
    ApplyFunc fv args store m r := by
  cases h with
  | closure_ok henv henv' heval hres =>
    exact .closure_ok henv henv'
      (Eval.fuel_mono heval hle (notFuelError_of_return_match hres hnf)) hres
  | non_function hne => exact .non_function hne
  termination_by (n, 1)
  decreasing_by
    all_goals simp_wf
    all_goals first
      | apply Prod.Lex.left; omega
      | (apply Prod.Lex.right; subst_vars; simp [List.length_cons]; try omega)

def EvalFields.fuel_mono
    (h : EvalFields env store n fields acc r) (hle : n ≤ m) (hnf : notFuelError r) :
    EvalFields env store m fields acc r := by
  cases h with
  | nil => exact .nil
  | cons_ok he hr =>
    exact .cons_ok (Eval.fuel_mono he hle trivial) (EvalFields.fuel_mono hr hle hnf)
  | cons_signal he hs =>
    exact .cons_signal (Eval.fuel_mono he hle hnf) hs
  termination_by (n, fields.length)
  decreasing_by
    all_goals simp_wf
    all_goals first
      | apply Prod.Lex.left; omega
      | (apply Prod.Lex.right; subst_vars; simp [List.length_cons]; try omega)

def EvalElems.fuel_mono
    (h : EvalElems env store n elems acc r) (hle : n ≤ m) (hnf : notFuelError r) :
    EvalElems env store m elems acc r := by
  cases h with
  | nil => exact .nil
  | cons_ok he hr =>
    exact .cons_ok (Eval.fuel_mono he hle trivial) (EvalElems.fuel_mono hr hle hnf)
  | cons_signal he hs =>
    exact .cons_signal (Eval.fuel_mono he hle hnf) hs
  termination_by (n, elems.length)
  decreasing_by
    all_goals simp_wf
    all_goals first
      | apply Prod.Lex.left; omega
      | (apply Prod.Lex.right; subst_vars; simp [List.length_cons]; try omega)

def EvalLoop.fuel_mono
    (h : EvalLoop env store n condE body r) (hle : n ≤ m) (hnf : notFuelError r) :
    EvalLoop env store m condE body r := by
  cases h with
  | fuel_zero => exact absurd hnf id
  | cond_false hc ht =>
    obtain ⟨m', rfl⟩ := succ_le_succ hle
    exact .cond_false (Eval.fuel_mono hc (by omega) trivial) ht
  | body_val hc ht hb hl =>
    obtain ⟨m', rfl⟩ := succ_le_succ hle
    exact .body_val (Eval.fuel_mono hc (by omega) trivial) ht
      (Eval.fuel_mono hb (by omega) trivial) (EvalLoop.fuel_mono hl (by omega) hnf)
  | body_continue hc ht hb hl =>
    obtain ⟨m', rfl⟩ := succ_le_succ hle
    exact .body_continue (Eval.fuel_mono hc (by omega) trivial) ht
      (Eval.fuel_mono hb (by omega) trivial) (EvalLoop.fuel_mono hl (by omega) hnf)
  | body_break hc ht hb =>
    obtain ⟨m', rfl⟩ := succ_le_succ hle
    exact .body_break (Eval.fuel_mono hc (by omega) trivial) ht
      (Eval.fuel_mono hb (by omega) trivial)
  | body_other hc ht hb hnv hnc hnb =>
    obtain ⟨m', rfl⟩ := succ_le_succ hle
    exact .body_other (Eval.fuel_mono hc (by omega) trivial) ht
      (Eval.fuel_mono hb (by omega) hnf) hnv hnc hnb
  | cond_signal hc hs =>
    obtain ⟨m', rfl⟩ := succ_le_succ hle
    exact .cond_signal (Eval.fuel_mono hc (by omega) hnf) hs
  termination_by (n, 0)
  decreasing_by
    all_goals simp_wf
    all_goals first
      | apply Prod.Lex.left; omega
      | (apply Prod.Lex.right; subst_vars; simp [List.length_cons]; try omega)

def EvalSeq.fuel_mono
    (h : EvalSeq env store n exprs r) (hle : n ≤ m) (hnf : notFuelError r) :
    EvalSeq env store m exprs r := by
  cases h with
  | nil => exact .nil
  | singleton he =>
    exact .singleton (Eval.fuel_mono he hle hnf)
  | cons_ok he hr hne =>
    exact .cons_ok (Eval.fuel_mono he hle trivial) (EvalSeq.fuel_mono hr hle hnf) hne
  | cons_signal he hs hne =>
    exact .cons_signal (Eval.fuel_mono he hle hnf) hs hne
  termination_by (n, exprs.length)
  decreasing_by
    all_goals simp_wf
    all_goals first
      | apply Prod.Lex.left; omega
      | (apply Prod.Lex.right; subst_vars; simp [List.length_cons]; try omega)

def EvalMatch.fuel_mono
    (h : EvalMatch env store n scrutinee cases r) (hle : n ≤ m) (hnf : notFuelError r) :
    EvalMatch env store m scrutinee cases r := by
  cases h with
  | no_cases => exact .no_cases
  | match_ok hm he =>
    exact .match_ok hm (Eval.fuel_mono he hle hnf)
  | match_fail hm hr =>
    exact .match_fail hm (EvalMatch.fuel_mono hr hle hnf)
  termination_by (n, cases.length)
  decreasing_by
    all_goals simp_wf
    all_goals first
      | apply Prod.Lex.left; omega
      | (apply Prod.Lex.right; subst_vars; simp [List.length_cons]; try omega)

end

-- Wrapper theorems
theorem eval_fuel_mono (h : Eval env store n e r) (hle : n ≤ m) (hnf : notFuelError r) :
    Eval env store m e r := Eval.fuel_mono h hle hnf

end LeanJS.Semantics
