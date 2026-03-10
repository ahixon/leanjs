/-
  Determinism of the big-step evaluation relation.

  If `Eval env store fuel e r1` and `Eval env store fuel e r2` then `r1 = r2`.
  Proved by mutual well-founded recursion on fuel.
-/
import LeanJS.Semantics.Relation

set_option autoImplicit true

namespace LeanJS.Semantics

open LeanJS.IR

-- Helper: signal and val are contradictory
private theorem signal_val_absurd {r : EvalResult} (hs : isSignal r) (heq : r = .val v s) : False := by
  subst heq; exact hs

set_option maxHeartbeats 12800000 in
set_option maxRecDepth 2048 in
mutual

def Eval.deterministic
    (h1 : Eval env store fuel e r1) (h2 : Eval env store fuel e r2) : r1 = r2 := by
  cases h1 with
  | fuel_zero => cases h2 with | fuel_zero => rfl
  | lit => cases h2 with | lit => rfl
  | var_ok h => cases h2 with
    | var_ok h2 => rw [h] at h2; cases h2; rfl
    | var_unbound h2 => rw [h] at h2; cases h2
  | var_unbound h => cases h2 with
    | var_ok h2 => rw [h] at h2; cases h2
    | var_unbound => rfl
  | undefined => cases h2 with | undefined => rfl
  | this_ok h => cases h2 with
    | this_ok h2 => rw [h] at h2; cases h2; rfl
    | this_none h2 => rw [h] at h2; cases h2
  | this_none h => cases h2 with
    | this_ok h2 => rw [h] at h2; cases h2
    | this_none => rfl
  | let_ok hv1 hb1 =>
    cases h2 with
    | let_ok hv2 hb2 =>
      have := Eval.deterministic hv1 hv2; cases this
      exact Eval.deterministic hb1 hb2
    | let_signal hv2 hs =>
      have := Eval.deterministic hv1 hv2; subst this; simp [isSignal] at hs
  | let_signal hv1 hs1 =>
    cases h2 with
    | let_ok hv2 _ =>
      have := Eval.deterministic hv1 hv2; subst this; simp [isSignal] at hs1
    | let_signal hv2 _ => exact Eval.deterministic hv1 hv2
  | lam heq =>
    cases h2 with
    | lam heq2 => subst heq; subst heq2; rfl
  | app_ok hf1 ha1 hap1 =>
    cases h2 with
    | app_ok hf2 ha2 hap2 =>
      have := Eval.deterministic hf1 hf2; cases this
      have := EvalArgs.deterministic ha1 ha2; cases this
      exact ApplyFunc.deterministic hap1 hap2
    | app_func_signal hf2 hs =>
      have := Eval.deterministic hf1 hf2; subst this; simp [isSignal] at hs
    | app_args_signal hf2 ha2 hs =>
      have := Eval.deterministic hf1 hf2; cases this
      have := EvalArgs.deterministic ha1 ha2; subst this; simp [isSignal] at hs
  | app_func_signal hf1 hs1 =>
    cases h2 with
    | app_ok hf2 _ _ =>
      have := Eval.deterministic hf1 hf2; subst this; simp [isSignal] at hs1
    | app_func_signal hf2 _ => exact Eval.deterministic hf1 hf2
    | app_args_signal hf2 _ _ =>
      have := Eval.deterministic hf1 hf2; subst this; simp [isSignal] at hs1
  | app_args_signal hf1 ha1 hs1 =>
    cases h2 with
    | app_ok hf2 ha2 _ =>
      have := Eval.deterministic hf1 hf2; cases this
      have := EvalArgs.deterministic ha1 ha2; subst this; simp [isSignal] at hs1
    | app_func_signal hf2 hs =>
      have := Eval.deterministic hf1 hf2; subst this; simp [isSignal] at hs
    | app_args_signal hf2 ha2 _ =>
      have := Eval.deterministic hf1 hf2; cases this
      exact EvalArgs.deterministic ha1 ha2
  | binOp_ok hl1 hr1 heq1 =>
    cases h2 with
    | binOp_ok hl2 hr2 heq2 =>
      have := Eval.deterministic hl1 hl2; cases this
      have := Eval.deterministic hr1 hr2; cases this
      rw [← heq1, ← heq2]
    | binOp_left_signal hl2 hs =>
      have := Eval.deterministic hl1 hl2; subst this; simp [isSignal] at hs
    | binOp_right_signal hl2 hr2 hs =>
      have := Eval.deterministic hl1 hl2; cases this
      have := Eval.deterministic hr1 hr2; subst this; simp [isSignal] at hs
  | binOp_left_signal hl1 hs1 =>
    cases h2 with
    | binOp_ok hl2 _ _ =>
      have := Eval.deterministic hl1 hl2; subst this; simp [isSignal] at hs1
    | binOp_left_signal hl2 _ => exact Eval.deterministic hl1 hl2
    | binOp_right_signal hl2 _ _ =>
      have := Eval.deterministic hl1 hl2; subst this; simp [isSignal] at hs1
  | binOp_right_signal hl1 hr1 hs1 =>
    cases h2 with
    | binOp_ok hl2 hr2 _ =>
      have := Eval.deterministic hl1 hl2; cases this
      have := Eval.deterministic hr1 hr2; subst this; simp [isSignal] at hs1
    | binOp_left_signal hl2 hs =>
      have := Eval.deterministic hl1 hl2; subst this; simp [isSignal] at hs
    | binOp_right_signal hl2 hr2 _ =>
      have := Eval.deterministic hl1 hl2; cases this
      exact Eval.deterministic hr1 hr2
  | unaryOp_ok ha1 heq1 =>
    cases h2 with
    | unaryOp_ok ha2 heq2 =>
      have := Eval.deterministic ha1 ha2; cases this; rw [← heq1, ← heq2]
    | unaryOp_signal ha2 hs =>
      have := Eval.deterministic ha1 ha2; subst this; simp [isSignal] at hs
  | unaryOp_signal ha1 hs1 =>
    cases h2 with
    | unaryOp_ok ha2 _ =>
      have := Eval.deterministic ha1 ha2; subst this; simp [isSignal] at hs1
    | unaryOp_signal ha2 _ => exact Eval.deterministic ha1 ha2
  | mkRef_ok hv1 halloc1 =>
    cases h2 with
    | mkRef_ok hv2 halloc2 =>
      have := Eval.deterministic hv1 hv2; cases this
      rw [halloc1] at halloc2; cases halloc2; rfl
    | mkRef_signal hv2 hs =>
      have := Eval.deterministic hv1 hv2; subst this; simp [isSignal] at hs
  | mkRef_signal hv1 hs1 =>
    cases h2 with
    | mkRef_ok hv2 _ =>
      have := Eval.deterministic hv1 hv2; subst this; simp [isSignal] at hs1
    | mkRef_signal hv2 _ => exact Eval.deterministic hv1 hv2
  | deref_ok hr1 hread1 =>
    cases h2 with
    | deref_ok hr2 hread2 =>
      have := Eval.deterministic hr1 hr2; cases this; rw [hread1] at hread2; cases hread2; rfl
    | deref_dangling hr2 hread2 =>
      have := Eval.deterministic hr1 hr2; cases this; rw [hread1] at hread2; cases hread2
    | deref_non_ref hr2 hne =>
      have := Eval.deterministic hr1 hr2; cases this; exact absurd rfl (hne _)
    | deref_signal hr2 hs =>
      have := Eval.deterministic hr1 hr2; subst this; simp [isSignal] at hs
  | deref_dangling hr1 hread1 =>
    cases h2 with
    | deref_ok hr2 hread2 =>
      have := Eval.deterministic hr1 hr2; cases this; rw [hread1] at hread2; cases hread2
    | deref_dangling hr2 _ => have := Eval.deterministic hr1 hr2; cases this; rfl
    | deref_non_ref hr2 hne =>
      have := Eval.deterministic hr1 hr2; cases this; exact absurd rfl (hne _)
    | deref_signal hr2 hs =>
      have := Eval.deterministic hr1 hr2; subst this; simp [isSignal] at hs
  | deref_non_ref hr1 hne1 =>
    cases h2 with
    | deref_ok hr2 _ =>
      have := Eval.deterministic hr1 hr2; cases this; exact absurd rfl (hne1 _)
    | deref_dangling hr2 _ =>
      have := Eval.deterministic hr1 hr2; cases this; exact absurd rfl (hne1 _)
    | deref_non_ref hr2 _ => have := Eval.deterministic hr1 hr2; cases this; rfl
    | deref_signal hr2 hs =>
      have := Eval.deterministic hr1 hr2; subst this; simp [isSignal] at hs
  | deref_signal hr1 hs1 =>
    cases h2 with
    | deref_ok hr2 _ =>
      have := Eval.deterministic hr1 hr2; subst this; simp [isSignal] at hs1
    | deref_dangling hr2 _ =>
      have := Eval.deterministic hr1 hr2; subst this; simp [isSignal] at hs1
    | deref_non_ref hr2 _ =>
      have := Eval.deterministic hr1 hr2; subst this; simp [isSignal] at hs1
    | deref_signal hr2 _ => exact Eval.deterministic hr1 hr2
  | assign_ok hr1 hv1 hw1 =>
    cases h2 with
    | assign_ok hr2 hv2 hw2 =>
      have := Eval.deterministic hr1 hr2; cases this
      have := Eval.deterministic hv1 hv2; cases this
      rw [hw1] at hw2; cases hw2; rfl
    | assign_dangling hr2 hv2 hw2 =>
      have := Eval.deterministic hr1 hr2; cases this
      have := Eval.deterministic hv1 hv2; cases this
      rw [hw1] at hw2; cases hw2
    | assign_val_signal hr2 hv2 hs =>
      have := Eval.deterministic hr1 hr2; cases this
      have := Eval.deterministic hv1 hv2; subst this; simp [isSignal] at hs
    | assign_non_ref hr2 hne =>
      have := Eval.deterministic hr1 hr2; cases this; exact absurd rfl (hne _)
    | assign_ref_signal hr2 hs =>
      have := Eval.deterministic hr1 hr2; subst this; simp [isSignal] at hs
  | assign_dangling hr1 hv1 hw1 =>
    cases h2 with
    | assign_ok hr2 hv2 hw2 =>
      have := Eval.deterministic hr1 hr2; cases this
      have := Eval.deterministic hv1 hv2; cases this
      rw [hw1] at hw2; cases hw2
    | assign_dangling hr2 hv2 _ =>
      have := Eval.deterministic hr1 hr2; cases this
      have := Eval.deterministic hv1 hv2; cases this; rfl
    | assign_val_signal hr2 hv2 hs =>
      have := Eval.deterministic hr1 hr2; cases this
      have := Eval.deterministic hv1 hv2; subst this; simp [isSignal] at hs
    | assign_non_ref hr2 hne =>
      have := Eval.deterministic hr1 hr2; cases this; exact absurd rfl (hne _)
    | assign_ref_signal hr2 hs =>
      have := Eval.deterministic hr1 hr2; subst this; simp [isSignal] at hs
  | assign_val_signal hr1 hv1 hs1 =>
    cases h2 with
    | assign_ok hr2 hv2 _ =>
      have := Eval.deterministic hr1 hr2; cases this
      have := Eval.deterministic hv1 hv2; subst this; simp [isSignal] at hs1
    | assign_dangling hr2 hv2 _ =>
      have := Eval.deterministic hr1 hr2; cases this
      have := Eval.deterministic hv1 hv2; subst this; simp [isSignal] at hs1
    | assign_val_signal hr2 hv2 _ =>
      have := Eval.deterministic hr1 hr2; cases this
      exact Eval.deterministic hv1 hv2
    | assign_non_ref hr2 hne =>
      have := Eval.deterministic hr1 hr2; cases this; exact absurd rfl (hne _)
    | assign_ref_signal hr2 hs =>
      have := Eval.deterministic hr1 hr2; subst this; simp [isSignal] at hs
  | assign_non_ref hr1 hne1 =>
    cases h2 with
    | assign_ok hr2 _ _ =>
      have := Eval.deterministic hr1 hr2; cases this; exact absurd rfl (hne1 _)
    | assign_dangling hr2 _ _ =>
      have := Eval.deterministic hr1 hr2; cases this; exact absurd rfl (hne1 _)
    | assign_val_signal hr2 _ _ =>
      have := Eval.deterministic hr1 hr2; cases this; exact absurd rfl (hne1 _)
    | assign_non_ref hr2 _ => have := Eval.deterministic hr1 hr2; cases this; rfl
    | assign_ref_signal hr2 hs =>
      have := Eval.deterministic hr1 hr2; subst this; simp [isSignal] at hs
  | assign_ref_signal hr1 hs1 =>
    cases h2 with
    | assign_ok hr2 _ _ =>
      have := Eval.deterministic hr1 hr2; subst this; simp [isSignal] at hs1
    | assign_dangling hr2 _ _ =>
      have := Eval.deterministic hr1 hr2; subst this; simp [isSignal] at hs1
    | assign_val_signal hr2 _ _ =>
      have := Eval.deterministic hr1 hr2; subst this; simp [isSignal] at hs1
    | assign_non_ref hr2 _ =>
      have := Eval.deterministic hr1 hr2; subst this; simp [isSignal] at hs1
    | assign_ref_signal hr2 _ => exact Eval.deterministic hr1 hr2
  | record hf1 => cases h2 with
    | record hf2 => exact EvalFields.deterministic hf1 hf2
  | project_record_ok he1 hl1 =>
    cases h2 with
    | project_record_ok he2 hl2 =>
      have := Eval.deterministic he1 he2; cases this; rw [hl1] at hl2; cases hl2; rfl
    | project_record_missing he2 hn =>
      have := Eval.deterministic he1 he2; cases this; rw [hl1] at hn; cases hn
    | project_constructed_tag he2 _ => have := Eval.deterministic he1 he2; cases this
    | project_constructed_other he2 _ => have := Eval.deterministic he1 he2; cases this
    | project_non_record he2 hne _ =>
      have := Eval.deterministic he1 he2; cases this; exact absurd rfl (hne _)
    | project_signal he2 hs =>
      have := Eval.deterministic he1 he2; subst this; simp [isSignal] at hs
  | project_record_missing he1 hn1 =>
    cases h2 with
    | project_record_ok he2 hl => have := Eval.deterministic he1 he2; cases this; rw [hn1] at hl; cases hl
    | project_record_missing he2 _ => have := Eval.deterministic he1 he2; cases this; rfl
    | project_constructed_tag he2 _ => have := Eval.deterministic he1 he2; cases this
    | project_constructed_other he2 _ => have := Eval.deterministic he1 he2; cases this
    | project_non_record he2 hne _ =>
      have := Eval.deterministic he1 he2; cases this; exact absurd rfl (hne _)
    | project_signal he2 hs =>
      have := Eval.deterministic he1 he2; subst this; simp [isSignal] at hs
  | project_constructed_tag he1 ht1 =>
    cases h2 with
    | project_record_ok he2 _ => have := Eval.deterministic he1 he2; cases this
    | project_record_missing he2 _ => have := Eval.deterministic he1 he2; cases this
    | project_constructed_tag he2 _ => have := Eval.deterministic he1 he2; cases this; rfl
    | project_constructed_other he2 hne =>
      have := Eval.deterministic he1 he2; cases this; subst ht1; exact absurd rfl hne
    | project_non_record he2 _ hne =>
      have := Eval.deterministic he1 he2; cases this; exact absurd rfl (hne _ _)
    | project_signal he2 hs =>
      have := Eval.deterministic he1 he2; subst this; simp [isSignal] at hs
  | project_constructed_other he1 hne1 =>
    cases h2 with
    | project_record_ok he2 _ => have := Eval.deterministic he1 he2; cases this
    | project_record_missing he2 _ => have := Eval.deterministic he1 he2; cases this
    | project_constructed_tag he2 ht =>
      have := Eval.deterministic he1 he2; cases this; subst ht; exact absurd rfl hne1
    | project_constructed_other he2 _ => have := Eval.deterministic he1 he2; cases this; rfl
    | project_non_record he2 _ hne =>
      have := Eval.deterministic he1 he2; cases this; exact absurd rfl (hne _ _)
    | project_signal he2 hs =>
      have := Eval.deterministic he1 he2; subst this; simp [isSignal] at hs
  | project_non_record he1 hne1 hne1c =>
    cases h2 with
    | project_record_ok he2 _ =>
      have := Eval.deterministic he1 he2; cases this; exact absurd rfl (hne1 _)
    | project_record_missing he2 _ =>
      have := Eval.deterministic he1 he2; cases this; exact absurd rfl (hne1 _)
    | project_constructed_tag he2 _ =>
      have := Eval.deterministic he1 he2; cases this; exact absurd rfl (hne1c _ _)
    | project_constructed_other he2 _ =>
      have := Eval.deterministic he1 he2; cases this; exact absurd rfl (hne1c _ _)
    | project_non_record he2 _ _ => have := Eval.deterministic he1 he2; cases this; rfl
    | project_signal he2 hs =>
      have := Eval.deterministic he1 he2; subst this; simp [isSignal] at hs
  | project_signal he1 hs1 =>
    cases h2 with
    | project_record_ok he2 _ =>
      have := Eval.deterministic he1 he2; subst this; simp [isSignal] at hs1
    | project_record_missing he2 _ =>
      have := Eval.deterministic he1 he2; subst this; simp [isSignal] at hs1
    | project_constructed_tag he2 _ =>
      have := Eval.deterministic he1 he2; subst this; simp [isSignal] at hs1
    | project_constructed_other he2 _ =>
      have := Eval.deterministic he1 he2; subst this; simp [isSignal] at hs1
    | project_non_record he2 _ _ =>
      have := Eval.deterministic he1 he2; subst this; simp [isSignal] at hs1
    | project_signal he2 _ => exact Eval.deterministic he1 he2
  -- projectIdx: 9 cases × counterparts
  | projectIdx_string_record_ok he1 hi1 hrv1 hl1 =>
    cases h2 with
    | projectIdx_string_record_ok he2 hi2 hrv2 hl2 =>
      have := Eval.deterministic he1 he2; cases this
      have := Eval.deterministic hi1 hi2; cases this
      subst hrv1; cases hrv2; rw [hl1] at hl2; cases hl2; rfl
    | projectIdx_string_record_missing he2 hi2 hrv2 hn2 =>
      have := Eval.deterministic he1 he2; cases this
      have := Eval.deterministic hi1 hi2; cases this
      subst hrv1; cases hrv2; rw [hl1] at hn2; cases hn2
    | projectIdx_string_non_record he2 hi2 hne =>
      have := Eval.deterministic he1 he2; cases this
      have := Eval.deterministic hi1 hi2; cases this
      subst hrv1; exact absurd rfl (hne _)
    | projectIdx_number_array_ok he2 hi2 _ _ _ =>
      have := Eval.deterministic he1 he2; cases this
      have := Eval.deterministic hi1 hi2; cases this
    | projectIdx_number_array_oob he2 hi2 _ _ =>
      have := Eval.deterministic he1 he2; cases this
      have := Eval.deterministic hi1 hi2; cases this
    | projectIdx_number_non_array he2 hi2 _ =>
      have := Eval.deterministic he1 he2; cases this
      have := Eval.deterministic hi1 hi2; cases this
    | projectIdx_bad_index he2 hi2 hns hnn =>
      have := Eval.deterministic he1 he2; cases this
      have := Eval.deterministic hi1 hi2; cases this; exact absurd rfl (hns _)
    | projectIdx_idx_signal he2 hi2 hs =>
      have := Eval.deterministic he1 he2; cases this
      have := Eval.deterministic hi1 hi2; subst this; simp [isSignal] at hs
    | projectIdx_expr_signal he2 hs =>
      have := Eval.deterministic he1 he2; subst this; simp [isSignal] at hs
  | projectIdx_string_record_missing he1 hi1 hrv1 hn1 =>
    cases h2 with
    | projectIdx_string_record_ok he2 hi2 hrv2 hl2 =>
      have := Eval.deterministic he1 he2; cases this
      have := Eval.deterministic hi1 hi2; cases this
      subst hrv1; cases hrv2; rw [hn1] at hl2; cases hl2
    | projectIdx_string_record_missing he2 hi2 _ _ =>
      have := Eval.deterministic he1 he2; cases this
      have := Eval.deterministic hi1 hi2; cases this; rfl
    | projectIdx_string_non_record he2 hi2 hne =>
      have := Eval.deterministic he1 he2; cases this
      have := Eval.deterministic hi1 hi2; cases this
      subst hrv1; exact absurd rfl (hne _)
    | projectIdx_number_array_ok he2 hi2 _ _ _ =>
      have := Eval.deterministic he1 he2; cases this
      have := Eval.deterministic hi1 hi2; cases this
    | projectIdx_number_array_oob he2 hi2 _ _ =>
      have := Eval.deterministic he1 he2; cases this
      have := Eval.deterministic hi1 hi2; cases this
    | projectIdx_number_non_array he2 hi2 _ =>
      have := Eval.deterministic he1 he2; cases this
      have := Eval.deterministic hi1 hi2; cases this
    | projectIdx_bad_index he2 hi2 hns _ =>
      have := Eval.deterministic he1 he2; cases this
      have := Eval.deterministic hi1 hi2; cases this; exact absurd rfl (hns _)
    | projectIdx_idx_signal he2 hi2 hs =>
      have := Eval.deterministic he1 he2; cases this
      have := Eval.deterministic hi1 hi2; subst this; simp [isSignal] at hs
    | projectIdx_expr_signal he2 hs =>
      have := Eval.deterministic he1 he2; subst this; simp [isSignal] at hs
  | projectIdx_string_non_record he1 hi1 hne1 =>
    cases h2 with
    | projectIdx_string_record_ok he2 hi2 hrv2 _ =>
      have := Eval.deterministic he1 he2; cases this
      have := Eval.deterministic hi1 hi2; cases this; subst hrv2; exact absurd rfl (hne1 _)
    | projectIdx_string_record_missing he2 hi2 hrv2 _ =>
      have := Eval.deterministic he1 he2; cases this
      have := Eval.deterministic hi1 hi2; cases this; subst hrv2; exact absurd rfl (hne1 _)
    | projectIdx_string_non_record he2 hi2 _ =>
      have := Eval.deterministic he1 he2; cases this
      have := Eval.deterministic hi1 hi2; cases this; rfl
    | projectIdx_number_array_ok he2 hi2 _ _ _ =>
      have := Eval.deterministic he1 he2; cases this
      have := Eval.deterministic hi1 hi2; cases this
    | projectIdx_number_array_oob he2 hi2 _ _ =>
      have := Eval.deterministic he1 he2; cases this
      have := Eval.deterministic hi1 hi2; cases this
    | projectIdx_number_non_array he2 hi2 _ =>
      have := Eval.deterministic he1 he2; cases this
      have := Eval.deterministic hi1 hi2; cases this
    | projectIdx_bad_index he2 hi2 hns _ =>
      have := Eval.deterministic he1 he2; cases this
      have := Eval.deterministic hi1 hi2; cases this; exact absurd rfl (hns _)
    | projectIdx_idx_signal he2 hi2 hs =>
      have := Eval.deterministic he1 he2; cases this
      have := Eval.deterministic hi1 hi2; subst this; simp [isSignal] at hs
    | projectIdx_expr_signal he2 hs =>
      have := Eval.deterministic he1 he2; subst this; simp [isSignal] at hs
  | projectIdx_number_array_ok he1 hi1 hrv1 hidx1 hlt1 =>
    cases h2 with
    | projectIdx_string_record_ok he2 hi2 _ _ =>
      have := Eval.deterministic he1 he2; cases this
      have := Eval.deterministic hi1 hi2; cases this
    | projectIdx_string_record_missing he2 hi2 _ _ =>
      have := Eval.deterministic he1 he2; cases this
      have := Eval.deterministic hi1 hi2; cases this
    | projectIdx_string_non_record he2 hi2 _ =>
      have := Eval.deterministic he1 he2; cases this
      have := Eval.deterministic hi1 hi2; cases this
    | projectIdx_number_array_ok he2 hi2 hrv2 hidx2 hlt2 =>
      have := Eval.deterministic he1 he2; cases this
      have := Eval.deterministic hi1 hi2; cases this
      subst hrv1; cases hrv2; subst hidx1; subst hidx2; rfl
    | projectIdx_number_array_oob he2 hi2 hrv2 hge =>
      have := Eval.deterministic he1 he2; cases this
      have := Eval.deterministic hi1 hi2; cases this
      subst hrv1; cases hrv2; subst hidx1; omega
    | projectIdx_number_non_array he2 hi2 hne =>
      have := Eval.deterministic he1 he2; cases this
      have := Eval.deterministic hi1 hi2; cases this
      subst hrv1; exact absurd rfl (hne _)
    | projectIdx_bad_index he2 hi2 _ hnn =>
      have := Eval.deterministic he1 he2; cases this
      have := Eval.deterministic hi1 hi2; cases this; exact absurd rfl (hnn _)
    | projectIdx_idx_signal he2 hi2 hs =>
      have := Eval.deterministic he1 he2; cases this
      have := Eval.deterministic hi1 hi2; subst this; simp [isSignal] at hs
    | projectIdx_expr_signal he2 hs =>
      have := Eval.deterministic he1 he2; subst this; simp [isSignal] at hs
  | projectIdx_number_array_oob he1 hi1 hrv1 hge1 =>
    cases h2 with
    | projectIdx_string_record_ok he2 hi2 _ _ =>
      have := Eval.deterministic he1 he2; cases this
      have := Eval.deterministic hi1 hi2; cases this
    | projectIdx_string_record_missing he2 hi2 _ _ =>
      have := Eval.deterministic he1 he2; cases this
      have := Eval.deterministic hi1 hi2; cases this
    | projectIdx_string_non_record he2 hi2 _ =>
      have := Eval.deterministic he1 he2; cases this
      have := Eval.deterministic hi1 hi2; cases this
    | projectIdx_number_array_ok he2 hi2 hrv2 hidx2 hlt2 =>
      have := Eval.deterministic he1 he2; cases this
      have := Eval.deterministic hi1 hi2; cases this
      subst hrv1; cases hrv2; subst hidx2; omega
    | projectIdx_number_array_oob he2 hi2 _ _ =>
      have := Eval.deterministic he1 he2; cases this
      have := Eval.deterministic hi1 hi2; cases this; rfl
    | projectIdx_number_non_array he2 hi2 hne =>
      have := Eval.deterministic he1 he2; cases this
      have := Eval.deterministic hi1 hi2; cases this
      subst hrv1; exact absurd rfl (hne _)
    | projectIdx_bad_index he2 hi2 _ hnn =>
      have := Eval.deterministic he1 he2; cases this
      have := Eval.deterministic hi1 hi2; cases this; exact absurd rfl (hnn _)
    | projectIdx_idx_signal he2 hi2 hs =>
      have := Eval.deterministic he1 he2; cases this
      have := Eval.deterministic hi1 hi2; subst this; simp [isSignal] at hs
    | projectIdx_expr_signal he2 hs =>
      have := Eval.deterministic he1 he2; subst this; simp [isSignal] at hs
  | projectIdx_number_non_array he1 hi1 hne1 =>
    cases h2 with
    | projectIdx_string_record_ok he2 hi2 _ _ =>
      have := Eval.deterministic he1 he2; cases this
      have := Eval.deterministic hi1 hi2; cases this
    | projectIdx_string_record_missing he2 hi2 _ _ =>
      have := Eval.deterministic he1 he2; cases this
      have := Eval.deterministic hi1 hi2; cases this
    | projectIdx_string_non_record he2 hi2 _ =>
      have := Eval.deterministic he1 he2; cases this
      have := Eval.deterministic hi1 hi2; cases this
    | projectIdx_number_array_ok he2 hi2 hrv2 _ _ =>
      have := Eval.deterministic he1 he2; cases this
      have := Eval.deterministic hi1 hi2; cases this; subst hrv2; exact absurd rfl (hne1 _)
    | projectIdx_number_array_oob he2 hi2 hrv2 _ =>
      have := Eval.deterministic he1 he2; cases this
      have := Eval.deterministic hi1 hi2; cases this; subst hrv2; exact absurd rfl (hne1 _)
    | projectIdx_number_non_array he2 hi2 _ =>
      have := Eval.deterministic he1 he2; cases this
      have := Eval.deterministic hi1 hi2; cases this; rfl
    | projectIdx_bad_index he2 hi2 _ hnn =>
      have := Eval.deterministic he1 he2; cases this
      have := Eval.deterministic hi1 hi2; cases this; exact absurd rfl (hnn _)
    | projectIdx_idx_signal he2 hi2 hs =>
      have := Eval.deterministic he1 he2; cases this
      have := Eval.deterministic hi1 hi2; subst this; simp [isSignal] at hs
    | projectIdx_expr_signal he2 hs =>
      have := Eval.deterministic he1 he2; subst this; simp [isSignal] at hs
  | projectIdx_bad_index he1 hi1 hns1 hnn1 =>
    cases h2 with
    | projectIdx_string_record_ok he2 hi2 _ _ =>
      have := Eval.deterministic he1 he2; cases this
      have := Eval.deterministic hi1 hi2; cases this; exact absurd rfl (hns1 _)
    | projectIdx_string_record_missing he2 hi2 _ _ =>
      have := Eval.deterministic he1 he2; cases this
      have := Eval.deterministic hi1 hi2; cases this; exact absurd rfl (hns1 _)
    | projectIdx_string_non_record he2 hi2 _ =>
      have := Eval.deterministic he1 he2; cases this
      have := Eval.deterministic hi1 hi2; cases this; exact absurd rfl (hns1 _)
    | projectIdx_number_array_ok he2 hi2 _ _ _ =>
      have := Eval.deterministic he1 he2; cases this
      have := Eval.deterministic hi1 hi2; cases this; exact absurd rfl (hnn1 _)
    | projectIdx_number_array_oob he2 hi2 _ _ =>
      have := Eval.deterministic he1 he2; cases this
      have := Eval.deterministic hi1 hi2; cases this; exact absurd rfl (hnn1 _)
    | projectIdx_number_non_array he2 hi2 _ =>
      have := Eval.deterministic he1 he2; cases this
      have := Eval.deterministic hi1 hi2; cases this; exact absurd rfl (hnn1 _)
    | projectIdx_bad_index he2 hi2 _ _ =>
      have := Eval.deterministic he1 he2; cases this
      have := Eval.deterministic hi1 hi2; cases this; rfl
    | projectIdx_idx_signal he2 hi2 hs =>
      have := Eval.deterministic he1 he2; cases this
      have := Eval.deterministic hi1 hi2; subst this; simp [isSignal] at hs
    | projectIdx_expr_signal he2 hs =>
      have := Eval.deterministic he1 he2; subst this; simp [isSignal] at hs
  | projectIdx_idx_signal he1 hi1 hs1 =>
    cases h2 with
    | projectIdx_string_record_ok he2 hi2 _ _ =>
      have := Eval.deterministic he1 he2; cases this
      have := Eval.deterministic hi1 hi2; subst this; simp [isSignal] at hs1
    | projectIdx_string_record_missing he2 hi2 _ _ =>
      have := Eval.deterministic he1 he2; cases this
      have := Eval.deterministic hi1 hi2; subst this; simp [isSignal] at hs1
    | projectIdx_string_non_record he2 hi2 _ =>
      have := Eval.deterministic he1 he2; cases this
      have := Eval.deterministic hi1 hi2; subst this; simp [isSignal] at hs1
    | projectIdx_number_array_ok he2 hi2 _ _ _ =>
      have := Eval.deterministic he1 he2; cases this
      have := Eval.deterministic hi1 hi2; subst this; simp [isSignal] at hs1
    | projectIdx_number_array_oob he2 hi2 _ _ =>
      have := Eval.deterministic he1 he2; cases this
      have := Eval.deterministic hi1 hi2; subst this; simp [isSignal] at hs1
    | projectIdx_number_non_array he2 hi2 _ =>
      have := Eval.deterministic he1 he2; cases this
      have := Eval.deterministic hi1 hi2; subst this; simp [isSignal] at hs1
    | projectIdx_bad_index he2 hi2 _ _ =>
      have := Eval.deterministic he1 he2; cases this
      have := Eval.deterministic hi1 hi2; subst this; simp [isSignal] at hs1
    | projectIdx_idx_signal he2 hi2 _ =>
      have := Eval.deterministic he1 he2; cases this
      exact Eval.deterministic hi1 hi2
    | projectIdx_expr_signal he2 hs =>
      have := Eval.deterministic he1 he2; subst this; simp [isSignal] at hs
  | projectIdx_expr_signal he1 hs1 =>
    cases h2 with
    | projectIdx_expr_signal he2 _ => exact Eval.deterministic he1 he2
    | _ => have := Eval.deterministic he1 (by assumption); subst this; simp [isSignal] at hs1
  -- array
  | array hf1 => cases h2 with | array hf2 => exact EvalElems.deterministic hf1 hf2
  -- index
  | index_ok ha1 hi1 hidx1 hlt1 =>
    cases h2 with
    | index_ok ha2 hi2 hidx2 hlt2 =>
      have := Eval.deterministic ha1 ha2; cases this
      have := Eval.deterministic hi1 hi2; cases this; subst hidx1; subst hidx2; rfl
    | index_oob ha2 hi2 hge =>
      have := Eval.deterministic ha1 ha2; cases this
      have := Eval.deterministic hi1 hi2; cases this; subst hidx1; omega
    | index_bad_idx ha2 hi2 hne =>
      have := Eval.deterministic ha1 ha2; cases this
      have := Eval.deterministic hi1 hi2; cases this; exact absurd rfl (hne _)
    | index_idx_signal ha2 hi2 hs =>
      have := Eval.deterministic ha1 ha2; cases this
      have := Eval.deterministic hi1 hi2; subst this; simp [isSignal] at hs
    | index_non_array ha2 hne =>
      have := Eval.deterministic ha1 ha2; cases this; exact absurd rfl (hne _)
    | index_arr_signal ha2 hs =>
      have := Eval.deterministic ha1 ha2; subst this; simp [isSignal] at hs
  | index_oob ha1 hi1 hge1 =>
    cases h2 with
    | index_ok ha2 hi2 hidx2 hlt2 =>
      have := Eval.deterministic ha1 ha2; cases this
      have := Eval.deterministic hi1 hi2; cases this; subst hidx2; omega
    | index_oob ha2 hi2 _ =>
      have := Eval.deterministic ha1 ha2; cases this
      have := Eval.deterministic hi1 hi2; cases this; rfl
    | index_bad_idx ha2 hi2 hne =>
      have := Eval.deterministic ha1 ha2; cases this
      have := Eval.deterministic hi1 hi2; cases this; exact absurd rfl (hne _)
    | index_idx_signal ha2 hi2 hs =>
      have := Eval.deterministic ha1 ha2; cases this
      have := Eval.deterministic hi1 hi2; subst this; simp [isSignal] at hs
    | index_non_array ha2 hne =>
      have := Eval.deterministic ha1 ha2; cases this; exact absurd rfl (hne _)
    | index_arr_signal ha2 hs =>
      have := Eval.deterministic ha1 ha2; subst this; simp [isSignal] at hs
  | index_bad_idx ha1 hi1 hne1 =>
    cases h2 with
    | index_ok ha2 hi2 _ _ =>
      have := Eval.deterministic ha1 ha2; cases this
      have := Eval.deterministic hi1 hi2; cases this; exact absurd rfl (hne1 _)
    | index_oob ha2 hi2 _ =>
      have := Eval.deterministic ha1 ha2; cases this
      have := Eval.deterministic hi1 hi2; cases this; exact absurd rfl (hne1 _)
    | index_bad_idx ha2 hi2 _ =>
      have := Eval.deterministic ha1 ha2; cases this
      have := Eval.deterministic hi1 hi2; cases this; rfl
    | index_idx_signal ha2 hi2 hs =>
      have := Eval.deterministic ha1 ha2; cases this
      have := Eval.deterministic hi1 hi2; subst this; simp [isSignal] at hs
    | index_non_array ha2 hne =>
      have := Eval.deterministic ha1 ha2; cases this; exact absurd rfl (hne _)
    | index_arr_signal ha2 hs =>
      have := Eval.deterministic ha1 ha2; subst this; simp [isSignal] at hs
  | index_idx_signal ha1 hi1 hs1 =>
    cases h2 with
    | index_ok ha2 hi2 _ _ =>
      have := Eval.deterministic ha1 ha2; cases this
      have := Eval.deterministic hi1 hi2; subst this; simp [isSignal] at hs1
    | index_oob ha2 hi2 _ =>
      have := Eval.deterministic ha1 ha2; cases this
      have := Eval.deterministic hi1 hi2; subst this; simp [isSignal] at hs1
    | index_bad_idx ha2 hi2 _ =>
      have := Eval.deterministic ha1 ha2; cases this
      have := Eval.deterministic hi1 hi2; subst this; simp [isSignal] at hs1
    | index_idx_signal ha2 hi2 _ =>
      have := Eval.deterministic ha1 ha2; cases this; exact Eval.deterministic hi1 hi2
    | index_non_array ha2 hne =>
      have := Eval.deterministic ha1 ha2; cases this; exact absurd rfl (hne _)
    | index_arr_signal ha2 hs =>
      have := Eval.deterministic ha1 ha2; subst this; simp [isSignal] at hs
  | index_non_array ha1 hne1 =>
    cases h2 with
    | index_ok ha2 _ _ _ =>
      have := Eval.deterministic ha1 ha2; cases this; exact absurd rfl (hne1 _)
    | index_oob ha2 _ _ =>
      have := Eval.deterministic ha1 ha2; cases this; exact absurd rfl (hne1 _)
    | index_bad_idx ha2 _ _ =>
      have := Eval.deterministic ha1 ha2; cases this; exact absurd rfl (hne1 _)
    | index_idx_signal ha2 _ _ =>
      have := Eval.deterministic ha1 ha2; cases this; exact absurd rfl (hne1 _)
    | index_non_array ha2 _ => have := Eval.deterministic ha1 ha2; cases this; rfl
    | index_arr_signal ha2 hs =>
      have := Eval.deterministic ha1 ha2; subst this; simp [isSignal] at hs
  | index_arr_signal ha1 hs1 =>
    cases h2 with
    | index_non_array ha2 _ =>
      have := Eval.deterministic ha1 ha2; subst this; simp [isSignal] at hs1
    | index_arr_signal ha2 _ => exact Eval.deterministic ha1 ha2
    | _ => have := Eval.deterministic ha1 (by assumption); subst this; simp [isSignal] at hs1
  -- if/ternary
  | if_true hc1 ht1 hb1 =>
    cases h2 with
    | if_true hc2 _ hb2 =>
      have := Eval.deterministic hc1 hc2; cases this; exact Eval.deterministic hb1 hb2
    | if_false hc2 ht2 _ =>
      have := Eval.deterministic hc1 hc2; cases this; rw [ht1] at ht2; cases ht2
    | if_signal hc2 hs =>
      have := Eval.deterministic hc1 hc2; subst this; simp [isSignal] at hs
  | if_false hc1 ht1 hb1 =>
    cases h2 with
    | if_true hc2 ht2 _ =>
      have := Eval.deterministic hc1 hc2; cases this; rw [ht1] at ht2; cases ht2
    | if_false hc2 _ hb2 =>
      have := Eval.deterministic hc1 hc2; cases this; exact Eval.deterministic hb1 hb2
    | if_signal hc2 hs =>
      have := Eval.deterministic hc1 hc2; subst this; simp [isSignal] at hs
  | if_signal hc1 hs1 =>
    cases h2 with
    | if_true hc2 _ _ =>
      have := Eval.deterministic hc1 hc2; subst this; simp [isSignal] at hs1
    | if_false hc2 _ _ =>
      have := Eval.deterministic hc1 hc2; subst this; simp [isSignal] at hs1
    | if_signal hc2 _ => exact Eval.deterministic hc1 hc2
  | ternary_true hc1 ht1 hb1 =>
    cases h2 with
    | ternary_true hc2 _ hb2 =>
      have := Eval.deterministic hc1 hc2; cases this; exact Eval.deterministic hb1 hb2
    | ternary_false hc2 ht2 _ =>
      have := Eval.deterministic hc1 hc2; cases this; rw [ht1] at ht2; cases ht2
    | ternary_signal hc2 hs =>
      have := Eval.deterministic hc1 hc2; subst this; simp [isSignal] at hs
  | ternary_false hc1 ht1 hb1 =>
    cases h2 with
    | ternary_true hc2 ht2 _ =>
      have := Eval.deterministic hc1 hc2; cases this; rw [ht1] at ht2; cases ht2
    | ternary_false hc2 _ hb2 =>
      have := Eval.deterministic hc1 hc2; cases this; exact Eval.deterministic hb1 hb2
    | ternary_signal hc2 hs =>
      have := Eval.deterministic hc1 hc2; subst this; simp [isSignal] at hs
  | ternary_signal hc1 hs1 =>
    cases h2 with
    | ternary_true hc2 _ _ =>
      have := Eval.deterministic hc1 hc2; subst this; simp [isSignal] at hs1
    | ternary_false hc2 _ _ =>
      have := Eval.deterministic hc1 hc2; subst this; simp [isSignal] at hs1
    | ternary_signal hc2 _ => exact Eval.deterministic hc1 hc2
  -- loop/seq
  | loop hl1 => cases h2 with | loop hl2 => exact EvalLoop.deterministic hl1 hl2
  | seq hs1 => cases h2 with | seq hs2 => exact EvalSeq.deterministic hs1 hs2
  -- return/break/continue/throw
  | return_ok hv1 =>
    cases h2 with
    | return_ok hv2 => have := Eval.deterministic hv1 hv2; cases this; rfl
    | return_signal hv2 hs =>
      have := Eval.deterministic hv1 hv2; subst this; simp [isSignal] at hs
  | return_signal hv1 hs1 =>
    cases h2 with
    | return_ok hv2 =>
      have := Eval.deterministic hv1 hv2; subst this; simp [isSignal] at hs1
    | return_signal hv2 _ => exact Eval.deterministic hv1 hv2
  | «break» => cases h2 with | «break» => rfl
  | «continue» => cases h2 with | «continue» => rfl
  | throw_ok hv1 =>
    cases h2 with
    | throw_ok hv2 => have := Eval.deterministic hv1 hv2; cases this; rfl
    | throw_signal hv2 hs =>
      have := Eval.deterministic hv1 hv2; subst this; simp [isSignal] at hs
  | throw_signal hv1 hs1 =>
    cases h2 with
    | throw_ok hv2 =>
      have := Eval.deterministic hv1 hv2; subst this; simp [isSignal] at hs1
    | throw_signal hv2 _ => exact Eval.deterministic hv1 hv2
  -- tryCatch (6 constructors)
  | tryCatch_ok_no_fin hb1 hnt1 =>
    cases h2 with
    | tryCatch_ok_no_fin hb2 _ => exact Eval.deterministic hb1 hb2
    | tryCatch_throw_no_fin hb2 _ _ =>
      have := Eval.deterministic hb1 hb2; subst this; exact absurd rfl (hnt1 _ _)
  | tryCatch_throw_no_fin hb1 hce1 hh1 =>
    cases h2 with
    | tryCatch_ok_no_fin hb2 hnt2 =>
      have := Eval.deterministic hb1 hb2; subst this; exact absurd rfl (hnt2 _ _)
    | tryCatch_throw_no_fin hb2 hce2 hh2 =>
      have := Eval.deterministic hb1 hb2; cases this; subst hce1; subst hce2
      exact Eval.deterministic hh1 hh2
  | tryCatch_ok_fin_ok hb1 hnt1 hac1 hfs1 hfin1 hres1 =>
    cases h2 with
    | tryCatch_ok_fin_ok hb2 _ hac2 hfs2 hfin2 hres2 =>
      have := Eval.deterministic hb1 hb2
      subst this; subst hac1; subst hac2; subst hfs1; subst hfs2
      have := Eval.deterministic hfin1 hfin2; cases this
      subst hres1; subst hres2; rfl
    | tryCatch_throw_fin_ok hb2 _ _ _ _ _ =>
      have := Eval.deterministic hb1 hb2; subst this; exact absurd rfl (hnt1 _ _)
    | tryCatch_ok_fin_signal hb2 _ _ hfs2 hfin2 hs2 =>
      have := Eval.deterministic hb1 hb2
      subst this; subst hac1; subst hfs1; subst hfs2
      have := Eval.deterministic hfin1 hfin2; subst this; simp [isSignal] at hs2
    | tryCatch_throw_fin_signal hb2 _ _ _ _ _ _ =>
      have := Eval.deterministic hb1 hb2; subst this; exact absurd rfl (hnt1 _ _)
  | tryCatch_throw_fin_ok hb1 hce1 hh1 hfs1 hfin1 hres1 =>
    cases h2 with
    | tryCatch_ok_fin_ok hb2 hnt2 _ _ _ _ =>
      have := Eval.deterministic hb1 hb2; subst this; exact absurd rfl (hnt2 _ _)
    | tryCatch_throw_fin_ok hb2 hce2 hh2 hfs2 hfin2 hres2 =>
      have := Eval.deterministic hb1 hb2; cases this; subst hce1; subst hce2
      have := Eval.deterministic hh1 hh2; subst this; subst hfs1; subst hfs2
      have := Eval.deterministic hfin1 hfin2; cases this
      subst hres1; subst hres2; rfl
    | tryCatch_ok_fin_signal hb2 hnt2 _ _ _ _ =>
      have := Eval.deterministic hb1 hb2; subst this; exact absurd rfl (hnt2 _ _)
    | tryCatch_throw_fin_signal hb2 hce2 hh2 _ hfs2 hfin2 hs2 =>
      have := Eval.deterministic hb1 hb2; cases this; subst hce1; subst hce2
      have := Eval.deterministic hh1 hh2; subst this; subst hfs1; subst hfs2
      have := Eval.deterministic hfin1 hfin2; subst this; simp [isSignal] at hs2
  | tryCatch_ok_fin_signal hb1 hnt1 _ hfs1 hfin1 hs1 =>
    cases h2 with
    | tryCatch_ok_fin_ok hb2 _ hac2 hfs2 hfin2 _ =>
      have := Eval.deterministic hb1 hb2
      subst this; subst hac2; subst hfs1; subst hfs2
      have := Eval.deterministic hfin1 hfin2; subst this; simp [isSignal] at hs1
    | tryCatch_throw_fin_ok hb2 _ _ _ _ _ =>
      have := Eval.deterministic hb1 hb2; subst this; exact absurd rfl (hnt1 _ _)
    | tryCatch_ok_fin_signal hb2 _ _ hfs2 hfin2 _ =>
      have := Eval.deterministic hb1 hb2
      subst this; subst hfs1; subst hfs2
      exact Eval.deterministic hfin1 hfin2
    | tryCatch_throw_fin_signal hb2 _ _ _ _ _ _ =>
      have := Eval.deterministic hb1 hb2; subst this; exact absurd rfl (hnt1 _ _)
  | tryCatch_throw_fin_signal hb1 hce1 hh1 _ hfs1 hfin1 hs1 =>
    cases h2 with
    | tryCatch_ok_fin_ok hb2 hnt2 _ _ _ _ =>
      have := Eval.deterministic hb1 hb2; subst this; exact absurd rfl (hnt2 _ _)
    | tryCatch_throw_fin_ok hb2 hce2 hh2 hfs2 hfin2 _ =>
      have := Eval.deterministic hb1 hb2; cases this; subst hce1; subst hce2
      have := Eval.deterministic hh1 hh2; subst this; subst hfs1; subst hfs2
      have := Eval.deterministic hfin1 hfin2; subst this; simp [isSignal] at hs1
    | tryCatch_ok_fin_signal hb2 hnt2 _ _ _ _ =>
      have := Eval.deterministic hb1 hb2; subst this; exact absurd rfl (hnt2 _ _)
    | tryCatch_throw_fin_signal hb2 hce2 hh2 _ hfs2 hfin2 _ =>
      have := Eval.deterministic hb1 hb2; cases this; subst hce1; subst hce2
      have := Eval.deterministic hh1 hh2; subst this; subst hfs1; subst hfs2
      exact Eval.deterministic hfin1 hfin2
  -- match
  | «match» hs1 hm1 =>
    cases h2 with
    | «match» hs2 hm2 =>
      have := Eval.deterministic hs1 hs2; cases this
      exact EvalMatch.deterministic hm1 hm2
    | match_signal hs2 hsig =>
      have := Eval.deterministic hs1 hs2; subst this; simp [isSignal] at hsig
  | match_signal hs1 hsig1 =>
    cases h2 with
    | «match» hs2 _ =>
      have := Eval.deterministic hs1 hs2; subst this; simp [isSignal] at hsig1
    | match_signal hs2 _ => exact Eval.deterministic hs1 hs2
  -- construct
  | construct_ok ha1 =>
    cases h2 with
    | construct_ok ha2 => have := EvalArgs.deterministic ha1 ha2; cases this; rfl
    | construct_signal ha2 hs =>
      have := EvalArgs.deterministic ha1 ha2; subst this; simp [isSignal] at hs
  | construct_signal ha1 hs1 =>
    cases h2 with
    | construct_ok ha2 =>
      have := EvalArgs.deterministic ha1 ha2; subst this; simp [isSignal] at hs1
    | construct_signal ha2 _ => exact EvalArgs.deterministic ha1 ha2
  -- newObj
  | newObj_ok hc1 ha1 hap1 =>
    cases h2 with
    | newObj_ok hc2 ha2 hap2 =>
      have := Eval.deterministic hc1 hc2; cases this
      have := EvalArgs.deterministic ha1 ha2; cases this
      exact ApplyFunc.deterministic hap1 hap2
    | newObj_callee_signal hc2 hs =>
      have := Eval.deterministic hc1 hc2; subst this; simp [isSignal] at hs
    | newObj_args_signal hc2 ha2 hs =>
      have := Eval.deterministic hc1 hc2; cases this
      have := EvalArgs.deterministic ha1 ha2; subst this; simp [isSignal] at hs
  | newObj_callee_signal hc1 hs1 =>
    cases h2 with
    | newObj_ok hc2 _ _ =>
      have := Eval.deterministic hc1 hc2; subst this; simp [isSignal] at hs1
    | newObj_callee_signal hc2 _ => exact Eval.deterministic hc1 hc2
    | newObj_args_signal hc2 _ _ =>
      have := Eval.deterministic hc1 hc2; subst this; simp [isSignal] at hs1
  | newObj_args_signal hc1 ha1 hs1 =>
    cases h2 with
    | newObj_ok hc2 ha2 _ =>
      have := Eval.deterministic hc1 hc2; cases this
      have := EvalArgs.deterministic ha1 ha2; subst this; simp [isSignal] at hs1
    | newObj_callee_signal hc2 hs =>
      have := Eval.deterministic hc1 hc2; subst this; simp [isSignal] at hs
    | newObj_args_signal hc2 ha2 _ =>
      have := Eval.deterministic hc1 hc2; cases this
      exact EvalArgs.deterministic ha1 ha2
  -- await/yield/spread
  | «await» he1 => cases h2 with | «await» he2 => exact Eval.deterministic he1 he2
  | yield_some he1 => cases h2 with | yield_some he2 => exact Eval.deterministic he1 he2
  | yield_none => cases h2 with | yield_none => rfl
  | spread he1 => cases h2 with | spread he2 => exact Eval.deterministic he1 he2
  termination_by (fuel, 0)
  decreasing_by
    all_goals simp_wf
    all_goals first
      | apply Prod.Lex.left; omega
      | (apply Prod.Lex.right; subst_vars; simp [List.length_cons]; try omega)

def EvalArgs.deterministic
    (h1 : EvalArgs env store fuel args acc r1) (h2 : EvalArgs env store fuel args acc r2) :
    r1 = r2 := by
  cases h1 with
  | nil => cases h2 with | nil => rfl
  | cons_ok ha1 hr1 =>
    cases h2 with
    | cons_ok ha2 hr2 =>
      have := Eval.deterministic ha1 ha2; cases this
      exact EvalArgs.deterministic hr1 hr2
    | cons_signal ha2 hs =>
      have := Eval.deterministic ha1 ha2; subst this; simp [isSignal] at hs
  | cons_signal ha1 hs1 =>
    cases h2 with
    | cons_ok ha2 _ =>
      have := Eval.deterministic ha1 ha2; subst this; simp [isSignal] at hs1
    | cons_signal ha2 _ => exact Eval.deterministic ha1 ha2
  termination_by (fuel, args.length)
  decreasing_by
    all_goals simp_wf
    all_goals first
      | apply Prod.Lex.left; omega
      | (apply Prod.Lex.right; subst_vars; simp [List.length_cons]; try omega)

def ApplyFunc.deterministic
    (h1 : ApplyFunc fv args store fuel r1) (h2 : ApplyFunc fv args store fuel r2) :
    r1 = r2 := by
  cases h1 with
  | closure_ok henv1 henv1' heval1 hres1 =>
    cases h2 with
    | closure_ok henv2 henv2' heval2 hres2 =>
      subst henv1; subst henv1'; subst henv2; subst henv2'
      have := Eval.deterministic heval1 heval2
      subst this; subst hres1; subst hres2; rfl
    | non_function hne => exact absurd rfl (hne _ _ _ _)
  | non_function hne1 =>
    cases h2 with
    | closure_ok _ _ _ _ => exact absurd rfl (hne1 _ _ _ _)
    | non_function _ => rfl
  termination_by (fuel, 1)
  decreasing_by
    all_goals simp_wf
    all_goals first
      | apply Prod.Lex.left; omega
      | (apply Prod.Lex.right; subst_vars; simp [List.length_cons]; try omega)

def EvalFields.deterministic
    (h1 : EvalFields env store fuel fields acc r1)
    (h2 : EvalFields env store fuel fields acc r2) : r1 = r2 := by
  cases h1 with
  | nil => cases h2 with | nil => rfl
  | cons_ok he1 hr1 =>
    cases h2 with
    | cons_ok he2 hr2 =>
      have := Eval.deterministic he1 he2; cases this
      exact EvalFields.deterministic hr1 hr2
    | cons_signal he2 hs =>
      have := Eval.deterministic he1 he2; subst this; simp [isSignal] at hs
  | cons_signal he1 hs1 =>
    cases h2 with
    | cons_ok he2 _ =>
      have := Eval.deterministic he1 he2; subst this; simp [isSignal] at hs1
    | cons_signal he2 _ => exact Eval.deterministic he1 he2
  termination_by (fuel, fields.length)
  decreasing_by
    all_goals simp_wf
    all_goals first
      | apply Prod.Lex.left; omega
      | (apply Prod.Lex.right; subst_vars; simp [List.length_cons]; try omega)

def EvalElems.deterministic
    (h1 : EvalElems env store fuel elems acc r1)
    (h2 : EvalElems env store fuel elems acc r2) : r1 = r2 := by
  cases h1 with
  | nil => cases h2 with | nil => rfl
  | cons_ok he1 hr1 =>
    cases h2 with
    | cons_ok he2 hr2 =>
      have := Eval.deterministic he1 he2; cases this
      exact EvalElems.deterministic hr1 hr2
    | cons_signal he2 hs =>
      have := Eval.deterministic he1 he2; subst this; simp [isSignal] at hs
  | cons_signal he1 hs1 =>
    cases h2 with
    | cons_ok he2 _ =>
      have := Eval.deterministic he1 he2; subst this; simp [isSignal] at hs1
    | cons_signal he2 _ => exact Eval.deterministic he1 he2
  termination_by (fuel, elems.length)
  decreasing_by
    all_goals simp_wf
    all_goals first
      | apply Prod.Lex.left; omega
      | (apply Prod.Lex.right; subst_vars; simp [List.length_cons]; try omega)

def EvalLoop.deterministic
    (h1 : EvalLoop env store fuel condE body r1)
    (h2 : EvalLoop env store fuel condE body r2) : r1 = r2 := by
  cases h1 with
  | fuel_zero => cases h2 with | fuel_zero => rfl
  | cond_false hc1 ht1 =>
    cases h2 with
    | cond_false hc2 _ => have := Eval.deterministic hc1 hc2; cases this; rfl
    | body_val hc2 ht2 _ _ =>
      have := Eval.deterministic hc1 hc2; cases this; rw [ht1] at ht2; cases ht2
    | body_continue hc2 ht2 _ _ =>
      have := Eval.deterministic hc1 hc2; cases this; rw [ht1] at ht2; cases ht2
    | body_break hc2 ht2 _ =>
      have := Eval.deterministic hc1 hc2; cases this; rw [ht1] at ht2; cases ht2
    | body_other hc2 ht2 _ _ _ _ =>
      have := Eval.deterministic hc1 hc2; cases this; rw [ht1] at ht2; cases ht2
    | cond_signal hc2 hs =>
      have := Eval.deterministic hc1 hc2; subst this; simp [isSignal] at hs
  | body_val hc1 ht1 hb1 hl1 =>
    cases h2 with
    | cond_false hc2 ht2 =>
      have := Eval.deterministic hc1 hc2; cases this; rw [ht1] at ht2; cases ht2
    | body_val hc2 _ hb2 hl2 =>
      have := Eval.deterministic hc1 hc2; cases this
      have := Eval.deterministic hb1 hb2; cases this
      exact EvalLoop.deterministic hl1 hl2
    | body_continue hc2 _ hb2 _ =>
      have := Eval.deterministic hc1 hc2; cases this
      have := Eval.deterministic hb1 hb2; cases this
    | body_break hc2 _ hb2 =>
      have := Eval.deterministic hc1 hc2; cases this
      have := Eval.deterministic hb1 hb2; cases this
    | body_other hc2 _ hb2 hne _ _ =>
      have := Eval.deterministic hc1 hc2; cases this
      have := Eval.deterministic hb1 hb2; subst this; exact absurd rfl (hne _ _)
    | cond_signal hc2 hs =>
      have := Eval.deterministic hc1 hc2; subst this; simp [isSignal] at hs
  | body_continue hc1 ht1 hb1 hl1 =>
    cases h2 with
    | cond_false hc2 ht2 =>
      have := Eval.deterministic hc1 hc2; cases this; rw [ht1] at ht2; cases ht2
    | body_val hc2 _ hb2 _ =>
      have := Eval.deterministic hc1 hc2; cases this
      have := Eval.deterministic hb1 hb2; cases this
    | body_continue hc2 _ hb2 hl2 =>
      have := Eval.deterministic hc1 hc2; cases this
      have := Eval.deterministic hb1 hb2; cases this
      exact EvalLoop.deterministic hl1 hl2
    | body_break hc2 _ hb2 =>
      have := Eval.deterministic hc1 hc2; cases this
      have := Eval.deterministic hb1 hb2; cases this
    | body_other hc2 _ hb2 _ hne _ =>
      have := Eval.deterministic hc1 hc2; cases this
      have := Eval.deterministic hb1 hb2; subst this; exact absurd rfl (hne _)
    | cond_signal hc2 hs =>
      have := Eval.deterministic hc1 hc2; subst this; simp [isSignal] at hs
  | body_break hc1 ht1 hb1 =>
    cases h2 with
    | cond_false hc2 ht2 =>
      have := Eval.deterministic hc1 hc2; cases this; rw [ht1] at ht2; cases ht2
    | body_val hc2 _ hb2 _ =>
      have := Eval.deterministic hc1 hc2; cases this; have := Eval.deterministic hb1 hb2; cases this
    | body_continue hc2 _ hb2 _ =>
      have := Eval.deterministic hc1 hc2; cases this; have := Eval.deterministic hb1 hb2; cases this
    | body_break hc2 _ hb2 =>
      have := Eval.deterministic hc1 hc2; cases this
      have := Eval.deterministic hb1 hb2; cases this; rfl
    | body_other hc2 _ hb2 _ _ hne =>
      have := Eval.deterministic hc1 hc2; cases this
      have := Eval.deterministic hb1 hb2; subst this; exact absurd rfl (hne _)
    | cond_signal hc2 hs =>
      have := Eval.deterministic hc1 hc2; subst this; simp [isSignal] at hs
  | body_other hc1 ht1 hb1 hne1v hne1c hne1b =>
    cases h2 with
    | cond_false hc2 ht2 =>
      have := Eval.deterministic hc1 hc2; cases this; rw [ht1] at ht2; cases ht2
    | body_val hc2 _ hb2 _ =>
      have := Eval.deterministic hc1 hc2; cases this
      have := Eval.deterministic hb1 hb2; subst this; exact absurd rfl (hne1v _ _)
    | body_continue hc2 _ hb2 _ =>
      have := Eval.deterministic hc1 hc2; cases this
      have := Eval.deterministic hb1 hb2; subst this; exact absurd rfl (hne1c _)
    | body_break hc2 _ hb2 =>
      have := Eval.deterministic hc1 hc2; cases this
      have := Eval.deterministic hb1 hb2; subst this; exact absurd rfl (hne1b _)
    | body_other hc2 _ hb2 _ _ _ =>
      have := Eval.deterministic hc1 hc2; cases this; exact Eval.deterministic hb1 hb2
    | cond_signal hc2 hs =>
      have := Eval.deterministic hc1 hc2; subst this; simp [isSignal] at hs
  | cond_signal hc1 hs1 =>
    cases h2 with
    | cond_false hc2 _ =>
      have := Eval.deterministic hc1 hc2; subst this; simp [isSignal] at hs1
    | body_val hc2 _ _ _ =>
      have := Eval.deterministic hc1 hc2; subst this; simp [isSignal] at hs1
    | body_continue hc2 _ _ _ =>
      have := Eval.deterministic hc1 hc2; subst this; simp [isSignal] at hs1
    | body_break hc2 _ _ =>
      have := Eval.deterministic hc1 hc2; subst this; simp [isSignal] at hs1
    | body_other hc2 _ _ _ _ _ =>
      have := Eval.deterministic hc1 hc2; subst this; simp [isSignal] at hs1
    | cond_signal hc2 _ => exact Eval.deterministic hc1 hc2
  termination_by (fuel, 0)
  decreasing_by
    all_goals simp_wf
    all_goals first
      | apply Prod.Lex.left; omega
      | (apply Prod.Lex.right; subst_vars; simp [List.length_cons]; try omega)

def EvalSeq.deterministic
    (h1 : EvalSeq env store fuel exprs r1)
    (h2 : EvalSeq env store fuel exprs r2) : r1 = r2 := by
  cases h1 with
  | nil => cases h2 with | nil => rfl
  | singleton he1 =>
    cases h2 with
    | singleton he2 => exact Eval.deterministic he1 he2
    | cons_ok _ _ hne => exact absurd rfl hne
    | cons_signal _ _ hne => exact absurd rfl hne
  | cons_ok he1 hr1 hne1 =>
    cases h2 with
    | singleton _ => exact absurd rfl hne1
    | cons_ok he2 hr2 _ =>
      have := Eval.deterministic he1 he2; cases this
      exact EvalSeq.deterministic hr1 hr2
    | cons_signal he2 hs _ =>
      have := Eval.deterministic he1 he2; subst this; simp [isSignal] at hs
  | cons_signal he1 hs1 hne1 =>
    cases h2 with
    | singleton _ => exact absurd rfl hne1
    | cons_ok he2 _ _ =>
      have := Eval.deterministic he1 he2; subst this; simp [isSignal] at hs1
    | cons_signal he2 _ _ => exact Eval.deterministic he1 he2
  termination_by (fuel, exprs.length)
  decreasing_by
    all_goals simp_wf
    all_goals first
      | apply Prod.Lex.left; omega
      | (apply Prod.Lex.right; subst_vars; simp [List.length_cons]; try omega)

def EvalMatch.deterministic
    (h1 : EvalMatch env store fuel scrutinee cases r1)
    (h2 : EvalMatch env store fuel scrutinee cases r2) : r1 = r2 := by
  cases h1 with
  | no_cases => cases h2 with | no_cases => rfl
  | match_ok hm1 he1 =>
    cases h2 with
    | match_ok hm2 he2 => rw [hm1] at hm2; cases hm2; exact Eval.deterministic he1 he2
    | match_fail hm2 _ => rw [hm1] at hm2; cases hm2
  | match_fail hm1 hr1 =>
    cases h2 with
    | match_ok hm2 _ => rw [hm1] at hm2; cases hm2
    | match_fail _ hr2 => exact EvalMatch.deterministic hr1 hr2
  termination_by (fuel, cases.length)
  decreasing_by
    all_goals simp_wf
    all_goals first
      | apply Prod.Lex.left; omega
      | (apply Prod.Lex.right; subst_vars; simp [List.length_cons]; try omega)

end

-- Promote to theorems for downstream use
theorem eval_deterministic (h1 : Eval env store fuel e r1) (h2 : Eval env store fuel e r2) :
    r1 = r2 := Eval.deterministic h1 h2
theorem evalArgs_deterministic (h1 : EvalArgs env store fuel args acc r1) (h2 : EvalArgs env store fuel args acc r2) :
    r1 = r2 := EvalArgs.deterministic h1 h2
theorem evalLoop_deterministic (h1 : EvalLoop env store fuel c b r1) (h2 : EvalLoop env store fuel c b r2) :
    r1 = r2 := EvalLoop.deterministic h1 h2
theorem evalSeq_deterministic (h1 : EvalSeq env store fuel es r1) (h2 : EvalSeq env store fuel es r2) :
    r1 = r2 := EvalSeq.deterministic h1 h2
theorem evalMatch_deterministic (h1 : EvalMatch env store fuel sv cs r1) (h2 : EvalMatch env store fuel sv cs r2) :
    r1 = r2 := EvalMatch.deterministic h1 h2

end LeanJS.Semantics
