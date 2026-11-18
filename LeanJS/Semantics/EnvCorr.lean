/-
  Value, environment and result correspondence for the simulation proofs.

  All four passes share one generic correspondence, parameterised by a
  `CorrSpec`:
  * where the source's `unit` and `undefined` go in the target (e.g. IR→JS
    maps both to `undefined`, IR→Lean maps both to `()`), and
  * which source closures correspond to which target closures (`Clo`), which
    is where each pass's translation relation on function bodies enters.

  Primitive values (numbers, strings, booleans) correspond only to
  themselves; records and arrays correspond pointwise.

  Results correspond when they have the same shape, the same store, and
  corresponding values. There is deliberately no case for `.error`: the
  simulation theorems assume the source program does not go wrong.
-/
import LeanJS.Semantics.JSEval

set_option autoImplicit true

namespace LeanJS.Semantics

open LeanJS.IR

/-! ## Value classes -/

/-- Function values of any of the three languages -/
inductive IsFun : IRValue → Prop where
  | closure : IsFun (.closure e n ps b)
  | js : IsFun (.jsClosure e n ps b)
  | lean : IsFun (.leanClosure e n p b)

/-- `unit` or `undefined` -/
inductive IsNullish : IRValue → Prop where
  | unit : IsNullish .unit
  | undefined : IsNullish .undefined

/-- Numbers, strings and booleans -/
inductive IsPrim : IRValue → Prop where
  | number : IsPrim (.number n)
  | string : IsPrim (.string s)
  | bool : IsPrim (.bool b)

/-! ## Correspondence -/

structure CorrSpec where
  /-- Image of the source `unit` -/
  uUnit : IRValue
  /-- Image of the source `undefined` -/
  uUndef : IRValue
  hUnit : IsNullish uUnit
  hUndef : IsNullish uUndef
  /-- `Clo v v' e e'`: source closure `v` over `e` corresponds to target
      closure `v'` over `e'` (provided `e` and `e'` correspond). -/
  Clo : IRValue → IRValue → Env → Env → Prop
  clo_src : Clo v v' e e' → IsFun v
  clo_tgt : Clo v v' e e' → IsFun v'

mutual

inductive VCorr (S : CorrSpec) : IRValue → IRValue → Prop where
  | number : VCorr S (.number n) (.number n)
  | string : VCorr S (.string s) (.string s)
  | bool : VCorr S (.bool b) (.bool b)
  | unit : VCorr S .unit S.uUnit
  | undefined : VCorr S .undefined S.uUndef
  | clo : S.Clo v v' e e' → EnvCorr S e e' → VCorr S v v'
  | record : FieldsCorr S fs fs' → VCorr S (.record fs) (.record fs')
  | array : ListCorr S vs vs' → VCorr S (.array vs) (.array vs')

inductive EnvCorr (S : CorrSpec) : Env → Env → Prop where
  | nil : EnvCorr S .nil .nil
  | cons : VCorr S v v' → EnvCorr S e e' → EnvCorr S (.cons x v e) (.cons x v' e')

inductive ListCorr (S : CorrSpec) : List IRValue → List IRValue → Prop where
  | nil : ListCorr S [] []
  | cons : VCorr S v v' → ListCorr S vs vs' → ListCorr S (v :: vs) (v' :: vs')

inductive FieldsCorr (S : CorrSpec) : List (String × IRValue) → List (String × IRValue) → Prop where
  | nil : FieldsCorr S [] []
  | cons : VCorr S v v' → FieldsCorr S fs fs' →
      FieldsCorr S ((k, v) :: fs) ((k, v') :: fs')

end

/-- Corresponding results: same shape, same store, corresponding values. -/
inductive ResultCorr (S : CorrSpec) : EvalResult → EvalResult → Prop where
  | val : VCorr S v v' → ResultCorr S (.val v s) (.val v' s)
  | ret : VCorr S v v' → ResultCorr S (.return_ v s) (.return_ v' s)
  | throw : VCorr S v v' → ResultCorr S (.throw_ v s) (.throw_ v' s)
  | brk : ResultCorr S (.break_ s) (.break_ s)
  | cont : ResultCorr S (.continue_ s) (.continue_ s)

/-- The result is not a runtime error ("the program does not go wrong"). -/
def NoErr : EvalResult → Prop
  | .error _ => False
  | _ => True

/-! ## Basic lemmas -/

theorem IsPrim.vcorr (h : IsPrim v) : VCorr S v v := by
  cases h <;> constructor

theorem ResultCorr.noErr_right (h : ResultCorr S r r') : NoErr r' := by
  cases h <;> trivial

theorem ResultCorr.signal (h : ResultCorr S r r') (hs : isSignal r) : isSignal r' := by
  cases h <;> simp_all [isSignal]

theorem ResultCorr.signal_iff (h : ResultCorr S r r') : isSignal r ↔ isSignal r' := by
  cases h <;> simp [isSignal]

theorem ResultCorr.unwrapReturn (h : ResultCorr S r r') :
    ResultCorr S (unwrapReturn r) (unwrapReturn r') := by
  cases h with
  | val hv => exact .val hv
  | ret hv => exact .val hv
  | throw hv => exact .throw hv
  | brk => exact .brk
  | cont => exact .cont

theorem unwrapReturn_noErr (h : NoErr (unwrapReturn r)) : NoErr r := by
  cases r <;> simp_all [unwrapReturn, NoErr]

theorem unwrapBlockResult_noErr (h : NoErr (unwrapBlockResult r)) : NoErr r := by
  cases r <;> simp_all [unwrapBlockResult, NoErr]

/-- Truthiness is preserved -/
theorem VCorr.truthy (h : VCorr S v v') : isTruthy v = isTruthy v' := by
  cases h with
  | number | string | bool => rfl
  | unit => have h := S.hUnit; generalize S.uUnit = u at h ⊢; cases h <;> rfl
  | undefined => have h := S.hUndef; generalize S.uUndef = u at h ⊢; cases h <;> rfl
  | clo hc _ =>
    have h1 := S.clo_src hc
    have h2 := S.clo_tgt hc
    cases h1 <;> cases h2 <;> rfl
  | record | array => rfl

theorem EnvCorr.lookup (h : EnvCorr S e e') (hl : e.lookup x = some v) :
    ∃ v', e'.lookup x = some v' ∧ VCorr S v v' := by
  match h with
  | .nil => simp [Env.lookup] at hl
  | .cons (x := y) hv he =>
    simp only [Env.lookup] at hl ⊢
    split at hl
    · simp at hl; subst hl; exact ⟨_, by simp_all, hv⟩
    · rename_i hne; simp [hne]; exact EnvCorr.lookup he hl

theorem FieldsCorr.lookup (h : FieldsCorr S fs fs') (k : String) :
    (fs.lookup k = none ∧ fs'.lookup k = none) ∨
    (∃ v v', fs.lookup k = some v ∧ fs'.lookup k = some v' ∧ VCorr S v v') := by
  match h with
  | .nil => left; simp [List.lookup]
  | .cons (k := k') hv hf =>
    by_cases hk : k = k'
    · subst hk; right; exact ⟨_, _, by simp [List.lookup], by simp [List.lookup], hv⟩
    · have hk' : (k == k') = false := by simp [hk]
      simp only [List.lookup, hk']
      exact FieldsCorr.lookup hf k

theorem ListCorr.append (h1 : ListCorr S a a') (h2 : ListCorr S b b') :
    ListCorr S (a ++ b) (a' ++ b') := by
  match h1 with
  | .nil => simpa using h2
  | .cons hv ht => exact .cons hv (ListCorr.append ht h2)

theorem ListCorr.reverse (h : ListCorr S a a') : ListCorr S a.reverse a'.reverse := by
  match h with
  | .nil => exact .nil
  | .cons hv ht =>
    simp only [List.reverse_cons]
    exact ListCorr.append (ListCorr.reverse ht) (.cons hv .nil)

theorem FieldsCorr.append (h1 : FieldsCorr S a a') (h2 : FieldsCorr S b b') :
    FieldsCorr S (a ++ b) (a' ++ b') := by
  match h1 with
  | .nil => simpa using h2
  | .cons hv ht => exact .cons hv (FieldsCorr.append ht h2)

theorem FieldsCorr.reverse (h : FieldsCorr S a a') : FieldsCorr S a.reverse a'.reverse := by
  match h with
  | .nil => exact .nil
  | .cons hv ht =>
    simp only [List.reverse_cons]
    exact FieldsCorr.append (FieldsCorr.reverse ht) (.cons hv .nil)

theorem EnvCorr.extendMany (he : EnvCorr S e e') (hv : ListCorr S vs vs') (ns : List String) :
    EnvCorr S (e.extendMany (ns.zip vs)) (e'.extendMany (ns.zip vs')) := by
  induction ns generalizing e e' vs vs' with
  | nil => simpa [Env.extendMany] using he
  | cons n ns ih =>
    cases hv with
    | nil => simpa [Env.extendMany] using he
    | cons hv1 hvs =>
      simp only [List.zip_cons_cons, Env.extendMany, List.foldl_cons] at ih ⊢
      exact ih (.cons hv1 he) hvs

theorem EnvCorr.ofCall (he : EnvCorr S e e') (hv : ListCorr S vs vs')
    (hf : VCorr S fv fv') (ps : List String) (self : Option String) :
    EnvCorr S (callEnv e self ps vs fv) (callEnv e' self ps vs' fv') := by
  unfold LeanJS.Semantics.callEnv
  cases self with
  | none => exact he.extendMany hv ps
  | some n => exact .cons hf (he.extendMany hv ps)

/-! ## Operators -/

theorem evalBinOp_and (l r : IRValue) (s : Store) :
    evalBinOp .and l r s = (if isTruthy l then .val r s else .val l s) := by
  cases l <;> rfl

theorem evalBinOp_or (l r : IRValue) (s : Store) :
    evalBinOp .or l r s = (if isTruthy l then .val l s else .val r s) := by
  cases l <;> rfl

set_option maxHeartbeats 4000000 in
/-- For operators other than `&&`/`||`, a non-error result is a primitive. -/
theorem evalBinOp_prim (op : IRBinOp) (hop : op ≠ .and ∧ op ≠ .or) (l r : IRValue) (s : Store)
    (hne : NoErr (evalBinOp op l r s)) :
    ∃ b, evalBinOp op l r s = .val b s ∧ IsPrim b := by
  unfold evalBinOp at hne ⊢
  split <;> simp_all [NoErr] <;> constructor

/-- A non-base left operand makes every non-logical operator fail. -/
theorem evalBinOp_err_left (op : IRBinOp) (hop : op ≠ .and ∧ op ≠ .or)
    (hl : ¬ IsPrim l ∧ ¬ IsNullish l) (r : IRValue) (s : Store) :
    ¬ NoErr (evalBinOp op l r s) := by
  obtain ⟨h1, h2⟩ := hop
  cases l with
  | number => exact absurd .number hl.1
  | string => exact absurd .string hl.1
  | bool => exact absurd .bool hl.1
  | unit => exact absurd .unit hl.2
  | undefined => exact absurd .undefined hl.2
  | _ => cases op <;> simp_all [evalBinOp, NoErr]

theorem evalBinOp_err_right (op : IRBinOp) (hop : op ≠ .and ∧ op ≠ .or)
    (hr : ¬ IsPrim r ∧ ¬ IsNullish r) (l : IRValue) (s : Store) :
    ¬ NoErr (evalBinOp op l r s) := by
  obtain ⟨h1, h2⟩ := hop
  cases r with
  | number => exact absurd .number hr.1
  | string => exact absurd .string hr.1
  | bool => exact absurd .bool hr.1
  | unit => exact absurd .unit hr.2
  | undefined => exact absurd .undefined hr.2
  | _ => cases op <;> cases l <;> simp_all [evalBinOp, NoErr]

/-- Nullish against primitive: every non-logical operator fails. -/
theorem evalBinOp_err_nullish_prim (op : IRBinOp) (hop : op ≠ .and ∧ op ≠ .or)
    (hl : IsNullish l) (hr : IsPrim r) (s : Store) :
    ¬ NoErr (evalBinOp op l r s) ∧ ¬ NoErr (evalBinOp op r l s) := by
  obtain ⟨h1, h2⟩ := hop
  cases hl <;> cases hr <;> cases op <;> simp_all [evalBinOp, NoErr]

/-- Two nullish operands: the result only depends on whether they are
    "the same kind" of nullish, which `NoErr` pins down. -/
theorem evalBinOp_nullish (op : IRBinOp) (hop : op ≠ .and ∧ op ≠ .or)
    (hl : IsNullish l) (hr : IsNullish r) (hl' : IsNullish l') (hr' : IsNullish r')
    (hsame : l = r → l' = r') (s : Store)
    (hne : NoErr (evalBinOp op l r s)) :
    evalBinOp op l' r' s = evalBinOp op l r s := by
  obtain ⟨h1, h2⟩ := hop
  cases hl <;> cases hr <;> cases hl' <;> cases hr' <;> cases op <;>
    simp_all [evalBinOp, NoErr]

/-- The value a base source value maps to under a spec -/
inductive BaseImage (S : CorrSpec) : IRValue → IRValue → Prop where
  | prim : IsPrim v → BaseImage S v v
  | unit : BaseImage S .unit S.uUnit
  | undefined : BaseImage S .undefined S.uUndef

theorem BaseImage.functional (h1 : BaseImage S v a) (h2 : BaseImage S v b) : a = b := by
  cases h1 <;> cases h2 <;> first | rfl | (rename_i h; cases h)

/-- Classify a value correspondence: either a base value and its image, or a
    non-base value on both sides. -/
theorem VCorr.classify (h : VCorr S v v') :
    BaseImage S v v' ∨ ((¬ IsPrim v ∧ ¬ IsNullish v) ∧ (¬ IsPrim v' ∧ ¬ IsNullish v')) := by
  cases h with
  | number => exact .inl (.prim .number)
  | string => exact .inl (.prim .string)
  | bool => exact .inl (.prim .bool)
  | unit => exact .inl .unit
  | undefined => exact .inl .undefined
  | clo hc _ =>
    right
    have h1 := S.clo_src hc
    have h2 := S.clo_tgt hc
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> intro h <;> cases h1 <;> cases h2 <;> cases h
  | record => right; refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> intro h <;> cases h
  | array => right; refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> intro h <;> cases h

theorem BaseImage.nullish_iff (h : BaseImage S v v') : IsNullish v ↔ IsNullish v' := by
  cases h with
  | prim hp => rfl
  | unit => exact ⟨fun _ => S.hUnit, fun _ => .unit⟩
  | undefined => exact ⟨fun _ => S.hUndef, fun _ => .undefined⟩

theorem BaseImage.prim_eq (h : BaseImage S v v') (hp : IsPrim v) : v' = v := by
  cases h with
  | prim => rfl
  | unit => cases hp
  | undefined => cases hp

theorem BaseImage.base (h : BaseImage S v v') : IsPrim v ∨ IsNullish v := by
  cases h with
  | prim hp => exact .inl hp
  | unit => exact .inr .unit
  | undefined => exact .inr .undefined

/-- Non-logical operators on base values: the target computes the same result. -/
theorem evalBinOp_base (op : IRBinOp) (hop : op ≠ .and ∧ op ≠ .or)
    (hl : BaseImage S l l') (hr : BaseImage S r r') (s : Store)
    (hne : NoErr (evalBinOp op l r s)) :
    evalBinOp op l' r' s = evalBinOp op l r s := by
  rcases hl.base with hlp | hln
  · rw [hl.prim_eq hlp]
    rcases hr.base with hrp | hrn
    · rw [hr.prim_eq hrp]
    · exact absurd hne (evalBinOp_err_nullish_prim op hop hrn hlp s).2
  · rcases hr.base with hrp | hrn
    · exact absurd hne (evalBinOp_err_nullish_prim op hop hln hrp s).1
    · exact evalBinOp_nullish op hop hln hrn (hl.nullish_iff.1 hln) (hr.nullish_iff.1 hrn)
        (fun heq => by subst heq; exact hl.functional hr) s hne

/-- Main operator lemma. `op'` is the target operator: the same, or `+` for
    IR's string concatenation. -/
theorem evalBinOp_corr {op op' : IRBinOp}
    (hop : op' = op ∨ (op = .strConcat ∧ op' = .add))
    (hl : VCorr S l l') (hr : VCorr S r r') (s : Store)
    (hne : NoErr (evalBinOp op l r s)) :
    ResultCorr S (evalBinOp op l r s) (evalBinOp op' l' r' s) := by
  rcases hop with hop' | ⟨rfl, rfl⟩
  · rw [hop']
    by_cases hand : op = .and
    · subst hand
      rw [evalBinOp_and, evalBinOp_and, ← hl.truthy]
      split <;> constructor <;> assumption
    by_cases hor : op = .or
    · subst hor
      rw [evalBinOp_or, evalBinOp_or, ← hl.truthy]
      split <;> constructor <;> assumption
    have hop : op ≠ .and ∧ op ≠ .or := ⟨hand, hor⟩
    rcases hl.classify with hlb | ⟨hln, _⟩
    · rcases hr.classify with hrb | ⟨hrn, _⟩
      · rw [evalBinOp_base op hop hlb hrb s hne]
        obtain ⟨b, hb, hp⟩ := evalBinOp_prim op hop l r s hne
        rw [hb]; exact .val hp.vcorr
      · exact absurd hne (evalBinOp_err_right op hop hrn l s)
    · exact absurd hne (evalBinOp_err_left op hop hln r s)
  · -- strConcat ↦ add: both operands must be strings
    have : ∃ a b, l = .string a ∧ r = .string b := by
      cases l <;> cases r <;> simp_all [evalBinOp, NoErr]
    obtain ⟨a, b, rfl, rfl⟩ := this
    cases hl with
    | string =>
      cases hr with
      | string => exact .val .string
      | clo hc _ => cases S.clo_src hc
    | clo hc _ => cases S.clo_src hc

theorem evalUnaryOp_corr (op : IRUnaryOp) (hv : VCorr S v v') (s : Store)
    (hne : NoErr (evalUnaryOp op v s)) :
    ResultCorr S (evalUnaryOp op v s) (evalUnaryOp op v' s) := by
  cases op with
  | not =>
    simp only [evalUnaryOp, hv.truthy]; exact .val .bool
  | neg | bitNot =>
    cases hv with
    | number => exact .val .number
    | string | bool | record | array => simp [evalUnaryOp, NoErr] at hne
    | unit | undefined => simp [evalUnaryOp, NoErr] at hne
    | clo hc _ =>
      have := S.clo_src hc
      cases this <;> simp [evalUnaryOp, NoErr] at hne
  | typeof =>
    cases hv with
    | number | string | bool => exact .val .string
    | unit =>
      have h := S.hUnit; generalize S.uUnit = u at h ⊢; cases h <;> exact .val .string
    | undefined =>
      have h := S.hUndef; generalize S.uUndef = u at h ⊢; cases h <;> exact .val .string
    | record | array => exact .val .string
    | clo hc _ =>
      have h1 := S.clo_src hc
      have h2 := S.clo_tgt hc
      cases h1 <;> cases h2 <;> exact .val .string

end LeanJS.Semantics
