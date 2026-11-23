import JSProofs.ForIn2
import JSProofs.Switch
import JSProofs.Auto

/-!
# Rules for updateProperties' loops (zippy docs/react-proofs.md)

A `for (var x in o)` loop's variable bound to the key (`wp_bindForVar`), and member calls whose method a plain
object inherits (`wp_callMemberT`: `props.hasOwnProperty(k)`, the method on `Object.prototype`).
-/

open ES ES.M HostRuns
open Std (HashMap)

namespace Logic

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ}

theorem binaryOp_eq_null_obj (o : ObjId) (s : State) (hf : s.fuel ≠ 0) :
    Sem.binaryOp .eq .null (.obj o) s = .ok (.bool false) s := by
  obtain ⟨k, hk⟩ : ∃ k, s.fuel = k + 1 := ⟨s.fuel - 1, by omega⟩
  simp only [Sem.binaryOp, isLooselyEqual, M.bind_eq, M.bind_apply]; unfold repeatFrom; rw [hk]
  rfl

theorem binaryOp_eq_null_str (k : JSStr) (s : State) (hf : s.fuel ≠ 0) :
    Sem.binaryOp .eq .null (.str k) s = .ok (.bool false) s := by
  obtain ⟨j, hj⟩ : ∃ j, s.fuel = j + 1 := ⟨s.fuel - 1, by omega⟩
  simp only [Sem.binaryOp, isLooselyEqual, M.bind_eq, M.bind_apply]; unfold repeatFrom; rw [hj]
  rfl

/-- **`null == o`**, `o` an object: `false`. -/
theorem wp_eqNullObj {n : Nat} {h : σ} {o : ObjId} {s : State} {Q : Value → State → σ → Prop}
    (hf : s.fuel ≠ 0) (hq : Q (.bool false) s h) : WP eng answer n h (Sem.binaryOp .eq .null (.obj o)) s Q :=
  wp_of_eq (binaryOp_eq_null_obj o s hf) hq

/-- **`null == k`**, `k` a string: `false`. -/
theorem wp_eqNullStr {n : Nat} {h : σ} {k : JSStr} {s : State} {Q : Value → State → σ → Prop}
    (hf : s.fuel ≠ 0) (hq : Q (.bool false) s h) : WP eng answer n h (Sem.binaryOp .eq .null (.str k)) s Q :=
  wp_of_eq (binaryOp_eq_null_str k s hf) hq

/-- **`for (var x in …)`'s binding**: the key assigned to the variable `Scope.resolve` finds; the context unchanged. -/
theorem wp_bindForVar {N n : Nat} {h : σ} {x : JSStr} {ie : Option Expr} {ctx : Ctx} {v : Value} {s : State}
    {Q : Ctx → State → σ → Prop} (hk : depth ≤ s.fuel)
    (hw : match Scope.resolve s depth ctx.lex x with
      | some e => SetsC s e x v fun w => Q ctx w h
      | none => False) :
    WP eng answer N h (bindForLhs (n + 1) ctx (.decl .var (.ident x) ie) v) s Q := by
  cases hr : Scope.resolve s depth ctx.lex x with
  | none => rw [hr] at hw; exact hw.elim
  | some e =>
    rw [hr] at hw
    obtain ⟨bm, o, bd, he, hd, hb, hv, hm, q⟩ := setsC_setsVar hw
    rw [wp_iff_wpr]
    simp only [bindForLhs, M.bind_eq, M.bind_apply,
      Scope.resolveBinding_of_resolve s depth ctx.lex x ctx.strict e hr hk, M.bindRes_ok]
    rw [show putRefValue (.env (some e) x ctx.strict) v s = setMutableBinding e x v ctx.strict s from rfl,
      setMutableBinding_declLike e x v ctx.strict s he hd hb hv hm, M.bindRes_ok]
    exact wpr_ok q

/-- **`for (x in …)`'s binding** (`x` declared elsewhere): the key assigned to the variable. -/
theorem wp_bindForPat {N n : Nat} {h : σ} {x : JSStr} {ctx : Ctx} {v : Value} {s : State}
    {Q : Ctx → State → σ → Prop} (hk : depth ≤ s.fuel)
    (hw : match Scope.resolve s depth ctx.lex x with
      | some e => SetsC s e x v fun w => Q ctx w h
      | none => False) :
    WP eng answer N h (bindForLhs (n + 1) ctx (.pattern (.ident x)) v) s Q := by
  cases hr : Scope.resolve s depth ctx.lex x with
  | none => rw [hr] at hw; exact hw.elim
  | some e =>
    rw [hr] at hw
    obtain ⟨bm, o, bd, he, hd, hb, hv, hm, q⟩ := setsC_setsVar hw
    rw [wp_iff_wpr]
    simp only [bindForLhs, M.bind_eq, M.bind_apply,
      Scope.resolveBinding_of_resolve s depth ctx.lex x ctx.strict e hr hk, M.bindRes_ok]
    rw [show putRefValue (.env (some e) x ctx.strict) v s = setMutableBinding e x v ctx.strict s from rfl,
      setMutableBinding_declLike e x v ctx.strict s he hd hb hv hm, M.bindRes_ok]
    exact wpr_ok q

/-- **`obj[key]`**, the key a string naming an own data property of a plain object. -/
theorem wp_getStrKey {n : Nat} {h : σ} {obj ke : Sem.CExpr} {ctx : Ctx} {s : State} {Q : Value → State → σ → Prop}
    (hw : WP eng answer n h (obj ctx) s fun bv w1 h1 => WP eng answer n h1 (ke ctx) w1 fun kv w2 h2 =>
      ∃ ks, kv = .str ks ∧ GetsC w2 bv ks fun v => Q v w2 h2) :
    WP eng answer n h (Sem.getValue (Sem.memberRef obj (.computed ke) false) ctx) s Q := by
  rw [wp_iff_wpr]
  simp only [Sem.getValue, Sem.memberRef, M.bind_eq, M.bind_apply]
  apply wpr_bind
  apply wpr_bind
  refine wp_mono hw fun bv w1 h1 hk => ?_
  simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  apply wp_bind
  refine wp_mono hk fun kv w2 h2 ⟨ks, hkv, hg⟩ => ?_
  subst hkv
  refine wp_of_eq (a := Ref.prop bv (.str ks) ctx.strict none) rfl ?_
  match bv, hg with
  | .obj o, ⟨hlt, hka, hm⟩ =>
    cases hp : (w2.objEntry o).props.get? (.str ks) with
    | none => rw [hp] at hm; exact hm.elim
    | some p =>
      rw [hp] at hm
      cases p with
      | accessor => exact hm.elim
      | data v ww ee cc =>
        refine wp_of_eq ?_ hm
        rw [getRefValue_prop]
        have := Obj'.get_entry_data o (.str ks) (.obj o) w2 hlt hka (by simp [hp, isOwnData])
        rw [this, hp]; rfl

/-- **`obj.k(args)`**, `k` a data property found on `obj`'s chain of plain objects (own or inherited). -/
theorem wp_callMemberT {n : Nat} {h : σ} {obj : Sem.CExpr} {k : JSStr} {as : Array Sem.ArgD} {name : CalleeDesc}
    {ctx : Ctx} {s : State} {Q : Value → State → σ → Prop}
    (hw : WP eng answer (n + 1) h (obj ctx) s fun bv w h1 => GetsTo w bv k fun fv =>
      ArgsWP eng answer (n + 1) ctx as.toList #[] h1 w fun args w2 h2 =>
        CallableC w2 fv ∧ WP eng answer n h2 (callImpl eng fv bv args) w2 Q) :
    WP eng answer (n + 1) h (Sem.call (Sem.memberRef obj (.name k) false) (Sem.args as) false name ctx) s Q := by
  rw [wp_iff_wpr]
  simp only [Sem.call, Sem.memberRef, M.bind_eq, M.bind_apply]
  apply wpr_bind
  apply wpr_bind
  refine wp_mono hw fun bv w h1 q => ?_
  obtain ⟨o, m, hb, hc, hm, hna, q'⟩ := q
  subst hb
  simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  refine wp_of_eq (a := Ref.prop (.obj o) (.str k) ctx.strict none) rfl ?_
  rw [wp_iff_wpr]
  simp only [M.bind_apply, getRefValue_prop, Obj'.get_chain w _ _ m o hc hm hna, M.bindRes_ok, refThisValue]
  show WPR eng answer (n + 1) h1 (M.bindRes _ (M.pure (Value.obj o) w)) Q
  simp only [M.pure, M.bindRes_ok]
  apply wpr_bind
  refine wp_mono (wp_args q') fun args w2 h2 ⟨hcl, hq⟩ => ?_
  rw [wp_iff_wpr]
  simp only [M.bind_apply, isCallable_of hcl, M.bindRes_ok, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [← wp_iff_wpr]
  exact wp_call hq

end

end Logic
