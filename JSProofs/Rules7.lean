import JSProofs.Rules6

/-!
# `typeof obj.k` (zippy docs/react-proofs.md)

React's `shouldSetTextContent`: `"string" === typeof props.children`.
-/

open ES ES.M HostRuns
open Std (HashMap)

namespace Logic

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ}

/-- **`typeof obj.k`** for an own data property of a plain object. -/
theorem wp_typeofMemberC {n : Nat} {h : σ} {obj : Sem.CExpr} {k : JSStr} {ctx : Ctx} {s : State}
    {Q : Value → State → σ → Prop}
    (hw : WP eng answer n h (obj ctx) s fun bv w h1 => GetsC w bv k fun v => TypeofC w v fun t => Q (.str t) w h1) :
    WP eng answer n h (Sem.typeofRef (Sem.memberRef obj (.name k) false) ctx) s Q := by
  rw [wp_iff_wpr]
  simp only [Sem.typeofRef, Sem.memberRef, M.bind_eq, M.bind_apply]
  apply wpr_bind
  apply wpr_bind
  refine wp_mono hw fun bv w h1 q => ?_
  obtain ⟨o, m, hb, hc, hm, hna, q'⟩ := getsC_getsTo q
  subst hb
  obtain ⟨t, ht, hq⟩ := typeOf_of q'
  simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  refine wp_of_eq (a := Ref.prop (.obj o) (.str k) ctx.strict none) rfl ?_
  rw [wp_iff_wpr]
  simp only [M.bind_apply, getRefValue_prop, Obj'.get_chain w _ _ m o hc hm hna, M.bindRes_ok]
  rw [ht]
  exact wp_of_eq rfl hq

end

end Logic
