import JSProofs.Accessor
import JSProofs.Proto
import JSProofs.Frame
import JSProofs.SemRules

/-!
# Assigning through a setter (zippy docs/react-proofs.md)

`o.k = v` where `o`'s chain finds an accessor with a setter for `k` (DOM nodes' properties, e.g. a text node's
`nodeValue`): the setter called with `o` and `v`, one level down; the assignment's value is `v`.
-/

open ES ES.M HostRuns
open Std (HashMap)

namespace Logic

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ}

/-- Nothing changed, twice: nothing changed. -/
theorem frame_empty_trans {s u w : State} (h1 : Frame {} s u) (h2 : Frame {} u w) : Frame {} s w :=
  frame_mono (frame_trans h1 h2) (fun p hp => by simpa [Footprint.union] using hp)
    (fun p hp => by simpa [Footprint.union] using hp) (fun _ => by simp [Footprint.union])

/-- A variable `lookup` finds is one `resolve` finds, bound to that value. -/
theorem resolve_of_lookup (s : State) (x : JSStr) : ∀ (k : Nat) (e : EnvId) (v : Value),
    Scope.lookup s k e x = some v → ∃ e' bm o bd, Scope.resolve s k e x = some e' ∧ e' < s.envs.size ∧
      Scope.declLike? (s.envEntry e') = some (bm, o) ∧ bm[x]? = some bd ∧ bd.value = some v := by
  intro k
  induction k with
  | zero => intro e v hl; simp [Scope.lookup] at hl
  | succ k ih =>
    intro e v hl
    by_cases he : e < s.envs.size
    · cases hev : s.envEntry e with
      | decl b o =>
        simp only [Scope.lookup, he, hev, ↓reduceIte] at hl
        cases hb : b[x]? with
        | some bd =>
          rw [hb] at hl
          exact ⟨e, b, o, bd, by simp [Scope.resolve, he, hev, Scope.declLike?, Std.HashMap.contains_eq_isSome_getElem?, hb],
            he, by simp [hev, Scope.declLike?], hb, hl⟩
        | none =>
          rw [hb] at hl
          cases o with
          | none => exact absurd hl (by simp)
          | some o =>
            obtain ⟨e', bm, o', bd, hr, rest⟩ := ih o v hl
            refine ⟨e', bm, o', bd, ?_, rest⟩
            have : b.contains x = false := by simp [Std.HashMap.contains_eq_isSome_getElem?, hb]
            simp [Scope.resolve, he, hev, Scope.declLike?, this, hr]
      | func b o a1 a2 a3 =>
        simp only [Scope.lookup, he, hev, ↓reduceIte] at hl
        cases hb : b[x]? with
        | some bd =>
          rw [hb] at hl
          exact ⟨e, b, o, bd, by simp [Scope.resolve, he, hev, Scope.declLike?, Std.HashMap.contains_eq_isSome_getElem?, hb],
            he, by simp [hev, Scope.declLike?], hb, hl⟩
        | none =>
          rw [hb] at hl
          cases o with
          | none => exact absurd hl (by simp)
          | some o =>
            obtain ⟨e', bm, o', bd, hr, rest⟩ := ih o v hl
            refine ⟨e', bm, o', bd, ?_, rest⟩
            have : b.contains x = false := by simp [Std.HashMap.contains_eq_isSome_getElem?, hb]
            simp [Scope.resolve, he, hev, Scope.declLike?, this, hr]
      | _ => simp [Scope.lookup, he, hev] at hl
    · simp [Scope.lookup, he] at hl

/-- **`typeof x`** of a variable `lookup` finds (as `wp_ident`). -/
theorem wp_typeof_lookup {n : Nat} {h : σ} {x : JSStr} {ctx : Ctx} {s : State} {Q : Value → State → σ → Prop}
    (k : Nat) {v : Value} (hl : Scope.lookup s k ctx.lex x = some v) (hk : k ≤ s.fuel)
    (hw : WP eng answer n h (typeOf v) s fun t w h1 => Q (.str t) w h1) :
    WP eng answer n h (Sem.typeofRef (Sem.identRef x) ctx) s Q := by
  obtain ⟨e', bm, o, bd, hr, he, hd, hb, hv⟩ := resolve_of_lookup s x k ctx.lex v hl
  exact wp_typeof_ident k hr hk he hd hb hv hw

/-- **A call request** at this level: the callee one level down, then the continuation with its value. -/
theorem wpr_reqCall {α : Type} {n : Nat} {h : σ} {f t : Value} {args : Array Value} {s : State}
    {K : Outcome → State → Res α} {Q : α → State → σ → Prop}
    (hc : WP eng answer n h (callImpl eng f t args) s fun x w1 h1 => WPR eng answer (n + 1) h1 (K (.normal x) w1) Q) :
    WPR eng answer (n + 1) h (.req (.call f t args) s K) Q := by
  obtain ⟨x, w1, h1, k1, hr, b, w, h2, k2, hk, q⟩ := hc
  exact ⟨b, w, h2, k1 + k2, .call n h f t args s K x w1 h1 k1 b w h2 k2 hr hk, q⟩

/-- **`return;`**: completes with `undefined`, nothing changed. -/
theorem wp_retNone {n : Nat} {h : σ} {ctx : Ctx} {s : State} {Q : Compl → State → σ → Prop}
    (hq : Q (.ret .undefined) s h) : WP eng answer n h (Sem.ret none ctx) s Q := by
  rw [wp_iff_wpr]
  simp only [Sem.ret, M.bind_eq, M.bind_apply, Option.isSome_none, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
  exact wp_of_eq rfl hq

theorem binaryOp_ne_null_obj (o : ObjId) (s : State) (hf : s.fuel ≠ 0) :
    Sem.binaryOp .ne .null (.obj o) s = .ok (.bool true) s := by
  obtain ⟨k, hk⟩ : ∃ k, s.fuel = k + 1 := ⟨s.fuel - 1, by omega⟩
  simp only [Sem.binaryOp, isLooselyEqual, M.bind_eq, M.bind_apply]; unfold repeatFrom; rw [hk]
  rfl

theorem binaryOp_ne_null_str (k : JSStr) (s : State) (hf : s.fuel ≠ 0) :
    Sem.binaryOp .ne .null (.str k) s = .ok (.bool true) s := by
  obtain ⟨j, hj⟩ : ∃ j, s.fuel = j + 1 := ⟨s.fuel - 1, by omega⟩
  simp only [Sem.binaryOp, isLooselyEqual, M.bind_eq, M.bind_apply]; unfold repeatFrom; rw [hj]
  rfl

/-- **`null != o`**, `o` an object: `true` (fuel left: the loose equality's loop). -/
theorem wp_neNullObj {n : Nat} {h : σ} {o : ObjId} {s : State} {Q : Value → State → σ → Prop}
    (hf : s.fuel ≠ 0) (hq : Q (.bool true) s h) : WP eng answer n h (Sem.binaryOp .ne .null (.obj o)) s Q :=
  wp_of_eq (binaryOp_ne_null_obj o s hf) hq

/-- **`null != k`**, `k` a string: `true`. -/
theorem wp_neNullStr {n : Nat} {h : σ} {k : JSStr} {s : State} {Q : Value → State → σ → Prop}
    (hf : s.fuel ≠ 0) (hq : Q (.bool true) s h) : WP eng answer n h (Sem.binaryOp .ne .null (.str k)) s Q :=
  wp_of_eq (binaryOp_ne_null_str k s hf) hq

/-- `o.k = v` finds a setter for `k` on `o`'s chain; it is called next (one level down). -/
def SetsAcc (eng : Engine) (answer : HostAnswer σ) (n : Nat) (h : σ) (s : State) (base : Value) (k : JSStr)
    (v : Value) (Q : State → σ → Prop) : Prop :=
  ∃ o m g sf e c, base = .obj o ∧ PlainChain s m o (.str k) ∧ m ≤ 9999 ∧
    ordLookup s m o (.str k) = some (.accessor g sf e c) ∧ sf.isUndefined = false ∧
    WP eng answer n h (callImpl eng sf (.obj o) #[v]) s fun _ w h1 => Q w h1

theorem setsAcc_mono {n : Nat} {h : σ} {s : State} {b : Value} {k : JSStr} {v : Value} {P Q : State → σ → Prop}
    (hg : SetsAcc eng answer n h s b k v P) (hpq : ∀ w h', P w h' → Q w h') : SetsAcc eng answer n h s b k v Q := by
  obtain ⟨o, m, g, sf, e, c, hb, hc, hm, hl, hsf, q⟩ := hg
  exact ⟨o, m, g, sf, e, c, hb, hc, hm, hl, hsf, wp_mono q fun _ w h' p => hpq w h' p⟩

/-- **`obj.k = rhs`, a setter**: the setter's call with `obj` as `this` and the value. -/
theorem wp_assignMemberSet {n : Nat} {h : σ} {obj rhs : Sem.CExpr} {k : JSStr} {ctx : Ctx} {s : State}
    {Q : Value → State → σ → Prop}
    (hw : WP eng answer (n + 1) h (obj ctx) s fun bv w1 h1 =>
      WP eng answer (n + 1) h1 (rhs ctx) w1 fun v w2 h2 => SetsAcc eng answer n h2 w2 bv k v fun w3 h3 => Q v w3 h3) :
    WP eng answer (n + 1) h (Sem.assign (Sem.memberRef obj (.name k) false) rhs ctx) s Q := by
  rw [wp_iff_wpr]
  simp only [Sem.assign, Sem.memberRef, M.bind_eq, M.bind_apply]
  apply wpr_bind
  apply wpr_bind
  refine wp_mono hw fun bv w1 h1 hr => ?_
  simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  refine wp_of_eq (a := Ref.prop bv (.str k) ctx.strict none) rfl ?_
  apply wp_bind
  refine wp_mono hr fun v w2 h2 ⟨o, m, g, sf, e, c, hb, hc, hm, hl, hsf, q⟩ => ?_
  subst hb
  obtain ⟨K, hK, hKx⟩ := putRefValue_setter o k ctx.strict v w2 m g sf e c hsf hc hm hl
  rw [wp_iff_wpr]
  show WPR eng answer (n + 1) h2 (M.bindRes (fun _ => Pure.pure v) (putRefValue _ v w2)) Q
  rw [hK, M.bindRes_req]
  refine wpr_reqCall (wp_mono q fun x w3 h3 q3 => ?_)
  simp only [hKx, M.bindRes_ok]
  exact wpr_ok q3

end

end Logic
