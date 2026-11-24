import JSProofs.Accessor
import JSProofs.Destructure

/-!
# [[Get]] of a proxy (zippy docs/react-proofs.md)

A proxy whose handler's `get` is a built-in function: `p.k` is the trap's call `get(target, k, receiver)`, followed by
the invariant check against the target's own property `k` (ECMA-262 10.5.8), which an absent own property passes. A
legacy platform object (the document) is such a proxy over its wrapper on Zippy's Lean engine.
-/

open ES ES.M HostRuns
open Std (HashMap)

namespace Logic

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ}

/-- **[[Get]] of a proxy**: its handler `H`'s `get` (a built-in `f`, a data property of the plain handler) called with
the target, the key and the receiver; the result returned when the target has, after the call, no own property `k`. -/
theorem wp_get_proxy {n : Nat} {h : σ} {o t H f : ObjId} {cl ct : Bool} {k : JSStr} {r : Value} {s : State}
    {bd : BuiltinData} {w e c : Bool} {Q : Value → State → σ → Prop}
    (ho : o < s.heap.size) (hk : (s.objEntry o).kind = .proxy (some t) (some H) cl ct)
    (hH : H < s.heap.size) (hHk : (s.objEntry H).kind.isPlain = true)
    (hHg : (s.objEntry H).props.get? (.str (JSStr.ofString "get")) = some (.data (.obj f) w e c))
    (hf : f < s.heap.size) (hfk : (s.objEntry f).kind = .builtin bd)
    (hc : WP eng answer n h (callImpl eng (.obj f) (.obj H) #[.obj t, .str k, r]) s fun v w' h' =>
      t < w'.heap.size ∧ (w'.objEntry t).kind.isPlain = true ∧ (w'.objEntry t).props.get? (.str k) = none ∧
        Q v w' h') :
    WP eng answer (n + 1) h (Obj'.get o (.str k) r) s Q := by
  have hgm : getMethod 19999 (.obj H) (.str (JSStr.ofString "get")) s = .ok (some (.obj f)) s := by
    rw [show (19999 : Nat) = 19998 + 1 from rfl]
    simp only [getMethod, M.bind_eq, M.bind_apply]
    rw [show (19998 : Nat) = 19997 + 1 from rfl]
    simp only [getV]
    rw [show (19997 : Nat) = 19994 + 3 from rfl,
      get_entry_data 19994 H _ (.obj H) s hH hHk (by rw [hHg]; rfl), hHg]
    simp [ownDataValue, Value.isNullish, isCallable, readObj_entry' _ _ _ hf, hfk, M.bindRes_ok, Pure.pure, M.pure]
  unfold Obj'.get
  rw [show maxDepth = 19999 + 1 from rfl, ES.get.eq_2, wp_iff_wpr]
  simp only [M.bind_eq, M.bind_apply, objKind, readObj_entry' _ _ _ ho, M.bindRes_ok, hk, proxyParts, Pure.pure,
    M.pure]
  rw [hgm, M.bindRes_ok]
  apply wpr_bind
  refine wp_call (wp_mono hc fun v w' h' ⟨htl, htk, htn, q⟩ => ?_)
  rw [wp_iff_wpr]
  simp only [M.bind_eq, M.bind_apply]
  rw [show (19999 : Nat) = 19998 + 1 from rfl, getOwnProperty_entry 19998 t _ w' htl htk, M.bindRes_ok, htn]
  exact wpr_ok q

end

end Logic
