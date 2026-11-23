import JSProofs.Builtins

/-!
# `Math` built-ins (zippy docs/react-proofs.md)

React binds `clz32 = Math.clz32`; its lane loops call it. The call of a one-argument `Math` function on a Number:
the function's value, nothing changed, one step of fuel.
-/

open ES ES.M HostRuns
open Std (HashMap)

namespace Logic

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ}

theorem toNum_num' (x : F64) (s : State) : toNum (.num x) s = .ok x s := by
  unfold toNum; rfl

/-- **`Math.f(x)`** of a Number, `f` a one-argument `Math` function. -/
theorem mathFn1_spec {n : Nat} {h : σ} {fo : ObjId} {bd : BuiltinData} {t : Value} {x : F64} {s : State}
    {f : F64 → F64}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .builtin bd)
    (hfn : eng.builtins[bd.id]? = some (ES.Builtins.Text.mathFn1 f)) (hf : s.fuel ≠ 0) :
    WP eng answer n h (callImpl eng (.obj fo) t #[.num x]) s fun v w h' =>
      v = .num (f x) ∧ Frame {} s w ∧ s.fuel ≤ w.fuel + 1 ∧ h' = h := by
  rw [wp_iff_wpr, callImpl_builtin eng fo bd _ t _ s hlt hk hfn hf, ← wp_iff_wpr]
  apply wp_inCallee
  have he : ES.Builtins.Text.mathFn1 f fo t #[.num x] .undefined
      { { s with fuel := s.fuel - 1 } with realm := bd.realm, script := s.script } =
      .ok (.num (f x)) { { s with fuel := s.fuel - 1 } with realm := bd.realm, script := s.script } := by
    simp only [ES.Builtins.Text.mathFn1, M.bind_eq, M.bind_apply, ES.arg]
    rw [show (#[Value.num x][0]?.getD Value.undefined) = .num x from rfl, toNum_num']
    rfl
  exact wp_of_eq he ⟨rfl, frame_same rfl rfl rfl rfl, by simp; omega, rfl⟩

set_option maxRecDepth 100000 in
/-- `Math.clz32(2)` is 30. -/
theorem clz32_two : Num.ofNat (Num.clz32 (F64.fin false 4503599627370496 (-51))) = F64.fin false 8444249301319680 (-48) := by
  rfl

end

end Logic
