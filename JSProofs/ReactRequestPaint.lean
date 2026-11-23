import JSProofs.ReactDSSI
import JSProofs.SchedPaintGen
import JSProofs.Rebase
import JSProofs.Setter

/-!
# The scheduler's `requestPaint` (zippy docs/react-proofs.md)

```js
exports.unstable_requestPaint = function () {
  needsPaint = !0;
};
```
called by `flushSpawnedWork` (as React's `requestPaint`): the scheduler's `needsPaint` set, nothing else written.
-/

open ES ES.M HostRuns Logic
open Std (HashMap)

namespace ReactRequestPaint

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ}

theorem simple (d : FuncData) (hc : d.code = SchedPaintGen.fn0_func) : FDI.Simple d := by
  constructor <;> rw [hc] <;> try rfl
  simp [SchedPaintGen.fn0_func, Func.params, Func.info]

set_option maxRecDepth 20000 in
/-- **The call**: `needsPaint` true in the scheduler's record, nothing else written, the host untouched. -/
theorem call_spec {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t : Value} {s : State}
    {bG : HashMap JSStr Binding} {oG : Option EnvId} {bdN : Binding}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : 20 ≤ s.fuel)
    (hcode : d.code = SchedPaintGen.fn0_func) (hcls : d.isClassCtor = false) (hmode : d.thisMode = .strict)
    (hG : d.env < s.envs.size) (hGe : Scope.declLike? (s.envEntry d.env) = some (bG, oG))
    (hGN : bG[JSStr.ofString "needsPaint"]? = some bdN) (hGNm : bdN.mutable = true)
    (hGNv : bdN.value.isSome = true) :
    WP eng answer (n + 1) h (callImpl eng (.obj fo) t #[]) s fun v w h' =>
      v = .undefined ∧ Frame ⟨[(d.env, JSStr.ofString "needsPaint")], [], false⟩ s w ∧ s.fuel ≤ w.fuel + 20 ∧
        h' = h := by
  apply wp_callGen SchedPaintGen.fn0_eq (by decide) hlt hk (by omega) hcls hmode
    (by rw [hcode]; rfl) (by rw [hcode]; rfl) (simple d hcode) (by rw [hcode]; rfl) (by rw [hcode]; rfl)
  have hpn : d.code.info.fdi.paramNames = #[] := by rw [hcode]; rfl
  have hv : d.code.info.fdi.varNames = #[] := by rw [hcode]; rfl
  have hl : FDI.lexDecls d = #[] := by simp [FDI.lexDecls, hcode, SchedPaintGen.fn0_func, Func.info]
  have ha : d.code.isAsync = false := by rw [hcode]; rfl
  have hne : s.envs.size ≠ d.env := Nat.ne_of_gt hG
  have hG1 : d.env < s.envs.size + 1 := Nat.lt_succ_of_lt hG
  clear hcode
  simp only [SchedPaintGen.fn0]
  js [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGN, hGNm, hGNv, FDI.fdiCtx, Sem.inner]
  refine ⟨?fr, ?fu⟩
  case fu => first | omega | (simp [bodyState, entryState]; omega)
  case fr =>
    refine frame_restore ?_ s
    refine frame_setEnv_with_in ?_ hG (bodyState_envEntry_lt (s := s) (fo := fo) (d := d) (t := t)
      (args := #[]) _ hG) (by rw [hGe]; rfl) (by simp) _
    frame_go' []

end

end ReactRequestPaint
