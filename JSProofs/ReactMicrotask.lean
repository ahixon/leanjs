import JSProofs.ReactSchedTask

/-!
# React's microtask callback (zippy docs/react-proofs.md)

```js
function () {
  0 !== (executionContext & 6)
    ? scheduleCallback$3(ImmediatePriority, processRootScheduleInImmediateTask)
    : processRootScheduleInMicrotask();
}
```
The job a click queued (`ReactClick`): run from the event loop, outside rendering and committing, it calls
`processRootScheduleInMicrotask()` (a hypothesis here). Its names are read through its closure: the record of the
call that made it (empty), then the module's.
-/

open ES ES.M HostRuns Logic
open Std (HashMap)

namespace ReactMicrotask

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ} {HI : σ → Prop}

theorem simple (d : FuncData) (hc : d.code = SIRGen.fn5_func) : FDI.Simple d := by
  constructor <;> rw [hc] <;> try rfl
  simp [SIRGen.fn5_func, Func.params, Func.info]

theorem call_spec {n : Nat} {h : σ} {c : ObjId} {e g : EnvId} {s : State} {bG : HashMap JSStr Binding}
    {oG : Option EnvId} {bdX bdP : Binding} {ec : F64} {fP : ObjId} {dP : FuncData} {Q : State → σ → Prop}
    (hcb : ReactSchedTask.Callback s c e g) (hf : 20 ≤ s.fuel)
    (hG : g < s.envs.size) (hGe : Scope.declLike? (s.envEntry g) = some (bG, oG))
    (hGX : bG[JSStr.ofString "executionContext"]? = some bdX) (hGXv : bdX.value = some (.num ec))
    (hec : isStrictlyEqual (.num (F64.fin false 0 (-1074)))
      (.num (numberBinOp .bitAnd ec (F64.fin false 6755399441055744 (-50)))) = true)
    (hGP : bG[JSStr.ofString "processRootScheduleInMicrotask"]? = some bdP) (hGPv : bdP.value = some (.obj fP))
    (hPo : fP < s.heap.size) (hPk : (s.objEntry fP).kind = .func dP)
    (hSpec : ∀ w h1, Frame {} s w → HI h1 → s.fuel ≤ w.fuel + 2 →
      WP eng answer n h1 (callImpl eng (.obj fP) .undefined #[]) w fun _ w' h' => Q (w'.restore s) h') (hHI : HI h) :
    WP eng answer (n + 1) h (callImpl eng (.obj c) .undefined #[]) s fun v w h' => v = .undefined ∧ Q w h' := by
  replace hSpec := ReactDSSI.Hold.mk hSpec
  obtain ⟨hlt, d, hk, hcode, hmode, hcls, hde, he, hE⟩ := hcb
  subst hde
  apply wp_callGen SIRGen.fn5_eq (by decide) hlt hk (by omega) hcls hmode
    (by rw [hcode]; rfl) (by rw [hcode]; rfl) (simple d hcode) (by rw [hcode]; rfl) (by rw [hcode]; rfl)
  have hpn : d.code.info.fdi.paramNames = #[] := by rw [hcode]; rfl
  have hv : d.code.info.fdi.varNames = #[] := by rw [hcode]; rfl
  have hl : FDI.lexDecls d = #[] := by simp [FDI.lexDecls, hcode, SIRGen.fn5_func, Func.info]
  have ha : d.code.isAsync = false := by rw [hcode]; rfl
  have hne : s.envs.size ≠ d.env := Nat.ne_of_gt he
  have hne' : s.envs.size ≠ g := Nat.ne_of_gt hG
  have he1 : d.env < s.envs.size + 1 := Nat.lt_succ_of_lt he
  have hG1 : g < s.envs.size + 1 := Nat.lt_succ_of_lt hG
  clear hcode
  simp only [SIRGen.fn5]
  js [hpn, hv, hl, ha, he, he1, hG, hG1, hne, hne', Ne.symm hne, Ne.symm hne', hE, hGe, hGX, hGXv, hec, hGP, hGPv,
    hPo, hPk, FDI.fdiCtx, Sem.inner]
  refine ⟨by js_norm [CallableC, *], ?_⟩
  refine wp_mono ((ReactDSSI.Hold.get hSpec) _ h (frame_bodyState (frame_refl {} s) c d .undefined #[])
    hHI (by simp; omega)) ?post
  case post =>
    intro b w1 h1 hQ
    js [FDI.fdiCtx, Sem.inner, hQ]

end

end ReactMicrotask
