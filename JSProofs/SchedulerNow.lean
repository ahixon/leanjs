import JSProofs.ReactSchedTaskRoot
import JSProofs.NOWGen

/-!
# The scheduler's `unstable_now` (React's `now`) (zippy docs/react-proofs.md)

```js
exports.unstable_now = function () { return localPerformance.now(); };
```
With `performance` present: the host's `performance.now()` (a hypothesis in the reads-only shape: some Number, nothing
written). The first proof through a method call (`Logic.wp_callMemberC`).
-/

open ES ES.M HostRuns Logic
open Std (HashMap)

namespace SchedulerNow

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ} {HI : σ → Prop}

/-- A host function that only reads, called with `this` and `args`, giving `v`: from any host state the host
invariant `HI` holds of, which it keeps. -/
def HostReads (eng : Engine) (answer : HostAnswer σ) (HI : σ → Prop) (n : Nat) (f : ObjId) (thisV : Value)
    (args : Array Value) (v : Value) (s : State) (k : Nat) : Prop :=
  ∀ w h1, Frame {} s w → HI h1 → s.fuel ≤ w.fuel + 5 → 2 ≤ w.fuel →
    WP eng answer n h1 (callImpl eng (.obj f) thisV args) w fun r w' h' =>
      r = v ∧ Frame {} w w' ∧ w.fuel ≤ w'.fuel + k ∧ HI h'

theorem simple (d : FuncData) (hc : d.code = NOWGen.fn0_func) : FDI.Simple d := by
  constructor <;> rw [hc] <;> try rfl
  simp [NOWGen.fn0_func, Func.params, Func.info]

set_option maxRecDepth 10000 in
theorem call_spec {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t : Value} {s : State}
    {bG : HashMap JSStr Binding} {oG : Option EnvId} {bdP : Binding} {P PP fN : ObjId} {bP : BuiltinData}
    {pw pe pc : Bool} {tm : F64}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : 20 ≤ s.fuel)
    (hcode : d.code = NOWGen.fn0_func) (hcls : d.isClassCtor = false) (hmode : d.thisMode = .strict)
    (hG : d.env < s.envs.size) (hGe : Scope.declLike? (s.envEntry d.env) = some (bG, oG))
    (hGP : bG[JSStr.ofString "localPerformance"]? = some bdP) (hGPv : bdP.value = some (.obj P))
    (hP : P < s.heap.size) (hPk : (s.objEntry P).kind.isPlain = true)
    (hPn0 : (s.objEntry P).props.get? (.str "now") = none) (hPp : (s.objEntry P).proto = .obj PP)
    (hPP : PP < s.heap.size) (hPPk : (s.objEntry PP).kind.isPlain = true)
    (hPn : (s.objEntry PP).props.get? (.str "now") = some (.data (.obj fN) pw pe pc))
    (hNo : fN < s.heap.size) (hNk : (s.objEntry fN).kind = .builtin bP)
    (hNow : HostReads eng answer HI n fN (.obj P) #[] (.num tm) s 5) (hHI : HI h) :
    WP eng answer (n + 1) h (callImpl eng (.obj fo) t #[]) s fun v w h' =>
      v = .num tm ∧ Frame {} s w ∧ s.fuel ≤ w.fuel + 10 ∧ HI h' := by
  replace hNow := ReactDSSI.Hold.mk hNow
  apply wp_callGen NOWGen.fn0_eq (by decide) hlt hk (by omega) hcls hmode
    (by rw [hcode]; rfl) (by rw [hcode]; rfl) (simple d hcode) (by rw [hcode]; rfl) (by rw [hcode]; rfl)
  have hpn : d.code.info.fdi.paramNames = #[] := by rw [hcode]; rfl
  have hv : d.code.info.fdi.varNames = #[] := by rw [hcode]; rfl
  have hl : FDI.lexDecls d = #[] := by simp [FDI.lexDecls, hcode, NOWGen.fn0_func, Func.info]
  have ha : d.code.isAsync = false := by rw [hcode]; rfl
  have hne : s.envs.size ≠ d.env := Nat.ne_of_gt hG
  have hG1 : d.env < s.envs.size + 1 := Nat.lt_succ_of_lt hG
  clear hcode
  simp only [NOWGen.fn0]
  js [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGP, hGPv, hP, hPk, hPn0, hPp, hPP, hPPk, hPn, hNo, hNk, FDI.fdiCtx, Sem.inner]
  refine ⟨by js_norm [CallableC, *], ?_⟩
  refine wp_mono ((ReactDSSI.Hold.get hNow) _ h (frame_bodyState (frame_refl {} s) fo d t #[]) hHI (by simp; omega) (by simp; omega)) ?post
  case post =>
  intro r w1 h1 ⟨hr, hF1, hfu1, hHI1⟩
  subst hr
  try simp only [js_simp] at hfu1
  js [FDI.fdiCtx, Sem.inner, envEntry_frame0 hF1, objEntry_frame0 hF1, heap_frame hF1, envs_frame hF1]
  all_goals (try apply And.intro)
  all_goals (try apply And.intro)
  all_goals first | rfl | omega | frame_go' [*]

end

end SchedulerNow
