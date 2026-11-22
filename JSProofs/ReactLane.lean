import JSProofs.Calls2
import JSProofs.RULGen

/-!
# React's update lane for a click (zippy docs/react-proofs.md)

```js
function resolveUpdatePriority() {
  var updatePriority = ReactDOMSharedInternals.p;
  if (0 !== updatePriority) return updatePriority;
  ...
}
function requestUpdateLane() {
  return 0 !== (executionContext & 2) && 0 !== workInProgressRootRenderLanes
    ? workInProgressRootRenderLanes & -workInProgressRootRenderLanes
    : null !== ReactSharedInternals.T ? requestTransitionLane() : resolveUpdatePriority();
}
```
`setState` asks `requestUpdateLane()` which lane an update gets. Outside rendering and transitions it is the
current event's priority, which React's event system set (`ReactDOMSharedInternals.p`): `resolveUpdatePriority`
returns it (`rup_spec`), and `requestUpdateLane` returns what `resolveUpdatePriority` does (`rul_spec`), the second
function's proof using the first's theorem at its call.
-/

open ES ES.M HostRuns Logic
open Std (HashMap)

namespace ReactLane

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ}

theorem simple_rup (d : FuncData) (hc : d.code = RULGen.resolveUpdatePriority_func) : FDI.Simple d := by
  constructor <;> rw [hc] <;> try rfl
  simp [RULGen.resolveUpdatePriority_func, Func.params, Func.info]

/-- **`resolveUpdatePriority()`** while an event's priority `p ≠ 0` is set returns it. The module's record (the
function's environment, a declarative record) holds `ReactDOMSharedInternals`, a plain object with own `p`. -/
theorem rup_spec {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t : Value} {s : State}
    {bG : HashMap JSStr Binding} {oG : Option EnvId} {bdI : Binding} {I : ObjId} {p : F64} {wp ep cp : Bool}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : 20 ≤ s.fuel)
    (hcode : d.code = RULGen.resolveUpdatePriority_func) (hcls : d.isClassCtor = false)
    (hmode : d.thisMode = .strict)
    (hG : d.env < s.envs.size) (hGe : s.envEntry d.env = .decl bG oG)
    (hGb : bG[JSStr.ofString "ReactDOMSharedInternals"]? = some bdI) (hGv : bdI.value = some (.obj I))
    (hI : I < s.heap.size) (hIk : (s.objEntry I).kind.isPlain = true)
    (hIp : (s.objEntry I).props.get? (.str "p") = some (.data (.num p) wp ep cp))
    (hp : isStrictlyEqual (.num (F64.fin false 0 (-1074))) (.num p) = false) :
    WP eng answer n h (callImpl eng (.obj fo) t #[]) s fun v _ _ => v = .num p := by
  apply wp_callGen RULGen.resolveUpdatePriority_eq (by decide) hlt hk (by omega) hcls hmode
    (by rw [hcode]; rfl) (by rw [hcode]; rfl) (simple_rup d hcode) (by rw [hcode]; rfl) (by rw [hcode]; rfl)
  have hpn : d.code.info.fdi.paramNames = #[] := by rw [hcode]; rfl
  have hv : d.code.info.fdi.varNames = #[JSStr.ofString "updatePriority"] := by rw [hcode]; rfl
  have hl : FDI.lexDecls d = #[] := by simp [FDI.lexDecls, hcode, RULGen.resolveUpdatePriority_func, Func.info]
  have ha : d.code.isAsync = false := by rw [hcode]; rfl
  have hne : s.envs.size ≠ d.env := Nat.ne_of_gt hG
  have hG1 : d.env < s.envs.size + 1 := Nat.lt_succ_of_lt hG
  clear hcode
  simp only [RULGen.resolveUpdatePriority]
  js [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGb, hGv, hI, hIk, hIp, hp, FDI.fdiCtx, Sem.inner]

theorem simple_rul (d : FuncData) (hc : d.code = RULGen.requestUpdateLane_func) : FDI.Simple d := by
  constructor <;> rw [hc] <;> try rfl
  simp [RULGen.requestUpdateLane_func, Func.params, Func.info]

/-- **`requestUpdateLane()`** outside rendering (`executionContext` without the render bit) and outside
transitions (`ReactSharedInternals.T` null) returns the event's priority, by `resolveUpdatePriority`'s theorem. -/
theorem rul_spec {n : Nat} {h : σ} {fo fR : ObjId} {d dR : FuncData} {t : Value} {s : State}
    {bG : HashMap JSStr Binding} {oG : Option EnvId} {bdI bdS bdE bdR : Binding} {I S : ObjId} {p ec : F64}
    {wp ep cp wt et ct : Bool}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : 40 ≤ s.fuel)
    (hcode : d.code = RULGen.requestUpdateLane_func) (hcls : d.isClassCtor = false)
    (hmode : d.thisMode = .strict)
    (hG : d.env < s.envs.size) (hGe : s.envEntry d.env = .decl bG oG)
    (hGI : bG[JSStr.ofString "ReactDOMSharedInternals"]? = some bdI) (hGIv : bdI.value = some (.obj I))
    (hGS : bG[JSStr.ofString "ReactSharedInternals"]? = some bdS) (hGSv : bdS.value = some (.obj S))
    (hGE : bG[JSStr.ofString "executionContext"]? = some bdE) (hGEv : bdE.value = some (.num ec))
    (hGR : bG[JSStr.ofString "resolveUpdatePriority"]? = some bdR) (hGRv : bdR.value = some (.obj fR))
    (hec : isStrictlyEqual (.num (F64.fin false 0 (-1074)))
      (.num (numberBinOp .bitAnd ec (F64.fin false 4503599627370496 (-51)))) = true)
    (hR : fR < s.heap.size) (hRk : (s.objEntry fR).kind = .func dR)
    (hRcode : dR.code = RULGen.resolveUpdatePriority_func) (hRcls : dR.isClassCtor = false)
    (hRmode : dR.thisMode = .strict) (hRenv : dR.env = d.env)
    (hI : I < s.heap.size) (hIk : (s.objEntry I).kind.isPlain = true)
    (hIp : (s.objEntry I).props.get? (.str "p") = some (.data (.num p) wp ep cp))
    (hp : isStrictlyEqual (.num (F64.fin false 0 (-1074))) (.num p) = false)
    (hS : S < s.heap.size) (hSk : (s.objEntry S).kind.isPlain = true)
    (hST : (s.objEntry S).props.get? (.str "T") = some (.data .null wt et ct)) :
    WP eng answer (n + 1) h (callImpl eng (.obj fo) t #[]) s fun v _ _ => v = .num p := by
  apply wp_callGen RULGen.requestUpdateLane_eq (by decide) hlt hk (by omega) hcls hmode
    (by rw [hcode]; rfl) (by rw [hcode]; rfl) (simple_rul d hcode) (by rw [hcode]; rfl) (by rw [hcode]; rfl)
  have hpn : d.code.info.fdi.paramNames = #[] := by rw [hcode]; rfl
  have hv : d.code.info.fdi.varNames = #[] := by rw [hcode]; rfl
  have hl : FDI.lexDecls d = #[] := by simp [FDI.lexDecls, hcode, RULGen.requestUpdateLane_func, Func.info]
  have ha : d.code.isAsync = false := by rw [hcode]; rfl
  have hne : s.envs.size ≠ d.env := Nat.ne_of_gt hG
  have hG1 : d.env < s.envs.size + 1 := Nat.lt_succ_of_lt hG
  clear hcode
  simp only [RULGen.requestUpdateLane]
  js [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGI, hGIv, hGS, hGSv, hGE, hGEv, hGR, hGRv, hec,
    hS, hSk, hST, FDI.fdiCtx, Sem.inner]
  -- (the call `resolveUpdatePriority()`: its theorem, in this body's state)
  refine ⟨by simp [CallableC, hR, hRk], ?_⟩
  have hGd' : (bodyState s fo d t #[]).envEntry dR.env = .decl bG oG := by
    rw [hRenv, bodyState_envEntry_lt _ _ _ _ _ _ hG, hGe]
  exact rup_spec (by simpa using hR) (by simpa using hRk) (by simp; omega) hRcode hRcls hRmode
    (by simpa [hRenv] using hG1) hGd' hGI hGIv (by simpa using hI) (by simpa using hIk) (by simpa using hIp) hp

end

end ReactLane
