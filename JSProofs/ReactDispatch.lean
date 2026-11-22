import JSProofs.ReactLane
import JSProofs.DSSGen

/-!
# React's `dispatchSetState` (zippy docs/react-proofs.md)

```js
function dispatchSetState(fiber, queue, action) {
  var lane = requestUpdateLane();
  dispatchSetStateInternal(fiber, queue, action, lane);
}
```
`setN(v)` is `dispatchSetState` bound to the hook's fiber and queue. In a click it asks for the lane (the event's
priority, `ReactLane.rul_spec`) and hands the update to `dispatchSetStateInternal` with it. The proof reads its own
variables and the module's after the first call through that call's frame (`envEntry_frame`); the second callee is a
hypothesis here (`hD`: its spec from any state the first call can leave, i.e. framed from the start).
-/

open ES ES.M HostRuns Logic
open Std (HashMap)

namespace ReactDispatch

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ}

theorem simple (d : FuncData) (hc : d.code = DSSGen.dispatchSetState_func) : FDI.Simple d := by
  constructor <;> rw [hc] <;> try rfl
  simp [DSSGen.dispatchSetState_func, Func.params, Func.info]

/-- **`dispatchSetState(fiber, queue, action)`** in a click calls `dispatchSetStateInternal(fiber, queue, action,
p)` with the event's priority `p` as the lane, from a state framed from the start; whatever that call ensures
(`R`) holds at the end, and `dispatchSetState` returns `undefined`. -/
theorem call_spec {n : Nat} {h : σ} {fo fL fR fD : ObjId} {d dL dR : FuncData} {t fiber queue action : Value}
    {s : State} {bG : HashMap JSStr Binding} {oG : Option EnvId} {bdI bdS bdE bdR bdL bdD : Binding}
    {I S : ObjId} {p ec : F64} {wp ep cp wt et ct : Bool} {R : State → σ → Prop}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : 60 ≤ s.fuel)
    (hcode : d.code = DSSGen.dispatchSetState_func) (hcls : d.isClassCtor = false) (hmode : d.thisMode = .strict)
    (hG : d.env < s.envs.size) (hGe : s.envEntry d.env = .decl bG oG)
    (hGL : bG[JSStr.ofString "requestUpdateLane"]? = some bdL) (hGLv : bdL.value = some (.obj fL))
    (hGD : bG[JSStr.ofString "dispatchSetStateInternal"]? = some bdD) (hGDv : bdD.value = some (.obj fD))
    (hGI : bG[JSStr.ofString "ReactDOMSharedInternals"]? = some bdI) (hGIv : bdI.value = some (.obj I))
    (hGS : bG[JSStr.ofString "ReactSharedInternals"]? = some bdS) (hGSv : bdS.value = some (.obj S))
    (hGE : bG[JSStr.ofString "executionContext"]? = some bdE) (hGEv : bdE.value = some (.num ec))
    (hGR : bG[JSStr.ofString "resolveUpdatePriority"]? = some bdR) (hGRv : bdR.value = some (.obj fR))
    (hec : isStrictlyEqual (.num (F64.fin false 0 (-1074)))
      (.num (numberBinOp .bitAnd ec (F64.fin false 4503599627370496 (-51)))) = true)
    (hL : fL < s.heap.size) (hLk : (s.objEntry fL).kind = .func dL)
    (hLcode : dL.code = RULGen.requestUpdateLane_func) (hLcls : dL.isClassCtor = false)
    (hLmode : dL.thisMode = .strict) (hLenv : dL.env = d.env)
    (hR : fR < s.heap.size) (hRk : (s.objEntry fR).kind = .func dR)
    (hRcode : dR.code = RULGen.resolveUpdatePriority_func) (hRcls : dR.isClassCtor = false)
    (hRmode : dR.thisMode = .strict) (hRenv : dR.env = d.env)
    (hI : I < s.heap.size) (hIk : (s.objEntry I).kind.isPlain = true)
    (hIp : (s.objEntry I).props.get? (.str "p") = some (.data (.num p) wp ep cp))
    (hp : isStrictlyEqual (.num (F64.fin false 0 (-1074))) (.num p) = false)
    (hS : S < s.heap.size) (hSk : (s.objEntry S).kind.isPlain = true)
    (hST : (s.objEntry S).props.get? (.str "T") = some (.data .null wt et ct))
    (hD : fD < s.heap.size ∧ ∃ dD, (s.objEntry fD).kind = .func dD)
    (hDspec : ∀ w h1, Frame {} s w → s.fuel ≤ w.fuel + 4 →
      WP eng answer (n + 1) h1 (callImpl eng (.obj fD) .undefined #[fiber, queue, action, .num p]) w
        fun _ w' h' => R (w'.restore s) h') :
    WP eng answer (n + 2) h (callImpl eng (.obj fo) t #[fiber, queue, action]) s fun v w h' =>
      v = .undefined ∧ R w h' := by
  apply wp_callGen DSSGen.dispatchSetState_eq (by decide) hlt hk (by omega) hcls hmode
    (by rw [hcode]; rfl) (by rw [hcode]; rfl) (simple d hcode) (by rw [hcode]; rfl) (by rw [hcode]; rfl)
  have hpn : d.code.info.fdi.paramNames =
      #[JSStr.ofString "fiber", JSStr.ofString "queue", JSStr.ofString "action"] := by rw [hcode]; rfl
  have hv : d.code.info.fdi.varNames = #[JSStr.ofString "lane"] := by rw [hcode]; rfl
  have hl : FDI.lexDecls d = #[] := by simp [FDI.lexDecls, hcode, DSSGen.dispatchSetState_func, Func.info]
  have ha : d.code.isAsync = false := by rw [hcode]; rfl
  have hne : s.envs.size ≠ d.env := Nat.ne_of_gt hG
  have hG1 : d.env < s.envs.size + 1 := Nat.lt_succ_of_lt hG
  clear hcode
  simp only [DSSGen.dispatchSetState]
  js [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGL, hGLv, hGD, hGDv, hL, hLk, FDI.fdiCtx, Sem.inner]
  -- (`requestUpdateLane()`: its theorem, then the rest through its frame)
  refine ⟨by simp [CallableC, hL, hLk], ?_⟩
  have hGd' : (bodyState s fo d t #[fiber, queue, action]).envEntry dL.env = .decl bG oG := by
    rw [hLenv, bodyState_envEntry_lt _ _ _ _ _ _ hG, hGe]
  refine wp_mono (ReactLane.rul_spec (by simpa using hL) (by simpa using hLk) (by simp; omega) hLcode hLcls
    hLmode (by simpa [hLenv] using hG1) hGd' hGI hGIv hGS hGSv hGE hGEv hGR hGRv hec (by simpa using hR)
    (by simpa using hRk) hRcode hRcls hRmode (by rw [hRenv, hLenv]) (by simpa using hI) (by simpa using hIk)
    (by simpa using hIp) hp (by simpa using hS) (by simpa using hSk) (by simpa using hST)) ?_
  intro v w1 h1 ⟨hv, hF, hfu⟩
  subst hv
  have hE1 : s.envs.size < w1.envs.size := by have := hF.envs_le; simp at this; omega
  have hEe := envEntry_frame hF (e := s.envs.size) (by simp) (by simp)
  have hGe1 := envEntry_frame hF (e := d.env) (by simp; omega) (by simp)
  have hfu1 : 50 ≤ w1.fuel := by simp at hfu; omega
  have hGw1 : d.env < w1.envs.size := Nat.lt_trans hG hE1
  have hD1 : fD < w1.heap.size := Nat.lt_of_lt_of_le (by simpa using hD.1) hF.heap_le
  obtain ⟨dD, hDk⟩ := hD.2
  have hDk1 := objEntry_frame hF (o := fD) (by simpa using hD.1) (by simp)
  rw [bodyState_objEntry] at hDk1
  js [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGL, hGLv, hGD, hGDv, hE1, hEe, hGe1, hfu1, hGw1, hD1, hDk1,
    hDk, FDI.fdiCtx, Sem.inner]
  -- (`dispatchSetStateInternal(fiber, queue, action, lane)`: from a state framed from the start)
  have hF1 : Frame {} s w1 := by simpa using frame_trans (frame_bodyState (frame_refl {} s) fo d t _) hF
  refine ⟨by simp [CallableC, hD1, hDk1, hDk], wp_mono (hDspec _ h1 (frame_setEnv_new hF1 (by simp) _) ?_) ?_⟩
  · simp at hfu ⊢; omega
  · intro v' w' h' r
    simp only [StmtsWP_nil]
    exact ⟨trivial, r⟩

end

end ReactDispatch
