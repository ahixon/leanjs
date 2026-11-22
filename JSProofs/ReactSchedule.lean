import JSProofs.ReactMarkRoot
import JSProofs.ReactDSSI
import JSProofs.SUFGen

/-!
# React's `scheduleUpdateOnFiber` for a click (zippy docs/react-proofs.md)

```js
function scheduleUpdateOnFiber(root, fiber, lane) {
  if ((root === workInProgressRoot && (2 === workInProgressSuspendedReason || 9 === …)) ||
      null !== root.cancelPendingCommit)
    prepareFreshStack(root, 0), markRootSuspended(…);
  markRootUpdated$1(root, lane);
  if (0 === (executionContext & 2) || root !== workInProgressRoot)
    root === workInProgressRoot && (…), ensureRootIsScheduled(root);
}
```
Between renders (`workInProgressRoot` null, no commit pending) and outside rendering (`executionContext & 2` is 0):
the root records the lane (`markRootUpdated$1`, `ReactMarkRoot`) and `ensureRootIsScheduled(root)` is called (a
hypothesis here, from any state framed from the start through `markRootUpdated$1`'s footprint, with the root's new
`pendingLanes`).
-/

open ES ES.M HostRuns Logic
open Std (HashMap)

namespace ReactSchedule

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ}

theorem simple (d : FuncData) (hc : d.code = SUFGen.scheduleUpdateOnFiber_func) : FDI.Simple d := by
  constructor <;> rw [hc] <;> try rfl
  simp [SUFGen.scheduleUpdateOnFiber_func, Func.params, Func.info]

/-- What `markRootUpdated$1` writes. -/
def fpM (R : ObjId) : Footprint :=
  ⟨[], [(R, .str "pendingLanes"), (R, .str "suspendedLanes"), (R, .str "pingedLanes"), (R, .str "warmLanes")], false⟩

set_option maxHeartbeats 1000000 in
theorem call_spec {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t fiber : Value} {s : State}
    {bG : HashMap JSStr Binding} {oG : Option EnvId} {bdW bdM bdX bdE : Binding} {R fM fE : ObjId}
    {dM : FuncData} {dE : FuncData} {p pl ec : F64} {pe pc ue uc ie ic we wc ce cw cc : Bool} {u i wv : Value}
    {Q : State → σ → Prop}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : 40 ≤ s.fuel)
    (hcode : d.code = SUFGen.scheduleUpdateOnFiber_func) (hcls : d.isClassCtor = false)
    (hmode : d.thisMode = .strict)
    (hG : d.env < s.envs.size) (hGe : Scope.declLike? (s.envEntry d.env) = some (bG, oG))
    (hGW : bG[JSStr.ofString "workInProgressRoot"]? = some bdW) (hGWv : bdW.value = some .null)
    (hGM : bG[JSStr.ofString "markRootUpdated$1"]? = some bdM) (hGMv : bdM.value = some (.obj fM))
    (hGX : bG[JSStr.ofString "executionContext"]? = some bdX) (hGXv : bdX.value = some (.num ec))
    (hec : isStrictlyEqual (.num (F64.fin false 0 (-1074)))
      (.num (numberBinOp .bitAnd ec (F64.fin false 4503599627370496 (-51)))) = true)
    (hGE : bG[JSStr.ofString "ensureRootIsScheduled"]? = some bdE) (hGEv : bdE.value = some (.obj fE))
    (hMo : fM < s.heap.size) (hMk : (s.objEntry fM).kind = .func dM) (hMcode : dM.code = MRUGen.fn0_func)
    (hMcls : dM.isClassCtor = false) (hMmode : dM.thisMode = .strict)
    (hEo : fE < s.heap.size) (hEk : (s.objEntry fE).kind = .func dE) (hER : fE ≠ R) (hMR : fM ≠ R)
    (hp : isStrictlyEqual (.num (F64.fin false 4503599627370496 (-24))) (.num p) = false)
    (hR : R < s.heap.size) (hRk : (s.objEntry R).kind.isPlain = true)
    (hRc : (s.objEntry R).props.get? (.str "cancelPendingCommit") = some (.data .null cw ce cc))
    (hRp : (s.objEntry R).props.get? (.str "pendingLanes") = some (.data (.num pl) true pe pc))
    (hRs : (s.objEntry R).props.get? (.str "suspendedLanes") = some (.data u true ue uc))
    (hRi : (s.objEntry R).props.get? (.str "pingedLanes") = some (.data i true ie ic))
    (hRw : (s.objEntry R).props.get? (.str "warmLanes") = some (.data wv true we wc))
    (hSpec : ∀ w h1, Frame (fpM R) s w →
      (w.objEntry R).props.get? (.str "pendingLanes") = some (.data (.num (numberBinOp .bitOr pl p)) true pe pc) →
      s.fuel ≤ w.fuel + 20 →
      WP eng answer n h1 (callImpl eng (.obj fE) .undefined #[.obj R]) w fun _ w' h' => Q (w'.restore s) h') :
    WP eng answer (n + 1) h (callImpl eng (.obj fo) t #[.obj R, fiber, .num p]) s fun v w h' =>
      v = .undefined ∧ Q w h' := by
  replace hSpec := ReactDSSI.Hold.mk hSpec
  apply wp_callGen SUFGen.scheduleUpdateOnFiber_eq (by decide) hlt hk (by omega) hcls hmode
    (by rw [hcode]; rfl) (by rw [hcode]; rfl) (simple d hcode) (by rw [hcode]; rfl) (by rw [hcode]; rfl)
  have hpn : d.code.info.fdi.paramNames = #[JSStr.ofString "root", JSStr.ofString "fiber", JSStr.ofString "lane"] := by
    rw [hcode]; rfl
  have hv : d.code.info.fdi.varNames = #[] := by rw [hcode]; rfl
  have hl : FDI.lexDecls d = #[] := by simp [FDI.lexDecls, hcode, SUFGen.scheduleUpdateOnFiber_func, Func.info]
  have ha : d.code.isAsync = false := by rw [hcode]; rfl
  have hne : s.envs.size ≠ d.env := Nat.ne_of_gt hG
  have hG1 : d.env < s.envs.size + 1 := Nat.lt_succ_of_lt hG
  clear hcode
  simp only [SUFGen.scheduleUpdateOnFiber]
  js [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGW, hGWv, hGM, hGMv, hGX, hGXv, hGE, hGEv, hMo, hMk,
    hEo, hEk, hR, hRk, hRc, FDI.fdiCtx, Sem.inner]
  refine ⟨by js_norm [CallableC, *], ?_⟩
  -- (`markRootUpdated$1(root, lane)`: its theorem)
  refine wp_mono (ReactMarkRoot.call_spec (h := h) (t := .undefined) (u := u) (i := i) (wv := wv)
    (by simpa using hMo) (by simpa using hMk) (by simp; omega) hMcode hMcls hMmode hp (by simpa using hR)
    (by simpa using hRk) (by simpa using hRp) (by simpa using hRs) (by simpa using hRi) (by simpa using hRw)) ?post
  case post =>
  intro b w1 h1 ⟨_, hFr, hfu, hp1, _, _, _⟩
  have hB : s.envs.size < (bodyState s fo d t #[.obj R, fiber, .num p]).envs.size := by simp
  have hGB : d.env < (bodyState s fo d t #[.obj R, fiber, .num p]).envs.size := by simp; omega
  have hE1 := envEntry_frame hFr hB (by simp [fpM])
  have hG1e := envEntry_frame hFr hGB (by simp [fpM])
  have hE1s : s.envs.size < w1.envs.size := envs_frame hFr hB
  have hG1s : d.env < w1.envs.size := envs_frame hFr hGB
  have hEo1 : fE < w1.heap.size := heap_frame hFr (by simpa using hEo)
  have hEk1 : (w1.objEntry fE).kind = .func dE := by
    rw [objEntry_frame hFr (by simpa using hEo) (by simp [fpM, Ne.symm hER])]; simpa using hEk
  have hRo1 : R < w1.heap.size := heap_frame hFr (by simpa using hR)
  have hRk1 : (w1.objEntry R).kind.isPlain = true := by
    rw [kind_frame hFr (by simpa using hR)]; simpa using hRk
  try simp only [js_simp] at hfu
  simp only [bodyState_envEntry] at hE1 hG1e
  js [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGW, hGWv, hGX, hGXv, hec, hGE, hGEv, hE1, hG1e, hE1s, hG1s,
    hEo1, hEk1, hRo1, hRk1, FDI.fdiCtx, Sem.inner]
  -- (`ensureRootIsScheduled(root)`: the hypothesis)
  refine ⟨by js_norm [CallableC, *], ?_⟩
  refine wp_mono ((ReactDSSI.Hold.get hSpec) _ h1 ?fr ?pend ?fu) ?post2
  case fr =>
    have := frame_trans (frame_bodyState (frame_refl {} s) fo d t #[.obj R, fiber, .num p]) hFr
    simpa [fpM, Footprint.union] using this
  case pend => simpa using hp1
  case fu => simp at hfu ⊢; omega
  case post2 =>
  intro b w2 h2 hQ
  js [FDI.fdiCtx, Sem.inner, hQ]

end

end ReactSchedule
