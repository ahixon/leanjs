import JSProofs.ReactDSSI
import JSProofs.STRGen

/-!
# React's `scheduleTaskForRootDuringMicrotask` for a click's root (zippy docs/react-proofs.md)

The root after a click: pending lanes `SyncLane` (2), nothing suspended or pinged, the lane's expiration time unset
(-1), no callback scheduled, not rendering. The lane loop runs once (`clz32(2)` = 30: index 1), the lane's expiration
time is computed (`computeExpirationTime`), `getNextLanes` gives the sync lane, `checkIfRootIsPrerendering` says no,
the root's callback priority becomes 2 with no callback node, and 2 is returned. The four callees only read; they are
hypotheses here.
-/

open ES ES.M HostRuns Logic
open Std (HashMap)

namespace ReactSchedTaskRoot

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ}

theorem simple (d : FuncData) (hc : d.code = STRGen.scheduleTaskForRootDuringMicrotask_func) : FDI.Simple d := by
  constructor <;> rw [hc] <;> try rfl
  simp [STRGen.scheduleTaskForRootDuringMicrotask_func, Func.params, Func.info]

/-- What it writes: the lane's expiration time, the root's callback priority and node. -/
def fp (R A : ObjId) : Footprint :=
  ⟨[], [(A, .str "1"), (R, .str "callbackPriority"), (R, .str "callbackNode")], false⟩

/-- A call that only reads, giving `v`. -/
def Reads (eng : Engine) (answer : HostAnswer σ) (n : Nat) (f : ObjId) (args : Array Value) (v : Value)
    (s : State) (fpS : Footprint) (k : Nat) : Prop :=
  ∀ w h1, Frame fpS s w → s.fuel ≤ w.fuel + 40 →
    WP eng answer n h1 (callImpl eng (.obj f) .undefined args) w fun r w' _ =>
      r = v ∧ Frame {} w w' ∧ w.fuel ≤ w'.fuel + k

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
theorem call_spec {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t tm : Value} {s : State}
    {bG : HashMap JSStr Binding} {oG : Option EnvId}
    {bdC bdE bdW bdL bdG bdP : Binding} {R A fC fE fG fP : ObjId} {dE dG dP : FuncData} {bC : BuiltinData}
    {et : F64} {wl : F64} {cp : Value}
    {sw se sc pw pe pc xw xe xc lw le lc cw ce cc tw te tc nw ne nc qe qc ae ac : Bool} {L : F64}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : 100 ≤ s.fuel)
    (hcode : d.code = STRGen.scheduleTaskForRootDuringMicrotask_func) (hcls : d.isClassCtor = false)
    (hmode : d.thisMode = .strict)
    (hG : d.env < s.envs.size) (hGe : Scope.declLike? (s.envEntry d.env) = some (bG, oG))
    (hGC : bG[JSStr.ofString "clz32"]? = some bdC) (hGCv : bdC.value = some (.obj fC))
    (hGE : bG[JSStr.ofString "computeExpirationTime"]? = some bdE) (hGEv : bdE.value = some (.obj fE))
    (hGW : bG[JSStr.ofString "workInProgressRoot"]? = some bdW) (hGWv : bdW.value = some .null)
    (hGL : bG[JSStr.ofString "workInProgressRootRenderLanes"]? = some bdL) (hGLv : bdL.value = some (.num wl))
    (hGG : bG[JSStr.ofString "getNextLanes"]? = some bdG) (hGGv : bdG.value = some (.obj fG))
    (hGP : bG[JSStr.ofString "checkIfRootIsPrerendering"]? = some bdP) (hGPv : bdP.value = some (.obj fP))
    (hCo : fC < s.heap.size) (hCk : (s.objEntry fC).kind = .builtin bC)
    (hEo : fE < s.heap.size) (hEk : (s.objEntry fE).kind = .func dE)
    (hGo : fG < s.heap.size) (hGk : (s.objEntry fG).kind = .func dG)
    (hPo : fP < s.heap.size) (hPk : (s.objEntry fP).kind = .func dP)
    (hR : R < s.heap.size) (hRk : (s.objEntry R).kind.isPlain = true) (hRA : R ≠ A)
    (hRs : (s.objEntry R).props.get? (.str "suspendedLanes") = some (.data (.num (F64.fin false 0 (-1074))) sw se sc))
    (hRi : (s.objEntry R).props.get? (.str "pingedLanes") = some (.data (.num (F64.fin false 0 (-1074))) pw pe pc))
    (hRx : (s.objEntry R).props.get? (.str "expirationTimes") = some (.data (.obj A) xw xe xc))
    (hRp : (s.objEntry R).props.get? (.str "pendingLanes") =
      some (.data (.num (F64.fin false 4503599627370496 (-51))) lw le lc))
    (hRc : (s.objEntry R).props.get? (.str "cancelPendingCommit") = some (.data .null cw ce cc))
    (hRt : (s.objEntry R).props.get? (.str "timeoutHandle") =
      some (.data (.num (F64.fin false 4503599627370496 (-52)).neg) tw te tc))
    (hRn : (s.objEntry R).props.get? (.str "callbackNode") = some (.data .null true ne nc))
    (hRq : (s.objEntry R).props.get? (.str "callbackPriority") = some (.data cp true qe qc))
    (hA : A < s.heap.size) (hAk : (s.objEntry A).kind = .array) (hAE : A ≠ fE) (hAG : A ≠ fG) (hAP : A ≠ fP)
    (hRG : R ≠ fG) (hRP : R ≠ fP)
    (hA1 : (s.objEntry A).props.get? (.str "1") = some (.data (.num (F64.fin false 4503599627370496 (-52)).neg) true ae ac))
    (hAL : (s.objEntry A).props.get? (.str "length") = some (.data (.num L) true false false))
    (hL : 1 < (Conv.toNat? L).getD 0)
    (hClz : Reads eng answer n fC #[.num (F64.fin false 4503599627370496 (-51))]
      (.num (F64.fin false 8444249301319680 (-48))) s (fp R A) 2)
    (hExp : Reads eng answer n fE #[.num (F64.fin false 4503599627370496 (-51)), tm] (.num et) s (fp R A) 10)
    (hNext : Reads eng answer n fG #[.obj R, .num (F64.fin false 0 (-1074)), .bool false]
      (.num (F64.fin false 4503599627370496 (-51))) s (fp R A) 20)
    (hPre : Reads eng answer n fP #[.obj R, .num (F64.fin false 4503599627370496 (-51))] (.bool false) s (fp R A) 10) :
    WP eng answer (n + 1) h (callImpl eng (.obj fo) t #[.obj R, tm]) s fun v w _ =>
      v = .num (F64.fin false 4503599627370496 (-51)) ∧ Frame (fp R A) s w ∧ s.fuel ≤ w.fuel + 60 ∧
      (w.objEntry A).props.get? (.str "1") = some (.data (.num et) true ae ac) ∧
      (w.objEntry R).props.get? (.str "callbackPriority") =
        some (.data (.num (F64.fin false 4503599627370496 (-51))) true qe qc) ∧
      (w.objEntry R).props.get? (.str "callbackNode") = some (.data .null true ne nc) := by
  replace hClz := ReactDSSI.Hold.mk hClz
  replace hExp := ReactDSSI.Hold.mk hExp
  replace hNext := ReactDSSI.Hold.mk hNext
  replace hPre := ReactDSSI.Hold.mk hPre
  apply wp_callGen STRGen.scheduleTaskForRootDuringMicrotask_eq (by decide) hlt hk (by omega) hcls hmode
    (by rw [hcode]; rfl) (by rw [hcode]; rfl) (simple d hcode) (by rw [hcode]; rfl) (by rw [hcode]; rfl)
  have hpn : d.code.info.fdi.paramNames = #[JSStr.ofString "root", JSStr.ofString "currentTime"] := by
    rw [hcode]; rfl
  have hv : d.code.info.fdi.varNames = #[JSStr.ofString "suspendedLanes", JSStr.ofString "pingedLanes",
      JSStr.ofString "expirationTimes", JSStr.ofString "lanes", JSStr.ofString "index$5", JSStr.ofString "lane",
      JSStr.ofString "expirationTime"] := by rw [hcode]; rfl
  have hl : FDI.lexDecls d = #[] := by
    simp [FDI.lexDecls, hcode, STRGen.scheduleTaskForRootDuringMicrotask_func, Func.info]
  have ha : d.code.isAsync = false := by rw [hcode]; rfl
  have hne : s.envs.size ≠ d.env := Nat.ne_of_gt hG
  have hG1 : d.env < s.envs.size + 1 := Nat.lt_succ_of_lt hG
  clear hcode
  simp only [STRGen.scheduleTaskForRootDuringMicrotask]
  js [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGC, hGCv, hCo, hCk, hR, hRk, hRA, Ne.symm hRA, hRs, hRi, hRx,
    hRp, hA, hAk, hA1, FDI.fdiCtx, Sem.inner]
  refine ⟨by js_norm [CallableC, *], ?_⟩
  refine wp_mono ((ReactDSSI.Hold.get hClz) _ h ?fr1 ?fu1) ?post1
  case fr1 => simp only [fp]; frame_go' [*, hne, Ne.symm hne, hG1]
  case fu1 => js_side
  case post1 =>
  intro r w1 h1 ⟨hr, hF1, hfu1⟩
  subst hr
  try simp only [js_simp] at hfu1
  js [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGE, hGEv, hEo, hEk, hR, hRk, hRA, Ne.symm hRA, hRs, hRi, hRx,
    hRp, hA, hAk, hA1, hAL, hL, envEntry_frame0 hF1, objEntry_frame0 hF1, heap_frame hF1, envs_frame hF1,
    FDI.fdiCtx, Sem.inner]
  -- (`computeExpirationTime(lane, currentTime)`)
  refine ⟨by js_norm [CallableC, *, objEntry_frame0 hF1, heap_frame hF1], ?_⟩
  refine wp_mono ((ReactDSSI.Hold.get hExp) _ h1 ?fr2 ?fu2) ?post2
  case fr2 => simp only [fp]; frame_go' [*, hne, Ne.symm hne, hG1]
  case fu2 => js_side
  case post2 =>
  intro r w2 h2 ⟨hr, hF2, hfu2⟩
  subst hr
  try simp only [js_simp] at hfu2
  js [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGE, hGEv, hGW, hGWv, hGL, hGLv, hGG, hGGv, hGP, hGPv, hEo, hEk,
    hGo, hGk, hPo, hPk, hR, hRk, hRA, Ne.symm hRA, hRs, hRi, hRx, hRp, hRc, hRt, hRn, hRq, hA, hAk, hA1, hAL, hL, hAE, hAG, hAP, hRG, hRP, envEntry_frame0 hF1, objEntry_frame0 hF1, heap_frame hF1, envs_frame hF1,
    envEntry_frame0 hF2, objEntry_frame0 hF2, heap_frame hF2, envs_frame hF2, FDI.fdiCtx, Sem.inner]
  -- (`getNextLanes(root, 0, false)`)
  refine ⟨by js_norm [CallableC, *, objEntry_frame0 hF1, heap_frame hF1, objEntry_frame0 hF2, heap_frame hF2, Ne.symm hAG], ?_⟩
  refine wp_mono ((ReactDSSI.Hold.get hNext) _ h2 ?fr3 ?fu3) ?post3
  case fr3 => simp only [fp]; frame_go' [*, hne, Ne.symm hne, hG1]
  case fu3 => js_side
  case post3 =>
  intro r w3 h3 ⟨hr, hF3, hfu3⟩
  subst hr
  try simp only [js_simp] at hfu3
  js [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGE, hGEv, hGW, hGWv, hGL, hGLv, hGG, hGGv, hGP, hGPv, hEo, hEk,
    hGo, hGk, hPo, hPk, hR, hRk, hRA, Ne.symm hRA, hRs, hRi, hRx, hRp, hRc, hRt, hRn, hRq, hA, hAk, hA1, hAL, hL, hAE, hAG, hAP, hRG, hRP, envEntry_frame0 hF1, objEntry_frame0 hF1, heap_frame hF1, envs_frame hF1, envEntry_frame0 hF2, objEntry_frame0 hF2, heap_frame hF2, envs_frame hF2,
    envEntry_frame0 hF3, objEntry_frame0 hF3, heap_frame hF3, envs_frame hF3, FDI.fdiCtx, Sem.inner]
  -- (`checkIfRootIsPrerendering(root, 2)`)
  refine ⟨by js_norm [CallableC, *, objEntry_frame0 hF1, heap_frame hF1, objEntry_frame0 hF2, heap_frame hF2, objEntry_frame0 hF3, heap_frame hF3, Ne.symm hAP], ?_⟩
  refine wp_mono ((ReactDSSI.Hold.get hPre) _ h3 ?fr4 ?fu4) ?post4
  case fr4 => simp only [fp]; frame_go' [*, hne, Ne.symm hne, hG1]
  case fu4 => js_side
  case post4 =>
  intro r w4 h4 ⟨hr, hF4, hfu4⟩
  subst hr
  try simp only [js_simp] at hfu4
  js [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGE, hGEv, hGW, hGWv, hGL, hGLv, hGG, hGGv, hGP, hGPv, hEo, hEk,
    hGo, hGk, hPo, hPk, hR, hRk, hRA, Ne.symm hRA, hRs, hRi, hRx, hRp, hRc, hRt, hRn, hRq, hA, hAk, hA1, hAL, hL, hAE, hAG, hAP, hRG, hRP, envEntry_frame0 hF1, objEntry_frame0 hF1, heap_frame hF1, envs_frame hF1, envEntry_frame0 hF2, objEntry_frame0 hF2, heap_frame hF2, envs_frame hF2,
    envEntry_frame0 hF3, objEntry_frame0 hF3, heap_frame hF3, envs_frame hF3,
    envEntry_frame0 hF4, objEntry_frame0 hF4, heap_frame hF4, envs_frame hF4, FDI.fdiCtx, Sem.inner]
  all_goals (try apply And.intro)
  all_goals (try apply And.intro)
  all_goals first | rfl | omega | (simp only [fp]; frame_go' [*, hne, Ne.symm hne, hG1, hRA, Ne.symm hRA])

end

end ReactSchedTaskRoot
