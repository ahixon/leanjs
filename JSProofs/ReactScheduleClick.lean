import JSProofs.ReactSchedule
import JSProofs.ReactEnsureRoot
import JSProofs.ReactSchedTask

/-!
# A click's update scheduled, down to the microtask (zippy docs/react-proofs.md)

`scheduleUpdateOnFiber(root, fiber, lane)` (`ReactSchedule`) with its hypothesis about `ensureRootIsScheduled`
discharged by `ReactEnsureRoot`, whose hypothesis about `scheduleImmediateRootScheduleTask` is discharged by
`ReactSchedTask`: what is left is the host's `queueMicrotask`, called with React's closure (`Callback`) from a state
in which the root records the lane, the schedule holds the root, and a microtask is marked scheduled. The module's
functions share one record (`d.env`); each callee's premises are the start's, read through the frames so far.
-/

open ES ES.M HostRuns Logic
open Std (HashMap)

namespace ReactScheduleClick

/-- What scheduling a click's update writes, up to `queueMicrotask`. -/
def fpAll (R : ObjId) (e : EnvId) : Footprint :=
  ⟨[(e, "firstScheduledRoot"), (e, "lastScheduledRoot"), (e, "mightHavePendingSyncWork"), (e, "didScheduleMicrotask")],
   [(R, .str "pendingLanes"), (R, .str "suspendedLanes"), (R, .str "pingedLanes"), (R, .str "warmLanes")], false⟩

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ}

theorem call_spec {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t fiber : Value} {s : State}
    {bG : HashMap JSStr Binding} {oG : Option EnvId} {bdW bdM bdX bdE : Binding} {R fM fE : ObjId}
    {dM : FuncData} {dE : FuncData} {p pl ec : F64} {pe pc ue uc ie ic we wc ce cw cc : Bool} {u i wv : Value}
    {bdF bdL bdMP bdD bdS bdQ : Binding} {fS fQ : ObjId} {dS : FuncData} {bQ : BuiltinData} {ne nw nc : Bool}
    {Q : State → σ → Prop}
    -- (`scheduleUpdateOnFiber`)
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : 60 ≤ s.fuel)
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
    -- (`ensureRootIsScheduled`: the module's record; the schedule empty, no microtask pending)
    (hEcode : dE.code = ERSGen.ensureRootIsScheduled_func) (hEcls : dE.isClassCtor = false)
    (hEmode : dE.thisMode = .strict) (hEenv : dE.env = d.env)
    (hGF : bG[JSStr.ofString "firstScheduledRoot"]? = some bdF) (hGFm : bdF.mutable = true)
    (hGFv : bdF.value.isSome = true)
    (hGL : bG[JSStr.ofString "lastScheduledRoot"]? = some bdL) (hGLm : bdL.mutable = true)
    (hGLv : bdL.value = some .null)
    (hGP : bG[JSStr.ofString "mightHavePendingSyncWork"]? = some bdMP) (hGPm : bdMP.mutable = true)
    (hGPv : bdMP.value.isSome = true)
    (hGD : bG[JSStr.ofString "didScheduleMicrotask"]? = some bdD) (hGDm : bdD.mutable = true)
    (hGDv : bdD.value = some (.bool false))
    (hGS : bG[JSStr.ofString "scheduleImmediateRootScheduleTask"]? = some bdS) (hGSv : bdS.value = some (.obj fS))
    (hSo : fS < s.heap.size) (hSk : (s.objEntry fS).kind = .func dS) (hSR : fS ≠ R)
    (hRn : (s.objEntry R).props.get? (.str "next") = some (.data .null nw ne nc))
    -- (`scheduleImmediateRootScheduleTask`)
    (hScode : dS.code = SIRGen.scheduleImmediateRootScheduleTask_func) (hScls : dS.isClassCtor = false)
    (hSmode : dS.thisMode = .strict) (hSenv : dS.env = d.env)
    (hGQ : bG[JSStr.ofString "scheduleMicrotask"]? = some bdQ) (hGQv : bdQ.value = some (.obj fQ))
    (hQo : fQ < s.heap.size) (hQk : (s.objEntry fQ).kind = .builtin bQ) (hQR : fQ ≠ R)
    (hP : ((s.realms[dS.realm]!).intrinsics["%Function.prototype%"]?).isSome = true)
    -- (the host's `queueMicrotask(callback)`)
    (hQM : ∀ w h1 c e, Frame (fpAll R d.env) s w → ReactEnsureRoot.Scheduled w d.env oG R →
      ReactSchedTask.Callback w c e d.env →
      (w.objEntry R).props.get? (.str "pendingLanes") = some (.data (.num (numberBinOp .bitOr pl p)) true pe pc) →
      s.fuel ≤ w.fuel + 24 →
      WP eng answer n h1 (callImpl eng (.obj fQ) .undefined #[.obj c]) w fun _ w' h' => Q (w'.restore s) h') :
    WP eng answer (n + 3) h (callImpl eng (.obj fo) t #[.obj R, fiber, .num p]) s fun v w h' =>
      v = .undefined ∧ Q w h' := by
  refine ReactSchedule.call_spec (u := u) (i := i) (wv := wv) hlt hk (by omega) hcode hcls hmode hG hGe hGW hGWv hGM
    hGMv hGX hGXv hec hGE hGEv hMo hMk hMcode hMcls hMmode hEo hEk hER hMR hp hR hRk hRc hRp hRs hRi hRw ?ers
  case ers =>
  intro w h1 hF1 hpend1 hfu1
  -- (`ensureRootIsScheduled(root)` from `w`: the start's facts through `markRootUpdated$1`'s frame)
  have hGw : d.env < w.envs.size := envs_frame hF1 hG
  have hGew : w.envEntry d.env = s.envEntry d.env := envEntry_frame hF1 hG (by simp [ReactSchedule.fpM])
  have hobj : ∀ o, o < s.heap.size → o ≠ R → w.objEntry o = s.objEntry o := fun o ho hoR =>
    objEntry_frame hF1 ho (by simp [ReactSchedule.fpM, Ne.symm hoR])
  refine wp_mono (ReactEnsureRoot.call_spec (n := n + 1) (h := h1) (fo := fE) (d := dE) (t := .undefined) (s := w)
    (bG := bG) (oG := oG) (R := R) (fS := fS) (dS := dS) (Q := fun x h => Q (x.restore s) h)
    (heap_frame hF1 hEo) (by rw [hobj _ hEo hER]; exact hEk) (by omega) hEcode hEcls hEmode (by rw [hEenv]; exact hGw)
    (by rw [hEenv, hGew]; exact hGe) hGF hGFm hGFv hGL hGLm hGLv hGP hGPm hGPv hGD hGDm hGDv hGS hGSv
    (heap_frame hF1 hSo) (by rw [hobj _ hSo hSR]; exact hSk) (heap_frame hF1 hR)
    (by rw [kind_frame hF1 hR]; exact hRk)
    (by rw [props_frame hF1 hR (by simp [ReactSchedule.fpM])]; exact hRn) ?sir) fun _ w' h' ⟨_, q⟩ => q
  case sir =>
  intro w2 h2 hF2 hSch2 hfu2
  rw [hEenv] at hF2 hSch2
  -- (`scheduleImmediateRootScheduleTask()` from `w2`)
  have hG2 : d.env < w2.envs.size := envs_frame hF2 hGw
  obtain ⟨bW, hW, hWx⟩ := declLike_frame hF2 hGw (bs := bG) (o := oG) (by rw [hGew]; exact hGe)
  have hWQ : bW[JSStr.ofString "scheduleMicrotask"]? = some bdQ := by
    rw [hWx _ (by simp [ReactEnsureRoot.fp])]; exact hGQ
  have hobj2 : ∀ o, o < w.heap.size → w2.objEntry o = w.objEntry o := fun o ho =>
    objEntry_frame hF2 ho (by simp [ReactEnsureRoot.fp])
  refine wp_mono (ReactSchedTask.call_spec (n := n) (h := h2) (fo := fS) (d := dS) (t := .undefined) (s := w2)
    (bG := bW) (oG := oG) (fM := fQ) (bM := bQ) (Q := fun x h => Q (x.restore s) h)
    (heap_frame hF2 (heap_frame hF1 hSo)) (by rw [hobj2 _ (heap_frame hF1 hSo), hobj _ hSo hSR]; exact hSk)
    (by omega) hScode hScls hSmode (by rw [hSenv]; exact hG2) (by rw [hSenv]; exact hW) hWQ hGQv
    (heap_frame hF2 (heap_frame hF1 hQo)) (by rw [hobj2 _ (heap_frame hF1 hQo), hobj _ hQo hQR]; exact hQk)
    (by rw [hF2.realms_eq, hF1.realms_eq]; exact hP) ?qm) fun _ w' h' ⟨_, q⟩ => by simpa using q
  case qm =>
  intro w3 h3 hF3 hCb hfu3
  rw [hSenv] at hCb
  refine wp_mono (hQM w3 h3 _ _ ?fr ?sch hCb ?pend (by omega)) fun _ w' h' q => by simpa using q
  case fr =>
    have := frame_trans (frame_trans hF1 hF2) hF3
    simpa [Footprint.union, ReactSchedule.fpM, ReactEnsureRoot.fp, fpAll] using this
  case sch =>
    obtain ⟨bS, hS1, hS2⟩ := hSch2
    exact ⟨bS, by rw [envEntry_frame0 hF3 hG2]; exact hS1, hS2⟩
  case pend =>
    rw [objEntry_frame0 hF3 (heap_frame hF2 (heap_frame hF1 hR)), hobj2 _ (heap_frame hF1 hR)]
    exact hpend1

end

end ReactScheduleClick
