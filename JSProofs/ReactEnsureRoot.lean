import JSProofs.ReactDSSI
import JSProofs.ERSGen
import JSProofs.Rebase
import JSProofs.Setter

/-!
# React's `ensureRootIsScheduled` after a click's update (zippy docs/react-proofs.md)

```js
function ensureRootIsScheduled(root) {
  root !== lastScheduledRoot && null === root.next &&
    (null === lastScheduledRoot
      ? (firstScheduledRoot = lastScheduledRoot = root)
      : (lastScheduledRoot = lastScheduledRoot.next = root));
  mightHavePendingSyncWork = !0;
  didScheduleMicrotask ||
    ((didScheduleMicrotask = !0), scheduleImmediateRootScheduleTask());
}
```
In the steady state between clicks no root is scheduled (`lastScheduledRoot` null, the root's `next` null) and no
microtask is pending: the root becomes the schedule's only root, pending sync work is noted, a microtask is marked
scheduled and `scheduleImmediateRootScheduleTask` called (a hypothesis here: from any state framed from the start).
-/

open ES ES.M HostRuns Logic
open Std (HashMap)

namespace ReactEnsureRoot

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ}

theorem simple (d : FuncData) (hc : d.code = ERSGen.ensureRootIsScheduled_func) : FDI.Simple d := by
  constructor <;> rw [hc] <;> try rfl
  simp [ERSGen.ensureRootIsScheduled_func, Func.params, Func.info]

/-- What `ensureRootIsScheduled` writes. -/
def fp (e : EnvId) : Footprint :=
  ⟨[(e, "firstScheduledRoot"), (e, "lastScheduledRoot"), (e, "mightHavePendingSyncWork"),
    (e, "didScheduleMicrotask")], [], false⟩

/-- The schedule after the call: the root first and last, sync work pending, a microtask marked scheduled. -/
def Scheduled (w : State) (e : EnvId) (oG : Option EnvId) (R : ObjId) : Prop :=
  ∃ bW, Scope.declLike? (w.envEntry e) = some (bW, oG) ∧
    (bW[JSStr.ofString "firstScheduledRoot"]?.bind (·.value)) = some (.obj R) ∧
    (bW[JSStr.ofString "lastScheduledRoot"]?.bind (·.value)) = some (.obj R) ∧
    (bW[JSStr.ofString "mightHavePendingSyncWork"]?.bind (·.value)) = some (.bool true) ∧
    (bW[JSStr.ofString "didScheduleMicrotask"]?.bind (·.value)) = some (.bool true)

theorem call_spec {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t : Value} {s : State}
    {bG : HashMap JSStr Binding} {oG : Option EnvId} {bdF bdL bdM bdD bdS : Binding} {R fS : ObjId} {dS : FuncData}
    {ne nw nc : Bool} {Q : State → σ → Prop}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : 20 ≤ s.fuel)
    (hcode : d.code = ERSGen.ensureRootIsScheduled_func) (hcls : d.isClassCtor = false)
    (hmode : d.thisMode = .strict)
    (hG : d.env < s.envs.size) (hGe : Scope.declLike? (s.envEntry d.env) = some (bG, oG))
    (hGF : bG[JSStr.ofString "firstScheduledRoot"]? = some bdF) (hGFm : bdF.mutable = true)
    (hGFv : bdF.value.isSome = true)
    (hGL : bG[JSStr.ofString "lastScheduledRoot"]? = some bdL) (hGLm : bdL.mutable = true)
    (hGLv : bdL.value = some .null)
    (hGM : bG[JSStr.ofString "mightHavePendingSyncWork"]? = some bdM) (hGMm : bdM.mutable = true)
    (hGMv : bdM.value.isSome = true)
    (hGD : bG[JSStr.ofString "didScheduleMicrotask"]? = some bdD) (hGDm : bdD.mutable = true)
    (hGDv : bdD.value = some (.bool false))
    (hGS : bG[JSStr.ofString "scheduleImmediateRootScheduleTask"]? = some bdS) (hGSv : bdS.value = some (.obj fS))
    (hSo : fS < s.heap.size) (hSk : (s.objEntry fS).kind = .func dS)
    (hR : R < s.heap.size) (hRk : (s.objEntry R).kind.isPlain = true)
    (hRn : (s.objEntry R).props.get? (.str "next") = some (.data .null nw ne nc))
    (hSpec : ∀ w h1, Frame (fp d.env) s w → Scheduled w d.env oG R → s.fuel ≤ w.fuel + 2 →
      WP eng answer n h1 (callImpl eng (.obj fS) .undefined #[]) w fun _ w' h' => Q (w'.restore s) h') :
    WP eng answer (n + 1) h (callImpl eng (.obj fo) t #[.obj R]) s fun v w h' => v = .undefined ∧ Q w h' := by
  replace hSpec := ReactDSSI.Hold.mk hSpec
  apply wp_callGen ERSGen.ensureRootIsScheduled_eq (by decide) hlt hk (by omega) hcls hmode
    (by rw [hcode]; rfl) (by rw [hcode]; rfl) (simple d hcode) (by rw [hcode]; rfl) (by rw [hcode]; rfl)
  have hpn : d.code.info.fdi.paramNames = #[JSStr.ofString "root"] := by rw [hcode]; rfl
  have hv : d.code.info.fdi.varNames = #[] := by rw [hcode]; rfl
  have hl : FDI.lexDecls d = #[] := by simp [FDI.lexDecls, hcode, ERSGen.ensureRootIsScheduled_func, Func.info]
  have ha : d.code.isAsync = false := by rw [hcode]; rfl
  have hne : s.envs.size ≠ d.env := Nat.ne_of_gt hG
  have hG1 : d.env < s.envs.size + 1 := Nat.lt_succ_of_lt hG
  clear hcode
  simp only [ERSGen.ensureRootIsScheduled]
  js [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGF, hGFm, hGFv, hGL, hGLm, hGLv, hGM, hGMm, hGMv, hGD, hGDm,
    hGDv, hGS, hGSv, hSo, hSk, hR, hRk, hRn, FDI.fdiCtx, Sem.inner]
  refine ⟨by js_norm [CallableC, *], ?_⟩
  refine wp_mono ((ReactDSSI.Hold.get hSpec) _ _ ?fr ?sch ?fu) ?post
  case fr => simp only [fp]; frame_go' [*, hne, Ne.symm hne, hG1]
  case sch =>
    simp only [Scheduled]
    js_norm [*]
    refine ⟨_, rfl, ?_⟩
    simp only [Std.HashMap.getElem?_modify, js_simp, hGF, hGL, hGM, hGD, Option.map_some]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> rfl
  case fu => js_side
  case post =>
    intro b w1 h1 hQ
    js [*, FDI.fdiCtx, Sem.inner]


set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
/-- **The root already scheduled** (`lastScheduledRoot` is the root, as during the commit inside the microtask that
reset `didScheduleMicrotask`): the schedule's list unchanged, pending sync work noted, a microtask marked scheduled and
`scheduleImmediateRootScheduleTask` called (the same hypothesis as `call_spec`). -/
theorem call_scheduled {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t : Value} {s : State}
    {bG : HashMap JSStr Binding} {oG : Option EnvId} {bdF bdL bdM bdD bdS : Binding} {R fS : ObjId} {dS : FuncData}
    {Q : State → σ → Prop}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : 20 ≤ s.fuel)
    (hcode : d.code = ERSGen.ensureRootIsScheduled_func) (hcls : d.isClassCtor = false)
    (hmode : d.thisMode = .strict)
    (hG : d.env < s.envs.size) (hGe : Scope.declLike? (s.envEntry d.env) = some (bG, oG))
    (hGF : bG[JSStr.ofString "firstScheduledRoot"]? = some bdF) (hGFv : bdF.value = some (.obj R))
    (hGL : bG[JSStr.ofString "lastScheduledRoot"]? = some bdL) (hGLv : bdL.value = some (.obj R))
    (hGM : bG[JSStr.ofString "mightHavePendingSyncWork"]? = some bdM) (hGMm : bdM.mutable = true)
    (hGMv : bdM.value.isSome = true)
    (hGD : bG[JSStr.ofString "didScheduleMicrotask"]? = some bdD) (hGDm : bdD.mutable = true)
    (hGDv : bdD.value = some (.bool false))
    (hGS : bG[JSStr.ofString "scheduleImmediateRootScheduleTask"]? = some bdS) (hGSv : bdS.value = some (.obj fS))
    (hSo : fS < s.heap.size) (hSk : (s.objEntry fS).kind = .func dS)
    (hR : R < s.heap.size) (hRk : (s.objEntry R).kind.isPlain = true)
    (hSpec : ∀ w h1, Frame (fp d.env) s w → Scheduled w d.env oG R → s.fuel ≤ w.fuel + 2 →
      WP eng answer n h1 (callImpl eng (.obj fS) .undefined #[]) w fun _ w' h' => Q (w'.restore s) h') :
    WP eng answer (n + 1) h (callImpl eng (.obj fo) t #[.obj R]) s fun v w h' => v = .undefined ∧ Q w h' := by
  apply wp_callGen ERSGen.ensureRootIsScheduled_eq (by decide) hlt hk (by omega) hcls hmode
    (by rw [hcode]; rfl) (by rw [hcode]; rfl) (simple d hcode) (by rw [hcode]; rfl) (by rw [hcode]; rfl)
  have hpn : d.code.info.fdi.paramNames = #[JSStr.ofString "root"] := by rw [hcode]; rfl
  have hv : d.code.info.fdi.varNames = #[] := by rw [hcode]; rfl
  have hl : FDI.lexDecls d = #[] := by simp [FDI.lexDecls, hcode, ERSGen.ensureRootIsScheduled_func, Func.info]
  have ha : d.code.isAsync = false := by rw [hcode]; rfl
  have hne : s.envs.size ≠ d.env := Nat.ne_of_gt hG
  have hG1 : d.env < s.envs.size + 1 := Nat.lt_succ_of_lt hG
  have hRR : isStrictlyEqual (.obj R) (.obj R) = true := by simp [isStrictlyEqual, sameValue]
  clear hcode
  simp only [ERSGen.ensureRootIsScheduled]
  js [hRR, hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGF, hGFv, hGL, hGLv, hGM, hGMm, hGMv, hGD, hGDm,
    hGDv, hGS, hGSv, hSo, hSk, hR, hRk, FDI.fdiCtx, Sem.inner]
  refine ⟨by js_norm [CallableC, hSo, hSk], ?_⟩
  refine wp_mono (hSpec _ _ ?fr ?sch ?fu) ?post
  case fr =>
    simp only [fp]
    refine frame_setEnv_split (frame_setEnv_with_in ?_ hG (setEnv_envEntry_self _ _ _ (by simp; omega))
      (by simp only [declLike_isSome_withBindings]; rw [hGe]; rfl) (by simp) _)
    refine frame_setEnv_with_in ?_ hG (bodyState_envEntry_lt (s := s) (fo := fo) (d := d) (t := t)
      (args := #[.obj R]) _ hG) (by rw [hGe]; rfl) (by simp) _
    frame_go' []
  case sch =>
    refine ⟨_, by rw [setEnv_envEntry_self _ _ _ (by simp; omega)]; simp only [declLike_withBindings', hGe, Option.map]; rfl, ?_⟩
    simp [Std.HashMap.getElem?_modify, hGF, hGFv, hGL, hGLv, hGM, hGD]
  case fu => simp; omega
  case post =>
    intro b w1 h1 hQ
    js [hQ, FDI.fdiCtx, Sem.inner]

end

end ReactEnsureRoot
