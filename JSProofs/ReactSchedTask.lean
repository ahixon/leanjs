import JSProofs.ReactDSSI
import JSProofs.SIRGen

/-!
# React's `scheduleImmediateRootScheduleTask` (zippy docs/react-proofs.md)

```js
function scheduleImmediateRootScheduleTask() {
  scheduleMicrotask(function () {
    0 !== (executionContext & 6)
      ? scheduleCallback$3(ImmediatePriority, processRootScheduleInImmediateTask)
      : processRootScheduleInMicrotask();
  });
}
```
A closure is made (`Logic.closState`: the function object and its `prototype`) and passed to `scheduleMicrotask`
(the host's `queueMicrotask`; a hypothesis here, from any state framed from the start in which the closure is that
function over this call's record).
-/

open ES ES.M HostRuns Logic
open Std (HashMap)

namespace ReactSchedTask

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ}

theorem simple (d : FuncData) (hc : d.code = SIRGen.scheduleImmediateRootScheduleTask_func) : FDI.Simple d := by
  constructor <;> rw [hc] <;> try rfl
  simp [SIRGen.scheduleImmediateRootScheduleTask_func, Func.params, Func.info]

/-- The microtask's callback `c`: React's closure, over the record `e` of the call that made it (no bindings; its
outer record is the module's, `g`). -/
def Callback (w : State) (c : ObjId) (e g : EnvId) : Prop :=
  c < w.heap.size ∧ ∃ dc : FuncData, (w.objEntry c).kind = .func dc ∧ dc.code = SIRGen.fn5_func ∧
    dc.thisMode = .strict ∧ dc.isClassCtor = false ∧ dc.env = e ∧ e < w.envs.size ∧
    Scope.declLike? (w.envEntry e) = some (FDI.fdiMap #[] #[] #[] #[], some g)

theorem call_spec {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t : Value} {s : State}
    {bG : HashMap JSStr Binding} {oG : Option EnvId} {bdM : Binding} {fM : ObjId} {bM : BuiltinData}
    {Q : State → σ → Prop}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : 20 ≤ s.fuel)
    (hcode : d.code = SIRGen.scheduleImmediateRootScheduleTask_func) (hcls : d.isClassCtor = false)
    (hmode : d.thisMode = .strict)
    (hG : d.env < s.envs.size) (hGe : Scope.declLike? (s.envEntry d.env) = some (bG, oG))
    (hGM : bG[JSStr.ofString "scheduleMicrotask"]? = some bdM) (hGMv : bdM.value = some (.obj fM))
    (hMo : fM < s.heap.size) (hMk : (s.objEntry fM).kind = .builtin bM)
    (hP : ((s.realms[d.realm]!).intrinsics["%Function.prototype%"]?).isSome = true)
    (hSpec : ∀ w h1, Frame {} s w → Callback w s.heap.size s.envs.size d.env → s.fuel ≤ w.fuel + 2 →
      WP eng answer n h1 (callImpl eng (.obj fM) .undefined #[.obj s.heap.size]) w fun _ w' h' =>
        Q (w'.restore s) h') :
    WP eng answer (n + 1) h (callImpl eng (.obj fo) t #[]) s fun v w h' => v = .undefined ∧ Q w h' := by
  replace hSpec := ReactDSSI.Hold.mk hSpec
  apply wp_callGen SIRGen.scheduleImmediateRootScheduleTask_eq (by decide) hlt hk (by omega) hcls hmode
    (by rw [hcode]; rfl) (by rw [hcode]; rfl) (simple d hcode) (by rw [hcode]; rfl) (by rw [hcode]; rfl)
  have hpn : d.code.info.fdi.paramNames = #[] := by rw [hcode]; rfl
  have hv : d.code.info.fdi.varNames = #[] := by rw [hcode]; rfl
  have hl : FDI.lexDecls d = #[] := by
    simp [FDI.lexDecls, hcode, SIRGen.scheduleImmediateRootScheduleTask_func, Func.info]
  have ha : d.code.isAsync = false := by rw [hcode]; rfl
  have hne : s.envs.size ≠ d.env := Nat.ne_of_gt hG
  have hG1 : d.env < s.envs.size + 1 := Nat.lt_succ_of_lt hG
  clear hcode
  simp only [SIRGen.scheduleImmediateRootScheduleTask]
  js [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGM, hGMv, hMo, hMk, hP, FDI.fdiCtx, Sem.inner]
  have hMo' : fM < (bodyState s fo d t #[]).heap.size := by simpa using hMo
  refine ⟨⟨by simp [closState_heap_size]; exact Nat.lt_of_lt_of_le hMo (Nat.le_add_right _ _),
    by rw [closState_objEntry_lt _ _ _ _ hMo']; simp [hMk]⟩, ?_⟩
  refine wp_mono ((ReactDSSI.Hold.get hSpec) _ h ?fr ?cb ?fu) ?post
  case fr =>
    have := frame_trans (frame_bodyState (frame_refl {} s) fo d t #[]) (frame_closState _ SIRGen.fn5_func
      { lex := s.envs.size, var := s.envs.size, priv := d.privEnv, strict := true, fn := some fo, realm := d.realm,
        script := d.script, annexB := funcIds #[] } (funcProto (bodyState s fo d t #[])))
    simpa using this
  case cb =>
    have hk' := closState_kind (bodyState s fo d t #[]) SIRGen.fn5_func
      { lex := s.envs.size, var := s.envs.size, priv := d.privEnv, strict := true, fn := some fo, realm := d.realm,
        script := d.script, annexB := funcIds #[] } (funcProto (bodyState s fo d t #[]))
    simp only [bodyState_heap] at hk'
    refine ⟨by simp [closState_heap_size], _, hk', rfl, rfl, rfl, rfl, by simp [closState_envs, entryState, bodyState], ?_⟩
    rw [closState_envEntry, bodyState_self, hpn, hv, hl]
  case fu => js_side
  case post =>
    intro b w1 h1 hQ
    js [*, FDI.fdiCtx, Sem.inner]

end

end ReactSchedTask
