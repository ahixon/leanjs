import JSProofs.JsTactic
import JSProofs.FPAGen
import JSProofs.FLEGen
import JSProofs.FMEGen
import JSProofs.FSPGen
import JSProofs.FPEGen

/-!
# React's effect flushers with no effects pending (zippy docs/react-proofs.md)

`flushMutationEffects`, `flushLayoutEffects`, `flushSpawnedWork`, `flushPassiveEffects`: each starts by testing
`pendingEffectsStatus` (1, 2, 4 or 3, 5); with nothing pending (0) each does nothing (`flushPassiveEffects` returns
`false`). Before a click's render no effects are pending.
-/

open ES ES.M HostRuns Logic
open Std (HashMap)

namespace ReactNoEffects

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ}

theorem simple_passive (d : FuncData) (hc : d.code = FPAGen.flushPassiveEffects_func) : FDI.Simple d := by
  constructor <;> rw [hc] <;> try rfl
  simp [FPAGen.flushPassiveEffects_func, Func.params, Func.info]

set_option maxRecDepth 10000 in
/-- `flushPassiveEffects()` with no effects pending: nothing. -/
theorem passive_none {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t : Value} {s : State}
    {bG : HashMap JSStr Binding} {oG : Option EnvId} {bdS : Binding}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : 10 ≤ s.fuel)
    (hcode : d.code = FPAGen.flushPassiveEffects_func) (hcls : d.isClassCtor = false) (hmode : d.thisMode = .strict)
    (hG : d.env < s.envs.size) (hGe : Scope.declLike? (s.envEntry d.env) = some (bG, oG))
    (hGS : bG[JSStr.ofString "pendingEffectsStatus"]? = some bdS)
    (hGSv : bdS.value = some (.num (F64.fin false 0 (-1074)))) :
    WP eng answer n h (callImpl eng (.obj fo) t #[]) s fun v w _ =>
      v = (Value.bool false) ∧ Frame {} s w ∧ s.fuel ≤ w.fuel + 10 := by
  apply wp_callGen FPAGen.flushPassiveEffects_eq (by decide) hlt hk (by omega) hcls hmode
    (by rw [hcode]; rfl) (by rw [hcode]; rfl) (simple_passive d hcode) (by rw [hcode]; rfl) (by rw [hcode]; rfl)
  have hpn : d.code.info.fdi.paramNames = #[] := by rw [hcode]; rfl
  have hv : d.code.info.fdi.varNames = #[JSStr.ofString "root", JSStr.ofString "remainingLanes", JSStr.ofString "renderPriority", JSStr.ofString "prevTransition", JSStr.ofString "previousPriority", JSStr.ofString "root$jscomp$0", JSStr.ofString "lanes", JSStr.ofString "prevExecutionContext"] := by rw [hcode]; rfl
  have hl : FDI.lexDecls d = #[] := by simp [FDI.lexDecls, hcode, FPAGen.flushPassiveEffects_func, Func.info]
  have ha : d.code.isAsync = false := by rw [hcode]; rfl
  have hne : s.envs.size ≠ d.env := Nat.ne_of_gt hG
  have hG1 : d.env < s.envs.size + 1 := Nat.lt_succ_of_lt hG
  clear hcode
  simp only [FPAGen.flushPassiveEffects]
  js [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGS, hGSv, FDI.fdiCtx, Sem.inner]
  all_goals (try apply And.intro)
  all_goals (try apply And.intro)
  all_goals first | rfl | omega | frame_go' [*, hne, Ne.symm hne, hG1]

theorem simple_layout (d : FuncData) (hc : d.code = FLEGen.flushLayoutEffects_func) : FDI.Simple d := by
  constructor <;> rw [hc] <;> try rfl
  simp [FLEGen.flushLayoutEffects_func, Func.params, Func.info]

set_option maxRecDepth 10000 in
/-- `flushLayoutEffects()` with no effects pending: nothing. -/
theorem layout_none {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t : Value} {s : State}
    {bG : HashMap JSStr Binding} {oG : Option EnvId} {bdS : Binding}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : 10 ≤ s.fuel)
    (hcode : d.code = FLEGen.flushLayoutEffects_func) (hcls : d.isClassCtor = false) (hmode : d.thisMode = .strict)
    (hG : d.env < s.envs.size) (hGe : Scope.declLike? (s.envEntry d.env) = some (bG, oG))
    (hGS : bG[JSStr.ofString "pendingEffectsStatus"]? = some bdS)
    (hGSv : bdS.value = some (.num (F64.fin false 0 (-1074)))) :
    WP eng answer n h (callImpl eng (.obj fo) t #[]) s fun v w _ =>
      v = Value.undefined ∧ Frame {} s w ∧ s.fuel ≤ w.fuel + 10 := by
  apply wp_callGen FLEGen.flushLayoutEffects_eq (by decide) hlt hk (by omega) hcls hmode
    (by rw [hcode]; rfl) (by rw [hcode]; rfl) (simple_layout d hcode) (by rw [hcode]; rfl) (by rw [hcode]; rfl)
  have hpn : d.code.info.fdi.paramNames = #[] := by rw [hcode]; rfl
  have hv : d.code.info.fdi.varNames = #[JSStr.ofString "root", JSStr.ofString "finishedWork", JSStr.ofString "rootHasLayoutEffect", JSStr.ofString "previousPriority", JSStr.ofString "prevExecutionContext"] := by rw [hcode]; rfl
  have hl : FDI.lexDecls d = #[] := by simp [FDI.lexDecls, hcode, FLEGen.flushLayoutEffects_func, Func.info]
  have ha : d.code.isAsync = false := by rw [hcode]; rfl
  have hne : s.envs.size ≠ d.env := Nat.ne_of_gt hG
  have hG1 : d.env < s.envs.size + 1 := Nat.lt_succ_of_lt hG
  clear hcode
  simp only [FLEGen.flushLayoutEffects]
  js [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGS, hGSv, FDI.fdiCtx, Sem.inner]
  all_goals (try apply And.intro)
  all_goals (try apply And.intro)
  all_goals first | rfl | omega | frame_go' [*, hne, Ne.symm hne, hG1]

theorem simple_mutation (d : FuncData) (hc : d.code = FMEGen.flushMutationEffects_func) : FDI.Simple d := by
  constructor <;> rw [hc] <;> try rfl
  simp [FMEGen.flushMutationEffects_func, Func.params, Func.info]

set_option maxRecDepth 10000 in
/-- `flushMutationEffects()` with no effects pending: nothing. -/
theorem mutation_none {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t : Value} {s : State}
    {bG : HashMap JSStr Binding} {oG : Option EnvId} {bdS : Binding}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : 10 ≤ s.fuel)
    (hcode : d.code = FMEGen.flushMutationEffects_func) (hcls : d.isClassCtor = false) (hmode : d.thisMode = .strict)
    (hG : d.env < s.envs.size) (hGe : Scope.declLike? (s.envEntry d.env) = some (bG, oG))
    (hGS : bG[JSStr.ofString "pendingEffectsStatus"]? = some bdS)
    (hGSv : bdS.value = some (.num (F64.fin false 0 (-1074)))) :
    WP eng answer n h (callImpl eng (.obj fo) t #[]) s fun v w _ =>
      v = Value.undefined ∧ Frame {} s w ∧ s.fuel ≤ w.fuel + 10 := by
  apply wp_callGen FMEGen.flushMutationEffects_eq (by decide) hlt hk (by omega) hcls hmode
    (by rw [hcode]; rfl) (by rw [hcode]; rfl) (simple_mutation d hcode) (by rw [hcode]; rfl) (by rw [hcode]; rfl)
  have hpn : d.code.info.fdi.paramNames = #[] := by rw [hcode]; rfl
  have hv : d.code.info.fdi.varNames = #[JSStr.ofString "root", JSStr.ofString "finishedWork", JSStr.ofString "lanes", JSStr.ofString "rootMutationHasEffect", JSStr.ofString "previousPriority", JSStr.ofString "prevExecutionContext", JSStr.ofString "curFocusedElem", JSStr.ofString "priorFocusedElem", JSStr.ofString "priorSelectionRange", JSStr.ofString "start", JSStr.ofString "end", JSStr.ofString "doc", JSStr.ofString "win", JSStr.ofString "selection", JSStr.ofString "length", JSStr.ofString "start$jscomp$0", JSStr.ofString "end$jscomp$0", JSStr.ofString "startMarker", JSStr.ofString "endMarker", JSStr.ofString "range", JSStr.ofString "info"] := by rw [hcode]; rfl
  have hl : FDI.lexDecls d = #[] := by simp [FDI.lexDecls, hcode, FMEGen.flushMutationEffects_func, Func.info]
  have ha : d.code.isAsync = false := by rw [hcode]; rfl
  have hne : s.envs.size ≠ d.env := Nat.ne_of_gt hG
  have hG1 : d.env < s.envs.size + 1 := Nat.lt_succ_of_lt hG
  clear hcode
  simp only [FMEGen.flushMutationEffects]
  js [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGS, hGSv, FDI.fdiCtx, Sem.inner]
  all_goals (try apply And.intro)
  all_goals (try apply And.intro)
  all_goals first | rfl | omega | frame_go' [*, hne, Ne.symm hne, hG1]

theorem simple_spawned (d : FuncData) (hc : d.code = FSPGen.flushSpawnedWork_func) : FDI.Simple d := by
  constructor <;> rw [hc] <;> try rfl
  simp [FSPGen.flushSpawnedWork_func, Func.params, Func.info]

set_option maxRecDepth 10000 in
/-- `flushSpawnedWork()` with no effects pending: nothing. -/
theorem spawned_none {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t : Value} {s : State}
    {bG : HashMap JSStr Binding} {oG : Option EnvId} {bdS : Binding}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : 10 ≤ s.fuel)
    (hcode : d.code = FSPGen.flushSpawnedWork_func) (hcls : d.isClassCtor = false) (hmode : d.thisMode = .strict)
    (hG : d.env < s.envs.size) (hGe : Scope.declLike? (s.envEntry d.env) = some (bG, oG))
    (hGS : bG[JSStr.ofString "pendingEffectsStatus"]? = some bdS)
    (hGSv : bdS.value = some (.num (F64.fin false 0 (-1074)))) :
    WP eng answer n h (callImpl eng (.obj fo) t #[]) s fun v w _ =>
      v = Value.undefined ∧ Frame {} s w ∧ s.fuel ≤ w.fuel + 10 := by
  apply wp_callGen FSPGen.flushSpawnedWork_eq (by decide) hlt hk (by omega) hcls hmode
    (by rw [hcode]; rfl) (by rw [hcode]; rfl) (simple_spawned d hcode) (by rw [hcode]; rfl) (by rw [hcode]; rfl)
  have hpn : d.code.info.fdi.paramNames = #[] := by rw [hcode]; rfl
  have hv : d.code.info.fdi.varNames = #[JSStr.ofString "committedViewTransition", JSStr.ofString "root", JSStr.ofString "finishedWork", JSStr.ofString "lanes", JSStr.ofString "recoverableErrors", JSStr.ofString "passiveSubtreeMask", JSStr.ofString "onRecoverableError", JSStr.ofString "i", JSStr.ofString "recoverableError"] := by rw [hcode]; rfl
  have hl : FDI.lexDecls d = #[] := by simp [FDI.lexDecls, hcode, FSPGen.flushSpawnedWork_func, Func.info]
  have ha : d.code.isAsync = false := by rw [hcode]; rfl
  have hne : s.envs.size ≠ d.env := Nat.ne_of_gt hG
  have hG1 : d.env < s.envs.size + 1 := Nat.lt_succ_of_lt hG
  clear hcode
  simp only [FSPGen.flushSpawnedWork]
  js [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGS, hGSv, FDI.fdiCtx, Sem.inner]
  all_goals (try apply And.intro)
  all_goals (try apply And.intro)
  all_goals first | rfl | omega | frame_go' [*, hne, Ne.symm hne, hG1]

theorem simple_pending (d : FuncData) (hc : d.code = FPEGen.flushPendingEffects_func) : FDI.Simple d := by
  constructor <;> rw [hc] <;> try rfl
  simp [FPEGen.flushPendingEffects_func, Func.params, Func.info]

set_option maxRecDepth 10000 in
/-- **`flushPendingEffects()` with no effects pending**: each flusher does nothing; `false`. -/
theorem pending_none {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t : Value} {s : State}
    {bG : HashMap JSStr Binding} {oG : Option EnvId}
    {bdS bdV bdM bdL bdW bdP : Binding} {fM fL fW fP : ObjId} {dM dL dW dP : FuncData}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : 60 ≤ s.fuel)
    (hcode : d.code = FPEGen.flushPendingEffects_func) (hcls : d.isClassCtor = false) (hmode : d.thisMode = .strict)
    (hG : d.env < s.envs.size) (hGe : Scope.declLike? (s.envEntry d.env) = some (bG, oG))
    (hGS : bG[JSStr.ofString "pendingEffectsStatus"]? = some bdS)
    (hGSv : bdS.value = some (.num (F64.fin false 0 (-1074))))
    (hGV : bG[JSStr.ofString "pendingViewTransition"]? = some bdV) (hGVv : bdV.value = some .null)
    (hGM : bG[JSStr.ofString "flushMutationEffects"]? = some bdM) (hGMv : bdM.value = some (.obj fM))
    (hGL : bG[JSStr.ofString "flushLayoutEffects"]? = some bdL) (hGLv : bdL.value = some (.obj fL))
    (hGW : bG[JSStr.ofString "flushSpawnedWork"]? = some bdW) (hGWv : bdW.value = some (.obj fW))
    (hGP : bG[JSStr.ofString "flushPassiveEffects"]? = some bdP) (hGPv : bdP.value = some (.obj fP))
    (hMo : fM < s.heap.size) (hMk : (s.objEntry fM).kind = .func dM) (hMcode : dM.code = FMEGen.flushMutationEffects_func)
    (hMcls : dM.isClassCtor = false) (hMmode : dM.thisMode = .strict) (hMenv : dM.env = d.env)
    (hLo : fL < s.heap.size) (hLk : (s.objEntry fL).kind = .func dL) (hLcode : dL.code = FLEGen.flushLayoutEffects_func)
    (hLcls : dL.isClassCtor = false) (hLmode : dL.thisMode = .strict) (hLenv : dL.env = d.env)
    (hWo : fW < s.heap.size) (hWk : (s.objEntry fW).kind = .func dW) (hWcode : dW.code = FSPGen.flushSpawnedWork_func)
    (hWcls : dW.isClassCtor = false) (hWmode : dW.thisMode = .strict) (hWenv : dW.env = d.env)
    (hPo : fP < s.heap.size) (hPk : (s.objEntry fP).kind = .func dP) (hPcode : dP.code = FPAGen.flushPassiveEffects_func)
    (hPcls : dP.isClassCtor = false) (hPmode : dP.thisMode = .strict) (hPenv : dP.env = d.env) :
    WP eng answer (n + 1) h (callImpl eng (.obj fo) t #[]) s fun v w _ =>
      v = .bool false ∧ Frame {} s w ∧ s.fuel ≤ w.fuel + 60 := by
  apply wp_callGen FPEGen.flushPendingEffects_eq (by decide) hlt hk (by omega) hcls hmode
    (by rw [hcode]; rfl) (by rw [hcode]; rfl) (simple_pending d hcode) (by rw [hcode]; rfl) (by rw [hcode]; rfl)
  have hpn : d.code.info.fdi.paramNames = #[] := by rw [hcode]; rfl
  have hv : d.code.info.fdi.varNames = #[] := by rw [hcode]; rfl
  have hl : FDI.lexDecls d = #[] := by simp [FDI.lexDecls, hcode, FPEGen.flushPendingEffects_func, Func.info]
  have ha : d.code.isAsync = false := by rw [hcode]; rfl
  have hne : s.envs.size ≠ d.env := Nat.ne_of_gt hG
  have hG1 : d.env < s.envs.size + 1 := Nat.lt_succ_of_lt hG
  clear hcode
  simp only [FPEGen.flushPendingEffects]
  js [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGV, hGVv, hGM, hGMv, hMo, hMk, FDI.fdiCtx, Sem.inner]
  -- (each flusher by its theorem; the record and objects carried through each empty frame)
  refine ⟨by js_norm [CallableC, *], ?_⟩
  refine wp_mono (mutation_none (by simpa using hMo) (by simpa using hMk) (by simp; omega) hMcode hMcls hMmode
    (by rw [hMenv]; simp; omega) (by rw [hMenv]; js_norm [*, Ne.symm hne]; rfl) hGS hGSv) ?p1
  case p1 =>
  intro r w1 h1 ⟨_, hF1, hfu1⟩
  try simp only [js_simp] at hfu1
  js [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGL, hGLv, hLo, hLk, envEntry_frame0 hF1, objEntry_frame0 hF1,
    heap_frame hF1, envs_frame hF1, FDI.fdiCtx, Sem.inner]
  refine ⟨by js_norm [CallableC, *, envEntry_frame0 hF1, objEntry_frame0 hF1, heap_frame hF1, envs_frame hF1], ?_⟩
  refine wp_mono (layout_none (by js_norm [*, envEntry_frame0 hF1, objEntry_frame0 hF1, heap_frame hF1, envs_frame hF1]) (by js_norm [*, envEntry_frame0 hF1, objEntry_frame0 hF1, heap_frame hF1, envs_frame hF1]) (by simp at hfu1 ⊢; omega) hLcode hLcls hLmode
    (by rw [hLenv]; js_norm [*, envEntry_frame0 hF1, objEntry_frame0 hF1, heap_frame hF1, envs_frame hF1]) (by rw [hLenv]; js_norm [*, Ne.symm hne, envEntry_frame0 hF1, objEntry_frame0 hF1, heap_frame hF1, envs_frame hF1]; rfl) hGS hGSv) ?p2
  case p2 =>
  intro r w2 h2 ⟨_, hF2, hfu2⟩
  try simp only [js_simp] at hfu2
  js [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGW, hGWv, hWo, hWk, envEntry_frame0 hF1, objEntry_frame0 hF1, heap_frame hF1, envs_frame hF1, envEntry_frame0 hF2, objEntry_frame0 hF2, heap_frame hF2, envs_frame hF2, FDI.fdiCtx, Sem.inner]
  refine ⟨by js_norm [CallableC, *, envEntry_frame0 hF1, objEntry_frame0 hF1, heap_frame hF1, envs_frame hF1, envEntry_frame0 hF2, objEntry_frame0 hF2, heap_frame hF2, envs_frame hF2], ?_⟩
  refine wp_mono (spawned_none (by js_norm [*, envEntry_frame0 hF1, objEntry_frame0 hF1, heap_frame hF1, envs_frame hF1, envEntry_frame0 hF2, objEntry_frame0 hF2, heap_frame hF2, envs_frame hF2]) (by js_norm [*, envEntry_frame0 hF1, objEntry_frame0 hF1, heap_frame hF1, envs_frame hF1, envEntry_frame0 hF2, objEntry_frame0 hF2, heap_frame hF2, envs_frame hF2]) (by simp at hfu1 hfu2 ⊢; omega) hWcode hWcls hWmode
    (by rw [hWenv]; js_norm [*, envEntry_frame0 hF1, objEntry_frame0 hF1, heap_frame hF1, envs_frame hF1, envEntry_frame0 hF2, objEntry_frame0 hF2, heap_frame hF2, envs_frame hF2]) (by rw [hWenv]; js_norm [*, Ne.symm hne, envEntry_frame0 hF1, objEntry_frame0 hF1, heap_frame hF1, envs_frame hF1, envEntry_frame0 hF2, objEntry_frame0 hF2, heap_frame hF2, envs_frame hF2]; rfl) hGS hGSv) ?p3
  case p3 =>
  intro r w3 h3 ⟨_, hF3, hfu3⟩
  try simp only [js_simp] at hfu3
  js [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGP, hGPv, hPo, hPk, envEntry_frame0 hF1, objEntry_frame0 hF1, heap_frame hF1, envs_frame hF1, envEntry_frame0 hF2, objEntry_frame0 hF2, heap_frame hF2, envs_frame hF2, envEntry_frame0 hF3, objEntry_frame0 hF3, heap_frame hF3, envs_frame hF3, FDI.fdiCtx, Sem.inner]
  refine ⟨by js_norm [CallableC, *, envEntry_frame0 hF1, objEntry_frame0 hF1, heap_frame hF1, envs_frame hF1, envEntry_frame0 hF2, objEntry_frame0 hF2, heap_frame hF2, envs_frame hF2, envEntry_frame0 hF3, objEntry_frame0 hF3, heap_frame hF3, envs_frame hF3], ?_⟩
  refine wp_mono (passive_none (by js_norm [*, envEntry_frame0 hF1, objEntry_frame0 hF1, heap_frame hF1, envs_frame hF1, envEntry_frame0 hF2, objEntry_frame0 hF2, heap_frame hF2, envs_frame hF2, envEntry_frame0 hF3, objEntry_frame0 hF3, heap_frame hF3, envs_frame hF3]) (by js_norm [*, envEntry_frame0 hF1, objEntry_frame0 hF1, heap_frame hF1, envs_frame hF1, envEntry_frame0 hF2, objEntry_frame0 hF2, heap_frame hF2, envs_frame hF2, envEntry_frame0 hF3, objEntry_frame0 hF3, heap_frame hF3, envs_frame hF3]) (by simp at hfu1 hfu2 hfu3 ⊢; omega) hPcode hPcls hPmode
    (by rw [hPenv]; js_norm [*, envEntry_frame0 hF1, objEntry_frame0 hF1, heap_frame hF1, envs_frame hF1, envEntry_frame0 hF2, objEntry_frame0 hF2, heap_frame hF2, envs_frame hF2, envEntry_frame0 hF3, objEntry_frame0 hF3, heap_frame hF3, envs_frame hF3]) (by rw [hPenv]; js_norm [*, Ne.symm hne, envEntry_frame0 hF1, objEntry_frame0 hF1, heap_frame hF1, envs_frame hF1, envEntry_frame0 hF2, objEntry_frame0 hF2, heap_frame hF2, envs_frame hF2, envEntry_frame0 hF3, objEntry_frame0 hF3, heap_frame hF3, envs_frame hF3]; rfl) hGS hGSv) ?p4
  case p4 =>
  intro r w4 h4 ⟨hr, hF4, hfu4⟩
  subst hr
  try simp only [js_simp] at hfu4
  js [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, envEntry_frame0 hF1, objEntry_frame0 hF1, heap_frame hF1, envs_frame hF1, envEntry_frame0 hF2, objEntry_frame0 hF2, heap_frame hF2, envs_frame hF2, envEntry_frame0 hF3, objEntry_frame0 hF3, heap_frame hF3, envs_frame hF3, envEntry_frame0 hF4, objEntry_frame0 hF4, heap_frame hF4, envs_frame hF4, FDI.fdiCtx, Sem.inner]
  all_goals (try apply And.intro)
  all_goals (try apply And.intro)
  all_goals first | rfl | (simp at hfu1 hfu2 hfu3 hfu4 ⊢; omega) | frame_go' [*, hne, Ne.symm hne, hG1]

end

end ReactNoEffects
