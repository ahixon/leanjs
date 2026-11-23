import JSProofs.CLESwitch
import JSProofs.Setter
import JSProofs.ReactHostContainer
import JSProofs.Rebase

/-!
# commitLayoutEffectOnFiber for the counter's fibers (zippy docs/react-proofs.md)

The click's layout pass only reads: for each fiber the children are traversed (`recursivelyTraverseLayoutEffects`,
a contract) and no flag the fiber's case tests is set (no mount, ref, layout hook or callback). The text fiber (tag 6)
takes the `default` case.
-/

open ES ES.M HostRuns Logic
open Std (HashMap)

namespace ReactLayoutFiber

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ}

theorem simple (d : FuncData) (hc : d.code = CLEGen.commitLayoutEffectOnFiber_func) : FDI.Simple d := by
  constructor <;> rw [hc] <;> try rfl
  simp [CLEGen.commitLayoutEffectOnFiber_func, Func.params, Func.info]

set_option maxRecDepth 40000 in
set_option maxHeartbeats 8000000 in
/-- **The text fiber** (tag 6): the `default` case, the children traversed. -/
theorem cle_text {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t : Value} {s : State}
    {rv cv : Value} {B : ObjId} {fl : F64} {KR : Nat}
    {fw fe fc tw te tc : Bool}
    {bG : HashMap JSStr Binding} {oG : Option EnvId} {bdRT : Binding} {fRT : ObjId}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : KR + 300 ≤ s.fuel)
    (hcode : d.code = CLEGen.commitLayoutEffectOnFiber_func) (hcls : d.isClassCtor = false)
    (hmode : d.thisMode = .strict)
    (hB : B < s.heap.size) (hBk : (s.objEntry B).kind.isPlain = true)
    (hBf : (s.objEntry B).props.get? (.str (JSStr.ofString "flags")) = some (.data (.num fl) fw fe fc))
    (hBt : (s.objEntry B).props.get? (.str (JSStr.ofString "tag")) =
      some (.data (.num (F64.fin false 6755399441055744 (-50))) tw te tc))
    (hG : d.env < s.envs.size) (hGe : Scope.declLike? (s.envEntry d.env) = some (bG, oG))
    (hGRT : bG[JSStr.ofString "recursivelyTraverseLayoutEffects"]? = some bdRT) (hGRTv : bdRT.value = some (.obj fRT))
    (hRTo : fRT < s.heap.size) (hRTc : ∃ dd, (s.objEntry fRT).kind = .func dd)
    (hRT : ∀ w h1, Frame {} s w → KR ≤ w.fuel →
      WP eng answer (n + 1) h1 (callImpl eng (.obj fRT) .undefined #[rv, .obj B]) w fun v w' h' =>
        Frame {} w w' ∧ w.fuel ≤ w'.fuel + KR ∧ h' = h1) :
    WP eng answer (n + 2) h (callImpl eng (.obj fo) t #[rv, cv, .obj B]) s fun v w h' =>
      v = .undefined ∧ s.fuel ≤ w.fuel + KR + 200 ∧ Frame {} s w ∧ h' = h := by
  apply wp_callGen CLEGen.commitLayoutEffectOnFiber_eq (by decide) hlt hk (by omega) hcls hmode
    (by rw [hcode]; rfl) (by rw [hcode]; rfl) (simple d hcode) (by rw [hcode]; rfl) (by rw [hcode]; rfl)
  have hpn : d.code.info.fdi.paramNames = #[JSStr.ofString "finishedRoot", JSStr.ofString "current",
    JSStr.ofString "finishedWork"] := by rw [hcode]; rfl
  have hv : d.code.info.fdi.varNames = #[JSStr.ofString "flags", JSStr.ofString "prevProps",
    JSStr.ofString "newOffscreenSubtreeWasHidden"] := by rw [hcode]; rfl
  have hl : FDI.lexDecls d = #[] := by
    simp [FDI.lexDecls, hcode, CLEGen.commitLayoutEffectOnFiber_func, Func.info]
  have ha : d.code.isAsync = false := by rw [hcode]; rfl
  have e1 : d.env ≠ s.envs.size := Nat.ne_of_lt hG
  have e4 : d.env < s.envs.size + 1 := Nat.lt_succ_of_lt hG
  have e5 : d.env < s.envs.size + 1 + 1 := Nat.lt_succ_of_lt e4
  have e2 : d.env ≠ s.envs.size + 1 := Nat.ne_of_lt e4
  obtain ⟨dRT, hRTk⟩ := hRTc
  clear hcode
  simp only [CLEGen.commitLayoutEffectOnFiber]
  iterate 15 (first | js_go | js_norm [hB, hBk, hBf, hBt, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner] | js_split)
  js_until [] [e1, e2, e4, e5, Ne.symm e1, Ne.symm e2, hG, hGe, hGRT, hGRTv, hRTo, hRTk, hB, hBk, hBf, hBt, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  refine ⟨by js_norm [CallableC, e1, e2, e4, e5, Ne.symm e1, Ne.symm e2, hG, hGe, hGRT, hGRTv, hRTo, hRTk, hB, hBk, hBf, hBt, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner], ?_⟩
  refine wp_mono (hRT _ _ (by frame_go' [hB]) (by js_norm [e1, e2, e4, e5, Ne.symm e1, Ne.symm e2, hG, hGe, hGRT, hGRTv, hRTo, hRTk, hB, hBk, hBf, hBt, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]; omega)) ?_
  rintro v1 w1 h1 ⟨hF1, hfu1, rfl⟩
  have hfr1 : s.fuel ≤ w1.fuel + KR + 10 := by simp [bodyState, entryState] at hfu1; omega
  have hE1 := envEntry_frame0 hF1 (e := s.envs.size) (by js_norm [e1, e2, e4, e5, Ne.symm e1, Ne.symm e2, hG, hGe, hGRT, hGRTv, hRTo, hRTk, hB, hBk, hBf, hBt, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner])
  have hE2 := envEntry_frame0 hF1 (e := s.envs.size + 1) (by js_norm [e1, e2, e4, e5, Ne.symm e1, Ne.symm e2, hG, hGe, hGRT, hGRTv, hRTo, hRTk, hB, hBk, hBf, hBt, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner])
  have hS2 : s.envs.size + 1 < w1.envs.size := Nat.lt_of_lt_of_le (by js_norm [e1, e2, e4, e5, Ne.symm e1, Ne.symm e2, hG, hGe, hGRT, hGRTv, hRTo, hRTk, hB, hBk, hBf, hBt, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]) hF1.envs_le
  have hS1 : s.envs.size < w1.envs.size := by omega
  js_until [] [hE1, hE2, hS1, hS2, e1, e2, e4, e5, Ne.symm e1, Ne.symm e2, hG, hGe, hGRT, hGRTv, hRTo, hRTk, hB, hBk, hBf, hBt, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  refine ⟨by omega, frame_restore (frame_then_empty ?_ hF1) s⟩
  frame_go' [hB]


set_option maxRecDepth 40000 in
set_option maxHeartbeats 8000000 in
/-- **The button** (tag 5, `current` an object): the children traversed; not a mount, no ref. -/
theorem cle_button {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t : Value} {s : State}
    {rv : Value} {Bc : ObjId} {B : ObjId} {fl : F64} {KR : Nat}
    {fw fe fc tw te tc : Bool}
    {bG : HashMap JSStr Binding} {oG : Option EnvId} {bdRT : Binding} {fRT : ObjId}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : KR + 300 ≤ s.fuel)
    (hcode : d.code = CLEGen.commitLayoutEffectOnFiber_func) (hcls : d.isClassCtor = false)
    (hmode : d.thisMode = .strict)
    (hB : B < s.heap.size) (hBk : (s.objEntry B).kind.isPlain = true)
    (hBf : (s.objEntry B).props.get? (.str (JSStr.ofString "flags")) = some (.data (.num fl) fw fe fc))
    (hBt : (s.objEntry B).props.get? (.str (JSStr.ofString "tag")) =
      some (.data (.num (F64.fin false 5629499534213120 (-50))) tw te tc))
    (h512 : numberBinOp .bitAnd fl (F64.fin false 4503599627370496 (-43)) = F64.fin false 0 (-1074))
    (hG : d.env < s.envs.size) (hGe : Scope.declLike? (s.envEntry d.env) = some (bG, oG))
    (hGRT : bG[JSStr.ofString "recursivelyTraverseLayoutEffects"]? = some bdRT) (hGRTv : bdRT.value = some (.obj fRT))
    (hRTo : fRT < s.heap.size) (hRTc : ∃ dd, (s.objEntry fRT).kind = .func dd)
    (hRT : ∀ w h1, Frame {} s w → KR ≤ w.fuel →
      WP eng answer (n + 1) h1 (callImpl eng (.obj fRT) .undefined #[rv, .obj B]) w fun v w' h' =>
        Frame {} w w' ∧ w.fuel ≤ w'.fuel + KR ∧ h' = h1) :
    WP eng answer (n + 2) h (callImpl eng (.obj fo) t #[rv, .obj Bc, .obj B]) s fun v w h' =>
      v = .undefined ∧ s.fuel ≤ w.fuel + KR + 200 ∧ Frame {} s w ∧ h' = h := by
  apply wp_callGen CLEGen.commitLayoutEffectOnFiber_eq (by decide) hlt hk (by omega) hcls hmode
    (by rw [hcode]; rfl) (by rw [hcode]; rfl) (simple d hcode) (by rw [hcode]; rfl) (by rw [hcode]; rfl)
  have hpn : d.code.info.fdi.paramNames = #[JSStr.ofString "finishedRoot", JSStr.ofString "current",
    JSStr.ofString "finishedWork"] := by rw [hcode]; rfl
  have hv : d.code.info.fdi.varNames = #[JSStr.ofString "flags", JSStr.ofString "prevProps",
    JSStr.ofString "newOffscreenSubtreeWasHidden"] := by rw [hcode]; rfl
  have hl : FDI.lexDecls d = #[] := by
    simp [FDI.lexDecls, hcode, CLEGen.commitLayoutEffectOnFiber_func, Func.info]
  have ha : d.code.isAsync = false := by rw [hcode]; rfl
  have e1 : d.env ≠ s.envs.size := Nat.ne_of_lt hG
  have e4 : d.env < s.envs.size + 1 := Nat.lt_succ_of_lt hG
  have e5 : d.env < s.envs.size + 1 + 1 := Nat.lt_succ_of_lt e4
  have e2 : d.env ≠ s.envs.size + 1 := Nat.ne_of_lt e4
  obtain ⟨dRT, hRTk⟩ := hRTc
  clear hcode
  simp only [CLEGen.commitLayoutEffectOnFiber]
  iterate 15 (first | js_go | js_norm [hB, hBk, hBf, hBt, h512, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner] | js_split)
  js_until [] [e1, e2, e4, e5, Ne.symm e1, Ne.symm e2, hG, hGe, hGRT, hGRTv, hRTo, hRTk, hB, hBk, hBf, hBt, h512, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  refine ⟨by js_norm [CallableC, e1, e2, e4, e5, Ne.symm e1, Ne.symm e2, hG, hGe, hGRT, hGRTv, hRTo, hRTk, hB, hBk, hBf, hBt, h512, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner], ?_⟩
  refine wp_mono (hRT _ _ (by frame_go' [hB]) (by js_norm [e1, e2, e4, e5, Ne.symm e1, Ne.symm e2, hG, hGe, hGRT, hGRTv, hRTo, hRTk, hB, hBk, hBf, hBt, h512, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]; omega)) ?_
  rintro v1 w1 h1 ⟨hF1, hfu1, rfl⟩
  have hfr1 : s.fuel ≤ w1.fuel + KR + 10 := by simp [bodyState, entryState] at hfu1; omega
  have hE1 := envEntry_frame0 hF1 (e := s.envs.size) (by js_norm [e1, e2, e4, e5, Ne.symm e1, Ne.symm e2, hG, hGe, hGRT, hGRTv, hRTo, hRTk, hB, hBk, hBf, hBt, h512, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner])
  have hE2 := envEntry_frame0 hF1 (e := s.envs.size + 1) (by js_norm [e1, e2, e4, e5, Ne.symm e1, Ne.symm e2, hG, hGe, hGRT, hGRTv, hRTo, hRTk, hB, hBk, hBf, hBt, h512, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner])
  have hS2 : s.envs.size + 1 < w1.envs.size := Nat.lt_of_lt_of_le (by js_norm [e1, e2, e4, e5, Ne.symm e1, Ne.symm e2, hG, hGe, hGRT, hGRTv, hRTo, hRTk, hB, hBk, hBf, hBt, h512, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]) hF1.envs_le
  have hS1 : s.envs.size < w1.envs.size := by omega
  js_until [] [hE1, hE2, hS1, hS2, e1, e2, e4, e5, Ne.symm e1, Ne.symm e2, hG, hGe, hGRT, hGRTv, hRTo, hRTk, hB, hBk, hBf, hBt, h512, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  refine ⟨by omega, frame_restore (frame_then_empty ?_ hF1) s⟩
  frame_go' [hB]


set_option maxRecDepth 40000 in
set_option maxHeartbeats 8000000 in
/-- **The counter** (tag 0): the children traversed; no layout effect (`flags & 4` zero). -/
theorem cle_counter {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t : Value} {s : State}
    {rv cv : Value} {B : ObjId} {fl : F64} {KR : Nat}
    {fw fe fc tw te tc : Bool}
    {bG : HashMap JSStr Binding} {oG : Option EnvId} {bdRT : Binding} {fRT : ObjId}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : KR + 300 ≤ s.fuel)
    (hcode : d.code = CLEGen.commitLayoutEffectOnFiber_func) (hcls : d.isClassCtor = false)
    (hmode : d.thisMode = .strict)
    (hB : B < s.heap.size) (hBk : (s.objEntry B).kind.isPlain = true)
    (hBf : (s.objEntry B).props.get? (.str (JSStr.ofString "flags")) = some (.data (.num fl) fw fe fc))
    (hBt : (s.objEntry B).props.get? (.str (JSStr.ofString "tag")) =
      some (.data (.num (F64.fin false 0 (-1074))) tw te tc))
    (h4 : numberBinOp .bitAnd fl (F64.fin false 4503599627370496 (-50)) = F64.fin false 0 (-1074))
    (hG : d.env < s.envs.size) (hGe : Scope.declLike? (s.envEntry d.env) = some (bG, oG))
    (hGRT : bG[JSStr.ofString "recursivelyTraverseLayoutEffects"]? = some bdRT) (hGRTv : bdRT.value = some (.obj fRT))
    (hRTo : fRT < s.heap.size) (hRTc : ∃ dd, (s.objEntry fRT).kind = .func dd)
    (hRT : ∀ w h1, Frame {} s w → KR ≤ w.fuel →
      WP eng answer (n + 1) h1 (callImpl eng (.obj fRT) .undefined #[rv, .obj B]) w fun v w' h' =>
        Frame {} w w' ∧ w.fuel ≤ w'.fuel + KR ∧ h' = h1) :
    WP eng answer (n + 2) h (callImpl eng (.obj fo) t #[rv, cv, .obj B]) s fun v w h' =>
      v = .undefined ∧ s.fuel ≤ w.fuel + KR + 200 ∧ Frame {} s w ∧ h' = h := by
  apply wp_callGen CLEGen.commitLayoutEffectOnFiber_eq (by decide) hlt hk (by omega) hcls hmode
    (by rw [hcode]; rfl) (by rw [hcode]; rfl) (simple d hcode) (by rw [hcode]; rfl) (by rw [hcode]; rfl)
  have hpn : d.code.info.fdi.paramNames = #[JSStr.ofString "finishedRoot", JSStr.ofString "current",
    JSStr.ofString "finishedWork"] := by rw [hcode]; rfl
  have hv : d.code.info.fdi.varNames = #[JSStr.ofString "flags", JSStr.ofString "prevProps",
    JSStr.ofString "newOffscreenSubtreeWasHidden"] := by rw [hcode]; rfl
  have hl : FDI.lexDecls d = #[] := by
    simp [FDI.lexDecls, hcode, CLEGen.commitLayoutEffectOnFiber_func, Func.info]
  have ha : d.code.isAsync = false := by rw [hcode]; rfl
  have e1 : d.env ≠ s.envs.size := Nat.ne_of_lt hG
  have e4 : d.env < s.envs.size + 1 := Nat.lt_succ_of_lt hG
  have e5 : d.env < s.envs.size + 1 + 1 := Nat.lt_succ_of_lt e4
  have e2 : d.env ≠ s.envs.size + 1 := Nat.ne_of_lt e4
  obtain ⟨dRT, hRTk⟩ := hRTc
  clear hcode
  simp only [CLEGen.commitLayoutEffectOnFiber]
  iterate 15 (first | js_go | js_norm [hB, hBk, hBf, hBt, h4, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner] | js_split)
  js_until [] [e1, e2, e4, e5, Ne.symm e1, Ne.symm e2, hG, hGe, hGRT, hGRTv, hRTo, hRTk, hB, hBk, hBf, hBt, h4, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  refine ⟨by js_norm [CallableC, e1, e2, e4, e5, Ne.symm e1, Ne.symm e2, hG, hGe, hGRT, hGRTv, hRTo, hRTk, hB, hBk, hBf, hBt, h4, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner], ?_⟩
  refine wp_mono (hRT _ _ (by frame_go' [hB]) (by js_norm [e1, e2, e4, e5, Ne.symm e1, Ne.symm e2, hG, hGe, hGRT, hGRTv, hRTo, hRTk, hB, hBk, hBf, hBt, h4, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]; omega)) ?_
  rintro v1 w1 h1 ⟨hF1, hfu1, rfl⟩
  have hfr1 : s.fuel ≤ w1.fuel + KR + 10 := by simp [bodyState, entryState] at hfu1; omega
  have hE1 := envEntry_frame0 hF1 (e := s.envs.size) (by js_norm [e1, e2, e4, e5, Ne.symm e1, Ne.symm e2, hG, hGe, hGRT, hGRTv, hRTo, hRTk, hB, hBk, hBf, hBt, h4, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner])
  have hE2 := envEntry_frame0 hF1 (e := s.envs.size + 1) (by js_norm [e1, e2, e4, e5, Ne.symm e1, Ne.symm e2, hG, hGe, hGRT, hGRTv, hRTo, hRTk, hB, hBk, hBf, hBt, h4, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner])
  have hS2 : s.envs.size + 1 < w1.envs.size := Nat.lt_of_lt_of_le (by js_norm [e1, e2, e4, e5, Ne.symm e1, Ne.symm e2, hG, hGe, hGRT, hGRTv, hRTo, hRTk, hB, hBk, hBf, hBt, h4, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]) hF1.envs_le
  have hS1 : s.envs.size < w1.envs.size := by omega
  js_until [] [hE1, hE2, hS1, hS2, e1, e2, e4, e5, Ne.symm e1, Ne.symm e2, hG, hGe, hGRT, hGRTv, hRTo, hRTk, hB, hBk, hBf, hBt, h4, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  refine ⟨by omega, frame_restore (frame_then_empty ?_ hF1) s⟩
  frame_go' [hB]


set_option maxRecDepth 40000 in
set_option maxHeartbeats 8000000 in
/-- **The root** (tag 3): the children traversed; no callbacks (`flags & 64` zero). -/
theorem cle_root {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t : Value} {s : State}
    {rv cv : Value} {B : ObjId} {fl : F64} {KR : Nat}
    {fw fe fc tw te tc : Bool}
    {bG : HashMap JSStr Binding} {oG : Option EnvId} {bdRT : Binding} {fRT : ObjId}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : KR + 300 ≤ s.fuel)
    (hcode : d.code = CLEGen.commitLayoutEffectOnFiber_func) (hcls : d.isClassCtor = false)
    (hmode : d.thisMode = .strict)
    (hB : B < s.heap.size) (hBk : (s.objEntry B).kind.isPlain = true)
    (hBf : (s.objEntry B).props.get? (.str (JSStr.ofString "flags")) = some (.data (.num fl) fw fe fc))
    (hBt : (s.objEntry B).props.get? (.str (JSStr.ofString "tag")) =
      some (.data (.num (F64.fin false 6755399441055744 (-51))) tw te tc))
    (h64 : numberBinOp .bitAnd fl (F64.fin false 4503599627370496 (-46)) = F64.fin false 0 (-1074))
    (hG : d.env < s.envs.size) (hGe : Scope.declLike? (s.envEntry d.env) = some (bG, oG))
    (hGRT : bG[JSStr.ofString "recursivelyTraverseLayoutEffects"]? = some bdRT) (hGRTv : bdRT.value = some (.obj fRT))
    (hRTo : fRT < s.heap.size) (hRTc : ∃ dd, (s.objEntry fRT).kind = .func dd)
    (hRT : ∀ w h1, Frame {} s w → KR ≤ w.fuel →
      WP eng answer (n + 1) h1 (callImpl eng (.obj fRT) .undefined #[rv, .obj B]) w fun v w' h' =>
        Frame {} w w' ∧ w.fuel ≤ w'.fuel + KR ∧ h' = h1) :
    WP eng answer (n + 2) h (callImpl eng (.obj fo) t #[rv, cv, .obj B]) s fun v w h' =>
      v = .undefined ∧ s.fuel ≤ w.fuel + KR + 200 ∧ Frame {} s w ∧ h' = h := by
  apply wp_callGen CLEGen.commitLayoutEffectOnFiber_eq (by decide) hlt hk (by omega) hcls hmode
    (by rw [hcode]; rfl) (by rw [hcode]; rfl) (simple d hcode) (by rw [hcode]; rfl) (by rw [hcode]; rfl)
  have hpn : d.code.info.fdi.paramNames = #[JSStr.ofString "finishedRoot", JSStr.ofString "current",
    JSStr.ofString "finishedWork"] := by rw [hcode]; rfl
  have hv : d.code.info.fdi.varNames = #[JSStr.ofString "flags", JSStr.ofString "prevProps",
    JSStr.ofString "newOffscreenSubtreeWasHidden"] := by rw [hcode]; rfl
  have hl : FDI.lexDecls d = #[] := by
    simp [FDI.lexDecls, hcode, CLEGen.commitLayoutEffectOnFiber_func, Func.info]
  have ha : d.code.isAsync = false := by rw [hcode]; rfl
  have e1 : d.env ≠ s.envs.size := Nat.ne_of_lt hG
  have e4 : d.env < s.envs.size + 1 := Nat.lt_succ_of_lt hG
  have e5 : d.env < s.envs.size + 1 + 1 := Nat.lt_succ_of_lt e4
  have e2 : d.env ≠ s.envs.size + 1 := Nat.ne_of_lt e4
  obtain ⟨dRT, hRTk⟩ := hRTc
  clear hcode
  simp only [CLEGen.commitLayoutEffectOnFiber]
  iterate 15 (first | js_go | js_norm [hB, hBk, hBf, hBt, h64, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner] | js_split)
  js_until [] [e1, e2, e4, e5, Ne.symm e1, Ne.symm e2, hG, hGe, hGRT, hGRTv, hRTo, hRTk, hB, hBk, hBf, hBt, h64, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  refine ⟨by js_norm [CallableC, e1, e2, e4, e5, Ne.symm e1, Ne.symm e2, hG, hGe, hGRT, hGRTv, hRTo, hRTk, hB, hBk, hBf, hBt, h64, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner], ?_⟩
  refine wp_mono (hRT _ _ (by frame_go' [hB]) (by js_norm [e1, e2, e4, e5, Ne.symm e1, Ne.symm e2, hG, hGe, hGRT, hGRTv, hRTo, hRTk, hB, hBk, hBf, hBt, h64, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]; omega)) ?_
  rintro v1 w1 h1 ⟨hF1, hfu1, rfl⟩
  have hfr1 : s.fuel ≤ w1.fuel + KR + 10 := by simp [bodyState, entryState] at hfu1; omega
  have hE1 := envEntry_frame0 hF1 (e := s.envs.size) (by js_norm [e1, e2, e4, e5, Ne.symm e1, Ne.symm e2, hG, hGe, hGRT, hGRTv, hRTo, hRTk, hB, hBk, hBf, hBt, h64, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner])
  have hE2 := envEntry_frame0 hF1 (e := s.envs.size + 1) (by js_norm [e1, e2, e4, e5, Ne.symm e1, Ne.symm e2, hG, hGe, hGRT, hGRTv, hRTo, hRTk, hB, hBk, hBf, hBt, h64, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner])
  have hS2 : s.envs.size + 1 < w1.envs.size := Nat.lt_of_lt_of_le (by js_norm [e1, e2, e4, e5, Ne.symm e1, Ne.symm e2, hG, hGe, hGRT, hGRTv, hRTo, hRTk, hB, hBk, hBf, hBt, h64, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]) hF1.envs_le
  have hS1 : s.envs.size < w1.envs.size := by omega
  js_until [] [hE1, hE2, hS1, hS2, e1, e2, e4, e5, Ne.symm e1, Ne.symm e2, hG, hGe, hGRT, hGRTv, hRTo, hRTk, hB, hBk, hBf, hBt, h64, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  refine ⟨by omega, frame_restore (frame_then_empty ?_ hF1) s⟩
  frame_go' [hB]

end

end ReactLayoutFiber
