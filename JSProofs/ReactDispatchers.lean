import JSProofs.JsTactic
import JSProofs.PDGen
import JSProofs.PADGen

/-!
# React's `pushDispatcher` and `pushAsyncDispatcher` outside rendering (zippy docs/react-proofs.md)

At the start of a render: the hooks dispatcher (`ReactSharedInternals.H`, after the first render the dispatcher the
last render restored) becomes the context-only one and the previous is returned; the async dispatcher (`.A`) becomes the default one and the previous is returned.
-/

open ES ES.M HostRuns Logic
open Std (HashMap)

namespace ReactDispatchers

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ}

theorem simpleD (d : FuncData) (hc : d.code = PDGen.pushDispatcher_func) : FDI.Simple d := by
  constructor <;> rw [hc] <;> try rfl
  simp [PDGen.pushDispatcher_func, Func.params, Func.info]

theorem simpleA (d : FuncData) (hc : d.code = PADGen.pushAsyncDispatcher_func) : FDI.Simple d := by
  constructor <;> rw [hc] <;> try rfl
  simp [PADGen.pushAsyncDispatcher_func, Func.params, Func.info]

set_option maxRecDepth 10000 in
/-- **`pushDispatcher()`** outside rendering (after the first render `.H` holds a dispatcher object `P`): `.H` becomes
the context-only dispatcher; `P` is returned. -/
theorem push_spec {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t : Value} {s : State}
    {bG : HashMap JSStr Binding} {oG : Option EnvId} {bdI bdC : Binding} {I C P : ObjId} {he hc : Bool}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : 10 ≤ s.fuel)
    (hcode : d.code = PDGen.pushDispatcher_func) (hcls : d.isClassCtor = false) (hmode : d.thisMode = .strict)
    (hG : d.env < s.envs.size) (hGe : Scope.declLike? (s.envEntry d.env) = some (bG, oG))
    (hGI : bG[JSStr.ofString "ReactSharedInternals"]? = some bdI) (hGIv : bdI.value = some (.obj I))
    (hGC : bG[JSStr.ofString "ContextOnlyDispatcher"]? = some bdC) (hGCv : bdC.value = some (.obj C))
    (hI : I < s.heap.size) (hIk : (s.objEntry I).kind.isPlain = true)
    (hIH : (s.objEntry I).props.get? (.str "H") = some (.data (.obj P) true he hc)) :
    WP eng answer n h (callImpl eng (.obj fo) t #[]) s fun v w _ =>
      v = .obj P ∧ Frame ⟨[], [(I, .str "H")], false⟩ s w ∧ s.fuel ≤ w.fuel + 10 ∧
      (w.objEntry I).props.get? (.str "H") = some (.data (.obj C) true he hc) := by
  apply wp_callGen PDGen.pushDispatcher_eq (by decide) hlt hk (by omega) hcls hmode
    (by rw [hcode]; rfl) (by rw [hcode]; rfl) (simpleD d hcode) (by rw [hcode]; rfl) (by rw [hcode]; rfl)
  have hpn : d.code.info.fdi.paramNames = #[] := by rw [hcode]; rfl
  have hv : d.code.info.fdi.varNames = #[JSStr.ofString "prevDispatcher"] := by rw [hcode]; rfl
  have hl : FDI.lexDecls d = #[] := by simp [FDI.lexDecls, hcode, PDGen.pushDispatcher_func, Func.info]
  have ha : d.code.isAsync = false := by rw [hcode]; rfl
  have hne : s.envs.size ≠ d.env := Nat.ne_of_gt hG
  have hG1 : d.env < s.envs.size + 1 := Nat.lt_succ_of_lt hG
  clear hcode
  simp only [PDGen.pushDispatcher]
  js [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGI, hGIv, hGC, hGCv, hI, hIk, hIH, FDI.fdiCtx, Sem.inner]
  all_goals (try apply And.intro)
  all_goals (try apply And.intro)
  all_goals (try apply And.intro)
  all_goals first | rfl | omega | frame_go' [*, hne, Ne.symm hne, hG1]

set_option maxRecDepth 10000 in
/-- **`pushAsyncDispatcher()`**: `.A` becomes the default async dispatcher; the previous is returned. -/
theorem pushAsync_spec {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t : Value} {s : State}
    {bG : HashMap JSStr Binding} {oG : Option EnvId} {bdI bdD : Binding} {I D : ObjId} {a : Value} {ae ac : Bool}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : 10 ≤ s.fuel)
    (hcode : d.code = PADGen.pushAsyncDispatcher_func) (hcls : d.isClassCtor = false) (hmode : d.thisMode = .strict)
    (hG : d.env < s.envs.size) (hGe : Scope.declLike? (s.envEntry d.env) = some (bG, oG))
    (hGI : bG[JSStr.ofString "ReactSharedInternals"]? = some bdI) (hGIv : bdI.value = some (.obj I))
    (hGD : bG[JSStr.ofString "DefaultAsyncDispatcher"]? = some bdD) (hGDv : bdD.value = some (.obj D))
    (hI : I < s.heap.size) (hIk : (s.objEntry I).kind.isPlain = true)
    (hIA : (s.objEntry I).props.get? (.str "A") = some (.data a true ae ac)) :
    WP eng answer n h (callImpl eng (.obj fo) t #[]) s fun v w _ =>
      v = a ∧ Frame ⟨[], [(I, .str "A")], false⟩ s w ∧ s.fuel ≤ w.fuel + 10 ∧
      (w.objEntry I).props.get? (.str "A") = some (.data (.obj D) true ae ac) := by
  apply wp_callGen PADGen.pushAsyncDispatcher_eq (by decide) hlt hk (by omega) hcls hmode
    (by rw [hcode]; rfl) (by rw [hcode]; rfl) (simpleA d hcode) (by rw [hcode]; rfl) (by rw [hcode]; rfl)
  have hpn : d.code.info.fdi.paramNames = #[] := by rw [hcode]; rfl
  have hv : d.code.info.fdi.varNames = #[JSStr.ofString "prevAsyncDispatcher"] := by rw [hcode]; rfl
  have hl : FDI.lexDecls d = #[] := by simp [FDI.lexDecls, hcode, PADGen.pushAsyncDispatcher_func, Func.info]
  have ha : d.code.isAsync = false := by rw [hcode]; rfl
  have hne : s.envs.size ≠ d.env := Nat.ne_of_gt hG
  have hG1 : d.env < s.envs.size + 1 := Nat.lt_succ_of_lt hG
  clear hcode
  simp only [PADGen.pushAsyncDispatcher]
  js [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGI, hGIv, hGD, hGDv, hI, hIk, hIA, FDI.fdiCtx, Sem.inner]
  all_goals (try apply And.intro)
  all_goals (try apply And.intro)
  all_goals (try apply And.intro)
  all_goals first | rfl | omega | frame_go' [*, hne, Ne.symm hne, hG1]

end

end ReactDispatchers
