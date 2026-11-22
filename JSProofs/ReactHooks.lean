import JSProofs.JsTactic
import JSProofs.UWHGen

/-!
# React's hooks in a re-render (zippy docs/react-proofs.md)

`updateWorkInProgressHook()` for the first hook of a component re-rendering (`currentHook` and
`workInProgressHook` null, the work in progress's `memoizedState` cleared by `renderWithHooks`): the current
fiber's first hook is cloned into a fresh object, which becomes the work in progress's first hook.
-/

open ES ES.M HostRuns Logic
open Std (HashMap)

namespace ReactHooks

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ}

theorem simpleW (d : FuncData) (hc : d.code = UWHGen.updateWorkInProgressHook_func) : FDI.Simple d := by
  constructor <;> rw [hc] <;> try rfl
  simp [UWHGen.updateWorkInProgressHook_func, Func.params, Func.info]

/-- What it writes (besides the new hook). -/
def fpW (g : EnvId) (C1 : ObjId) : Footprint :=
  ⟨[(g, "currentHook"), (g, "workInProgressHook")], [(C1, .str "memoizedState")], false⟩

set_option maxRecDepth 20000 in
/-- **`updateWorkInProgressHook()`**, the first hook of a re-render: a clone of the current first hook. -/
theorem first_spec {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t : Value} {s : State}
    {bG : HashMap JSStr Binding} {oG : Option EnvId} {bdC bdW bdF : Binding} {C1 C0 H0 : ObjId}
    {ms bs bq q : Value} {aw ae ac mw me mc nw ne w1 e1 c1 w2 e2 c2 w3 e3 c3 w4 e4 c4 : Bool}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : 20 ≤ s.fuel)
    (hcode : d.code = UWHGen.updateWorkInProgressHook_func) (hcls : d.isClassCtor = false)
    (hmode : d.thisMode = .strict)
    (hG : d.env < s.envs.size) (hGe : Scope.declLike? (s.envEntry d.env) = some (bG, oG))
    (hGC : bG[JSStr.ofString "currentHook"]? = some bdC) (hGCm : bdC.mutable = true) (hGCv : bdC.value = some .null)
    (hGW : bG[JSStr.ofString "workInProgressHook"]? = some bdW) (hGWm : bdW.mutable = true)
    (hGWv : bdW.value = some .null)
    (hGF : bG[JSStr.ofString "currentlyRenderingFiber"]? = some bdF) (hGFv : bdF.value = some (.obj C1))
    (hC1 : C1 < s.heap.size) (hC1k : (s.objEntry C1).kind.isPlain = true)
    (hC1a : (s.objEntry C1).props.get? (.str "alternate") = some (.data (.obj C0) aw ae ac))
    (hC1m : (s.objEntry C1).props.get? (.str "memoizedState") = some (.data .null true me mc))
    (hC0 : C0 < s.heap.size) (hC0k : (s.objEntry C0).kind.isPlain = true)
    (hC0m : (s.objEntry C0).props.get? (.str "memoizedState") = some (.data (.obj H0) mw nw ne))
    (hH0 : H0 < s.heap.size) (hH0k : (s.objEntry H0).kind.isPlain = true)
    (hHm : (s.objEntry H0).props.get? (.str "memoizedState") = some (.data ms w1 e1 c1))
    (hHb : (s.objEntry H0).props.get? (.str "baseState") = some (.data bs w2 e2 c2))
    (hHq : (s.objEntry H0).props.get? (.str "baseQueue") = some (.data bq w3 e3 c3))
    (hHu : (s.objEntry H0).props.get? (.str "queue") = some (.data q w4 e4 c4))
    (d1 : C1 ≠ C0) (d2 : C1 ≠ H0) :
    WP eng answer n h (callImpl eng (.obj fo) t #[]) s fun v w h' =>
      v = .obj s.heap.size ∧ Frame (fpW d.env C1) s w ∧ s.fuel ≤ w.fuel + 20 ∧ h' = h ∧
      Scope.declLike? (w.envEntry d.env) = some ((bG.modify (JSStr.ofString "currentHook")
        (fun bd => { bd with value := some (.obj H0) })).modify (JSStr.ofString "workInProgressHook")
        (fun bd => { bd with value := some (.obj s.heap.size) }), oG) ∧
      (w.objEntry C1).props.get? (.str "memoizedState") = some (.data (.obj s.heap.size) true me mc) ∧
      w.heap.size = s.heap.size + 1 ∧ (w.objEntry s.heap.size).kind.isPlain = true ∧
      (w.objEntry s.heap.size).props.get? (.str "memoizedState") = some (.data ms true true true) ∧
      (w.objEntry s.heap.size).props.get? (.str "baseState") = some (.data bs true true true) ∧
      (w.objEntry s.heap.size).props.get? (.str "baseQueue") = some (.data bq true true true) ∧
      (w.objEntry s.heap.size).props.get? (.str "queue") = some (.data q true true true) ∧
      (w.objEntry s.heap.size).props.get? (.str "next") = some (.data .null true true true) := by
  apply wp_callGen UWHGen.updateWorkInProgressHook_eq (by decide) hlt hk (by omega) hcls hmode
    (by rw [hcode]; rfl) (by rw [hcode]; rfl) (simpleW d hcode) (by rw [hcode]; rfl) (by rw [hcode]; rfl)
  have hpn : d.code.info.fdi.paramNames = #[] := by rw [hcode]; rfl
  have hv : d.code.info.fdi.varNames = #[JSStr.ofString "nextCurrentHook", JSStr.ofString "nextWorkInProgressHook"] := by
    rw [hcode]; rfl
  have hl : FDI.lexDecls d = #[] := by simp [FDI.lexDecls, hcode, UWHGen.updateWorkInProgressHook_func, Func.info]
  have ha : d.code.isAsync = false := by rw [hcode]; rfl
  have hne : s.envs.size ≠ d.env := Nat.ne_of_gt hG
  have hG1 : d.env < s.envs.size + 1 := Nat.lt_succ_of_lt hG
  clear hcode
  simp only [UWHGen.updateWorkInProgressHook]
  js [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGC, hGCm, hGCv, hGW, hGWm, hGWv, hGF, hGFv, hC1, hC1k, hC1a,
    hC1m, hC0, hC0k, hC0m, hH0, hH0k, hHm, hHb, hHq, hHu, d1, d2, Ne.symm d1, Ne.symm d2, Nat.ne_of_lt hH0, Nat.ne_of_gt hH0, Nat.lt_succ_of_lt hH0, Nat.ne_of_lt hC1, Nat.ne_of_gt hC1, Nat.lt_succ_of_lt hC1, Nat.ne_of_lt hC0, Nat.ne_of_gt hC0, Nat.lt_succ_of_lt hC0, FDI.fdiCtx, Sem.inner]
  all_goals (repeat' apply And.intro)
  all_goals first | omega | (simp only [js_simp]; omega) | (simp only [fpW]; frame_go' [*, hne, Ne.symm hne, hG1]; done) | (js_norm [*]; done)

end

end ReactHooks
