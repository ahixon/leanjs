import JSProofs.JsTactic
import JSProofs.PRCGen
import JSProofs.CDRGen

/-!
# `prepareToReadContext` and `checkDidRenderIdHook` around the counter's render (zippy docs/react-proofs.md)

`prepareToReadContext(workInProgress)` for a fiber with no context dependencies (the counter reads no context), and
`checkDidRenderIdHook()` when no `useId` ran (`localIdCounter` 0): false.
-/

open ES ES.M HostRuns Logic
open Std (HashMap)

namespace ReactRenderPrep

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ}

theorem simpleP (d : FuncData) (hc : d.code = PRCGen.prepareToReadContext_func) : FDI.Simple d := by
  constructor <;> rw [hc] <;> try rfl
  simp [PRCGen.prepareToReadContext_func, Func.params, Func.info]

theorem simpleC (d : FuncData) (hc : d.code = CDRGen.checkDidRenderIdHook_func) : FDI.Simple d := by
  constructor <;> rw [hc] <;> try rfl
  simp [CDRGen.checkDidRenderIdHook_func, Func.params, Func.info]

/-- What `prepareToReadContext` writes. -/
def fpP (g : EnvId) : Footprint := ⟨[(g, "currentlyRenderingFiber$1"), (g, "lastContextDependency")], [], false⟩

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
set_option maxRecDepth 20000 in
/-- **`prepareToReadContext(W)`** for a fiber with no dependencies. -/
theorem prepare_spec {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t : Value} {s : State}
    {bG : HashMap JSStr Binding} {oG : Option EnvId} {bdF bdL : Binding} {W : ObjId} {dw de dc : Bool}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : 10 ≤ s.fuel)
    (hcode : d.code = PRCGen.prepareToReadContext_func) (hcls : d.isClassCtor = false) (hmode : d.thisMode = .strict)
    (hG : d.env < s.envs.size) (hGe : Scope.declLike? (s.envEntry d.env) = some (bG, oG))
    (hGF : bG[JSStr.ofString "currentlyRenderingFiber$1"]? = some bdF) (hGFm : bdF.mutable = true)
    (hGFi : bdF.value.isSome = true)
    (hGL : bG[JSStr.ofString "lastContextDependency"]? = some bdL) (hGLm : bdL.mutable = true)
    (hGLi : bdL.value.isSome = true)
    (hW : W < s.heap.size) (hWk : (s.objEntry W).kind.isPlain = true)
    (hWd : (s.objEntry W).props.get? (.str "dependencies") = some (.data .null dw de dc)) :
    WP eng answer n h (callImpl eng (.obj fo) t #[.obj W]) s fun v w h' =>
      v = .undefined ∧ Frame (fpP d.env) s w ∧ s.fuel ≤ w.fuel + 10 ∧ h' = h ∧ w.realm = s.realm ∧
      Scope.declLike? (w.envEntry d.env) = some ((bG.modify (JSStr.ofString "currentlyRenderingFiber$1")
        (fun bd => { bd with value := some (.obj W) })).modify (JSStr.ofString "lastContextDependency")
        (fun bd => { bd with value := some .null }), oG) := by
  apply wp_callGen PRCGen.prepareToReadContext_eq (by decide) hlt hk (by omega) hcls hmode
    (by rw [hcode]; rfl) (by rw [hcode]; rfl) (simpleP d hcode) (by rw [hcode]; rfl) (by rw [hcode]; rfl)
  have hpn : d.code.info.fdi.paramNames = #[JSStr.ofString "workInProgress"] := by rw [hcode]; rfl
  have hv : d.code.info.fdi.varNames = #[] := by rw [hcode]; rfl
  have hl : FDI.lexDecls d = #[] := by simp [FDI.lexDecls, hcode, PRCGen.prepareToReadContext_func, Func.info]
  have ha : d.code.isAsync = false := by rw [hcode]; rfl
  have hne : s.envs.size ≠ d.env := Nat.ne_of_gt hG
  have hG1 : d.env < s.envs.size + 1 := Nat.lt_succ_of_lt hG
  clear hcode
  simp only [PRCGen.prepareToReadContext]
  js [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGF, hGFm, hGFi, hGL, hGLm, hGLi, hW, hWk, hWd, FDI.fdiCtx,
    Sem.inner]
  all_goals (repeat' apply And.intro)
  all_goals first
    | rfl | omega | (simp only [js_simp]; omega) | (simp only [fpP]; frame_go' [*, hne, Ne.symm hne, hG1]; done)
    | (js_norm [*]; done) | skip

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
set_option maxRecDepth 20000 in
/-- **`checkDidRenderIdHook()`** when no `useId` ran: false. -/
theorem check_spec {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t : Value} {args : Array Value} {s : State}
    {bG : HashMap JSStr Binding} {oG : Option EnvId} {bdI : Binding}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : 10 ≤ s.fuel)
    (hcode : d.code = CDRGen.checkDidRenderIdHook_func) (hcls : d.isClassCtor = false) (hmode : d.thisMode = .strict)
    (hG : d.env < s.envs.size) (hGe : Scope.declLike? (s.envEntry d.env) = some (bG, oG))
    (hGI : bG[JSStr.ofString "localIdCounter"]? = some bdI) (hGIm : bdI.mutable = true)
    (hGIv : bdI.value = some (.num (F64.fin false 0 (-1074)))) :
    WP eng answer n h (callImpl eng (.obj fo) t args) s fun v w h' =>
      v = .bool false ∧ Frame ⟨[(d.env, "localIdCounter")], [], false⟩ s w ∧ s.fuel ≤ w.fuel + 10 ∧ h' = h ∧
      w.realm = s.realm ∧
      Scope.declLike? (w.envEntry d.env) = some (bG.modify (JSStr.ofString "localIdCounter")
        (fun bd => { bd with value := some (.num (F64.fin false 0 (-1074))) }), oG) := by
  apply wp_callGen CDRGen.checkDidRenderIdHook_eq (by decide) hlt hk (by omega) hcls hmode
    (by rw [hcode]; rfl) (by rw [hcode]; rfl) (simpleC d hcode) (by rw [hcode]; rfl) (by rw [hcode]; rfl)
  have hpn : d.code.info.fdi.paramNames = #[] := by rw [hcode]; rfl
  have hv : d.code.info.fdi.varNames = #[JSStr.ofString "didRenderIdHook"] := by rw [hcode]; rfl
  have hl : FDI.lexDecls d = #[] := by simp [FDI.lexDecls, hcode, CDRGen.checkDidRenderIdHook_func, Func.info]
  have ha : d.code.isAsync = false := by rw [hcode]; rfl
  have hne : s.envs.size ≠ d.env := Nat.ne_of_gt hG
  have hG1 : d.env < s.envs.size + 1 := Nat.lt_succ_of_lt hG
  clear hcode
  simp only [CDRGen.checkDidRenderIdHook]
  js [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGI, hGIm, hGIv, FDI.fdiCtx, Sem.inner]
  all_goals (repeat' apply And.intro)
  all_goals first
    | rfl | omega | (simp only [js_simp]; omega) | (frame_go' [*, hne, Ne.symm hne, hG1]; done)
    | (js_norm [*]; done) | skip

end

end ReactRenderPrep
