import JSProofs.JsTactic
import JSProofs.GRFGen

/-!
# React's `getRootForUpdatedFiber` (zippy docs/react-proofs.md)

```js
function getRootForUpdatedFiber(sourceFiber) {
  if (50 < nestedUpdateCount) throw (…);
  for (var parent = sourceFiber.return; null !== parent; )
    (sourceFiber = parent), (parent = sourceFiber.return);
  return 3 === sourceFiber.tag ? sourceFiber.stateNode : null;
}
```
The walk up the fiber tree to the root. For the counter's tree (the component's fiber `S`, whose `return` is the
host root fiber `R`: tag 3, `return` null, `stateNode` the root `Root`) it returns `Root`: the loop runs once, and
the proof follows its iterations like straight-line code. It writes nothing outside its own variables.
-/

open ES ES.M HostRuns Logic
open Std (HashMap)

namespace ReactRoot

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ}

theorem simple (d : FuncData) (hc : d.code = GRFGen.getRootForUpdatedFiber_func) : FDI.Simple d := by
  constructor <;> rw [hc] <;> try rfl
  simp [GRFGen.getRootForUpdatedFiber_func, Func.params, Func.info]

set_option maxRecDepth 10000 in
theorem call_spec {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t : Value} {s : State}
    {bG : HashMap JSStr Binding} {oG : Option EnvId} {bdN : Binding} {S R : ObjId} {Root : ObjId}
    {sw se sc rw re rc tw te tc nw ne nc : Bool}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : 20 ≤ s.fuel)
    (hcode : d.code = GRFGen.getRootForUpdatedFiber_func) (hcls : d.isClassCtor = false)
    (hmode : d.thisMode = .strict)
    (hG : d.env < s.envs.size) (hGe : s.envEntry d.env = .decl bG oG)
    (hGN : bG[JSStr.ofString "nestedUpdateCount"]? = some bdN)
    (hGNv : bdN.value = some (.num (F64.fin false 0 (-1074))))
    (hS : S < s.heap.size) (hSk : (s.objEntry S).kind.isPlain = true)
    (hSr : (s.objEntry S).props.get? (.str "return") = some (.data (.obj R) sw se sc))
    (hR : R < s.heap.size) (hRk : (s.objEntry R).kind.isPlain = true)
    (hRr : (s.objEntry R).props.get? (.str "return") = some (.data .null rw re rc))
    (hRt : (s.objEntry R).props.get? (.str "tag") = some (.data (.num (F64.fin false 6755399441055744 (-51))) tw te tc))
    (hRs : (s.objEntry R).props.get? (.str "stateNode") = some (.data (.obj Root) nw ne nc)) :
    WP eng answer (n + 1) h (callImpl eng (.obj fo) t #[.obj S]) s fun v w _ =>
      v = .obj Root ∧ Frame {} s w ∧ s.fuel ≤ w.fuel + 3 := by
  apply wp_callGen GRFGen.getRootForUpdatedFiber_eq (by decide) hlt hk (by omega) hcls hmode
    (by rw [hcode]; rfl) (by rw [hcode]; rfl) (simple d hcode) (by rw [hcode]; rfl) (by rw [hcode]; rfl)
  have hpn : d.code.info.fdi.paramNames = #[JSStr.ofString "sourceFiber"] := by rw [hcode]; rfl
  have hv : d.code.info.fdi.varNames = #[JSStr.ofString "parent"] := by rw [hcode]; rfl
  have hl : FDI.lexDecls d = #[] := by simp [FDI.lexDecls, hcode, GRFGen.getRootForUpdatedFiber_func, Func.info]
  have ha : d.code.isAsync = false := by rw [hcode]; rfl
  have hne : s.envs.size ≠ d.env := Nat.ne_of_gt hG
  have hG1 : d.env < s.envs.size + 1 := Nat.lt_succ_of_lt hG
  clear hcode
  simp only [GRFGen.getRootForUpdatedFiber]
  js [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGN, hGNv, hS, hSk, hSr, hR, hRk, hRr, hRt, hRs,
    FDI.fdiCtx, Sem.inner]
  all_goals (try apply And.intro)
  all_goals (try apply And.intro)
  all_goals first | omega | frame_go' [*, hG, hG1, hne, Ne.symm hne, hGe]

end

end ReactRoot
