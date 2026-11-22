import JSProofs.Rules7
import JSProofs.ReactHostContext
import JSProofs.PHCtxGen
import JSProofs.SSTCGen
import JSProofs.MRGen

/-!
# The button's beginWork helpers (zippy docs/react-proofs.md)

`getChildHostContextProd(0, "button")` (0), `pushHostContext(fiber)` for an HTML element without a state hook (no
push: same namespace), `shouldSetTextContent("button", props)` for a string child (true), `markRef(current, wip)`
with neither ref (nothing).
-/

open ES ES.M HostRuns Logic
open Std (HashMap)

namespace ReactButtonHelpers

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ}

set_option maxRecDepth 10000 in
/-- **`getChildHostContextProd(0, "button")`** is 0. -/
theorem child_button {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t : Value} {s : State}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : 10 ≤ s.fuel)
    (hcode : d.code = GCHCGen.getChildHostContextProd_func) (hcls : d.isClassCtor = false)
    (hmode : d.thisMode = .strict) :
    WP eng answer n h (callImpl eng (.obj fo) t #[.num (F64.fin false 0 (-1074)), .str (JSStr.ofString "button")]) s
      fun v w h' => v = .num (F64.fin false 0 (-1074)) ∧ Frame {} s w ∧ s.fuel ≤ w.fuel + 10 ∧ h' = h ∧
        w.realm = s.realm := by
  apply wp_callGen GCHCGen.getChildHostContextProd_eq (by decide) hlt hk (by omega) hcls hmode
    (by rw [hcode]; rfl) (by rw [hcode]; rfl) (ReactHostContext.simpleC d hcode) (by rw [hcode]; rfl) (by rw [hcode]; rfl)
  have hpn : d.code.info.fdi.paramNames = #[JSStr.ofString "parentNamespace", JSStr.ofString "type"] := by
    rw [hcode]; rfl
  have hv : d.code.info.fdi.varNames = #[] := by rw [hcode]; rfl
  have hl : FDI.lexDecls d = #[] := by simp [FDI.lexDecls, hcode, GCHCGen.getChildHostContextProd_func, Func.info]
  have ha : d.code.isAsync = false := by rw [hcode]; rfl
  clear hcode
  simp only [GCHCGen.getChildHostContextProd]
  js [hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner, List.findIdx?_toArray, List.findIdx?_cons, List.findIdx?_nil, Option.isNone_some, Option.isNone_none, Option.map_some, Option.map_none]
  all_goals (repeat' apply And.intro)
  all_goals first | rfl | omega | (simp only [js_simp]; omega) | frame_go' [*]

theorem simpleS (d : FuncData) (hc : d.code = SSTCGen.shouldSetTextContent_func) : FDI.Simple d := by
  constructor <;> rw [hc] <;> try rfl
  simp [SSTCGen.shouldSetTextContent_func, Func.params, Func.info]

set_option maxRecDepth 10000 in
/-- **`shouldSetTextContent("button", props)`** for a string child: true. -/
theorem sstc_string {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t : Value} {s : State} {C : ObjId} {str : JSStr}
    {cw ce cc : Bool}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : 10 ≤ s.fuel)
    (hcode : d.code = SSTCGen.shouldSetTextContent_func) (hcls : d.isClassCtor = false) (hmode : d.thisMode = .strict)
    (hC : C < s.heap.size) (hCk : (s.objEntry C).kind.isPlain = true)
    (hCc : (s.objEntry C).props.get? (.str "children") = some (.data (.str str) cw ce cc)) :
    WP eng answer n h (callImpl eng (.obj fo) t #[.str (JSStr.ofString "button"), .obj C]) s
      fun v w h' => v = .bool true ∧ Frame {} s w ∧ s.fuel ≤ w.fuel + 10 ∧ h' = h ∧ w.realm = s.realm := by
  apply wp_callGen SSTCGen.shouldSetTextContent_eq (by decide) hlt hk (by omega) hcls hmode
    (by rw [hcode]; rfl) (by rw [hcode]; rfl) (simpleS d hcode) (by rw [hcode]; rfl) (by rw [hcode]; rfl)
  have hpn : d.code.info.fdi.paramNames = #[JSStr.ofString "type", JSStr.ofString "props"] := by rw [hcode]; rfl
  have hv : d.code.info.fdi.varNames = #[] := by rw [hcode]; rfl
  have hl : FDI.lexDecls d = #[] := by simp [FDI.lexDecls, hcode, SSTCGen.shouldSetTextContent_func, Func.info]
  have ha : d.code.isAsync = false := by rw [hcode]; rfl
  clear hcode
  simp only [SSTCGen.shouldSetTextContent]
  js [hpn, hv, hl, ha, hC, hCk, hCc, FDI.fdiCtx, Sem.inner]
  refine wp_typeofMemberC ?_
  js [hpn, hv, hl, ha, hC, hCk, hCc, FDI.fdiCtx, Sem.inner, TypeofC]
  all_goals (repeat' apply And.intro)
  all_goals first | rfl | omega | (simp only [js_simp]; omega) | frame_go' [*] | (js_norm [*]; done)

theorem simpleM (d : FuncData) (hc : d.code = MRGen.markRef_func) : FDI.Simple d := by
  constructor <;> rw [hc] <;> try rfl
  simp [MRGen.markRef_func, Func.params, Func.info]

set_option maxRecDepth 10000 in
/-- **`markRef(current, workInProgress)`** with neither ref: nothing. -/
theorem markref_null {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t : Value} {s : State} {H X : ObjId}
    {xw xe xc hw he hc : Bool}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : 10 ≤ s.fuel)
    (hcode : d.code = MRGen.markRef_func) (hcls : d.isClassCtor = false) (hmode : d.thisMode = .strict)
    (hX : X < s.heap.size) (hXk : (s.objEntry X).kind.isPlain = true)
    (hXr : (s.objEntry X).props.get? (.str "ref") = some (.data .null xw xe xc))
    (hH : H < s.heap.size) (hHk : (s.objEntry H).kind.isPlain = true)
    (hHr : (s.objEntry H).props.get? (.str "ref") = some (.data .null hw he hc)) :
    WP eng answer n h (callImpl eng (.obj fo) t #[.obj H, .obj X]) s
      fun v w h' => v = .undefined ∧ Frame {} s w ∧ s.fuel ≤ w.fuel + 10 ∧ h' = h ∧ w.realm = s.realm := by
  apply wp_callGen MRGen.markRef_eq (by decide) hlt hk (by omega) hcls hmode
    (by rw [hcode]; rfl) (by rw [hcode]; rfl) (simpleM d hcode) (by rw [hcode]; rfl) (by rw [hcode]; rfl)
  have hpn : d.code.info.fdi.paramNames = #[JSStr.ofString "current", JSStr.ofString "workInProgress"] := by
    rw [hcode]; rfl
  have hv : d.code.info.fdi.varNames = #[JSStr.ofString "ref"] := by rw [hcode]; rfl
  have hl : FDI.lexDecls d = #[] := by simp [FDI.lexDecls, hcode, MRGen.markRef_func, Func.info]
  have ha : d.code.isAsync = false := by rw [hcode]; rfl
  clear hcode
  simp only [MRGen.markRef]
  js [hpn, hv, hl, ha, hX, hXk, hXr, hH, hHk, hHr, FDI.fdiCtx, Sem.inner]
  all_goals (repeat' apply And.intro)
  all_goals first | rfl | omega | (simp only [js_simp]; omega) | frame_go' [*] | (js_norm [*]; done)

end

end ReactButtonHelpers
