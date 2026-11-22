import JSProofs.JsTactic
import JSProofs.GOHCGen
import JSProofs.GCHCGen

/-!
# React's host-context helpers for an HTML container (zippy docs/react-proofs.md)

`getOwnHostContext(namespaceURI)` of the HTML namespace is 0 (none); `getChildHostContextProd(0, type)` of an
element that is neither `svg` nor `math` (the counter's container, a `DIV`) is 0.
-/

open ES ES.M HostRuns Logic
open Std (HashMap)

namespace ReactHostContext

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ}

theorem simpleO (d : FuncData) (hc : d.code = GOHCGen.getOwnHostContext_func) : FDI.Simple d := by
  constructor <;> rw [hc] <;> try rfl
  simp [GOHCGen.getOwnHostContext_func, Func.params, Func.info]

theorem simpleC (d : FuncData) (hc : d.code = GCHCGen.getChildHostContextProd_func) : FDI.Simple d := by
  constructor <;> rw [hc] <;> try rfl
  simp [GCHCGen.getChildHostContextProd_func, Func.params, Func.info]

set_option maxRecDepth 10000 in
/-- **`getOwnHostContext("http://www.w3.org/1999/xhtml")`** is 0. -/
theorem own_html {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t : Value} {s : State}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : 10 ≤ s.fuel)
    (hcode : d.code = GOHCGen.getOwnHostContext_func) (hcls : d.isClassCtor = false) (hmode : d.thisMode = .strict) :
    WP eng answer n h (callImpl eng (.obj fo) t #[.str (JSStr.ofString "http://www.w3.org/1999/xhtml")]) s
      fun v w h' => v = .num (F64.fin false 0 (-1074)) ∧ Frame {} s w ∧ s.fuel ≤ w.fuel + 10 ∧ h' = h := by
  apply wp_callGen GOHCGen.getOwnHostContext_eq (by decide) hlt hk (by omega) hcls hmode
    (by rw [hcode]; rfl) (by rw [hcode]; rfl) (simpleO d hcode) (by rw [hcode]; rfl) (by rw [hcode]; rfl)
  have hpn : d.code.info.fdi.paramNames = #[JSStr.ofString "namespaceURI"] := by rw [hcode]; rfl
  have hv : d.code.info.fdi.varNames = #[] := by rw [hcode]; rfl
  have hl : FDI.lexDecls d = #[] := by simp [FDI.lexDecls, hcode, GOHCGen.getOwnHostContext_func, Func.info]
  have ha : d.code.isAsync = false := by rw [hcode]; rfl
  clear hcode
  simp only [GOHCGen.getOwnHostContext]
  js [hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner, List.findIdx?_toArray, List.findIdx?_cons, List.findIdx?_nil, Option.isNone_some, Option.isNone_none, Option.map_some, Option.map_none]
  all_goals (repeat' apply And.intro)
  all_goals first | rfl | omega | (simp only [js_simp]; omega) | frame_go' [*]

set_option maxRecDepth 10000 in
/-- **`getChildHostContextProd(0, "DIV")`** is 0. -/
theorem child_div {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t : Value} {s : State}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : 10 ≤ s.fuel)
    (hcode : d.code = GCHCGen.getChildHostContextProd_func) (hcls : d.isClassCtor = false)
    (hmode : d.thisMode = .strict) :
    WP eng answer n h (callImpl eng (.obj fo) t #[.num (F64.fin false 0 (-1074)), .str (JSStr.ofString "DIV")]) s
      fun v w h' => v = .num (F64.fin false 0 (-1074)) ∧ Frame {} s w ∧ s.fuel ≤ w.fuel + 10 ∧ h' = h := by
  apply wp_callGen GCHCGen.getChildHostContextProd_eq (by decide) hlt hk (by omega) hcls hmode
    (by rw [hcode]; rfl) (by rw [hcode]; rfl) (simpleC d hcode) (by rw [hcode]; rfl) (by rw [hcode]; rfl)
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


set_option maxRecDepth 10000 in
theorem own_html_exact {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t : Value} {s : State}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : 10 ≤ s.fuel)
    (hcode : d.code = GOHCGen.getOwnHostContext_func) (hcls : d.isClassCtor = false) (hmode : d.thisMode = .strict) :
    WP eng answer n h (callImpl eng (.obj fo) t #[.str (JSStr.ofString "http://www.w3.org/1999/xhtml")]) s
      fun v w h' => v = .num (F64.fin false 0 (-1074)) ∧ h' = h ∧ w = ((bodyState s fo d t #[.str (JSStr.ofString "http://www.w3.org/1999/xhtml")]).pushEnv (Env.decl ∅ (some s.envs.size))).restore s := by
  apply wp_callGen GOHCGen.getOwnHostContext_eq (by decide) hlt hk (by omega) hcls hmode
    (by rw [hcode]; rfl) (by rw [hcode]; rfl) (simpleO d hcode) (by rw [hcode]; rfl) (by rw [hcode]; rfl)
  have hpn : d.code.info.fdi.paramNames = #[JSStr.ofString "namespaceURI"] := by rw [hcode]; rfl
  have hv : d.code.info.fdi.varNames = #[] := by rw [hcode]; rfl
  have hl : FDI.lexDecls d = #[] := by simp [FDI.lexDecls, hcode, GOHCGen.getOwnHostContext_func, Func.info]
  have ha : d.code.isAsync = false := by rw [hcode]; rfl
  clear hcode
  simp only [GOHCGen.getOwnHostContext]
  js [hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner, List.findIdx?_toArray, List.findIdx?_cons, List.findIdx?_nil, Option.isNone_some, Option.isNone_none, Option.map_some, Option.map_none]
  all_goals (repeat' apply And.intro)
  all_goals rfl


set_option maxRecDepth 10000 in
theorem child_div_exact {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t : Value} {s : State}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : 10 ≤ s.fuel)
    (hcode : d.code = GCHCGen.getChildHostContextProd_func) (hcls : d.isClassCtor = false)
    (hmode : d.thisMode = .strict) :
    WP eng answer n h (callImpl eng (.obj fo) t #[.num (F64.fin false 0 (-1074)), .str (JSStr.ofString "DIV")]) s
      fun v w h' => v = .num (F64.fin false 0 (-1074)) ∧ h' = h ∧ w = ((bodyState s fo d t #[.num (F64.fin false 0 (-1074)), .str (JSStr.ofString "DIV")]).pushEnv (Env.decl ∅ (some s.envs.size))).restore s := by
  apply wp_callGen GCHCGen.getChildHostContextProd_eq (by decide) hlt hk (by omega) hcls hmode
    (by rw [hcode]; rfl) (by rw [hcode]; rfl) (simpleC d hcode) (by rw [hcode]; rfl) (by rw [hcode]; rfl)
  have hpn : d.code.info.fdi.paramNames = #[JSStr.ofString "parentNamespace", JSStr.ofString "type"] := by
    rw [hcode]; rfl
  have hv : d.code.info.fdi.varNames = #[] := by rw [hcode]; rfl
  have hl : FDI.lexDecls d = #[] := by simp [FDI.lexDecls, hcode, GCHCGen.getChildHostContextProd_func, Func.info]
  have ha : d.code.isAsync = false := by rw [hcode]; rfl
  clear hcode
  simp only [GCHCGen.getChildHostContextProd]
  js [hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner, List.findIdx?_toArray, List.findIdx?_cons, List.findIdx?_nil, Option.isNone_some, Option.isNone_none, Option.map_some, Option.map_none]
  all_goals (repeat' apply And.intro)
  all_goals rfl

end

end ReactHostContext
