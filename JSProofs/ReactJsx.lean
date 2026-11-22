import JSProofs.Rules5
import JSProofs.JSXGen

/-!
# React's `jsxProd` (zippy docs/react-proofs.md)

`jsx(type, config)` (two arguments: no key) for a `config` object with neither `key` nor `ref` on its chain (an
object literal: `Object.prototype` has neither): the element object `{ $$typeof, type, key: null, ref: null,
props: config }`.
-/

open ES ES.M HostRuns Logic
open Std (HashMap)

namespace ReactJsx

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ}

theorem simpleJ (d : FuncData) (hc : d.code = JSXGen.jsxProd_func) : FDI.Simple d := by
  constructor <;> rw [hc] <;> try rfl
  simp [JSXGen.jsxProd_func, Func.params, Func.info]

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 20000 in
/-- **`jsx(type, config)`** for a key-less, ref-less `config`: a new element object. -/
theorem spec {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t : Value} {s : State}
    {bG : HashMap JSStr Binding} {oG : Option EnvId} {bdT : Binding} {C OP : ObjId} {ty vT : Value}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : 40 ≤ s.fuel)
    (hcode : d.code = JSXGen.jsxProd_func) (hcls : d.isClassCtor = false) (hmode : d.thisMode = .strict)
    (hG : d.env < s.envs.size) (hGe : Scope.declLike? (s.envEntry d.env) = some (bG, oG))
    (hGT : bG[JSStr.ofString "REACT_ELEMENT_TYPE"]? = some bdT) (hGTv : bdT.value = some vT)
    (hC : C < s.heap.size) (hCk : (s.objEntry C).kind.isPlain = true) (hCp : (s.objEntry C).proto = .obj OP)
    (hCkey : (s.objEntry C).props.get? (.str "key") = none) (hCref : (s.objEntry C).props.get? (.str "ref") = none)
    (hOP : OP < s.heap.size) (hOPk : (s.objEntry OP).kind.isPlain = true) (hOPp : (s.objEntry OP).proto = .null)
    (hOPkey : (s.objEntry OP).props.get? (.str "key") = none)
    (hOPref : (s.objEntry OP).props.get? (.str "ref") = none) :
    WP eng answer n h (callImpl eng (.obj fo) t #[ty, .obj C]) s fun v w h' =>
      v = .obj s.heap.size ∧ Frame {} s w ∧ s.fuel ≤ w.fuel + 40 ∧ h' = h ∧ w.heap.size = s.heap.size + 1 ∧
      (w.objEntry s.heap.size).kind = .ordinary ∧
      (w.objEntry s.heap.size).proto = .obj s.realms[d.realm]!.objectProto ∧
      (w.objEntry s.heap.size).props.get? (.str "$$typeof") = some (.data vT true true true) ∧
      (w.objEntry s.heap.size).props.get? (.str "type") = some (.data ty true true true) ∧
      (w.objEntry s.heap.size).props.get? (.str "key") = some (.data .null true true true) ∧
      (w.objEntry s.heap.size).props.get? (.str "ref") = some (.data .null true true true) ∧
      (w.objEntry s.heap.size).props.get? (.str "props") = some (.data (.obj C) true true true) ∧
      w.realm = s.realm := by
  apply wp_callGen JSXGen.jsxProd_eq (by decide) hlt hk (by omega) hcls hmode
    (by rw [hcode]; rfl) (by rw [hcode]; rfl) (simpleJ d hcode) (by rw [hcode]; rfl) (by rw [hcode]; rfl)
  have hpn : d.code.info.fdi.paramNames = #[JSStr.ofString "type", JSStr.ofString "config", JSStr.ofString "maybeKey"] := by
    rw [hcode]; rfl
  have hv : d.code.info.fdi.varNames = #[JSStr.ofString "key", JSStr.ofString "propName"] := by rw [hcode]; rfl
  have hl : FDI.lexDecls d = #[] := by simp [FDI.lexDecls, hcode, JSXGen.jsxProd_func, Func.info]
  have ha : d.code.isAsync = false := by rw [hcode]; rfl
  have hne : s.envs.size ≠ d.env := Nat.ne_of_gt hG
  have hG1 : d.env < s.envs.size + 1 := Nat.lt_succ_of_lt hG
  clear hcode
  simp only [JSXGen.jsxProd]
  js [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGT, hGTv, hC, hCk, hCp, hCkey, hCref, hOP, hOPk, hOPp, hOPkey,
    hOPref, FDI.fdiCtx, Sem.inner]
  refine wp_void ?_
  js [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGT, hGTv, hC, hCk, hCp, hCkey, hCref, hOP, hOPk, hOPp, hOPkey,
    hOPref, FDI.fdiCtx, Sem.inner]
  refine wp_void ?_
  iterate 1 (first | js_go | js_norm [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGT, hGTv, hC, hCk, hCp, hCkey, hCref, hOP, hOPk, hOPp, hOPkey, hOPref, FDI.fdiCtx, Sem.inner] | js_split)
  -- (`config.key`: on neither `config` nor `Object.prototype`)
  refine wp_getMemberAbsent2 ?_
  js [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGT, hGTv, hC, hCk, hCp, hCkey, hCref, hOP, hOPk, hOPp, hOPkey, hOPref, FDI.fdiCtx, Sem.inner]
  refine ⟨C, OP, rfl, ?_⟩
  refine ⟨by js_norm [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGT, hGTv, hC, hCk, hCp, hCkey, hCref, hOP, hOPk, hOPp, hOPkey, hOPref, FDI.fdiCtx, Sem.inner], by js_norm [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGT, hGTv, hC, hCk, hCp, hCkey, hCref, hOP, hOPk, hOPp, hOPkey, hOPref, FDI.fdiCtx, Sem.inner], by js_norm [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGT, hGTv, hC, hCk, hCp, hCkey, hCref, hOP, hOPk, hOPp, hOPkey, hOPref, FDI.fdiCtx, Sem.inner], by js_norm [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGT, hGTv, hC, hCk, hCp, hCkey, hCref, hOP, hOPk, hOPp, hOPkey, hOPref, FDI.fdiCtx, Sem.inner],
    by js_norm [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGT, hGTv, hC, hCk, hCp, hCkey, hCref, hOP, hOPk, hOPp, hOPkey, hOPref, FDI.fdiCtx, Sem.inner], by js_norm [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGT, hGTv, hC, hCk, hCp, hCkey, hCref, hOP, hOPk, hOPp, hOPkey, hOPref, FDI.fdiCtx, Sem.inner], by js_norm [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGT, hGTv, hC, hCk, hCp, hCkey, hCref, hOP, hOPk, hOPp, hOPkey, hOPref, FDI.fdiCtx, Sem.inner], by js_norm [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGT, hGTv, hC, hCk, hCp, hCkey, hCref, hOP, hOPk, hOPp, hOPkey, hOPref, FDI.fdiCtx, Sem.inner], ?_⟩
  js [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGT, hGTv, hC, hCk, hCp, hCkey, hCref, hOP, hOPk, hOPp, hOPkey, hOPref, FDI.fdiCtx, Sem.inner]
  -- (`"key" in config`: false)
  refine wp_inPlain (m := 2) ⟨by js_norm [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGT, hGTv, hC, hCk, hCp, hCkey, hCref, hOP, hOPk, hOPp, hOPkey, hOPref, FDI.fdiCtx, Sem.inner], by js_norm [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGT, hGTv, hC, hCk, hCp, hCkey, hCref, hOP, hOPk, hOPp, hOPkey, hOPref, FDI.fdiCtx, Sem.inner], fun _ => by
    js_norm [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGT, hGTv, hC, hCk, hCp, hCkey, hCref, hOP, hOPk, hOPp, hOPkey, hOPref, FDI.fdiCtx, Sem.inner]; exact ⟨by js_norm [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGT, hGTv, hC, hCk, hCp, hCkey, hCref, hOP, hOPk, hOPp, hOPkey, hOPref, FDI.fdiCtx, Sem.inner], by js_norm [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGT, hGTv, hC, hCk, hCp, hCkey, hCref, hOP, hOPk, hOPp, hOPkey, hOPref, FDI.fdiCtx, Sem.inner], fun _ => by js_norm [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGT, hGTv, hC, hCk, hCp, hCkey, hCref, hOP, hOPk, hOPp, hOPkey, hOPref, FDI.fdiCtx, Sem.inner]⟩⟩ (by decide) ?_
  iterate 11 (first | js_go | js_norm [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGT, hGTv, hC, hCk, hCp, hCkey, hCref, hOP, hOPk, hOPp, hOPkey, hOPref, FDI.fdiCtx, Sem.inner, ordLookup] | js_split)
  -- (`maybeKey.ref`, `maybeKey` being `config`: undefined)
  refine wp_getMemberAbsent2 ?_
  js [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGT, hGTv, hC, hCk, hCp, hCkey, hCref, hOP, hOPk, hOPp, hOPkey, hOPref, FDI.fdiCtx, Sem.inner, ordLookup]
  refine ⟨C, OP, rfl, ?_⟩
  refine ⟨by js_norm [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGT, hGTv, hC, hCk, hCp, hCkey, hCref, hOP, hOPk, hOPp, hOPkey, hOPref, FDI.fdiCtx, Sem.inner, ordLookup], by js_norm [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGT, hGTv, hC, hCk, hCp, hCkey, hCref, hOP, hOPk, hOPp, hOPkey, hOPref, FDI.fdiCtx, Sem.inner, ordLookup], by js_norm [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGT, hGTv, hC, hCk, hCp, hCkey, hCref, hOP, hOPk, hOPp, hOPkey, hOPref, FDI.fdiCtx, Sem.inner, ordLookup], by js_norm [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGT, hGTv, hC, hCk, hCp, hCkey, hCref, hOP, hOPk, hOPp, hOPkey, hOPref, FDI.fdiCtx, Sem.inner, ordLookup],
    by js_norm [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGT, hGTv, hC, hCk, hCp, hCkey, hCref, hOP, hOPk, hOPp, hOPkey, hOPref, FDI.fdiCtx, Sem.inner, ordLookup], by js_norm [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGT, hGTv, hC, hCk, hCp, hCkey, hCref, hOP, hOPk, hOPp, hOPkey, hOPref, FDI.fdiCtx, Sem.inner, ordLookup], by js_norm [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGT, hGTv, hC, hCk, hCp, hCkey, hCref, hOP, hOPk, hOPp, hOPkey, hOPref, FDI.fdiCtx, Sem.inner, ordLookup], by js_norm [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGT, hGTv, hC, hCk, hCp, hCkey, hCref, hOP, hOPk, hOPp, hOPkey, hOPref, FDI.fdiCtx, Sem.inner, ordLookup], ?_⟩
  js [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGT, hGTv, hC, hCk, hCp, hCkey, hCref, hOP, hOPk, hOPp, hOPkey, hOPref, FDI.fdiCtx, Sem.inner, ordLookup]
  refine wp_void ?_
  js [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGT, hGTv, hC, hCk, hCp, hCkey, hCref, hOP, hOPk, hOPp, hOPkey, hOPref, FDI.fdiCtx, Sem.inner, ordLookup]
  all_goals (repeat' apply And.intro)
  all_goals first
    | omega | (simp only [js_simp]; omega) | (frame_go' [*, hne, Ne.symm hne, hG1]; done)
    | (js_norm [*, Nat.ne_of_lt hC, Nat.ne_of_gt hC, Nat.ne_of_lt hOP, Nat.ne_of_gt hOP]; done)
    | (simp [ES.Obj.withProps_proto, State.curRealm, State.setEnv, bodyState, entryState]; done)
    | rfl

end

end ReactJsx
