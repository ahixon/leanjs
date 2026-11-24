import JSProofs.Setter
import JSProofs.ReactHostContainer
import JSProofs.STCGen

/-!
# setTextContent for the button's text (zippy docs/react-proofs.md)

`setTextContent(node, text)` for a non-empty text and a node whose one child is a text node: the text node's
`nodeValue` set (through its setter: a host operation). What the DOM answers is this theorem's premises: the reads
(`firstChild`, `lastChild`, `nodeType`) as `DomRead`s, the write as a `SetsAcc` into a relation `R` of the state and
host state it leaves.
-/

open ES ES.M HostRuns Logic
open Std (HashMap)

namespace ReactSetText

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ}

theorem simple (d : FuncData) (hc : d.code = STCGen.setTextContent_func) : FDI.Simple d := by
  constructor <;> rw [hc] <;> try rfl
  simp [STCGen.setTextContent_func, Func.params, Func.info]

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
/-- **`setTextContent(node, text)`**, `text` non-empty, `node`'s only child the text node `T`: `T.nodeValue = text`. -/
theorem stc_spec {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t : Value} {s : State} {node T : ObjId} {text : JSStr}
    {R : State → σ → Prop}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : 20 ≤ s.fuel)
    (hcode : d.code = STCGen.setTextContent_func) (hcls : d.isClassCtor = false) (hmode : d.thisMode = .strict)
    (htext : text.isEmpty = false)
    (hFC : ReactHostContainer.DomRead eng answer n s {} node "firstChild" (.obj T))
    (hLC : ReactHostContainer.DomRead eng answer n s {} node "lastChild" (.obj T))
    (hNT : ReactHostContainer.DomRead eng answer n s {} T "nodeType" (.num (F64.fin false 6755399441055744 (-51))))
    (hNV : ∀ w h1, Frame {} s w → SetsAcc eng answer n h1 w (.obj T) "nodeValue" (.str text)
      fun w' h' => R w' h' ∧ w.fuel ≤ w'.fuel + 1) :
    WP eng answer (n + 1) h (callImpl eng (.obj fo) t #[.obj node, .str text]) s fun v w h' =>
      v = .undefined ∧ (∃ w0, R w0 h' ∧ w = w0.restore s) ∧ s.fuel ≤ w.fuel + 24 := by
  apply wp_callGen STCGen.setTextContent_eq (by decide) hlt hk (by omega) hcls hmode
    (by rw [hcode]; rfl) (by rw [hcode]; rfl) (simple d hcode) (by rw [hcode]; rfl) (by rw [hcode]; rfl)
  have hpn : d.code.info.fdi.paramNames = #[JSStr.ofString "node", JSStr.ofString "text"] := by rw [hcode]; rfl
  have hv : d.code.info.fdi.varNames = #[JSStr.ofString "firstChild"] := by rw [hcode]; rfl
  have hl : FDI.lexDecls d = #[] := by simp [FDI.lexDecls, hcode, STCGen.setTextContent_func, Func.info]
  have ha : d.code.isAsync = false := by rw [hcode]; rfl
  have hTT : isStrictlyEqual (.obj T) (.obj T) = true := by simp [isStrictlyEqual, sameValue]
  have h33 : isStrictlyEqual (.num (F64.fin false 6755399441055744 (-51))) (.num (F64.fin false 6755399441055744 (-51))) = true := by decide
  clear hcode
  simp only [STCGen.setTextContent]
  js_until ["firstChild", "lastChild", "nodeType", "nodeValue"] [htext, hTT, h33, beq_self_eq_true, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  refine wp_getMemberAcc ?_
  js_until [] [htext, hTT, h33, beq_self_eq_true, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  refine getsAcc_mono (hFC _ _ ?fr1) ?k1
  case fr1 => frame_go' [*]
  case k1 =>
  intro v1 w1 h1 ⟨hv1, hh1, f_w1, hw1, hf_w1⟩
  subst hv1 hw1 hh1
  try simp only [js_simp, State.pushEnv_fuel] at hf_w1
  js_until ["lastChild", "nodeType", "nodeValue"] [htext, hTT, h33, beq_self_eq_true, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  refine wp_getMemberAcc ?_
  js_until [] [htext, hTT, h33, beq_self_eq_true, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  refine getsAcc_mono (hLC _ _ ?fr2) ?k2
  case fr2 => frame_go' [*]
  case k2 =>
  intro v2 w2 h2 ⟨hv2, hh2, f_w2, hw2, hf_w2⟩
  subst hv2 hw2 hh2
  try simp only [js_simp, State.pushEnv_fuel] at hf_w2
  js_until ["nodeType", "nodeValue"] [htext, hTT, h33, beq_self_eq_true, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  refine wp_getMemberAcc ?_
  js_until [] [htext, hTT, h33, beq_self_eq_true, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  refine getsAcc_mono (hNT _ _ ?fr3) ?k3
  case fr3 => frame_go' [*]
  case k3 =>
  intro v3 w3 h3 ⟨hv3, hh3, f_w3, hw3, hf_w3⟩
  subst hv3 hw3 hh3
  try simp only [js_simp, State.pushEnv_fuel] at hf_w3
  iterate 7 (first | js_go | js_norm [htext, hTT, h33, beq_self_eq_true, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner] | js_split)
  refine wp_assignMemberSet ?_
  js_until [] [htext, hTT, h33, beq_self_eq_true, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  refine setsAcc_mono (hNV _ _ ?frS) ?kS
  case frS => frame_go' [*]
  case kS =>
  intro w4 h4 ⟨hR, hfu⟩
  refine wp_retNone ?_
  js [htext, hTT, h33, beq_self_eq_true, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  refine ⟨⟨w4, hR, rfl⟩, ?_⟩
  simp only [js_simp] at hfu ⊢
  omega

end

end ReactSetText
