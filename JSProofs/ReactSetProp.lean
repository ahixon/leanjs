import JSProofs.Setter
import JSProofs.ReactSetText
import JSProofs.SPSwitch

/-!
# setProp for the button's two props (zippy docs/react-proofs.md)

`setProp(dom, tag, key, value, props, prev)` for the two keys a counter's button changes: `onClick` (a non-null
handler: `dom.onclick = noop$1`, through the element's setter) and `children` (a string: `setTextContent`).
-/

open ES ES.M HostRuns Logic
open Std (HashMap)

namespace ReactSetProp

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ} {HI : σ → Prop}

theorem simple (d : FuncData) (hc : d.code = SetPropGen.setProp_func) : FDI.Simple d := by
  constructor <;> rw [hc] <;> try rfl
  simp [SetPropGen.setProp_func, Func.params, Func.info]

set_option maxRecDepth 40000 in
set_option maxHeartbeats 8000000 in
/-- **`setProp(dom, tag, "onClick", f, props, prev)`**, `f` a function: `dom.onclick = noop$1`. -/
theorem onClick_spec {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t : Value} {s : State}
    {bG : HashMap JSStr Binding} {oG : Option EnvId} {bdN : Binding} {fN : ObjId}
    {dom fv : ObjId} {tag : JSStr} {props prev : Value} {R : State → σ → Prop}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : 20 ≤ s.fuel)
    (hcode : d.code = SetPropGen.setProp_func) (hcls : d.isClassCtor = false) (hmode : d.thisMode = .strict)
    (hG : d.env < s.envs.size) (hGe : Scope.declLike? (s.envEntry d.env) = some (bG, oG))
    (hGN : bG[JSStr.ofString "noop$1"]? = some bdN) (hGNv : bdN.value = some (.obj fN))
    (hOC : ∀ w h1, Frame {} s w → HI h1 → 2 ≤ w.fuel → SetsAcc eng answer n h1 w (.obj dom) "onclick" (.obj fN)
      fun w' h' => R w' h' ∧ HI h' ∧ Frame {} w w' ∧ w.fuel ≤ w'.fuel + 1) (hHI : HI h) :
    WP eng answer (n + 1) h
      (callImpl eng (.obj fo) t #[.obj dom, .str tag, .str (JSStr.ofString "onClick"), .obj fv, props, prev]) s
      fun v w h' => v = .undefined ∧ (∃ w0, R w0 h') ∧ HI h' ∧ Frame {} s w ∧ s.fuel ≤ w.fuel + 40 := by
  apply wp_callGen SetPropGen.setProp_eq (by decide) hlt hk (by omega) hcls hmode
    (by rw [hcode]; rfl) (by rw [hcode]; rfl) (simple d hcode) (by rw [hcode]; rfl) (by rw [hcode]; rfl)
  have hpn : d.code.info.fdi.paramNames = #[JSStr.ofString "domElement", JSStr.ofString "tag",
    JSStr.ofString "key", JSStr.ofString "value", JSStr.ofString "props", JSStr.ofString "prevValue"] := by
    rw [hcode]; rfl
  have hv : d.code.info.fdi.varNames = #[] := by rw [hcode]; rfl
  have hl : FDI.lexDecls d = #[] := by simp [FDI.lexDecls, hcode, SetPropGen.setProp_func, Func.info]
  have ha : d.code.isAsync = false := by rw [hcode]; rfl
  have e1 : d.env ≠ s.envs.size := Nat.ne_of_lt hG
  have e2 : d.env ≠ s.envs.size + 1 := Nat.ne_of_lt (Nat.lt_succ_of_lt hG)
  have e3 : d.env < s.envs.size + 1 + 1 := Nat.lt_succ_of_lt (Nat.lt_succ_of_lt hG)
  have e4 : d.env < s.envs.size + 1 := Nat.lt_succ_of_lt hG
  clear hcode
  simp only [SetPropGen.setProp]
  iterate 2 (first | js_go | js_norm [hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner] | js_split)
  refine wp_switchC SPSwitch.lex ?_
  js_until ["onclick"] [e1, e2, e3, e4, hGe, hGN, hGNv, hG, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  refine wp_neNullObj' (by simp; omega) ?_
  iterate 1 (first | js_go | js_norm [e1, e2, e3, e4, hGe, hGN, hGNv, hG, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner] | js_split)
  refine wp_assignMemberSet ?_
  js_until [] [e1, e2, e3, e4, hGe, hGN, hGNv, hG, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  refine setsAcc_mono (hOC _ _ ?frS hHI ?fuS) ?kS
  case frS => frame_go' [*]
  case fuS => (try simp only [js_simp, State.pushEnv_fuel]); omega
  case kS =>
  intro w4 h4 ⟨hR, hHI4, hF4, hfu4⟩
  js_until [] [e1, e2, e3, e4, hGe, hGN, hGNv, hG, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  refine wp_retNone ?_
  js [e1, e2, e3, e4, hGe, hGN, hGNv, hG, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  exact ⟨⟨w4, hR⟩, frame_restore (frame_empty_trans (by frame_go' [*]) hF4) s,
    by simp [bodyState, State.pushEnv, entryState] at hfu4 ⊢; omega⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 8000000 in
/-- **`setProp(dom, "button", "children", text, props, prev)`**, `text` a non-empty string, `dom`'s only child the
text node `T`: `setTextContent(dom, text)`, i.e. `T.nodeValue = text`. -/
theorem children_spec {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t : Value} {s : State}
    {bG : HashMap JSStr Binding} {oG : Option EnvId} {bdS bdV : Binding} {fS : ObjId} {dS : FuncData}
    {dom T : ObjId} {text : JSStr} {props prev : Value} {R : State → σ → Prop}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : 40 ≤ s.fuel)
    (hcode : d.code = SetPropGen.setProp_func) (hcls : d.isClassCtor = false) (hmode : d.thisMode = .strict)
    (hG : d.env < s.envs.size) (hGe : Scope.declLike? (s.envEntry d.env) = some (bG, oG))
    (hGS : bG[JSStr.ofString "setTextContent"]? = some bdS) (hGSv : bdS.value = some (.obj fS))
    (hGV : bG[JSStr.ofString "viewTransitionMutationContext"]? = some bdV) (hGVm : bdV.mutable = true)
    (hGVi : bdV.value.isSome = true)
    (hSo : fS < s.heap.size) (hSk : (s.objEntry fS).kind = .func dS) (hScode : dS.code = STCGen.setTextContent_func)
    (hScls : dS.isClassCtor = false) (hSmode : dS.thisMode = .strict)
    (htext : text.isEmpty = false)
    (hFC : ReactHostContainer.DomRead eng answer HI n s {} dom "firstChild" (.obj T))
    (hLC : ReactHostContainer.DomRead eng answer HI n s {} dom "lastChild" (.obj T))
    (hNT : ReactHostContainer.DomRead eng answer HI n s {} T "nodeType" (.num (F64.fin false 6755399441055744 (-51))))
    (hNV : ∀ w h1, Frame {} s w → HI h1 → 2 ≤ w.fuel → SetsAcc eng answer n h1 w (.obj T) "nodeValue" (.str text)
      fun w' h' => R w' h' ∧ HI h' ∧ Frame {} w w' ∧ w.fuel ≤ w'.fuel + 1) (hHI : HI h) :
    WP eng answer (n + 2) h
      (callImpl eng (.obj fo) t #[.obj dom, .str (JSStr.ofString "button"), .str (JSStr.ofString "children"),
        .str text, props, prev]) s
      fun v w h' => v = .undefined ∧ (∃ w0, R w0 h') ∧ HI h' ∧ s.fuel ≤ w.fuel + 40 ∧
        Frame ⟨[(d.env, JSStr.ofString "viewTransitionMutationContext")], [], false⟩ s w ∧
        ∃ bm, Scope.declLike? (w.envEntry d.env) = some (bm, oG) ∧
          (∃ bd, bm[JSStr.ofString "viewTransitionMutationContext"]? = some bd ∧ bd.value = some (.bool true) ∧ bd.mutable = true) ∧
          ∀ x, x ≠ JSStr.ofString "viewTransitionMutationContext" → bm[x]? = bG[x]? := by
  apply wp_callGen SetPropGen.setProp_eq (by decide) hlt hk (by omega) hcls hmode
    (by rw [hcode]; rfl) (by rw [hcode]; rfl) (simple d hcode) (by rw [hcode]; rfl) (by rw [hcode]; rfl)
  have hpn : d.code.info.fdi.paramNames = #[JSStr.ofString "domElement", JSStr.ofString "tag",
    JSStr.ofString "key", JSStr.ofString "value", JSStr.ofString "props", JSStr.ofString "prevValue"] := by
    rw [hcode]; rfl
  have hv : d.code.info.fdi.varNames = #[] := by rw [hcode]; rfl
  have hl : FDI.lexDecls d = #[] := by simp [FDI.lexDecls, hcode, SetPropGen.setProp_func, Func.info]
  have ha : d.code.isAsync = false := by rw [hcode]; rfl
  have e1 : d.env ≠ s.envs.size := Nat.ne_of_lt hG
  have e2 : d.env ≠ s.envs.size + 1 := Nat.ne_of_lt (Nat.lt_succ_of_lt hG)
  have e3 : d.env < s.envs.size + 1 + 1 := Nat.lt_succ_of_lt (Nat.lt_succ_of_lt hG)
  have e4 : d.env < s.envs.size + 1 := Nat.lt_succ_of_lt hG
  clear hcode
  simp only [SetPropGen.setProp]
  iterate 2 (first | js_go | js_norm [hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner] | js_split)
  refine wp_switchC SPSwitch.lex ?_
  js_until [] [htext, e1, e2, e3, e4, hGe, hGS, hGSv, hG, hSo, hSk, hScls, hSmode, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  refine wp_typeof_lookup 3 (v := .str text) (by js_norm [htext, e1, e2, e3, e4, hGe, hGS, hGSv, hG, hSo, hSk, hScls, hSmode, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]) (by simp; omega) ?_
  refine wp_typeOf_prim (by simp) rfl ?_
  js_until [] [htext, e1, e2, e3, e4, hGe, hGS, hGSv, hG, hSo, hSk, hScls, hSmode, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  refine ⟨by js_norm [CallableC, htext, e1, e2, e3, e4, hGe, hGS, hGSv, hG, hSo, hSk, hScls, hSmode, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner], ?_⟩
  have hw0 : Frame {} s ((bodyState s fo d t #[.obj dom, .str (JSStr.ofString "button"),
      .str (JSStr.ofString "children"), .str text, props, prev]).pushEnv (Env.decl ∅ (some s.envs.size))) := by
    frame_go' [*]
  refine wp_mono (ReactSetText.stc_spec (R := fun w' h' => R w' h' ∧ Frame {} ((bodyState s fo d t #[.obj dom, .str (JSStr.ofString "button"), .str (JSStr.ofString "children"), .str text, props, prev]).pushEnv (Env.decl ∅ (some s.envs.size))) w') (by js_norm [htext, e1, e2, e3, e4, hGe, hGS, hGSv, hG, hSo, hSk, hScls, hSmode, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]) (by js_norm [htext, e1, e2, e3, e4, hGe, hGS, hGSv, hG, hSo, hSk, hScls, hSmode, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]) (by simp; omega) hScode
    hScls hSmode htext (fun w' h1 hw hi => hFC w' h1 (frame_empty_trans hw0 hw) hi)
    (fun w' h1 hw hi => hLC w' h1 (frame_empty_trans hw0 hw) hi) (fun w' h1 hw hi => hNT w' h1 (frame_empty_trans hw0 hw) hi)
    (fun w' h1 hw hi hfu => setsAcc_mono (hNV w' h1 (frame_empty_trans hw0 hw) hi hfu)
      fun w2 h2 ⟨hR, hHI2, hF, hfu⟩ => ⟨⟨hR, frame_empty_trans hw hF⟩, hHI2, hfu⟩) hHI) ?_
  rintro v5 w5 h5 ⟨rfl, ⟨w0, ⟨hR, hF0⟩, rfl⟩, hfu0, hHI5⟩
  simp only [State.restore] at hfu0
  have hlt0 : s.envs.size < ((bodyState s fo d t #[.obj dom, .str (JSStr.ofString "button"), .str (JSStr.ofString "children"), .str text, props, prev]).pushEnv (Env.decl ∅ (some s.envs.size))).envs.size := by simp; omega
  have hd0 : Scope.declLike? (w0.envEntry d.env) = some (bG, oG) := by
    rw [envEntry_frame0 hF0 (by simp <;> omega)]; js_norm [hGe, e1, e2, e3, e4, hG]
  have hG0 : d.env < w0.envs.size := Nat.lt_of_lt_of_le (by simp <;> omega) hF0.envs_le
  have hS0 : s.envs.size < w0.envs.size := Nat.lt_of_lt_of_le (by simp <;> omega) hF0.envs_le
  have hE0 : w0.envEntry s.envs.size = ((bodyState s fo d t #[.obj dom, .str (JSStr.ofString "button"), .str (JSStr.ofString "children"), .str text, props, prev]).pushEnv (Env.decl ∅ (some s.envs.size))).envEntry s.envs.size := envEntry_frame0 hF0 hlt0
  js_until [] [hfu0, hE0, hS0, hd0, hG0, hGV, hGVm, hGVi, htext, e1, e2, e3, e4, hGe, hGS, hGSv, hG, hSo, hSk, hScls, hSmode, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  have hfw : depth ≤ w0.fuel := by
    show 8 ≤ w0.fuel
    simp [bodyState, State.pushEnv, entryState] at hfu0
    omega
  refine wp_assignIdentC (by simpa [State.restore] using hfw) ?_
  js [hfu0, hE0, hS0, hd0, hG0, hGV, hGVm, hGVi, htext, e1, e2, e3, e4, hGe, hGS, hGSv, hG, hSo, hSk, hScls, hSmode, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  have hFs : Frame {} s w0 := frame_empty_trans hw0 hF0
  have hFv : Frame ⟨[(d.env, JSStr.ofString "viewTransitionMutationContext")], [], false⟩ s w0 :=
    frame_mono hFs (fun p hp => by simp at hp) (fun p hp => by simp at hp) (fun _ => rfl)
  refine ⟨⟨w0, hR⟩, by simp [bodyState, State.pushEnv, entryState] at hfu0 ⊢; omega, ?_, _, rfl, ⟨{ value := some (.bool true), mutable := bdV.mutable, strict := bdV.strict, deletable := bdV.deletable }, Std.HashMap.getElem?_modify_self.trans (by rw [hGV]; rfl), rfl, hGVm⟩,
    fun x hx => by simp [Std.HashMap.getElem?_modify, Ne.symm hx]⟩
  refine frame_restore (frame_setEnv_with_in (frame_restore hFv _) hG rfl (by show (Scope.declLike? (w0.envEntry d.env)).isSome = true; rw [hd0]; rfl) (by simp) _) s


end

end ReactSetProp
