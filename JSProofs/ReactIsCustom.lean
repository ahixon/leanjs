import JSProofs.StrMember
import JSProofs.ICEGen
import JSProofs.ReactHostContainer

/-!
# isCustomElement for a tag without a hyphen (zippy docs/react-proofs.md)

`isCustomElement(tag)`: `tag.indexOf("-")` is `-1`, so `false`. The realm's `%String.prototype%.indexOf` is the
builtin (`StrGets`).
-/

open ES ES.M HostRuns Logic
open Std (HashMap)

namespace ReactIsCustom

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ}

theorem simple (d : FuncData) (hc : d.code = ICEGen.isCustomElement_func) : FDI.Simple d := by
  constructor <;> rw [hc] <;> try rfl
  simp [ICEGen.isCustomElement_func, Func.params, Func.info]

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
/-- **`isCustomElement(tag)`**, no `-` in `tag`: `false`. -/
theorem ice_spec {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t : Value} {s : State} {tag : JSStr}
    {fI : ObjId} {bdI : BuiltinData}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : 20 ≤ s.fuel)
    (hcode : d.code = ICEGen.isCustomElement_func) (hcls : d.isClassCtor = false) (hmode : d.thisMode = .strict)
    (hI : ∀ w, Frame {} s w → StrGets w tag (JSStr.ofString "indexOf") fun v => v = .obj fI)
    (hIlt : fI < s.heap.size) (hIk : (s.objEntry fI).kind = .builtin bdI)
    (hIfn : eng.builtins[bdI.id]? = some ES.Builtins.Text.stringProtoIndexOf)
    (hno : tag.indexOf (JSStr.ofString "-") 0 = none) :
    WP eng answer (n + 2) h (callImpl eng (.obj fo) t #[.str tag]) s fun v w h' =>
      v = .bool false ∧ Frame {} s w ∧ s.fuel ≤ w.fuel + 20 ∧ h' = h := by
  apply wp_callGen ICEGen.isCustomElement_eq (by decide) hlt hk (by omega) hcls hmode
    (by rw [hcode]; rfl) (by rw [hcode]; rfl) (simple d hcode) (by rw [hcode]; rfl) (by rw [hcode]; rfl)
  have hpn : d.code.info.fdi.paramNames = #[JSStr.ofString "tagName"] := by rw [hcode]; rfl
  have hv : d.code.info.fdi.varNames = #[] := by rw [hcode]; rfl
  have hl : FDI.lexDecls d = #[] := by simp [FDI.lexDecls, hcode, ICEGen.isCustomElement_func, Func.info]
  have ha : d.code.isAsync = false := by rw [hcode]; rfl
  clear hcode
  simp only [ICEGen.isCustomElement]
  iterate 7 (first | js_go | js_norm [hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner] | js_split)
  refine wp_callMemberStr ?_
  js_until [] [hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  have hw0 : Frame {} s (bodyState s fo d t #[.str tag]) := by frame_go' [*]
  obtain ⟨SP, v, we, ee, ce, hSP, hSPlt, hSPk, hv0, hkl, hki, rfl⟩ := hI _ hw0
  refine ⟨tag, rfl, SP, _, we, ee, ce, hSP, hSPlt, hSPk, hv0, hkl, hki, fun W => ?_⟩
  have hIe : ((bodyState s fo d t #[.str tag]).withHeap (·.push W)).objEntry fI = s.objEntry fI := by
    rw [objEntry_push_old _ _ _ (by simp; omega)]; simp
  js_until [] [hIe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  have hIlt' : fI < ((bodyState s fo d t #[.str tag]).withHeap (·.push W)).heap.size := by
    exact Nat.lt_of_lt_of_le hIlt (by rw [size_push]; simp [bodyState, entryState])
  refine ⟨by js_norm [CallableC, hIe, hIk, hIlt', hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner], ?_⟩
  refine wp_mono (indexOf_none_spec hIlt' (by rw [hIe]; exact hIk) hIfn (by simp; omega) hno) ?_
  rintro v1 w1 h1 ⟨rfl, hF1, hfu1, rfl⟩
  have hm1 : isStrictlyEqual (.num (F64.fin false 4503599627370496 (-52)).neg) (intV (-1)) = true := by decide
  js [hm1, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  refine ⟨frame_restore (frame_empty_trans (frame_empty_trans hw0 (frame_push _ _)) hF1) s, ?_⟩
  simp [bodyState, entryState, State.withHeap] at hfu1 ⊢
  omega

end

end ReactIsCustom
