import JSProofs.HSCGen
import JSProofs.StrMember
import JSProofs.ReactHostContainer

/-!
# hasSelectionCapabilities for the focused element (zippy docs/react-proofs.md)

`hasSelectionCapabilities(elem)`: `elem.nodeName.toLowerCase()` (a DOM read, then `String.prototype.toLowerCase`)
neither "input" nor "textarea", and `elem.contentEditable` (a DOM read) not "true": `false`.
-/

open ES ES.M HostRuns Logic
open Std (HashMap)

namespace ReactSelection

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ}

/-- **`str.toLowerCase()`**: the lowercase string; nothing changed, one step of fuel. -/
theorem toLower_spec {n : Nat} {h : σ} {fo : ObjId} {bd : BuiltinData} {str : JSStr} {s : State}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .builtin bd)
    (hfn : eng.builtins[bd.id]? = some (ES.Builtins.Text.stringCase true "toLowerCase")) (hf : s.fuel ≠ 0) :
    WP eng answer n h (callImpl eng (.obj fo) (.str str) #[]) s fun v w h' =>
      v = .str (Unicode.toLower str) ∧ Frame {} s w ∧ s.fuel ≤ w.fuel + 1 ∧ h' = h := by
  rw [wp_iff_wpr, callImpl_builtin eng fo bd _ (.str str) _ s hlt hk hfn hf, ← wp_iff_wpr]
  apply wp_inCallee
  refine wp_of_eq (a := .str (Unicode.toLower str)) (w := { s with realm := bd.realm, fuel := s.fuel - 1 }) ?eq ?post
  case eq =>
    simp [ES.Builtins.Text.stringCase, ES.Builtins.Text.thisStr, toStr, Value.isNullish, M.bind_apply, Pure.pure]
    rw [maxDepth_eq]
    simp [toJSString, M.bind_apply, Pure.pure, M.pure]
  case post => exact ⟨rfl, frame_same rfl rfl rfl rfl, by first | omega | (simp; omega) | simp, rfl⟩

@[simp] theorem envEntry_withHeap (s : State) (f : Array Obj → Array Obj) (e : EnvId) :
    (s.withHeap f).envEntry e = s.envEntry e := rfl
@[simp] theorem envs_withHeap (s : State) (f : Array Obj → Array Obj) : (s.withHeap f).envs = s.envs := rfl
@[simp] theorem fuel_withHeap (s : State) (f : Array Obj → Array Obj) : (s.withHeap f).fuel = s.fuel := rfl

theorem simple (d : FuncData) (hc : d.code = HSCGen.hasSelectionCapabilities_func) : FDI.Simple d := by
  constructor <;> rw [hc] <;> try rfl
  simp [HSCGen.hasSelectionCapabilities_func, Func.params, Func.info]

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
/-- **`hasSelectionCapabilities(E)`**, `E.nodeName` lowercased neither "input" nor "textarea", `E.contentEditable`
not "true": `false`. -/
theorem hsc_spec {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t : Value} {s : State} {E fTL : ObjId}
    {bdTL : BuiltinData} {nm ce : JSStr}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : 80 ≤ s.fuel)
    (hcode : d.code = HSCGen.hasSelectionCapabilities_func) (hcls : d.isClassCtor = false)
    (hmode : d.thisMode = .strict)
    (hNN : ReactHostContainer.DomRead eng answer n s {} E "nodeName" (.str nm))
    (hnm : nm.isEmpty = false)
    (hTL : ∀ w, Frame {} s w → StrGets w nm (JSStr.ofString "toLowerCase") fun v => v = .obj fTL)
    (hTLo : fTL < s.heap.size) (hTLk : (s.objEntry fTL).kind = .builtin bdTL)
    (hTLfn : eng.builtins[bdTL.id]? = some (ES.Builtins.Text.stringCase true "toLowerCase"))
    (hlnm : (Unicode.toLower nm).isEmpty = false)
    (hin : isStrictlyEqual (.str (JSStr.ofString "input")) (.str (Unicode.toLower nm)) = false)
    (hta : isStrictlyEqual (.str (JSStr.ofString "textarea")) (.str (Unicode.toLower nm)) = false)
    (hCE : ReactHostContainer.DomRead eng answer n s {} E "contentEditable" (.str ce))
    (hce : isStrictlyEqual (.str (JSStr.ofString "true")) (.str ce) = false) :
    WP eng answer (n + 1) h (callImpl eng (.obj fo) t #[.obj E]) s fun v w h' =>
      v = .bool false ∧ Frame {} s w ∧ s.fuel ≤ w.fuel + 80 ∧ h' = h := by
  apply wp_callGen HSCGen.hasSelectionCapabilities_eq (by decide) hlt hk (by omega) hcls hmode
    (by rw [hcode]; rfl) (by rw [hcode]; rfl) (simple d hcode) (by rw [hcode]; rfl) (by rw [hcode]; rfl)
  have hpn : d.code.info.fdi.paramNames = #[JSStr.ofString "elem"] := by rw [hcode]; rfl
  have hv : d.code.info.fdi.varNames = #[JSStr.ofString "nodeName"] := by rw [hcode]; rfl
  have hl : FDI.lexDecls d = #[] := by simp [FDI.lexDecls, hcode, HSCGen.hasSelectionCapabilities_func, Func.info]
  have ha : d.code.isAsync = false := by rw [hcode]; rfl
  clear hcode
  have hw0 : Frame {} s (bodyState s fo d t #[.obj E]) := by frame_go' [*]
  simp only [HSCGen.hasSelectionCapabilities]
  iterate 10 (first | js_go | js_norm [hnm, hlnm, hin, hta, hce, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner] | js_split)
  refine wp_getMemberAcc ?_
  js_until [] [hnm, hlnm, hin, hta, hce, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  refine getsAcc_mono (hNN _ _ ?_) ?_
  · frame_go' [*]
  intro _ _ _ ⟨hv_, hw_, hh_⟩
  subst hv_ hw_ hh_
  iterate 1 (first | js_go | js_norm [hnm, hlnm, hin, hta, hce, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner] | js_split)
  refine wp_callMemberStr ?_
  refine wp_getMemberAcc ?_
  js_until [] [hnm, hlnm, hin, hta, hce, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  refine getsAcc_mono (hNN _ _ ?_) ?_
  · frame_go' [*]
  intro _ _ _ ⟨hv_, hw_, hh_⟩
  subst hv_ hw_ hh_
  obtain ⟨SP, v0, a0, b0, c0, h1, h2, h3, h4, h5, h6, rfl⟩ := hTL _ hw0
  refine ⟨nm, rfl, SP, _, a0, b0, c0, h1, h2, h3, h4, h5, h6, fun W => ?_⟩
  js_until [] [envEntry_withHeap, envs_withHeap, fuel_withHeap, hnm, hlnm, hin, hta, hce, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  have hTLe : ((bodyState s fo d t #[.obj E]).withHeap (·.push W)).objEntry fTL = s.objEntry fTL := by
    rw [objEntry_push_old' _ _ _ (by simpa [bodyState, entryState] using hTLo)]; simp
  have hTLlt : fTL < ((bodyState s fo d t #[.obj E]).withHeap (·.push W)).heap.size := by
    exact Nat.lt_of_lt_of_le hTLo (by rw [size_push]; simp [bodyState, entryState])
  refine ⟨by js_norm [CallableC, hTLe, hTLk, hTLlt], ?_⟩
  refine wp_mono (toLower_spec hTLlt (by rw [hTLe]; exact hTLk) hTLfn (by simp; omega)) ?_
  rintro v1 w1 h1' ⟨rfl, hF1, hfu1, rfl⟩
  have hFs1 : Frame {} s w1 := frame_empty_trans (frame_empty_trans hw0 (frame_push _ _)) hF1
  have hE1 := envEntry_frame0 hF1 (e := s.envs.size) (by simp [State.withHeap])
  have hS1 : s.envs.size < w1.envs.size := Nat.lt_of_lt_of_le (by simp [State.withHeap]) hF1.envs_le
  have hfw1 : 50 ≤ w1.fuel := by simp [bodyState, entryState, State.withHeap] at hfu1; omega
  have hfr1 : s.fuel ≤ w1.fuel + 10 := by simp [bodyState, entryState, State.withHeap] at hfu1; omega
  js_until ["contentEditable"] [envEntry_withHeap, envs_withHeap, fuel_withHeap, hE1, hS1, hfw1, hnm, hlnm, hin, hta, hce, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  refine wp_getMemberAcc ?_
  js_until [] [envEntry_withHeap, envs_withHeap, fuel_withHeap, hE1, hS1, hfw1, hnm, hlnm, hin, hta, hce, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  refine getsAcc_mono (hCE _ _ ?_) ?_
  · exact frame_setEnv_new hFs1 (Nat.le_refl _) _
  intro _ _ _ ⟨hv_, hw_, hh_⟩
  subst hv_ hw_ hh_
  js [envEntry_withHeap, envs_withHeap, fuel_withHeap, hE1, hS1, hfw1, hnm, hlnm, hin, hta, hce, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  exact ⟨frame_restore (frame_setEnv_new hFs1 (Nat.le_refl _) _) s, by omega⟩

end

end ReactSelection
