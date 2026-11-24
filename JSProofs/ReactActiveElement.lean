import JSProofs.GAEGen
import JSProofs.GAEDGen
import JSProofs.Setter
import JSProofs.ReactHostContainer
import JSProofs.Rules6

/-!
# getActiveElement, getActiveElementDeep (zippy docs/react-proofs.md)

The focused element as `flushMutationEffects` asks for it: `doc.activeElement` (a DOM read). The DOM's answers are
premises (`DomRead`), as is the `instanceof` of the focused element against the window's `HTMLIFrameElement` (host
objects' prototype chains).
-/

open ES ES.M HostRuns Logic
open Std (HashMap)

namespace ReactActiveElement

/-- A DOM read `obj.k` answered by a `DomRead` premise `H` (its frame by `frame_go'` from the entry state). -/
macro "dom_read" H:term : tactic => `(tactic| (
  refine wp_getMemberAcc ?_
  js_until [] [FDI.fdiCtx, Sem.inner]
  refine getsAcc_mono ($H _ _ ?_) ?_
  · frame_go' [*]
  intro _ _ _ ⟨hv_, hh_, _, hw_, hf_⟩
  subst hv_ hw_ hh_
  try simp only [js_simp, State.pushEnv_fuel] at hf_))

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ} {HI : σ → Prop}

/-- **`l instanceof r`**: InstanceofOperator's Boolean. -/
theorem wp_instanceof {n : Nat} {h : σ} {lv rv : Value} {s : State} {Q : Value → State → σ → Prop}
    (hw : WP eng answer n h (instanceofOperator lv rv) s fun b w h1 => Q (.bool b) w h1) :
    WP eng answer n h (Sem.binaryOp .instanceof lv rv) s Q := by
  show WP eng answer n h (instanceofOperator lv rv >>= fun b => Pure.pure (Value.bool b)) s Q
  exact wp_bind (wp_mono hw fun _ _ _ q => wp_pure q)

/-- A host's object that is not callable: an internal object (Zippy's wrappers), or a proxy without [[Call]] (a legacy
platform object's wrapper: the document). -/
def HostObjKind (k : Kind) : Prop := (∃ t sl, k = .internal t sl) ∨ (∃ a b c, k = .proxy a b false c)

/-- `typeof v` as `TypeofC`, for a host's object (`HostObjKind`): not callable, `"object"`. -/
def TypeofCI (s : State) (v : Value) (P : JSStr → Prop) : Prop :=
  match v with
  | .obj o => o < s.heap.size ∧ HostObjKind (s.objEntry o).kind ∧ P "object"
  | _ => TypeofC s v P

theorem typeOf_ofI {s : State} {v : Value} {P : JSStr → Prop} (h : TypeofCI s v P) :
    ∃ t, typeOf v s = .ok t s ∧ P t := by
  cases v with
  | obj o =>
    obtain ⟨hlt, hk, hp⟩ := h
    refine ⟨"object", ?_, hp⟩
    rcases hk with ⟨_, _, hk⟩ | ⟨_, _, _, hk⟩ <;>
      simp [typeOf, isCallable, readObj_entry o _ s hlt, hk, M.bind_eq, M.bind_apply, Pure.pure, M.pure]
  | _ => exact typeOf_of h

/-- **`typeof x`** of a variable holding a host's object. -/
theorem wp_typeofIdentCI {n : Nat} {h : σ} {x : JSStr} {ctx : Ctx} {s : State} {Q : Value → State → σ → Prop}
    (hk : depth ≤ s.fuel)
    (hw : match Scope.resolve s depth ctx.lex x, Scope.lookup s depth ctx.lex x with
      | some _, some v => TypeofCI s v fun t => Q (.str t) s h
      | _, _ => False) :
    WP eng answer n h (Sem.typeofRef (Sem.identRef x) ctx) s Q := by
  cases hr : Scope.resolve s depth ctx.lex x with
  | none => rw [hr] at hw; exact hw.elim
  | some e =>
    cases hl : Scope.lookup s depth ctx.lex x with
    | none => rw [hr, hl] at hw; exact hw.elim
    | some v =>
      rw [hr, hl] at hw
      obtain ⟨bm, o, bd, he, hd, hb, hv⟩ := resolve_lookup s x v depth ctx.lex e hr hl
      have h1 : Sem.identRef x ctx s = .ok (.env (some e) x ctx.strict) s :=
        Scope.resolveBinding_of_resolve s depth ctx.lex x ctx.strict e hr hk
      have h2 := Scope.getRefValue_env s e x ctx.strict he bm o hd bd v hb hv
      obtain ⟨t, ht, hq⟩ := typeOf_ofI hw
      refine wp_of_eq ?_ hq
      simp only [Sem.typeofRef, M.bind_eq, M.bind_apply, h1, M.bindRes_ok]
      simp only [h2, M.bindRes_ok, M.bind_eq, M.bind_apply, ht]
      rfl

theorem simple (d : FuncData) (hc : d.code = GAEGen.getActiveElement_func) : FDI.Simple d := by
  constructor <;> rw [hc] <;> try rfl
  simp [GAEGen.getActiveElement_func, Func.params, Func.info]

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
/-- **`getActiveElement(doc)`**, `doc.activeElement` the element `E`: `E`. The document a host's object (`HostObjKind`: an
internal object, or a proxy without [[Call]], as Zippy's document is). -/
theorem gae_spec {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t : Value} {s : State} {Doc E : ObjId}
    {K : Kind}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : 60 ≤ s.fuel)
    (hcode : d.code = GAEGen.getActiveElement_func) (hcls : d.isClassCtor = false) (hmode : d.thisMode = .strict)
    (hDoc : Doc < s.heap.size)
    (hDocK : (s.objEntry Doc).kind = K) (hK : HostObjKind K)
    (hAE : ReactHostContainer.DomRead2 eng answer HI n s {} Doc "activeElement" (.obj E)) (hHI : HI h) :
    WP eng answer (n + 1) h (callImpl eng (.obj fo) t #[.obj Doc]) s fun v w h' =>
      v = .obj E ∧ Frame {} s w ∧ s.fuel ≤ w.fuel + 60 ∧ h' = h := by
  apply wp_callGen GAEGen.getActiveElement_eq (by decide) hlt hk (by omega) hcls hmode
    (by rw [hcode]; rfl) (by rw [hcode]; rfl) (simple d hcode) (by rw [hcode]; rfl) (by rw [hcode]; rfl)
  have hpn : d.code.info.fdi.paramNames = #[JSStr.ofString "doc"] := by rw [hcode]; rfl
  have hv : d.code.info.fdi.varNames = #[] := by rw [hcode]; rfl
  have hl : FDI.lexDecls d = #[] := by simp [FDI.lexDecls, hcode, GAEGen.getActiveElement_func, Func.info]
  have ha : d.code.isAsync = false := by rw [hcode]; rfl
  clear hcode
  have hw0 : Frame {} s (bodyState s fo d t #[.obj Doc]) := by frame_go' [*]
  simp only [GAEGen.getActiveElement]
  js_until ["activeElement"] [hDoc, hDocK, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  refine wp_typeofIdentCI (by show 8 ≤ _; simp; omega) ?_
  js_until ["activeElement"] [TypeofCI, hDoc, hDocK, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  js_until ["activeElement"] [hDoc, hDocK, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  refine wp_getMemberAcc ?_
  js_until [] [hDoc, hDocK, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  refine getsAcc_mono (hAE _ _ (by frame_go' [*]) hHI (by (try simp only [js_simp, State.pushEnv_fuel]); omega)) ?_
  intro v2 w2 h2 ⟨hv2, hh2, f_w2, hw2, hf_w2⟩
  subst hv2 hw2 hh2
  try simp only [js_simp, State.pushEnv_fuel] at hf_w2
  js [hDoc, hDocK, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  exact ⟨by frame_go' [*], by omega⟩

theorem getsTo_eq' {s : State} {b : Value} {k : JSStr} {v : Value} {Q : Value → Prop}
    (h : GetsTo s b k fun x => x = v) (hq : Q v) : GetsTo s b k Q := by
  obtain ⟨o, m, hb, hc, hm, hna, hp⟩ := h
  exact ⟨o, m, hb, hc, hm, hna, hp ▸ hq⟩

theorem simpleD (d : FuncData) (hc : d.code = GAEDGen.getActiveElementDeep_func) : FDI.Simple d := by
  constructor <;> rw [hc] <;> try rfl
  simp [GAEDGen.getActiveElementDeep_func, Func.params, Func.info]

set_option maxRecDepth 40000 in
set_option maxHeartbeats 8000000 in
/-- **`getActiveElementDeep(container)`**: the container's document's window (`ownerDocument.defaultView`), its
document's focused element `E` (`getActiveElement`, a contract), not an iframe: `E`. -/
theorem gaed_spec {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t : Value} {s : State}
    {Cont Doc Win E IFC fGA : ObjId} {bG : HashMap JSStr Binding} {oG : Option EnvId} {bdGA : Binding}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : 200 ≤ s.fuel)
    (hcode : d.code = GAEDGen.getActiveElementDeep_func) (hcls : d.isClassCtor = false) (hmode : d.thisMode = .strict)
    (hG : d.env < s.envs.size) (hGe : Scope.declLike? (s.envEntry d.env) = some (bG, oG))
    (hGGA : bG[JSStr.ofString "getActiveElement"]? = some bdGA) (hGGAv : bdGA.value = some (.obj fGA))
    (hGAo : fGA < s.heap.size) (hGAc : ∃ dd, (s.objEntry fGA).kind = .func dd)
    (hOD : ReactHostContainer.DomRead eng answer HI n s {} Cont "ownerDocument" (.obj Doc))
    (hDV : ReactHostContainer.DomRead2 eng answer HI n s {} Doc "defaultView" (.obj Win))
    (hWD : ReactHostContainer.DomRead eng answer HI n s {} Win "document" (.obj Doc))
    (hGA : ∀ w h1, Frame {} s w → HI h1 → 100 ≤ w.fuel →
      WP eng answer n h1 (callImpl eng (.obj fGA) .undefined #[.obj Doc]) w fun v w' h' =>
        v = .obj E ∧ Frame {} w w' ∧ w.fuel ≤ w'.fuel + 60 ∧ h' = h1)
    (hIF : ∀ w, Frame {} s w → GetsTo w (.obj Win) (JSStr.ofString "HTMLIFrameElement") fun v => v = .obj IFC)
    (hInst : ∀ w h1, Frame {} s w → 20 ≤ w.fuel → WP eng answer (n + 1) h1 (instanceofOperator (.obj E) (.obj IFC)) w fun b w' h' =>
      b = false ∧ Frame {} w w' ∧ w.fuel ≤ w'.fuel + 20 ∧ h' = h1) (hHI : HI h) :
    WP eng answer (n + 1) h (callImpl eng (.obj fo) t #[.obj Cont]) s fun v w h' =>
      v = .obj E ∧ Frame {} s w ∧ s.fuel ≤ w.fuel + 200 ∧ h' = h := by
  apply wp_callGen GAEDGen.getActiveElementDeep_eq (by decide) hlt hk (by omega) hcls hmode
    (by rw [hcode]; rfl) (by rw [hcode]; rfl) (simpleD d hcode) (by rw [hcode]; rfl) (by rw [hcode]; rfl)
  have hpn : d.code.info.fdi.paramNames = #[JSStr.ofString "containerInfo"] := by rw [hcode]; rfl
  have hv : d.code.info.fdi.varNames = #[JSStr.ofString "element", JSStr.ofString "JSCompiler_inline_result"] := by
    rw [hcode]; rfl
  have hl : FDI.lexDecls d = #[] := by simp [FDI.lexDecls, hcode, GAEDGen.getActiveElementDeep_func, Func.info]
  have ha : d.code.isAsync = false := by rw [hcode]; rfl
  have e1 : d.env ≠ s.envs.size := Nat.ne_of_lt hG
  have e1' : s.envs.size ≠ d.env := Ne.symm e1
  have e4 : d.env < s.envs.size + 1 := Nat.lt_succ_of_lt hG
  obtain ⟨dGA, hGAk⟩ := hGAc
  clear hcode
  simp only [GAEDGen.getActiveElementDeep]
  have hw0 : Frame {} s (bodyState s fo d t #[.obj Cont]) := by frame_go' [*]
  js_until ["ownerDocument"] [e1, e1', e4, hG, hGe, hGGA, hGGAv, hGAo, hGAk, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  refine wp_neNullObj' (by simp [js_simp]; omega) ?_
  iterate 3 (first | js_go | js_norm [e1, e1', e4, hG, hGe, hGGA, hGGAv, hGAo, hGAk, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner] | js_split)
  refine wp_getMemberAcc ?_
  js_until [] [e1, e1', e4, hG, hGe, hGGA, hGGAv, hGAo, hGAk, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  refine getsAcc_mono (hOD _ _ ?_ hHI ?_) ?_
  · frame_go' [*]
  · (try simp only [js_simp, State.pushEnv_fuel]); omega
  intro _ _ _ ⟨hv_, hh_, _, hw_, hf_⟩
  subst hv_ hw_ hh_
  try simp only [js_simp, State.pushEnv_fuel] at hf_
  refine wp_neNullObj' (by simp [js_simp]; omega) ?_
  iterate 3 (first | js_go | js_norm [e1, e1', e4, hG, hGe, hGGA, hGGAv, hGAo, hGAk, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner] | js_split)
  refine wp_getMemberAcc ?_
  refine wp_getMemberAcc ?_
  js_until [] [e1, e1', e4, hG, hGe, hGGA, hGGAv, hGAo, hGAk, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  refine getsAcc_mono (hOD _ _ ?_ hHI ?_) ?_
  · frame_go' [*]
  · (try simp only [js_simp, State.pushEnv_fuel]); omega
  intro _ _ _ ⟨hv_, hh_, _, hw_, hf_⟩
  subst hv_ hw_ hh_
  try simp only [js_simp, State.pushEnv_fuel] at hf_
  refine getsAcc_mono (hDV _ _ ?_ hHI ?_) ?_
  · frame_go' [*]
  · (try simp only [js_simp, State.pushEnv_fuel]); omega
  intro _ _ _ ⟨hv_, hh_, _, hw_, hf_⟩
  subst hv_ hw_ hh_
  try simp only [js_simp, State.pushEnv_fuel] at hf_
  refine wp_neNullObj' (by simp [js_simp]; omega) ?_
  iterate 2 (first | js_go | js_norm [e1, e1', e4, hG, hGe, hGGA, hGGAv, hGAo, hGAk, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner] | js_split)
  refine wp_getMemberAcc ?_
  refine wp_getMemberAcc ?_
  js_until [] [e1, e1', e4, hG, hGe, hGGA, hGGAv, hGAo, hGAk, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  refine getsAcc_mono (hOD _ _ ?_ hHI ?_) ?_
  · frame_go' [*]
  · (try simp only [js_simp, State.pushEnv_fuel]); omega
  intro _ _ _ ⟨hv_, hh_, _, hw_, hf_⟩
  subst hv_ hw_ hh_
  try simp only [js_simp, State.pushEnv_fuel] at hf_
  refine getsAcc_mono (hDV _ _ ?_ hHI ?_) ?_
  · frame_go' [*]
  · (try simp only [js_simp, State.pushEnv_fuel]); omega
  intro _ _ _ ⟨hv_, hh_, _, hw_, hf_⟩
  subst hv_ hw_ hh_
  try simp only [js_simp, State.pushEnv_fuel] at hf_
  iterate 9 (first | js_go | js_norm [e1, e1', e4, hG, hGe, hGGA, hGGAv, hGAo, hGAk, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner] | js_split)
  refine wp_getMemberAcc ?_
  js_until [] [e1, e1', e4, hG, hGe, hGGA, hGGAv, hGAo, hGAk, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  refine getsAcc_mono (hWD _ _ ?_ hHI ?_) ?_
  · frame_go' [*]
  · (try simp only [js_simp, State.pushEnv_fuel]); omega
  intro _ _ _ ⟨hv_, hh_, _, hw_, hf_⟩
  subst hv_ hw_ hh_
  try simp only [js_simp, State.pushEnv_fuel] at hf_
  js_until [] [e1, e1', e4, hG, hGe, hGGA, hGGAv, hGAo, hGAk, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  refine ⟨by js_norm [CallableC, e1, e1', e4, hG, hGe, hGGA, hGGAv, hGAo, hGAk, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner], ?_⟩
  refine wp_mono (hGA _ _ ?_ hHI ?_) ?_
  · frame_go' [*]
  · js_norm [e1, e1', e4, hG, hGe, hGGA, hGGAv, hGAo, hGAk, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]; omega
  rintro v1 w1 h1 ⟨rfl, hF1, hfu1, rfl⟩
  have hE1 := envEntry_frame0 hF1 (e := s.envs.size) (by js_norm [e1, e1', e4, hG, hGe, hGGA, hGGAv, hGAo, hGAk, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner])
  have hS1 : s.envs.size < w1.envs.size := Nat.lt_of_lt_of_le (by js_norm [e1, e1', e4, hG, hGe, hGGA, hGGAv, hGAo, hGAk, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]) hF1.envs_le
  have hfw1 : 100 ≤ w1.fuel := by (try simp only [js_simp] at hfu1); (try simp [bodyState, entryState] at hfu1); omega
  have hfr1 : s.fuel ≤ w1.fuel + 100 := by (try simp only [js_simp] at hfu1); (try simp [bodyState, entryState] at hfu1); omega
  have hFs1 : Frame {} s w1 := frame_empty_trans (by frame_go' [*]) hF1
  iterate 5 (first | js_go | js_norm [hE1, hS1, hfw1, e1, e1', e4, hG, hGe, hGGA, hGGAv, hGAo, hGAk, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner] | js_split)
  refine wp_getMember ?_
  js_until [] [hE1, hS1, hfw1, e1, e1', e4, hG, hGe, hGGA, hGGAv, hGAo, hGAk, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  refine getsTo_eq' (hIF _ (by frame_go' [*])) ?_
  refine wp_instanceof (wp_mono (hInst _ _ (by frame_go' [*]) (by (try simp only [js_simp, State.pushEnv_fuel]); omega)) ?_)
  rintro b2 w2 h2 ⟨rfl, hF2, hfu2, rfl⟩
  have hE2 := envEntry_frame0 hF2 (e := s.envs.size) (by js_norm [hE1, hS1, e1, e1', e4, hG, hGe, hGGA, hGGAv, hGAo, hGAk, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner])
  have hS2 : s.envs.size < w2.envs.size := Nat.lt_of_lt_of_le (by js_norm [hE1, hS1, e1, e1', e4, hG, hGe, hGGA, hGGAv, hGAo, hGAk, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]) hF2.envs_le
  have hfw2 : 50 ≤ w2.fuel := by simp [State.withFuel] at hfu2; omega
  have hfr2 : w1.fuel ≤ w2.fuel + 30 := by simp [State.withFuel] at hfu2; omega
  js [hE2, hS2, hfw2, hE1, hS1, hfw1, e1, e1', e4, hG, hGe, hGGA, hGGAv, hGAo, hGAk, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  exact ⟨frame_restore (frame_empty_trans (by frame_go' [*]) hF2) s, by omega⟩

end

end ReactActiveElement
