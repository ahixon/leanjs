import JSProofs.UPInfra
import JSProofs.CHUGen
import JSProofs.ReactHostContainer

/-!
# commitHostUpdate (zippy docs/react-proofs.md)

`commitHostUpdate(fiber, newProps, oldProps)`: `updateProperties(fiber.stateNode, fiber.type, oldProps, newProps)`
inside a `try`, then the element's props key (`dom[internalPropsKey] = newProps`). The callee's behaviour is a
premise (`hU`: at any state framed from the entry state, its contract), instantiated with `up_spec` by the caller.
-/

open ES ES.M HostRuns Logic
open Std (HashMap)

namespace ReactCommitHost

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ} {HI : σ → Prop}

/-- **`obj[key] = rhs`**, the key a string naming an own writable data property of a plain object. -/
theorem wp_assignStrKey {n : Nat} {h : σ} {obj ke rhs : Sem.CExpr} {ctx : Ctx} {s : State}
    {Q : Value → State → σ → Prop}
    (hw : WP eng answer n h (obj ctx) s fun bv w1 h1 => WP eng answer n h1 (ke ctx) w1 fun kv w2 h2 =>
      ∃ ks, kv = .str ks ∧ WP eng answer n h2 (rhs ctx) w2 fun v w3 h3 => PutsC w3 bv ks v fun w4 => Q v w4 h3) :
    WP eng answer n h (Sem.assign (Sem.memberRef obj (.computed ke) false) rhs ctx) s Q := by
  rw [wp_iff_wpr]
  simp only [Sem.assign, Sem.memberRef, M.bind_eq, M.bind_apply]
  apply wpr_bind
  apply wpr_bind
  refine wp_mono hw fun bv w1 h1 hk => ?_
  simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  apply wp_bind
  refine wp_mono hk fun kv w2 h2 ⟨ks, hkv, hr⟩ => ?_
  subst hkv
  refine wp_of_eq (a := Ref.prop bv (.str ks) ctx.strict none) rfl ?_
  apply wp_bind
  refine wp_mono hr fun v w3 h3 q => ?_
  obtain ⟨o, v0, e, c, hb, hlt, hkp, hp, hq⟩ := putsC_putsTo q
  subst hb
  apply wp_bind
  exact wp_of_eq (putRefValue_own o ks ctx.strict v w3 hlt hkp hp) (wp_pure hq)

theorem simple (d : FuncData) (hc : d.code = CHUGen.commitHostUpdate_func) : FDI.Simple d := by
  constructor <;> rw [hc] <;> try rfl
  simp [CHUGen.commitHostUpdate_func, Func.params, Func.info]

set_option maxRecDepth 40000 in
set_option maxHeartbeats 8000000 in
/-- **`commitHostUpdate(X, NP, LP)`** for a host fiber `X` (`stateNode` the element `dom`, `type` the tag): the
props updated (the callee's contract `hU`, its own fact `P`), then `dom[internalPropsKey] = NP`. -/
theorem chu_spec {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t : Value} {s : State}
    {bG : HashMap JSStr Binding} {oG : Option EnvId} {bdU bdK : Binding} {fU X dom LP NP : ObjId}
    {tag kP : JSStr} {sw se sc tw te tc : Bool} {P : State → σ → Prop} {fpU : Footprint}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : 3000 ≤ s.fuel)
    (hcode : d.code = CHUGen.commitHostUpdate_func) (hcls : d.isClassCtor = false) (hmode : d.thisMode = .strict)
    (hG : d.env < s.envs.size) (hGe : Scope.declLike? (s.envEntry d.env) = some (bG, oG))
    (hGU : bG[JSStr.ofString "updateProperties"]? = some bdU) (hGUv : bdU.value = some (.obj fU))
    (hGK : bG[JSStr.ofString "internalPropsKey"]? = some bdK) (hGKv : bdK.value = some (.str kP))
    (hUo : fU < s.heap.size) (hUc : ∃ dU, (s.objEntry fU).kind = .func dU)
    (hX : X < s.heap.size) (hXk : (s.objEntry X).kind.isPlain = true)
    (hXs : (s.objEntry X).props.get? (.str (JSStr.ofString "stateNode")) = some (.data (.obj dom) sw se sc))
    (hXt : (s.objEntry X).props.get? (.str (JSStr.ofString "type")) = some (.data (.str tag) tw te tc))
    (hD : dom < s.heap.size)
    (hU : ∀ w h1, Frame {} s w → HI h1 → 2900 ≤ w.fuel →
      WP eng answer (n + 1) h1 (callImpl eng (.obj fU) .undefined #[.obj dom, .str tag, .obj LP, .obj NP]) w
        fun v w' h' => v = .undefined ∧ Frame fpU w w' ∧ w.fuel ≤ w'.fuel + 2000 ∧ P w' h' ∧
          (w'.objEntry dom).kind.isPlain = true ∧
          ∃ v0 e c, (w'.objEntry dom).props.get? (.str kP) = some (.data v0 true e c))
    (hfpU : ∀ p, p ∈ fpU.binds → p.1 = d.env ∧ p.2 ≠ JSStr.ofString "internalPropsKey") (hHI : HI h) :
    WP eng answer (n + 2) h (callImpl eng (.obj fo) t #[.obj X, .obj NP, .obj LP]) s fun v w h' =>
      v = .undefined ∧ s.fuel ≤ w.fuel + 2100 ∧ ∃ wm e0 c0, P wm h' ∧ Frame fpU s wm ∧
        w = (wm.setProp dom (.str kP) (.data (.obj NP) true e0 c0)).restore s := by
  apply wp_callGen CHUGen.commitHostUpdate_eq (by decide) hlt hk (by omega) hcls hmode
    (by rw [hcode]; rfl) (by rw [hcode]; rfl) (simple d hcode) (by rw [hcode]; rfl) (by rw [hcode]; rfl)
  have hpn : d.code.info.fdi.paramNames = #[JSStr.ofString "finishedWork", JSStr.ofString "newProps",
    JSStr.ofString "oldProps"] := by rw [hcode]; rfl
  have hv : d.code.info.fdi.varNames = #[JSStr.ofString "domElement"] := by rw [hcode]; rfl
  have hl : FDI.lexDecls d = #[] := by simp [FDI.lexDecls, hcode, CHUGen.commitHostUpdate_func, Func.info]
  have ha : d.code.isAsync = false := by rw [hcode]; rfl
  have e1 : d.env ≠ s.envs.size := Nat.ne_of_lt hG
  have e2 : d.env ≠ s.envs.size + 1 := Nat.ne_of_lt (Nat.lt_succ_of_lt hG)
  have e3 : d.env < s.envs.size + 1 + 1 := Nat.lt_succ_of_lt (Nat.lt_succ_of_lt hG)
  have e4 : d.env < s.envs.size + 1 := Nat.lt_succ_of_lt hG
  clear hcode
  simp only [CHUGen.commitHostUpdate]
  iterate 2 (first | js_go | js_norm [hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner] | js_split)
  refine wp_tryS ?_
  js_until [] [e1, e2, e3, e4, hGe, hGU, hGUv, hGK, hGKv, hG, hUo, hX, hXk, hXs, hXt, Ne.symm e1, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  obtain ⟨dU, hUk⟩ := hUc
  refine ⟨by js_norm [CallableC, hUk, e1, e2, e3, e4, hGe, hGU, hGUv, hGK, hGKv, hG, hUo, hX, hXk, hXs, hXt, Ne.symm e1, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner], ?_⟩
  refine wp_mono (hU _ _ (by frame_go' [*]) hHI (by js_norm [e1, e2, e3, e4, hGe, hGU, hGUv, hGK, hGKv, hG, hUo, hX, hXk, hXs, hXt, Ne.symm e1, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]; omega)) ?_
  rintro v1 w1 h1 ⟨rfl, hF1, hfu1, hP1, hDk1, v0, e0, c0, hD1⟩
  have hlt0 : s.envs.size < (bodyState s fo d t #[.obj X, .obj NP, .obj LP]).envs.size := by simp
  have hE1 := envEntry_frame hF1 (e := s.envs.size) (by simpa using hlt0)
    (List.all_eq_true.mpr fun p hp => by simp [(hfpU p hp).1, e1])
  have hS1 : s.envs.size < w1.envs.size := Nat.lt_of_lt_of_le (by simpa using hlt0) hF1.envs_le
  obtain ⟨bw, hd1, hbw⟩ := declLike_frame hF1 (e := d.env) (bs := bG) (o := oG) (by simp; omega) (by js_norm [e1, e2, e3, e4, hGe, hGU, hGUv, hGK, hGKv, hG, hUo, hX, hXk, hXs, hXt, Ne.symm e1, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner])
  have hK1 : bw[JSStr.ofString "internalPropsKey"]? = some bdK := by
    have hx := hbw (JSStr.ofString "internalPropsKey") (fun hm => (hfpU _ hm).2 rfl)
    rw [hx]; exact hGK
  have hG1 : d.env < w1.envs.size := Nat.lt_of_lt_of_le (by simp; omega) hF1.envs_le
  have hfw1 : 900 ≤ w1.fuel := by simp [bodyState, entryState] at hfu1; omega
  have hDlt1 : dom < w1.heap.size := Nat.lt_of_lt_of_le (by simpa using hD) hF1.heap_le
  iterate 2 (first | js_go | js_norm [hE1, hS1, hd1, hK1, hG1, hfw1, hDk1, hD1, hDlt1, e1, e2, e3, e4, hGe, hGU, hGUv, hGK, hGKv, hG, hUo, hX, hXk, hXs, hXt, Ne.symm e1, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner] | js_split)
  refine wp_assignStrKey ?_
  js_until [] [hE1, hS1, hd1, hK1, hG1, hfw1, hDk1, hD1, hDlt1, e1, e2, e3, e4, hGe, hGU, hGUv, hGK, hGKv, hG, hUo, hX, hXk, hXs, hXt, Ne.symm e1, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  refine ⟨_, rfl, ?_⟩
  js [hE1, hS1, hd1, hK1, hG1, hfw1, hDk1, hD1, hDlt1, e1, e2, e3, e4, hGe, hGU, hGUv, hGK, hGKv, hG, hUo, hX, hXk, hXs, hXt, Ne.symm e1, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  refine ⟨by simp [bodyState, entryState] at hfu1; omega, w1, e0, c0, hP1, ?_, rfl⟩
  exact frame_mono (frame_trans (fp1 := {}) (s := s) (by frame_go' [*]) hF1)
    (fun p hp => by simpa [Footprint.union] using hp) (fun p hp => by simpa [Footprint.union] using hp)
    (fun hj => by simpa [Footprint.union] using hj)


end

end ReactCommitHost
