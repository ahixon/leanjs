import JSProofs.JsTactic
import JSProofs.RHSGen
import JSProofs.CSUGen
import JSProofs.PPRGen
import JSProofs.ReactStack

/-!
# Small steps on the host root's path through `beginWork` (zippy docs/react-proofs.md)

`resetHydrationState()` (not hydrating: three module bindings reset) and `checkScheduledUpdateOrContext(current, 2)`
for a fiber with no update in the render's lanes and no context dependencies (`false`).
-/

open ES ES.M HostRuns Logic
open Std (HashMap)

namespace ReactRootBailout

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ}

theorem simpleR (d : FuncData) (hc : d.code = RHSGen.resetHydrationState_func) : FDI.Simple d := by
  constructor <;> rw [hc] <;> try rfl
  simp [RHSGen.resetHydrationState_func, Func.params, Func.info]

theorem simpleC (d : FuncData) (hc : d.code = CSUGen.checkScheduledUpdateOrContext_func) : FDI.Simple d := by
  constructor <;> rw [hc] <;> try rfl
  simp [CSUGen.checkScheduledUpdateOrContext_func, Func.params, Func.info]

/-- What `resetHydrationState` writes. -/
def fpR (g : EnvId) : Footprint :=
  ⟨[(g, "nextHydratableInstance"), (g, "hydrationParentFiber"), (g, "isHydrating")], [], false⟩

set_option maxRecDepth 10000 in
/-- **`resetHydrationState()`**: the hydration bindings reset. -/
theorem reset_spec {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t : Value} {s : State}
    {bG : HashMap JSStr Binding} {oG : Option EnvId} {b1 b2 b3 : Binding}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : 10 ≤ s.fuel)
    (hcode : d.code = RHSGen.resetHydrationState_func) (hcls : d.isClassCtor = false) (hmode : d.thisMode = .strict)
    (hG : d.env < s.envs.size) (hGe : Scope.declLike? (s.envEntry d.env) = some (bG, oG))
    (g1 : bG[JSStr.ofString "nextHydratableInstance"]? = some b1) (g1m : b1.mutable = true) (g1v : b1.value.isSome = true)
    (g2 : bG[JSStr.ofString "hydrationParentFiber"]? = some b2) (g2m : b2.mutable = true) (g2v : b2.value.isSome = true)
    (g3 : bG[JSStr.ofString "isHydrating"]? = some b3) (g3m : b3.mutable = true) (g3v : b3.value.isSome = true) :
    WP eng answer n h (callImpl eng (.obj fo) t #[]) s fun v w h' =>
      v = .undefined ∧ Frame (fpR d.env) s w ∧ s.fuel ≤ w.fuel + 10 ∧ h' = h := by
  apply wp_callGen RHSGen.resetHydrationState_eq (by decide) hlt hk (by omega) hcls hmode
    (by rw [hcode]; rfl) (by rw [hcode]; rfl) (simpleR d hcode) (by rw [hcode]; rfl) (by rw [hcode]; rfl)
  have hpn : d.code.info.fdi.paramNames = #[] := by rw [hcode]; rfl
  have hv : d.code.info.fdi.varNames = #[] := by rw [hcode]; rfl
  have hl : FDI.lexDecls d = #[] := by simp [FDI.lexDecls, hcode, RHSGen.resetHydrationState_func, Func.info]
  have ha : d.code.isAsync = false := by rw [hcode]; rfl
  have hne : s.envs.size ≠ d.env := Nat.ne_of_gt hG
  have hG1 : d.env < s.envs.size + 1 := Nat.lt_succ_of_lt hG
  clear hcode
  simp only [RHSGen.resetHydrationState]
  js [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, g1, g1m, g1v, g2, g2m, g2v, g3, g3m, g3v, FDI.fdiCtx, Sem.inner]
  all_goals (repeat' apply And.intro)
  all_goals first | rfl | omega | (simp only [js_simp]; omega) | (simp only [fpR]; frame_go' [*, hne, Ne.symm hne, hG1])

set_option maxRecDepth 10000 in
/-- **`checkScheduledUpdateOrContext(current, 2)`**, no update in lane 2 and no dependencies: `false`. -/
theorem check_none {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t : Value} {s : State}
    {H : ObjId} {hl : F64} {lw le lc dw de dc : Bool}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : 10 ≤ s.fuel)
    (hcode : d.code = CSUGen.checkScheduledUpdateOrContext_func) (hcls : d.isClassCtor = false)
    (hmode : d.thisMode = .strict)
    (hH : H < s.heap.size) (hHk : (s.objEntry H).kind.isPlain = true)
    (hHl : (s.objEntry H).props.get? (.str "lanes") = some (.data (.num hl) lw le lc))
    (hHd : (s.objEntry H).props.get? (.str "dependencies") = some (.data .null dw de dc))
    (hl0 : isStrictlyEqual (.num (F64.fin false 0 (-1074)))
      (.num (numberBinOp .bitAnd hl (F64.fin false 4503599627370496 (-51)))) = true) :
    WP eng answer n h (callImpl eng (.obj fo) t #[.obj H, .num (F64.fin false 4503599627370496 (-51))]) s
      fun v w h' => v = .bool false ∧ Frame {} s w ∧ s.fuel ≤ w.fuel + 10 ∧ h' = h := by
  apply wp_callGen CSUGen.checkScheduledUpdateOrContext_eq (by decide) hlt hk (by omega) hcls hmode
    (by rw [hcode]; rfl) (by rw [hcode]; rfl) (simpleC d hcode) (by rw [hcode]; rfl) (by rw [hcode]; rfl)
  have hpn : d.code.info.fdi.paramNames = #[JSStr.ofString "current", JSStr.ofString "renderLanes"] := by
    rw [hcode]; rfl
  have hv : d.code.info.fdi.varNames = #[] := by rw [hcode]; rfl
  have hl : FDI.lexDecls d = #[] := by
    simp [FDI.lexDecls, hcode, CSUGen.checkScheduledUpdateOrContext_func, Func.info]
  have ha : d.code.isAsync = false := by rw [hcode]; rfl
  clear hcode
  simp only [CSUGen.checkScheduledUpdateOrContext]
  js [hpn, hv, hl, ha, hH, hHk, hHl, hHd, hl0, FDI.fdiCtx, Sem.inner]
  all_goals (repeat' apply And.intro)
  all_goals first | rfl | omega | (simp only [js_simp]; omega) | frame_go' [*]

theorem simpleP (d : FuncData) (hc : d.code = PPRGen.pushProvider_func) : FDI.Simple d := by
  constructor <;> rw [hc] <;> try rfl
  simp [PPRGen.pushProvider_func, Func.params, Func.info]

/-- What `pushProvider` writes: the stack (index, a slot, the value cursor) and the context's current value. -/
def fpP (g : EnvId) (VS Cu Cx : ObjId) (key : JSStr) : Footprint :=
  ⟨[(g, "index")], [(VS, .str key), (Cu, .str "current"), (Cx, .str "_currentValue")], false⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 2000000 in
/-- **`pushProvider(fiber, context, value)`**: the context's current value pushed on the value cursor, then
replaced. -/
theorem provider_spec {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t fib value : Value} {s : State}
    {bG : HashMap JSStr Binding} {oG : Option EnvId} {bdI bdV bdC bdP : Binding} {VS Cu Cx fP : ObjId} {dP : FuncData}
    {iv nv L : F64} {cur old cv : Value} {ce cc oe oc lw le lc xe xc : Bool} {i : Nat}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : 40 ≤ s.fuel)
    (hcode : d.code = PPRGen.pushProvider_func) (hcls : d.isClassCtor = false) (hmode : d.thisMode = .strict)
    (hG : d.env < s.envs.size) (hGe : Scope.declLike? (s.envEntry d.env) = some (bG, oG))
    (hGI : bG[JSStr.ofString "index"]? = some bdI) (hGIm : bdI.mutable = true) (hGIv : bdI.value = some (.num iv))
    (hGV : bG[JSStr.ofString "valueStack"]? = some bdV) (hGVv : bdV.value = some (.obj VS))
    (hGC : bG[JSStr.ofString "valueCursor"]? = some bdC) (hGCv : bdC.value = some (.obj Cu))
    (hGP : bG[JSStr.ofString "push"]? = some bdP) (hGPv : bdP.value = some (.obj fP))
    (hPo : fP < s.heap.size) (hPk : (s.objEntry fP).kind = .func dP) (hPcode : dP.code = PushGen.push_func)
    (hPcls : dP.isClassCtor = false) (hPmode : dP.thisMode = .strict) (hPenv : dP.env = d.env)
    (hVS : VS < s.heap.size) (hVSk : (s.objEntry VS).kind = .array) (hCu : Cu < s.heap.size)
    (hCuk : (s.objEntry Cu).kind.isPlain = true) (hCx : Cx < s.heap.size) (hCxk : (s.objEntry Cx).kind.isPlain = true)
    (d1 : VS ≠ Cu) (d2 : VS ≠ Cx) (d3 : Cu ≠ Cx) (d4 : fP ≠ VS) (d5 : fP ≠ Cu) (d6 : fP ≠ Cx)
    (hCc : (s.objEntry Cu).props.get? (.str "current") = some (.data cur true ce cc))
    (hCxv : (s.objEntry Cx).props.get? (.str "_currentValue") = some (.data cv true xe xc))
    (hnv : Conv.addF iv F64.one = nv)
    (hslot : (s.objEntry VS).props.get? (.str (numberToJSStr nv)) = some (.data old true oe oc))
    (hidx : (PropKey.str (numberToJSStr nv)).arrayIndex? = some i)
    (hlen : (s.objEntry VS).props.get? (.str "length") = some (.data (.num L) lw le lc))
    (hiL : i < (Conv.toNat? L).getD 0)
    (hnl : (PropKey.str (numberToJSStr nv) == PropKey.str (JSStr.ofString "length")) = false) :
    WP eng answer (n + 1) h (callImpl eng (.obj fo) t #[fib, .obj Cx, value]) s fun v w h' =>
      v = .undefined ∧ Frame (fpP d.env VS Cu Cx (numberToJSStr nv)) s w ∧ s.fuel ≤ w.fuel + 40 ∧ h' = h ∧
      Scope.declLike? (w.envEntry d.env) =
        some (bG.modify (JSStr.ofString "index") (fun bd => { bd with value := some (.num nv) }), oG) ∧
      (w.objEntry VS).props.get? (.str (numberToJSStr nv)) = some (.data cur true oe oc) ∧
      (w.objEntry Cu).props.get? (.str "current") = some (.data cv true ce cc) ∧
      (w.objEntry Cx).props.get? (.str "_currentValue") = some (.data value true xe xc) := by
  apply wp_callGen PPRGen.pushProvider_eq (by decide) hlt hk (by omega) hcls hmode
    (by rw [hcode]; rfl) (by rw [hcode]; rfl) (simpleP d hcode) (by rw [hcode]; rfl) (by rw [hcode]; rfl)
  have hpn : d.code.info.fdi.paramNames = #[JSStr.ofString "providerFiber", JSStr.ofString "context",
    JSStr.ofString "nextValue"] := by rw [hcode]; rfl
  have hv : d.code.info.fdi.varNames = #[] := by rw [hcode]; rfl
  have hl : FDI.lexDecls d = #[] := by simp [FDI.lexDecls, hcode, PPRGen.pushProvider_func, Func.info]
  have ha : d.code.isAsync = false := by rw [hcode]; rfl
  have hne : s.envs.size ≠ d.env := Nat.ne_of_gt hG
  have hG1 : d.env < s.envs.size + 1 := Nat.lt_succ_of_lt hG
  clear hcode
  simp only [PPRGen.pushProvider]
  js [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGI, hGIm, hGIv, hGV, hGVv, hGC, hGCv, hGP, hGPv, hPo, hPk,
    hVS, hVSk, hCu, hCuk, hCx, hCxk, hCc, hCxv, d1, d2, d3, d4, d5, d6, Ne.symm d1, Ne.symm d2, Ne.symm d3, Ne.symm d4,
    Ne.symm d5, Ne.symm d6, FDI.fdiCtx, Sem.inner]
  refine ⟨by js_norm [CallableC, *, Ne.symm d4, Ne.symm d5, Ne.symm d6], ?_⟩
  refine wp_mono (ReactStack.push_spec (d := dP) (bG := ?bG1) (oG := oG) (bdI := ?bI1) (bdV := bdV) (VS := VS) (Cu := Cu)
    (iv := iv) (nv := nv) (L := L) (cur := cur) (old := old) (ce := ce) (cc := cc) (oe := oe) (oc := oc) (lw := lw)
    (le := le) (lc := lc) (i := i) ?_ ?_ ?_ hPcode hPcls hPmode ?_ ?hGe1 ?hGI1 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hnv ?_ hidx ?_ hiL hnl) ?p1
  case hGe1 => rw [hPenv]; js_norm [*, Ne.symm hne]; rfl
  case hGI1 => js_norm [*]; rfl
  all_goals first | omega | (simp only [js_simp]; omega) | (js_norm [*, Ne.symm d1, Ne.symm d2, Ne.symm d3, Ne.symm d4, Ne.symm d5, Ne.symm d6]; done) | skip
  case p1 =>
    intro v1 w1 h1 ⟨hv1, hF1, hfu1, hh1, hR1, hS1, hC1⟩
    subst hv1 hh1
    rw [hPenv] at hF1 hR1
    try simp only [js_simp] at hfu1
    have hE1 : s.envs.size < w1.envs.size := envs_frame hF1 (by first | (simp only [js_simp]; done) | (simp only [js_simp]; omega))
    have hEw1 := envEntry_frame hF1 (e := s.envs.size) (by first | (simp only [js_simp]; done) | (simp only [js_simp]; omega)) (by simp [Nat.ne_of_lt hG])
    have hX1 : Cx < w1.heap.size := heap_frame hF1 (by simpa using hCx)
    have hXk1 : (w1.objEntry Cx).kind.isPlain = true := by rw [kind_frame hF1 (by simpa using hCx)]; simpa using hCxk
    have hXv1 : (w1.objEntry Cx).props.get? (.str "_currentValue") = some (.data cv true xe xc) := by
      rw [props_frame hF1 (by simpa using hCx) (by simp [Ne.symm d2, Ne.symm d3])]; simpa using hCxv
    js [hE1, hEw1, hX1, hXk1, hXv1, hpn, hv, hl, ha, Nat.ne_of_lt hE1, Nat.lt_succ_of_lt hE1, FDI.fdiCtx, Sem.inner]
    all_goals (repeat' apply And.intro)
    all_goals first | rfl | omega | (simp only [js_simp] at *; omega) | (js_norm [*, Ne.symm d2, Ne.symm d3]; done) | (simp only [fpP]; frame_go' [*, hne, Ne.symm hne, hG1]; done)

end

end ReactRootBailout
