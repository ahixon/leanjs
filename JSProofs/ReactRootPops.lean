import JSProofs.ReactStack
import JSProofs.ReactRootBailout
import JSProofs.PopProvGen
import JSProofs.PoHCGen
import JSProofs.FrameExt

/-!
# The root's completeWork pops (zippy docs/react-proofs.md)

`popProvider(context)`: the context's current value restored from the value cursor, which is popped;
`popHostContainer()`: the three host-context cursors popped (what the root's `beginWork` pushed, in reverse).
-/

open ES ES.M HostRuns Logic
open Std (HashMap)

namespace ReactRootPops

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ}

theorem simpleP (d : FuncData) (hc : d.code = PopProvGen.popProvider_func) : FDI.Simple d := by
  constructor <;> rw [hc] <;> try rfl
  simp [PopProvGen.popProvider_func, Func.params, Func.info]

/-- What `popProvider` writes: the stack (index, a slot, the value cursor) and the context's current value. -/
def fpPP (g : EnvId) (VS Cu Cx : ObjId) (key : JSStr) : Footprint :=
  ⟨[(g, "index")], [(Cx, .str "_currentValue"), (VS, .str key), (Cu, .str "current")], false⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 2000000 in
/-- **`popProvider(context)`**: `context._currentValue = valueCursor.current`, then `pop(valueCursor)`. -/
theorem pop_provider {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t : Value} {s : State}
    {bG : HashMap JSStr Binding} {oG : Option EnvId} {bdI bdV bdC bdO : Binding} {VS Cu Cx fO : ObjId} {dO : FuncData}
    {iv L : F64} {cur saved cv : Value} {ce cc oe oc lw le lc xe xc : Bool} {i : Nat}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : 30 ≤ s.fuel)
    (hcode : d.code = PopProvGen.popProvider_func) (hcls : d.isClassCtor = false) (hmode : d.thisMode = .strict)
    (hG : d.env < s.envs.size) (hGe : Scope.declLike? (s.envEntry d.env) = some (bG, oG))
    (hGI : bG[JSStr.ofString "index"]? = some bdI) (hGIm : bdI.mutable = true) (hGIv : bdI.value = some (.num iv))
    (hGV : bG[JSStr.ofString "valueStack"]? = some bdV) (hGVv : bdV.value = some (.obj VS))
    (hGC : bG[JSStr.ofString "valueCursor"]? = some bdC) (hGCv : bdC.value = some (.obj Cu))
    (hGO : bG[JSStr.ofString "pop"]? = some bdO) (hGOv : bdO.value = some (.obj fO))
    (hOo : fO < s.heap.size) (hOk : (s.objEntry fO).kind = .func dO) (hOcode : dO.code = PopGen.pop_func)
    (hOcls : dO.isClassCtor = false) (hOmode : dO.thisMode = .strict) (hOenv : dO.env = d.env)
    (hVS : VS < s.heap.size) (hVSk : (s.objEntry VS).kind = .array) (hCu : Cu < s.heap.size)
    (hCuk : (s.objEntry Cu).kind.isPlain = true) (hCx : Cx < s.heap.size) (hCxk : (s.objEntry Cx).kind.isPlain = true)
    (d1 : VS ≠ Cu) (d2 : VS ≠ Cx) (d3 : Cu ≠ Cx) (d4 : fO ≠ VS) (d5 : fO ≠ Cu) (d6 : fO ≠ Cx)
    (hCc : (s.objEntry Cu).props.get? (.str "current") = some (.data cur true ce cc))
    (hCxv : (s.objEntry Cx).props.get? (.str "_currentValue") = some (.data cv true xe xc))
    (hslot : (s.objEntry VS).props.get? (.str (numberToJSStr iv)) = some (.data saved true oe oc))
    (hidx : (PropKey.str (numberToJSStr iv)).arrayIndex? = some i)
    (hlen : (s.objEntry VS).props.get? (.str "length") = some (.data (.num L) lw le lc))
    (hiL : i < (Conv.toNat? L).getD 0)
    (hnl : (PropKey.str (numberToJSStr iv) == PropKey.str (JSStr.ofString "length")) = false)
    (hpos : ltNum iv (F64.fin false 0 (-1074)) = false) :
    WP eng answer (n + 1) h (callImpl eng (.obj fo) t #[.obj Cx]) s fun v w h' =>
      v = .undefined ∧ Frame (fpPP d.env VS Cu Cx (numberToJSStr iv)) s w ∧ s.fuel ≤ w.fuel + 30 ∧ h' = h ∧
      w.realm = s.realm ∧
      Scope.declLike? (w.envEntry d.env) =
        some (bG.modify (JSStr.ofString "index") (fun bd => { bd with value := some (.num (Conv.subF iv F64.one)) }), oG) ∧
      (w.objEntry VS).props.get? (.str (numberToJSStr iv)) = some (.data .null true oe oc) ∧
      (w.objEntry Cu).props.get? (.str "current") = some (.data saved true ce cc) ∧
      (w.objEntry Cx).props.get? (.str "_currentValue") = some (.data cur true xe xc) := by
  apply wp_callGen PopProvGen.popProvider_eq (by decide) hlt hk (by omega) hcls hmode
    (by rw [hcode]; rfl) (by rw [hcode]; rfl) (simpleP d hcode) (by rw [hcode]; rfl) (by rw [hcode]; rfl)
  have hpn : d.code.info.fdi.paramNames = #[JSStr.ofString "context"] := by rw [hcode]; rfl
  have hv : d.code.info.fdi.varNames = #[] := by rw [hcode]; rfl
  have hl : FDI.lexDecls d = #[] := by simp [FDI.lexDecls, hcode, PopProvGen.popProvider_func, Func.info]
  have ha : d.code.isAsync = false := by rw [hcode]; rfl
  have hne : s.envs.size ≠ d.env := Nat.ne_of_gt hG
  have hG1 : d.env < s.envs.size + 1 := Nat.lt_succ_of_lt hG
  clear hcode
  simp only [PopProvGen.popProvider]
  js [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGI, hGIm, hGIv, hGV, hGVv, hGC, hGCv, hGO, hGOv, hOo, hOk,
    hVS, hVSk, hCu, hCuk, hCx, hCxk, hCc, hCxv, d1, d2, d3, d4, d5, d6, Ne.symm d1, Ne.symm d2, Ne.symm d3, Ne.symm d4,
    Ne.symm d5, Ne.symm d6, FDI.fdiCtx, Sem.inner]
  refine ⟨by js_norm [CallableC, hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGI, hGIm, hGIv, hGV, hGVv, hGC, hGCv, hGO, hGOv, hOo, hOk, hVS, hVSk, hCu, hCuk, hCx, hCxk, hCc, hCxv, hslot, hlen, d1, d2, d3, d4, d5, d6, Ne.symm d1, Ne.symm d2, Ne.symm d3, Ne.symm d4, Ne.symm d5, Ne.symm d6, FDI.fdiCtx, Sem.inner], ?_⟩
  refine wp_mono (ReactStack.pop_spec (bG := bG) (oG := oG) (bdI := bdI) (bdV := bdV) (VS := VS) (Cu := Cu) (iv := iv)
    (L := L) (cur := cur) (saved := saved) (ce := ce) (cc := cc) (oe := oe) (oc := oc) (lw := lw) (le := le) (lc := lc)
    (i := i) (by js_norm [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGI, hGIm, hGIv, hGV, hGVv, hGC, hGCv, hGO, hGOv, hOo, hOk, hVS, hVSk, hCu, hCuk, hCx, hCxk, hCc, hCxv, hslot, hlen, d1, d2, d3, d4, d5, d6, Ne.symm d1, Ne.symm d2, Ne.symm d3, Ne.symm d4, Ne.symm d5, Ne.symm d6, FDI.fdiCtx, Sem.inner]) (by js_norm [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGI, hGIm, hGIv, hGV, hGVv, hGC, hGCv, hGO, hGOv, hOo, hOk, hVS, hVSk, hCu, hCuk, hCx, hCxk, hCc, hCxv, hslot, hlen, d1, d2, d3, d4, d5, d6, Ne.symm d1, Ne.symm d2, Ne.symm d3, Ne.symm d4, Ne.symm d5, Ne.symm d6, FDI.fdiCtx, Sem.inner]) (by simp only [js_simp]; omega) hOcode hOcls hOmode
    (by rw [hOenv]; js_norm [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGI, hGIm, hGIv, hGV, hGVv, hGC, hGCv, hGO, hGOv, hOo, hOk, hVS, hVSk, hCu, hCuk, hCx, hCxk, hCc, hCxv, hslot, hlen, d1, d2, d3, d4, d5, d6, Ne.symm d1, Ne.symm d2, Ne.symm d3, Ne.symm d4, Ne.symm d5, Ne.symm d6, FDI.fdiCtx, Sem.inner]) (by rw [hOenv]; js_norm [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGI, hGIm, hGIv, hGV, hGVv, hGC, hGCv, hGO, hGOv, hOo, hOk, hVS, hVSk, hCu, hCuk, hCx, hCxk, hCc, hCxv, hslot, hlen, d1, d2, d3, d4, d5, d6, Ne.symm d1, Ne.symm d2, Ne.symm d3, Ne.symm d4, Ne.symm d5, Ne.symm d6, FDI.fdiCtx, Sem.inner]) hGI hGIm hGIv hGV hGVv (by js_norm [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGI, hGIm, hGIv, hGV, hGVv, hGC, hGCv, hGO, hGOv, hOo, hOk, hVS, hVSk, hCu, hCuk, hCx, hCxk, hCc, hCxv, hslot, hlen, d1, d2, d3, d4, d5, d6, Ne.symm d1, Ne.symm d2, Ne.symm d3, Ne.symm d4, Ne.symm d5, Ne.symm d6, FDI.fdiCtx, Sem.inner])
    (by js_norm [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGI, hGIm, hGIv, hGV, hGVv, hGC, hGCv, hGO, hGOv, hOo, hOk, hVS, hVSk, hCu, hCuk, hCx, hCxk, hCc, hCxv, hslot, hlen, d1, d2, d3, d4, d5, d6, Ne.symm d1, Ne.symm d2, Ne.symm d3, Ne.symm d4, Ne.symm d5, Ne.symm d6, FDI.fdiCtx, Sem.inner]) (by js_norm [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGI, hGIm, hGIv, hGV, hGVv, hGC, hGCv, hGO, hGOv, hOo, hOk, hVS, hVSk, hCu, hCuk, hCx, hCxk, hCc, hCxv, hslot, hlen, d1, d2, d3, d4, d5, d6, Ne.symm d1, Ne.symm d2, Ne.symm d3, Ne.symm d4, Ne.symm d5, Ne.symm d6, FDI.fdiCtx, Sem.inner]) (by js_norm [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGI, hGIm, hGIv, hGV, hGVv, hGC, hGCv, hGO, hGOv, hOo, hOk, hVS, hVSk, hCu, hCuk, hCx, hCxk, hCc, hCxv, hslot, hlen, d1, d2, d3, d4, d5, d6, Ne.symm d1, Ne.symm d2, Ne.symm d3, Ne.symm d4, Ne.symm d5, Ne.symm d6, FDI.fdiCtx, Sem.inner]) d1 (by js_norm [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGI, hGIm, hGIv, hGV, hGVv, hGC, hGCv, hGO, hGOv, hOo, hOk, hVS, hVSk, hCu, hCuk, hCx, hCxk, hCc, hCxv, hslot, hlen, d1, d2, d3, d4, d5, d6, Ne.symm d1, Ne.symm d2, Ne.symm d3, Ne.symm d4, Ne.symm d5, Ne.symm d6, FDI.fdiCtx, Sem.inner]) (by js_norm [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGI, hGIm, hGIv, hGV, hGVv, hGC, hGCv, hGO, hGOv, hOo, hOk, hVS, hVSk, hCu, hCuk, hCx, hCxk, hCc, hCxv, hslot, hlen, d1, d2, d3, d4, d5, d6, Ne.symm d1, Ne.symm d2, Ne.symm d3, Ne.symm d4, Ne.symm d5, Ne.symm d6, FDI.fdiCtx, Sem.inner]) hidx
    (by js_norm [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGI, hGIm, hGIv, hGV, hGVv, hGC, hGCv, hGO, hGOv, hOo, hOk, hVS, hVSk, hCu, hCuk, hCx, hCxk, hCc, hCxv, hslot, hlen, d1, d2, d3, d4, d5, d6, Ne.symm d1, Ne.symm d2, Ne.symm d3, Ne.symm d4, Ne.symm d5, Ne.symm d6, FDI.fdiCtx, Sem.inner]) hiL hnl hpos) ?_
  intro v1 w1 h1 ⟨hv1, hF1, hfu1, hh1, hI1, hS1, hC1⟩
  subst hv1 hh1
  rw [hOenv] at hF1 hI1
  have hX1 : (w1.objEntry Cx).props.get? (.str "_currentValue") = some (.data cur true xe xc) := by
    rw [props_frame hF1 (by js_norm [hCx]) (by simp [Ne.symm d2, Ne.symm d3, d2, d3])]; js_norm [hCx]
  have hE1 : s.envs.size < w1.envs.size := envs_frame hF1 (by js_norm)
  have hEw1 := envEntry_frame hF1 (e := s.envs.size) (by js_norm) (by simp [Nat.ne_of_lt hG])
  js [hE1, hEw1, hpn, hv, hl, ha, Nat.ne_of_lt hE1, FDI.fdiCtx, Sem.inner]
  have gB : Frame (fpPP d.env VS Cu Cx (numberToJSStr iv)) s (bodyState s fo d t #[.obj Cx]) :=
    frame_mono (frame_bodyState (frame_refl ({} : Footprint) s) fo d t _) (by simp) (by simp) (fun _ => rfl)
  have g1 := frame_mono (fp' := fpPP d.env VS Cu Cx (numberToJSStr iv)) (frame_setProp_prop gB hCx
    (.str (JSStr.ofString "_currentValue")) (.data cur true xe xc)) (fun p hp => hp)
    (fun p hp => by simp only [List.mem_cons] at hp; rcases hp with rfl | hp; simp [fpPP]; exact hp) (fun h => h)
  have FW := frame_extend' g1 hF1 (fun q hq _ => by simp at hq; simp [fpPP, hq])
    (fun q hq _ => by simp at hq; rcases hq with hq | hq <;> simp [fpPP, hq]) (fun _ => rfl)
  simp only [js_simp] at hfu1
  all_goals (repeat' apply And.intro)
  all_goals first | rfl | omega | exact frame_restore FW s | assumption

theorem simpleH (d : FuncData) (hc : d.code = PoHCGen.popHostContainer_func) : FDI.Simple d := by
  constructor <;> rw [hc] <;> try rfl
  simp [PoHCGen.popHostContainer_func, Func.params, Func.info]

/-- What `popHostContainer` writes: the stack index, three slots, the three cursors. -/
def fpHC (g : EnvId) (VS CS CF RI : ObjId) : Footprint :=
  ⟨[(g, "index")], [(VS, .str "2"), (CS, .str "current"), (VS, .str "1"), (CF, .str "current"), (VS, .str "0"),
    (RI, .str "current")], false⟩

theorem idx_modify {bG : HashMap JSStr Binding} {bdI : Binding} (hGI : bG[JSStr.ofString "index"]? = some bdI)
    (f : Binding → Binding) :
    (bG.modify (JSStr.ofString "index") f)[JSStr.ofString "index"]? = some (f bdI) := by
  simp [Std.HashMap.getElem?_modify, hGI]

theorem other_modify {bG : HashMap JSStr Binding} (f : Binding → Binding) {x : JSStr}
    (hx : x ≠ JSStr.ofString "index") : (bG.modify (JSStr.ofString "index") f)[x]? = bG[x]? := by
  simp [Std.HashMap.getElem?_modify, Ne.symm hx]

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
/-- **`popHostContainer()`** with the host container's three entries on top of the stack (index 2): `pop` of the
context, fiber and root instance cursors; the index back to -1. -/
theorem pop_host_container {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t : Value} {s : State}
    {bG : HashMap JSStr Binding} {oG : Option EnvId} {bdI bdV bdCS bdCF bdRI bdO : Binding} {VS CS CF RI fO : ObjId}
    {dO : FuncData} {L : F64} {o0 o1 o2 vr vf vc : Value} {e0 c0 e1 c1 e2 c2 lw le lc re rc fe fc ce cc : Bool}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : 40 ≤ s.fuel)
    (hcode : d.code = PoHCGen.popHostContainer_func) (hcls : d.isClassCtor = false) (hmode : d.thisMode = .strict)
    (hG : d.env < s.envs.size) (hGe : Scope.declLike? (s.envEntry d.env) = some (bG, oG))
    (hGI : bG[JSStr.ofString "index"]? = some bdI) (hGIm : bdI.mutable = true)
    (hGIv : bdI.value = some (.num (F64.fin false 4503599627370496 (-51))))
    (hGV : bG[JSStr.ofString "valueStack"]? = some bdV) (hGVv : bdV.value = some (.obj VS))
    (hGCS : bG[JSStr.ofString "contextStackCursor"]? = some bdCS) (hGCSv : bdCS.value = some (.obj CS))
    (hGCF : bG[JSStr.ofString "contextFiberStackCursor"]? = some bdCF) (hGCFv : bdCF.value = some (.obj CF))
    (hGRI : bG[JSStr.ofString "rootInstanceStackCursor"]? = some bdRI) (hGRIv : bdRI.value = some (.obj RI))
    (hGO : bG[JSStr.ofString "pop"]? = some bdO) (hGOv : bdO.value = some (.obj fO))
    (hOo : fO < s.heap.size) (hOk : (s.objEntry fO).kind = .func dO) (hOcode : dO.code = PopGen.pop_func)
    (hOcls : dO.isClassCtor = false) (hOmode : dO.thisMode = .strict) (hOenv : dO.env = d.env)
    (hVS : VS < s.heap.size) (hVSk : (s.objEntry VS).kind = .array)
    (hV0 : (s.objEntry VS).props.get? (.str "0") = some (.data o0 true e0 c0))
    (hV1 : (s.objEntry VS).props.get? (.str "1") = some (.data o1 true e1 c1))
    (hV2 : (s.objEntry VS).props.get? (.str "2") = some (.data o2 true e2 c2))
    (hVL : (s.objEntry VS).props.get? (.str "length") = some (.data (.num L) lw le lc))
    (hL3 : 3 ≤ (Conv.toNat? L).getD 0)
    (hRI : RI < s.heap.size) (hRIk : (s.objEntry RI).kind.isPlain = true)
    (hRIc : (s.objEntry RI).props.get? (.str "current") = some (.data vr true re rc))
    (hCF : CF < s.heap.size) (hCFk : (s.objEntry CF).kind.isPlain = true)
    (hCFc : (s.objEntry CF).props.get? (.str "current") = some (.data vf true fe fc))
    (hCS : CS < s.heap.size) (hCSk : (s.objEntry CS).kind.isPlain = true)
    (hCSc : (s.objEntry CS).props.get? (.str "current") = some (.data vc true ce cc))
    (d1 : VS ≠ RI) (d2 : VS ≠ CF) (d3 : VS ≠ CS) (d4 : RI ≠ CF) (d5 : RI ≠ CS) (d6 : CF ≠ CS)
    (dO1 : fO ≠ VS) (dO2 : fO ≠ RI) (dO3 : fO ≠ CF) (dO4 : fO ≠ CS) :
    WP eng answer (n + 1) h (callImpl eng (.obj fo) t #[]) s fun v w h' =>
      v = .undefined ∧ Frame (fpHC d.env VS CS CF RI) s w ∧ s.fuel ≤ w.fuel + 40 ∧ h' = h ∧ w.realm = s.realm ∧
      (∃ bm, Scope.declLike? (w.envEntry d.env) = some (bm, oG) ∧
        (∃ bd, bm[JSStr.ofString "index"]? = some bd ∧ bd.value = some (.num (F64.fin true 4503599627370496 (-52))) ∧
          bd.mutable = true) ∧ ∀ x, x ≠ JSStr.ofString "index" → bm[x]? = bG[x]?) ∧
      (w.objEntry VS).props.get? (.str "0") = some (.data .null true e0 c0) ∧
      (w.objEntry VS).props.get? (.str "1") = some (.data .null true e1 c1) ∧
      (w.objEntry VS).props.get? (.str "2") = some (.data .null true e2 c2) ∧
      (w.objEntry CS).props.get? (.str "current") = some (.data o2 true ce cc) ∧
      (w.objEntry CF).props.get? (.str "current") = some (.data o1 true fe fc) ∧
      (w.objEntry RI).props.get? (.str "current") = some (.data o0 true re rc) := by
  apply wp_callGen PoHCGen.popHostContainer_eq (by decide) hlt hk (by omega) hcls hmode
    (by rw [hcode]; rfl) (by rw [hcode]; rfl) (simpleH d hcode) (by rw [hcode]; rfl) (by rw [hcode]; rfl)
  have hpn : d.code.info.fdi.paramNames = #[] := by rw [hcode]; rfl
  have hv : d.code.info.fdi.varNames = #[] := by rw [hcode]; rfl
  have hl : FDI.lexDecls d = #[] := by simp [FDI.lexDecls, hcode, PoHCGen.popHostContainer_func, Func.info]
  have ha : d.code.isAsync = false := by rw [hcode]; rfl
  have hne : s.envs.size ≠ d.env := Nat.ne_of_gt hG
  have hG1 : d.env < s.envs.size + 1 := Nat.lt_succ_of_lt hG
  clear hcode
  simp only [PoHCGen.popHostContainer]
  js [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGCS, hGCSv, hGO, hGOv, hOo, hOk, FDI.fdiCtx, Sem.inner]
  have n2 : numberToJSStr (F64.fin false 4503599627370496 (-51)) = JSStr.ofString "2" := by decide
  have n1 : numberToJSStr (F64.fin false 4503599627370496 (-52)) = JSStr.ofString "1" := by decide
  have n0 : numberToJSStr (F64.fin false 0 (-1074)) = JSStr.ofString "0" := by decide
  have s21 : Conv.subF (F64.fin false 4503599627370496 (-51)) F64.one = F64.fin false 4503599627370496 (-52) := by decide
  have s10 : Conv.subF (F64.fin false 4503599627370496 (-52)) F64.one = F64.fin false 0 (-1074) := by decide
  have s0m : Conv.subF (F64.fin false 0 (-1074)) F64.one = F64.fin true 4503599627370496 (-52) := by decide
  have hL : (Conv.toNat? L).getD 0 ≥ 3 := hL3
  -- (pop(contextStackCursor): slot 2)
  refine ⟨by js_norm [CallableC, hOo, hOk], ?_⟩
  refine wp_mono (ReactStack.pop_spec (bG := bG) (oG := oG) (bdI := bdI) (bdV := bdV) (VS := VS) (Cu := CS)
    (iv := F64.fin false 4503599627370496 (-51)) (L := L) (cur := vc) (saved := o2) (ce := ce) (cc := cc) (oe := e2) (oc := c2) (lw := lw) (le := le)
    (lc := lc) (i := 2) (by js_norm [hOo]) (by js_norm [hOk]) (by simp only [js_simp]; omega) hOcode hOcls hOmode
    (by rw [hOenv]; js_norm [hG1]) (by rw [hOenv]; js_norm [hG, hG1, hne, Ne.symm hne, hGe]) hGI hGIm hGIv hGV hGVv
    (by js_norm [hVS]) (by js_norm [hVSk]) (by js_norm [hCS]) (by js_norm [hCSk]) d3 (by js_norm [hCSc])
    (by rw [n2]; js_norm [hV2]) (by rw [n2]; js_norm) (by js_norm [hVL]) (by omega) (by rw [n2]; decide) (by decide)) ?_
  intro v1 w1 h1 ⟨hv1, hF1, hfu1, hh1, hI1, hS1, hC1⟩
  subst hv1 hh1
  rw [hOenv] at hF1 hI1
  rw [s21] at hI1
  rw [n2] at hS1 hF1
  have fp1 : ∀ o k, (o, k) ∉ [(VS, PropKey.str (JSStr.ofString "2")), (CS, PropKey.str (JSStr.ofString "current"))] →
      o < s.heap.size → (w1.objEntry o).props.get? k = (s.objEntry o).props.get? k := fun o k hk ho => by
    rw [props_frame hF1 (by js_norm [ho]) (by simpa using hk)]; js_norm [ho]
  have kd1 : ∀ o, o < s.heap.size → (w1.objEntry o).kind = (s.objEntry o).kind := fun o ho => by
    rw [kind_frame hF1 (by js_norm [ho])]; js_norm [ho]
  have z1 : s.heap.size ≤ w1.heap.size := by have := hF1.heap_le; simp only [js_simp] at this; exact this
  have E1 : s.envs.size + 1 ≤ w1.envs.size := by have := hF1.envs_le; simp only [js_simp] at this; exact this
  have hK1 := envEntry_frame hF1 (e := s.envs.size) (by js_norm) (by simp [Nat.ne_of_lt hG])
  simp only [js_simp] at hfu1 hK1
  have hV1' := fp1 VS (.str "1") (by simp [d1, d2, d3, d4, d5, d6, Ne.symm d1, Ne.symm d2, Ne.symm d3, Ne.symm d4, Ne.symm d5, Ne.symm d6] <;> decide) hVS
  have hV0' := fp1 VS (.str "0") (by simp [d1, d2, d3, d4, d5, d6, Ne.symm d1, Ne.symm d2, Ne.symm d3, Ne.symm d4, Ne.symm d5, Ne.symm d6] <;> decide) hVS
  have hVL' := fp1 VS (.str "length") (by simp [d1, d2, d3, d4, d5, d6, Ne.symm d1, Ne.symm d2, Ne.symm d3, Ne.symm d4, Ne.symm d5, Ne.symm d6] <;> decide) hVS
  have hCF1 := fp1 CF (.str "current") (by simp [d1, d2, d3, d4, d5, d6, Ne.symm d1, Ne.symm d2, Ne.symm d3, Ne.symm d4, Ne.symm d5, Ne.symm d6] <;> decide) hCF
  have hRI1 := fp1 RI (.str "current") (by simp [d1, d2, d3, d4, d5, d6, Ne.symm d1, Ne.symm d2, Ne.symm d3, Ne.symm d4, Ne.symm d5, Ne.symm d6] <;> decide) hRI
  have hO1 : w1.objEntry fO = s.objEntry fO := by
    rw [objEntry_frame hF1 (o := fO) (by js_norm [hOo]) (by simp [Ne.symm dO1, Ne.symm dO4, dO1, dO4])]; js_norm [hOo]
  js [hK1, Nat.lt_of_lt_of_le (Nat.lt_succ_self _) E1, Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) E1), hI1,
    hO1, hOk, Nat.lt_of_lt_of_le hOo z1, other_modify, idx_modify hGI, hGCF, hGCFv, hGO, hGOv, Nat.lt_of_lt_of_le hG (Nat.le_trans (Nat.le_succ _) E1),
    hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  -- (pop: slot 1)
  refine ⟨by js_norm [CallableC, hO1, hOk, Nat.lt_of_lt_of_le hOo z1], ?_⟩
  refine wp_mono (ReactStack.pop_spec (bG := bG.modify (JSStr.ofString "index") (fun bd => { bd with value := some (.num (F64.fin false 4503599627370496 (-52))) })) (oG := oG) (bdI := { bdI with value := some (.num (F64.fin false 4503599627370496 (-52))) }) (bdV := bdV) (VS := VS) (Cu := CF)
    (iv := F64.fin false 4503599627370496 (-52)) (L := L) (cur := vf) (saved := o1) (ce := fe) (cc := fc) (oe := e1) (oc := c1) (lw := lw) (le := le)
    (lc := lc) (i := 1) (Nat.lt_of_lt_of_le hOo z1) (by rw [hO1]; exact hOk) (by omega) hOcode hOcls hOmode
    (by rw [hOenv]; exact Nat.lt_of_lt_of_le hG (Nat.le_trans (Nat.le_succ _) E1)) (by rw [hOenv]; exact hI1)
    (idx_modify hGI _) hGIm rfl (by rw [other_modify _ (by decide)]; exact hGV) hGVv
    (Nat.lt_of_lt_of_le hVS z1) (by rw [kd1 VS hVS]; exact hVSk) (Nat.lt_of_lt_of_le hCF z1)
    (by rw [kd1 CF hCF]; exact hCFk) (by assumption) (hCF1.trans hCFc)
    (by rw [n1]; exact hV1'.trans hV1) (by rw [n1]; js_norm) (hVL'.trans hVL) (by omega) (by rw [n1]; decide) (by decide)) ?_
  intro v2 w2 h2 ⟨hv2, hF2, hfu2, hh2, hI2, hS2, hC2⟩
  subst hv2 hh2
  rw [hOenv] at hF2 hI2
  rw [s10] at hI2
  rw [n1] at hS2 hF2
  have fp2 : ∀ o k, (o, k) ∉ [(VS, PropKey.str (JSStr.ofString "1")), (CF, PropKey.str (JSStr.ofString "current"))] →
      o < s.heap.size → (w2.objEntry o).props.get? k = (w1.objEntry o).props.get? k := fun o k hk ho => by
    rw [props_frame hF2 (Nat.lt_of_lt_of_le ho z1) (by simpa using hk)]
  have kd2 : ∀ o, o < s.heap.size → (w2.objEntry o).kind = (s.objEntry o).kind := fun o ho => by
    rw [kind_frame hF2 (Nat.lt_of_lt_of_le ho z1), kd1 o ho]
  have z2 : s.heap.size ≤ w2.heap.size := Nat.le_trans z1 hF2.heap_le
  have E2 : s.envs.size + 1 ≤ w2.envs.size := Nat.le_trans E1 hF2.envs_le
  have hK2 : w2.envEntry s.envs.size = _ := (envEntry_frame hF2 (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) E1)
    (by simp [Nat.ne_of_lt hG])).trans hK1
  have hO2 : w2.objEntry fO = s.objEntry fO := by
    rw [objEntry_frame hF2 (o := fO) (Nat.lt_of_lt_of_le hOo z1) (by simp [d1, d2, d3, d4, d5, d6, Ne.symm d1, Ne.symm d2, Ne.symm d3, Ne.symm d4, Ne.symm d5, Ne.symm d6, dO1, dO2, dO3, dO4, Ne.symm dO1, Ne.symm dO2, Ne.symm dO3, Ne.symm dO4]), hO1]
  have hV0'' := (fp2 VS (.str "0") (by simp [d1, d2, d3, d4, d5, d6, Ne.symm d1, Ne.symm d2, Ne.symm d3, Ne.symm d4, Ne.symm d5, Ne.symm d6, dO1, dO2, dO3, dO4, Ne.symm dO1, Ne.symm dO2, Ne.symm dO3, Ne.symm dO4] <;> decide) hVS).trans hV0'
  have hVL'' := (fp2 VS (.str "length") (by simp [d1, d2, d3, d4, d5, d6, Ne.symm d1, Ne.symm d2, Ne.symm d3, Ne.symm d4, Ne.symm d5, Ne.symm d6, dO1, dO2, dO3, dO4, Ne.symm dO1, Ne.symm dO2, Ne.symm dO3, Ne.symm dO4] <;> decide) hVS).trans hVL'
  have hRI2 := (fp2 RI (.str "current") (by simp [d1, d2, d3, d4, d5, d6, Ne.symm d1, Ne.symm d2, Ne.symm d3, Ne.symm d4, Ne.symm d5, Ne.symm d6, dO1, dO2, dO3, dO4, Ne.symm dO1, Ne.symm dO2, Ne.symm dO3, Ne.symm dO4] <;> decide) hRI).trans hRI1
  have hV2' := (fp2 VS (.str "2") (by simp [d1, d2, d3, d4, d5, d6, Ne.symm d1, Ne.symm d2, Ne.symm d3, Ne.symm d4, Ne.symm d5, Ne.symm d6, dO1, dO2, dO3, dO4, Ne.symm dO1, Ne.symm dO2, Ne.symm dO3, Ne.symm dO4] <;> decide) hVS).trans hS1
  have hCS2 := (fp2 CS (.str "current") (by simp [d1, d2, d3, d4, d5, d6, Ne.symm d1, Ne.symm d2, Ne.symm d3, Ne.symm d4, Ne.symm d5, Ne.symm d6, dO1, dO2, dO3, dO4, Ne.symm dO1, Ne.symm dO2, Ne.symm dO3, Ne.symm dO4] <;> decide) hCS).trans hC1
  js [hK2, Nat.lt_of_lt_of_le (Nat.lt_succ_self _) E2, Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) E2), hI2,
    hO2, hOk, Nat.lt_of_lt_of_le hOo z2, other_modify, hGRI, hGRIv, hGO, hGOv, Nat.lt_of_lt_of_le hG (Nat.le_trans (Nat.le_succ _) E2),
    hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  -- (pop: slot 0)
  refine ⟨by js_norm [CallableC, hO2, hOk, Nat.lt_of_lt_of_le hOo z2], ?_⟩
  refine wp_mono (ReactStack.pop_spec (bG := (bG.modify (JSStr.ofString "index") (fun bd => { bd with value := some (.num (F64.fin false 4503599627370496 (-52))) })).modify (JSStr.ofString "index") (fun bd => { bd with value := some (.num (F64.fin false 0 (-1074))) })) (oG := oG) (bdI := { bdI with value := some (.num (F64.fin false 0 (-1074))) }) (bdV := bdV) (VS := VS) (Cu := RI)
    (iv := F64.fin false 0 (-1074)) (L := L) (cur := vr) (saved := o0) (ce := re) (cc := rc) (oe := e0) (oc := c0) (lw := lw) (le := le)
    (lc := lc) (i := 0) (Nat.lt_of_lt_of_le hOo z2) (by rw [hO2]; exact hOk) (by omega) hOcode hOcls hOmode
    (by rw [hOenv]; exact Nat.lt_of_lt_of_le hG (Nat.le_trans (Nat.le_succ _) E2)) (by rw [hOenv]; exact hI2)
    (idx_modify (idx_modify hGI _) _) hGIm rfl (by rw [other_modify _ (by decide)] ; rw [other_modify _ (by decide)]; exact hGV) hGVv
    (Nat.lt_of_lt_of_le hVS z2) (by rw [kd2 VS hVS]; exact hVSk) (Nat.lt_of_lt_of_le hRI z2)
    (by rw [kd2 RI hRI]; exact hRIk) (by assumption) (hRI2.trans hRIc)
    (by rw [n0]; exact hV0''.trans hV0) (by rw [n0]; js_norm) (hVL''.trans hVL) (by omega) (by rw [n0]; decide) (by decide)) ?_
  intro v3 w3 h3 ⟨hv3, hF3, hfu3, hh3, hI3, hS3, hC3⟩
  subst hv3 hh3
  rw [hOenv] at hF3 hI3
  rw [s0m] at hI3
  rw [n0] at hS3 hF3
  have fp3 : ∀ o k, (o, k) ∉ [(VS, PropKey.str (JSStr.ofString "0")), (RI, PropKey.str (JSStr.ofString "current"))] →
      o < s.heap.size → (w3.objEntry o).props.get? k = (w2.objEntry o).props.get? k := fun o k hk ho => by
    rw [props_frame hF3 (Nat.lt_of_lt_of_le ho z2) (by simpa using hk)]
  have kd3 : ∀ o, o < s.heap.size → (w3.objEntry o).kind = (s.objEntry o).kind := fun o ho => by
    rw [kind_frame hF3 (Nat.lt_of_lt_of_le ho z2), kd2 o ho]
  have z3 : s.heap.size ≤ w3.heap.size := Nat.le_trans z2 hF3.heap_le
  have E3 : s.envs.size + 1 ≤ w3.envs.size := Nat.le_trans E2 hF3.envs_le
  have hK3 : w3.envEntry s.envs.size = _ := (envEntry_frame hF3 (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) E2)
    (by simp [Nat.ne_of_lt hG])).trans hK2
  have hO3 : w3.objEntry fO = s.objEntry fO := by
    rw [objEntry_frame hF3 (o := fO) (Nat.lt_of_lt_of_le hOo z2) (by simp [d1, d2, d3, d4, d5, d6, Ne.symm d1, Ne.symm d2, Ne.symm d3, Ne.symm d4, Ne.symm d5, Ne.symm d6, dO1, dO2, dO3, dO4, Ne.symm dO1, Ne.symm dO2, Ne.symm dO3, Ne.symm dO4]), hO2]
  have hV2'' := (fp3 VS (.str "2") (by simp [d1, d2, d3, d4, d5, d6, Ne.symm d1, Ne.symm d2, Ne.symm d3, Ne.symm d4, Ne.symm d5, Ne.symm d6, dO1, dO2, dO3, dO4, Ne.symm dO1, Ne.symm dO2, Ne.symm dO3, Ne.symm dO4] <;> decide) hVS).trans hV2'
  have hV1'' := (fp3 VS (.str "1") (by simp [d1, d2, d3, d4, d5, d6, Ne.symm d1, Ne.symm d2, Ne.symm d3, Ne.symm d4, Ne.symm d5, Ne.symm d6, dO1, dO2, dO3, dO4, Ne.symm dO1, Ne.symm dO2, Ne.symm dO3, Ne.symm dO4] <;> decide) hVS).trans hS2
  have hCS3 := (fp3 CS (.str "current") (by simp [d1, d2, d3, d4, d5, d6, Ne.symm d1, Ne.symm d2, Ne.symm d3, Ne.symm d4, Ne.symm d5, Ne.symm d6, dO1, dO2, dO3, dO4, Ne.symm dO1, Ne.symm dO2, Ne.symm dO3, Ne.symm dO4] <;> decide) hCS).trans hCS2
  have hCF3 := (fp3 CF (.str "current") (by simp [d1, d2, d3, d4, d5, d6, Ne.symm d1, Ne.symm d2, Ne.symm d3, Ne.symm d4, Ne.symm d5, Ne.symm d6, dO1, dO2, dO3, dO4, Ne.symm dO1, Ne.symm dO2, Ne.symm dO3, Ne.symm dO4] <;> decide) hCF).trans hC2
  js [hK3, Nat.lt_of_lt_of_le (Nat.lt_succ_self _) E3, Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) E3),
    hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  have gB : Frame (fpHC d.env VS CS CF RI) s (bodyState s fo d t #[]) :=
    frame_mono (frame_bodyState (frame_refl ({} : Footprint) s) fo d t _) (by simp) (by simp) (fun _ => rfl)
  have FW1 := frame_extend' gB hF1 (fun q hq _ => by simp at hq; simp [fpHC, hq])
    (fun q hq _ => by simp at hq; rcases hq with hq | hq <;> simp [fpHC, hq]) (fun _ => rfl)
  have FW2 := frame_extend' FW1 hF2 (fun q hq _ => by simp at hq; simp [fpHC, hq])
    (fun q hq _ => by simp at hq; rcases hq with hq | hq <;> simp [fpHC, hq]) (fun _ => rfl)
  have FW3 := frame_extend' FW2 hF3 (fun q hq _ => by simp at hq; simp [fpHC, hq])
    (fun q hq _ => by simp at hq; rcases hq with hq | hq <;> simp [fpHC, hq]) (fun _ => rfl)
  (try simp only [js_simp] at hfu2); (try simp only [js_simp] at hfu3)
  refine And.intro (frame_restore FW3 s) (And.intro (by omega) (And.intro rfl ?_))
  refine Exists.intro _ (And.intro rfl ?_)
  all_goals (repeat' apply And.intro)
  · exact Exists.intro { bdI with value := some (.num (F64.fin true 4503599627370496 (-52))) }
      (And.intro (by simp [Std.HashMap.getElem?_modify, hGI]) (And.intro rfl hGIm))
  · intro x hx; simp [Std.HashMap.getElem?_modify, Ne.symm hx]
  all_goals first | assumption | rfl

end

end ReactRootPops
