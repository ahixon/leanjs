import JSProofs.MRFGen
import JSProofs.MathRules
import JSProofs.Setter
import JSProofs.ReactHostContainer
import JSProofs.Rebase
import JSProofs.Loops4

/-!
# markRootFinished for the click's commit (zippy docs/react-proofs.md)

`markRootFinished(root, SyncLane, 0, 0, 0, 0)` with SyncLane the only pending lane: the root's lane fields cleared,
lane 1's entanglement and expiration time reset (`hiddenUpdates[1]` null), nothing spawned or suspended.
-/

open ES ES.M HostRuns Logic
open Std (HashMap)

namespace ReactMarkFinished

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ}

/-- What `markRootFinished` writes: the root's lane fields and lane 1 of its entanglements and expiration times. -/
def FPM (FR EA XA : ObjId) : Footprint :=
  ⟨[], [(FR, .str (JSStr.ofString "pendingLanes")), (FR, .str (JSStr.ofString "suspendedLanes")),
    (FR, .str (JSStr.ofString "pingedLanes")), (FR, .str (JSStr.ofString "warmLanes")),
    (FR, .str (JSStr.ofString "expiredLanes")), (FR, .str (JSStr.ofString "entangledLanes")),
    (FR, .str (JSStr.ofString "errorRecoveryDisabledLanes")), (FR, .str (JSStr.ofString "shellSuspendCounter")),
    (EA, .str (JSStr.ofString "1")), (XA, .str (JSStr.ofString "1"))], false⟩

theorem simple (d : FuncData) (hc : d.code = MRFGen.markRootFinished_func) : FDI.Simple d := by
  constructor <;> rw [hc] <;> try rfl
  simp [MRFGen.markRootFinished_func, Func.params, Func.info]

set_option maxRecDepth 40000 in
set_option maxHeartbeats 8000000 in
theorem mrf_spec {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t : Value} {s : State}
    {bG : HashMap JSStr Binding} {oG : Option EnvId} {bdZ : Binding} {fZ : ObjId} {bdz : BuiltinData}
    {FR EA XA HA : ObjId} {xl el rl : F64}
    {pw pe pc sw se sc gw ge gc ww we wc xw xe xc ew ee ec rw re rc cw ce cc aw ae ac bw be bc dw de dc
      e1w e1e e1c x1w x1e x1c h1w h1e h1c : Bool} {sv gv wv cv ev1 xv1 : Value} {eL xL : F64}
    {lew lee lec lxw lxe lxc : Bool}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : 300 ≤ s.fuel)
    (hcode : d.code = MRFGen.markRootFinished_func) (hcls : d.isClassCtor = false) (hmode : d.thisMode = .strict)
    (hG : d.env < s.envs.size) (hGe : Scope.declLike? (s.envEntry d.env) = some (bG, oG))
    (hGZ : bG[JSStr.ofString "clz32"]? = some bdZ) (hGZv : bdZ.value = some (.obj fZ))
    (hZo : fZ < s.heap.size) (hZk : (s.objEntry fZ).kind = .builtin bdz)
    (hZfn : eng.builtins[bdz.id]? = some (ES.Builtins.Text.mathFn1 (fun x => Num.ofNat (Num.clz32 x))))
    (hFR : FR < s.heap.size) (hFRk : (s.objEntry FR).kind.isPlain = true)
    (hpl : (s.objEntry FR).props.get? (.str (JSStr.ofString "pendingLanes")) =
      some (.data (.num (F64.fin false 4503599627370496 (-51))) true pe pc))
    (hsl : (s.objEntry FR).props.get? (.str (JSStr.ofString "suspendedLanes")) = some (.data sv true se sc))
    (hgl : (s.objEntry FR).props.get? (.str (JSStr.ofString "pingedLanes")) = some (.data gv true ge gc))
    (hwl : (s.objEntry FR).props.get? (.str (JSStr.ofString "warmLanes")) = some (.data wv true we wc))
    (hxl : (s.objEntry FR).props.get? (.str (JSStr.ofString "expiredLanes")) = some (.data (.num xl) true xe xc))
    (hel : (s.objEntry FR).props.get? (.str (JSStr.ofString "entangledLanes")) = some (.data (.num el) true ee ec))
    (hrl : (s.objEntry FR).props.get? (.str (JSStr.ofString "errorRecoveryDisabledLanes")) =
      some (.data (.num rl) true re rc))
    (hcl : (s.objEntry FR).props.get? (.str (JSStr.ofString "shellSuspendCounter")) = some (.data cv true ce cc))
    (hea : (s.objEntry FR).props.get? (.str (JSStr.ofString "entanglements")) = some (.data (.obj EA) aw ae ac))
    (hxa : (s.objEntry FR).props.get? (.str (JSStr.ofString "expirationTimes")) = some (.data (.obj XA) bw be bc))
    (hha : (s.objEntry FR).props.get? (.str (JSStr.ofString "hiddenUpdates")) = some (.data (.obj HA) dw de dc))
    (hEA : EA < s.heap.size) (hEAk : (s.objEntry EA).kind = .array)
    (hEA1 : (s.objEntry EA).props.get? (.str (JSStr.ofString "1")) = some (.data ev1 true e1e e1c))
    (hEAl : (s.objEntry EA).props.get? (.str (JSStr.ofString "length")) = some (.data (.num eL) lew lee lec))
    (hEAL : 1 < (Conv.toNat? eL).getD 0)
    (hXA : XA < s.heap.size) (hXAk : (s.objEntry XA).kind = .array)
    (hXA1 : (s.objEntry XA).props.get? (.str (JSStr.ofString "1")) = some (.data xv1 true x1e x1c))
    (hXAl : (s.objEntry XA).props.get? (.str (JSStr.ofString "length")) = some (.data (.num xL) lxw lxe lxc))
    (hXAL : 1 < (Conv.toNat? xL).getD 0)
    (hHA : HA < s.heap.size) (hHAk : (s.objEntry HA).kind = .array)
    (hHA1 : (s.objEntry HA).props.get? (.str (JSStr.ofString "1")) = some (.data .null h1w h1e h1c))
    (dFE : FR ≠ EA) (dFX : FR ≠ XA) (dEX : EA ≠ XA) (dFH : FR ≠ HA) (dEH : EA ≠ HA) (dXH : XA ≠ HA)
    (dFZ : FR ≠ fZ) (dEZ : EA ≠ fZ) (dXZ : XA ≠ fZ) (dHZ : HA ≠ fZ) :
    WP eng answer (n + 2) h (callImpl eng (.obj fo) t #[.obj FR, .num (F64.fin false 4503599627370496 (-51)),
      .num (F64.fin false 0 (-1074)), .num (F64.fin false 0 (-1074)), .num (F64.fin false 0 (-1074)),
      .num (F64.fin false 0 (-1074))]) s fun v w h' => v = .undefined ∧
      (w.objEntry FR).props.get? (.str (JSStr.ofString "pendingLanes")) =
        some (.data (.num (F64.fin false 0 (-1074))) true pe pc) ∧
      Frame (FPM FR EA XA) s w ∧ s.fuel ≤ w.fuel + 300 ∧ h' = h := by
  apply wp_callGen MRFGen.markRootFinished_eq (by decide) hlt hk (by omega) hcls hmode
    (by rw [hcode]; rfl) (by rw [hcode]; rfl) (simple d hcode) (by rw [hcode]; rfl) (by rw [hcode]; rfl)
  have hpn : d.code.info.fdi.paramNames = #[JSStr.ofString "root", JSStr.ofString "finishedLanes",
    JSStr.ofString "remainingLanes", JSStr.ofString "spawnedLane", JSStr.ofString "updatedLanes",
    JSStr.ofString "suspendedRetryLanes"] := by rw [hcode]; rfl
  have hv : d.code.info.fdi.varNames = #[JSStr.ofString "previouslyPendingLanes", JSStr.ofString "entanglements",
    JSStr.ofString "expirationTimes", JSStr.ofString "hiddenUpdates", JSStr.ofString "index$7", JSStr.ofString "lane",
    JSStr.ofString "hiddenUpdatesForLane", JSStr.ofString "update"] := by rw [hcode]; rfl
  have hl : FDI.lexDecls d = #[] := by simp [FDI.lexDecls, hcode, MRFGen.markRootFinished_func, Func.info]
  have ha : d.code.isAsync = false := by rw [hcode]; rfl
  have e1 : d.env ≠ s.envs.size := Nat.ne_of_lt hG
  have e1' : s.envs.size ≠ d.env := Ne.symm e1
  have e4 : d.env < s.envs.size + 1 := Nat.lt_succ_of_lt hG
  clear hcode
  simp only [MRFGen.markRootFinished]
  js_until [] [e1, e1', e4, hG, hGe, hGZ, hGZv, hZo, hZk, hFR, hFRk, hpl, hsl, hgl, hwl, hxl, hel, hrl, hcl, hea, hxa, hha, dFE, Ne.symm dFE, dFX, Ne.symm dFX, dEX, Ne.symm dEX, dFH, Ne.symm dFH, dEH, Ne.symm dEH, dXH, Ne.symm dXH, dFZ, Ne.symm dFZ, dEZ, Ne.symm dEZ, dXZ, Ne.symm dXZ, dHZ, Ne.symm dHZ, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  refine wp_forExpr ?_
  js_until [] [e1, e1', e4, hG, hGe, hGZ, hGZv, hZo, hZk, hFR, hFRk, hpl, hsl, hgl, hwl, hxl, hel, hrl, hcl, hea, hxa, hha, dFE, Ne.symm dFE, dFX, Ne.symm dFX, dEX, Ne.symm dEX, dFH, Ne.symm dFH, dEH, Ne.symm dEH, dXH, Ne.symm dXH, dFZ, Ne.symm dFZ, dEZ, Ne.symm dEZ, dXZ, Ne.symm dXZ, dHZ, Ne.symm dHZ, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  refine ⟨by js_norm [CallableC, e1, e1', e4, hG, hGe, hGZ, hGZv, hZo, hZk, hFR, hFRk, hpl, hsl, hgl, hwl, hxl, hel, hrl, hcl, hea, hxa, hha, dFE, Ne.symm dFE, dFX, Ne.symm dFX, dEX, Ne.symm dEX, dFH, Ne.symm dFH, dEH, Ne.symm dEH, dXH, Ne.symm dXH, dFZ, Ne.symm dFZ, dEZ, Ne.symm dEZ, dXZ, Ne.symm dXZ, dHZ, Ne.symm dHZ, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner], wp_mono (mathFn1_spec (by js_norm [e1, e1', e4, hG, hGe, hGZ, hGZv, hZo, hZk, hFR, hFRk, hpl, hsl, hgl, hwl, hxl, hel, hrl, hcl, hea, hxa, hha, dFE, Ne.symm dFE, dFX, Ne.symm dFX, dEX, Ne.symm dEX, dFH, Ne.symm dFH, dEH, Ne.symm dEH, dXH, Ne.symm dXH, dFZ, Ne.symm dFZ, dEZ, Ne.symm dEZ, dXZ, Ne.symm dXZ, dHZ, Ne.symm dHZ, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]) (by js_norm [e1, e1', e4, hG, hGe, hGZ, hGZv, hZo, hZk, hFR, hFRk, hpl, hsl, hgl, hwl, hxl, hel, hrl, hcl, hea, hxa, hha, dFE, Ne.symm dFE, dFX, Ne.symm dFX, dEX, Ne.symm dEX, dFH, Ne.symm dFH, dEH, Ne.symm dEH, dXH, Ne.symm dXH, dFZ, Ne.symm dFZ, dEZ, Ne.symm dEZ, dXZ, Ne.symm dXZ, dHZ, Ne.symm dHZ, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]) hZfn
    (by show s.fuel - 1 - 1 ≠ 0; omega)) ?_⟩
  rintro v1 w1 h1 ⟨rfl, hF1, hfu1, rfl⟩
  have n31 : numberBinOp .sub (F64.fin false 8725724278030336 (-48)) (F64.fin false 8444249301319680 (-48)) =
    F64.fin false 4503599627370496 (-52) := by decide +kernel
  have nstr : numberToJSStr (F64.fin false 4503599627370496 (-52)) = JSStr.ofString "1" := by decide +kernel
  have nshl : numberBinOp .shl (F64.fin false 4503599627370496 (-52)) (F64.fin false 4503599627370496 (-52)) =
    F64.fin false 4503599627370496 (-51) := by decide +kernel
  have hfw1 : 100 ≤ w1.fuel := by have := hfu1; change s.fuel - 1 - 1 ≤ w1.fuel + 1 at this; omega
  have hE1 := envEntry_frame0 hF1 (e := s.envs.size) (by js_norm [e1, e1', e4, hG, hGe, hGZ, hGZv, hZo, hZk, hFR, hFRk, hpl, hsl, hgl, hwl, hxl, hel, hrl, hcl, hea, hxa, hha, dFE, Ne.symm dFE, dFX, Ne.symm dFX, dEX, Ne.symm dEX, dFH, Ne.symm dFH, dEH, Ne.symm dEH, dXH, Ne.symm dXH, dFZ, Ne.symm dFZ, dEZ, Ne.symm dEZ, dXZ, Ne.symm dXZ, dHZ, Ne.symm dHZ, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner])
  have hEd1 := envEntry_frame0 hF1 (e := d.env) (by js_norm [e1, e1', e4, hG, hGe, hGZ, hGZv, hZo, hZk, hFR, hFRk, hpl, hsl, hgl, hwl, hxl, hel, hrl, hcl, hea, hxa, hha, dFE, Ne.symm dFE, dFX, Ne.symm dFX, dEX, Ne.symm dEX, dFH, Ne.symm dFH, dEH, Ne.symm dEH, dXH, Ne.symm dXH, dFZ, Ne.symm dFZ, dEZ, Ne.symm dEZ, dXZ, Ne.symm dXZ, dHZ, Ne.symm dHZ, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner])
  have hS1 : s.envs.size < w1.envs.size := Nat.lt_of_lt_of_le (by js_norm [e1, e1', e4, hG, hGe, hGZ, hGZv, hZo, hZk, hFR, hFRk, hpl, hsl, hgl, hwl, hxl, hel, hrl, hcl, hea, hxa, hha, dFE, Ne.symm dFE, dFX, Ne.symm dFX, dEX, Ne.symm dEX, dFH, Ne.symm dFH, dEH, Ne.symm dEH, dXH, Ne.symm dXH, dFZ, Ne.symm dFZ, dEZ, Ne.symm dEZ, dXZ, Ne.symm dXZ, dHZ, Ne.symm dHZ, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]) hF1.envs_le
  have hGd1 : d.env < w1.envs.size := Nat.lt_trans hG hS1
  have hob1 : ∀ o, o < s.heap.size → w1.objEntry o = _ := fun o ho => objEntry_frame0 hF1 (by js_norm [ho, e1, e1', e4, hG, hGe, hGZ, hGZv, hZo, hZk, hFR, hFRk, hpl, hsl, hgl, hwl, hxl, hel, hrl, hcl, hea, hxa, hha, dFE, Ne.symm dFE, dFX, Ne.symm dFX, dEX, Ne.symm dEX, dFH, Ne.symm dFH, dEH, Ne.symm dEH, dXH, Ne.symm dXH, dFZ, Ne.symm dFZ, dEZ, Ne.symm dEZ, dXZ, Ne.symm dXZ, dHZ, Ne.symm dHZ, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner])
  have hlt1 : ∀ o, o < s.heap.size → o < w1.heap.size := fun o ho =>
    Nat.lt_of_lt_of_le (by js_norm [ho, e1, e1', e4, hG, hGe, hGZ, hGZv, hZo, hZk, hFR, hFRk, hpl, hsl, hgl, hwl, hxl, hel, hrl, hcl, hea, hxa, hha, dFE, Ne.symm dFE, dFX, Ne.symm dFX, dEX, Ne.symm dEX, dFH, Ne.symm dFH, dEH, Ne.symm dEH, dXH, Ne.symm dXH, dFZ, Ne.symm dFZ, dEZ, Ne.symm dEZ, dXZ, Ne.symm dXZ, dHZ, Ne.symm dHZ, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]) hF1.heap_le
  js_until [] [n31, nstr, nshl, hE1, hS1, hGd1, hEd1, hob1 EA hEA, hob1 XA hXA, hob1 HA hHA, hob1 FR hFR, hlt1 EA hEA, hlt1 XA hXA, hlt1 HA hHA, hfw1, hEA, hEAk, hEA1, hEAl, hEAL, hXA, hXAk, hXA1, hXAl, hXAL, hHA, hHAk, hHA1, e1, e1', e4, hG, hGe, hGZ, hGZv, hZo, hZk, hFR, hFRk, hpl, hsl, hgl, hwl, hxl, hel, hrl, hcl, hea, hxa, hha, dFE, Ne.symm dFE, dFX, Ne.symm dFX, dEX, Ne.symm dEX, dFH, Ne.symm dFH, dEH, Ne.symm dEH, dXH, Ne.symm dXH, dFZ, Ne.symm dFZ, dEZ, Ne.symm dEZ, dXZ, Ne.symm dXZ, dHZ, Ne.symm dHZ, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]

  refine ⟨?_, by have := hfu1; change s.fuel - 1 - 1 ≤ w1.fuel + 1 at this; show s.fuel ≤ w1.fuel - 1 + 300; omega⟩
  unfold FPM
  refine frame_restore ?_ _
  refine frame_withFuel ?_ _
  refine frame_setEnv_new ?_ (Nat.le_refl _) _
  refine frame_setProp_in ?_ hXA (by simp) _
  refine frame_setProp_in ?_ hEA (by simp) _
  refine frame_setEnv_new ?_ (Nat.le_refl _) _
  refine frame_then_empty ?_ hF1
  frame_go' [hFR]
end

end ReactMarkFinished
