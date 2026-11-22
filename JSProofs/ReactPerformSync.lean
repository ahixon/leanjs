import JSProofs.ReactNoEffects
import JSProofs.ReactDSSI
import JSProofs.PSWGen

/-!
# React's `performSyncWorkOnRoot` after a click (zippy docs/react-proofs.md)

```js
function performSyncWorkOnRoot(root, lanes) {
  if (flushPendingEffects()) return null;
  performWorkOnRoot(root, lanes, !0);
}
```
No effects pending (`flushPendingEffects` by its theorem: false), so the render runs: `performWorkOnRoot(root, lanes,
true)` (a hypothesis here).
-/

open ES ES.M HostRuns Logic
open Std (HashMap)

namespace ReactPerformSync

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ}

theorem simple (d : FuncData) (hc : d.code = PSWGen.performSyncWorkOnRoot_func) : FDI.Simple d := by
  constructor <;> rw [hc] <;> try rfl
  simp [PSWGen.performSyncWorkOnRoot_func, Func.params, Func.info]

set_option maxRecDepth 10000 in
theorem call_spec {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t root lanes : Value} {s : State}
    {bG : HashMap JSStr Binding} {oG : Option EnvId}
    {bdF bdW bdS bdV bdM bdL bdP bdX : Binding} {fF fW fM fL fX fP : ObjId} {dF dW dM dL dX dP : FuncData}
    {Q : State → σ → Prop} {fpW : Footprint} {kW : Nat}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : 100 ≤ s.fuel)
    (hcode : d.code = PSWGen.performSyncWorkOnRoot_func) (hcls : d.isClassCtor = false) (hmode : d.thisMode = .strict)
    (hG : d.env < s.envs.size) (hGe : Scope.declLike? (s.envEntry d.env) = some (bG, oG))
    (hGF : bG[JSStr.ofString "flushPendingEffects"]? = some bdF) (hGFv : bdF.value = some (.obj fF))
    (hGW : bG[JSStr.ofString "performWorkOnRoot"]? = some bdW) (hGWv : bdW.value = some (.obj fW))
    (hFo : fF < s.heap.size) (hFk : (s.objEntry fF).kind = .func dF)
    (hFcode : dF.code = FPEGen.flushPendingEffects_func) (hFcls : dF.isClassCtor = false)
    (hFmode : dF.thisMode = .strict) (hFenv : dF.env = d.env)
    (hWo : fW < s.heap.size) (hWk : (s.objEntry fW).kind = .func dW)
    -- (`flushPendingEffects`'s premises)
    (hGS : bG[JSStr.ofString "pendingEffectsStatus"]? = some bdS)
    (hGSv : bdS.value = some (.num (F64.fin false 0 (-1074))))
    (hGV : bG[JSStr.ofString "pendingViewTransition"]? = some bdV) (hGVv : bdV.value = some .null)
    (hGM : bG[JSStr.ofString "flushMutationEffects"]? = some bdM) (hGMv : bdM.value = some (.obj fM))
    (hGL : bG[JSStr.ofString "flushLayoutEffects"]? = some bdL) (hGLv : bdL.value = some (.obj fL))
    (hGX : bG[JSStr.ofString "flushSpawnedWork"]? = some bdX) (hGXv : bdX.value = some (.obj fX))
    (hGP : bG[JSStr.ofString "flushPassiveEffects"]? = some bdP) (hGPv : bdP.value = some (.obj fP))
    (hMo : fM < s.heap.size) (hMk : (s.objEntry fM).kind = .func dM) (hMcode : dM.code = FMEGen.flushMutationEffects_func)
    (hMcls : dM.isClassCtor = false) (hMmode : dM.thisMode = .strict) (hMenv : dM.env = d.env)
    (hLo : fL < s.heap.size) (hLk : (s.objEntry fL).kind = .func dL) (hLcode : dL.code = FLEGen.flushLayoutEffects_func)
    (hLcls : dL.isClassCtor = false) (hLmode : dL.thisMode = .strict) (hLenv : dL.env = d.env)
    (hXo : fX < s.heap.size) (hXk : (s.objEntry fX).kind = .func dX) (hXcode : dX.code = FSPGen.flushSpawnedWork_func)
    (hXcls : dX.isClassCtor = false) (hXmode : dX.thisMode = .strict) (hXenv : dX.env = d.env)
    (hPo : fP < s.heap.size) (hPk : (s.objEntry fP).kind = .func dP) (hPcode : dP.code = FPAGen.flushPassiveEffects_func)
    (hPcls : dP.isClassCtor = false) (hPmode : dP.thisMode = .strict) (hPenv : dP.env = d.env)
    -- (`performWorkOnRoot(root, lanes, true)`)
    (hWork : ∀ w h1, Frame {} s w → s.fuel ≤ w.fuel + 70 →
      WP eng answer (n + 1) h1 (callImpl eng (.obj fW) .undefined #[root, lanes, .bool true]) w fun _ w' h' =>
        Frame fpW w w' ∧ w.fuel ≤ w'.fuel + kW ∧ Q (w'.restore s) h')
    (hfpWB : fpW.binds.all (fun q => decide (q.1 < s.envs.size)) = true) :
    WP eng answer (n + 2) h (callImpl eng (.obj fo) t #[root, lanes]) s fun v w h' =>
      v = .undefined ∧ Frame fpW s w ∧ s.fuel ≤ w.fuel + kW + 100 ∧ Q w h' := by
  replace hWork := ReactDSSI.Hold.mk hWork
  apply wp_callGen PSWGen.performSyncWorkOnRoot_eq (by decide) hlt hk (by omega) hcls hmode
    (by rw [hcode]; rfl) (by rw [hcode]; rfl) (simple d hcode) (by rw [hcode]; rfl) (by rw [hcode]; rfl)
  have hpn : d.code.info.fdi.paramNames = #[JSStr.ofString "root", JSStr.ofString "lanes"] := by rw [hcode]; rfl
  have hv : d.code.info.fdi.varNames = #[] := by rw [hcode]; rfl
  have hl : FDI.lexDecls d = #[] := by simp [FDI.lexDecls, hcode, PSWGen.performSyncWorkOnRoot_func, Func.info]
  have ha : d.code.isAsync = false := by rw [hcode]; rfl
  have hne : s.envs.size ≠ d.env := Nat.ne_of_gt hG
  have hG1 : d.env < s.envs.size + 1 := Nat.lt_succ_of_lt hG
  clear hcode
  simp only [PSWGen.performSyncWorkOnRoot]
  js [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGF, hGFv, hFo, hFk, FDI.fdiCtx, Sem.inner]
  refine ⟨by js_norm [CallableC, *], ?_⟩
  refine wp_mono (ReactNoEffects.pending_none (n := n) (by simpa using hFo) (by simpa using hFk) (by simp; omega)
    hFcode hFcls hFmode (by rw [hFenv]; simp; omega) (by rw [hFenv]; js_norm [*, Ne.symm hne]; rfl) hGS hGSv hGV hGVv
    hGM hGMv hGL hGLv hGX hGXv hGP hGPv (by simpa using hMo) (by simpa using hMk) hMcode hMcls hMmode
    (by rw [hMenv, hFenv]) (by simpa using hLo) (by simpa using hLk) hLcode hLcls hLmode (by rw [hLenv, hFenv])
    (by simpa using hXo) (by simpa using hXk) hXcode hXcls hXmode (by rw [hXenv, hFenv]) (by simpa using hPo)
    (by simpa using hPk) hPcode hPcls hPmode (by rw [hPenv, hFenv])) ?p1
  case p1 =>
  intro r w1 h1 ⟨hr, hF1, hfu1⟩
  subst hr
  try simp only [js_simp] at hfu1
  js [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGW, hGWv, hWo, hWk, envEntry_frame0 hF1, objEntry_frame0 hF1,
    heap_frame hF1, envs_frame hF1, FDI.fdiCtx, Sem.inner]
  refine ⟨by js_norm [CallableC, *, objEntry_frame0 hF1, heap_frame hF1], ?_⟩
  refine wp_mono ((ReactDSSI.Hold.get hWork) _ h1 ?fr ?fu) ?post
  case fr => frame_go' [*, hne, Ne.symm hne, hG1]
  case fu => simp at hfu1 ⊢; omega
  case post =>
    intro b w2 h2 ⟨hF2, hfu2, hQ⟩
    have hE1s : s.envs.size < w1.envs.size := envs_frame hF1 (by simp)
    have hE2 := envEntry_frame hF2 (e := s.envs.size) (by first | exact hE1s | (simp only [js_simp]; exact hE1s))
      (binds_avoid hfpWB (Nat.le_refl _))
    js [FDI.fdiCtx, Sem.inner, hQ, hE2]
    all_goals (try apply And.intro)
    all_goals (try apply And.intro)
    all_goals (try apply And.intro)
    all_goals first | rfl | exact hQ | omega | (simp only [js_simp] at *; omega) | skip
    frame_go' [*, hne, Ne.symm hne, hG1]

end

end ReactPerformSync
