"""Generates JSProofs/ReactSpawnedFull.lean (zippy docs/react-proofs.md): fsp_spec with releaseRootPooledCache
(rrp_spec, premises L_), lanesToEventPriority (ltep_sync, T_), flushPendingEffects (pending_none, P_) and
flushSyncWorkAcrossRoots_impl (fsw_flushing, W_) and ensureRootIsScheduled (en_call, E_) discharged at the call states. requestPaint
stays a contract (the scheduler's)."""
import sys
sys.path.insert(0, "tools/react_commit")
from compose import binders, compose

SP = "JSProofs/ReactSpawned.lean"
SC = "JSProofs/ReactSpawnedCallees.lean"
NE = "JSProofs/ReactNoEffects.lean"
fb = binders(SP, "fsp_spec")
drop_outer = {"hRel", "hLP", "hPE", "hFSs", "hRelc", "hLPc", "hPEc", "hFSc", "K", "hK", "hEn", "hEnc", "fpE", "hfpE", "hfpEp"}
FPEN = "(ReactEnsureCall.fpEn d.env)"
outer = [f"{k}{nm} : {t}{'}' if k == '{' else ')'}" for nm, k, t in fb if nm not in drop_outer]
outer = [b.replace("WP eng answer (n + 1) h1 (callImpl eng (.obj fRP)", "WP eng answer (n + 3) h1 (callImpl eng (.obj fRP)").replace("fpE", FPEN).replace("K ≤ w.fuel", "60 ≤ w.fuel").replace("w.fuel ≤ w'.fuel + K", "w.fuel ≤ w'.fuel + 60") for b in outer]
L, _ = compose(SC, "rrp_spec", "L_", subst={"fo": "fRel", "t": ".undefined", "FR": "FR"}, given={},
               drop=("n", "h", "s", "hf", "hlt", "hFR", "hFRk"))
T, _ = compose(SC, "ltep_sync", "T_", subst={"fo": "fLP", "t": ".undefined"}, given={}, drop=("n", "h", "s", "hf", "hlt"))
P, _ = compose(NE, "pending_none", "P_", subst={"fo": "fPE", "t": ".undefined", "bG": "bG", "oG": "oG"}, given={},
               drop=("n", "h", "s", "hf", "hlt", "hG", "hGe", "hGS", "hGSv", "hGV", "hGVv", "bdS", "bdV"))
EC = "JSProofs/ReactEnsureCall.lean"
E, _ = compose(EC, "en_call", "E_", subst={"fo": "fEn", "t": ".undefined", "bG": "bG", "oG": "oG", "R": "FR"}, given={},
               drop=("n", "h", "s", "hf", "hlt", "hG", "hGe", "hR", "hRk"))
W, _ = compose(SC, "fsw_flushing", "W_", subst={"fo": "fFS", "t": ".undefined", "bG": "bG", "oG": "oG"}, given={},
               drop=("n", "h", "s", "hf", "hlt", "hG", "hGe"))
extra = ["(hf : 760 ≤ s.fuel)", "(P_hdenv : P_d.env = d.env)", "(W_hdenv : W_d.env = d.env)",
         "(E_hdenv : E_d.env = d.env)"]
binds = "\n    ".join(outer + L + T + P + W + E + extra)
fargs = " ".join(f"({nm} := {nm})" for nm, k, t in fb if nm not in drop_outer and nm not in ("n", "h", "s"))
def imps(path, thm, pre, skip):
    return " ".join(f"({nm} := {pre}{nm})" for nm, k, t in binders(path, thm) if k == "{" and nm not in skip)
l_imp = imps(SC, "rrp_spec", "L_", ("n", "h", "s", "fo", "t", "FR"))
p_imp = imps(NE, "pending_none", "P_", ("n", "h", "s", "fo", "t", "bG", "oG", "bdS", "bdV"))
w_imp = imps(SC, "fsw_flushing", "W_", ("n", "h", "s", "fo", "t", "bG", "oG"))
e_imp = imps(EC, "en_call", "E_", ("n", "h", "s", "fo", "t", "bG", "oG", "R"))
RB = "first | rebase_quick hw | (rw [hbw _ (by simp [FPA, FPS, Footprint.union])] <;> with_reducible assumption) | (rw [kind_frame hw (by with_reducible assumption)] <;> with_reducible assumption)"
stmt = f"""theorem fsp_full {binds} :
    WP eng answer (n + 4) h (callImpl eng (.obj fo) t #[]) s fun v w h' =>
      v = .undefined ∧ s.fuel ≤ w.fuel + 6 * 60 + 400 ∧ h' = h ∧ Frame ((FPA d.env gP FR).union {FPEN}) s w ∧
        Done w d.env oG FR bFSR bEn fEn := by
  refine fsp_spec (n := n + 2) (K := 60) (fpE := {FPEN}) {fargs} (hK := by omega)
    (hRelc := ⟨_, L_hk⟩) (hLPc := ⟨_, T_hk⟩) (hPEc := ⟨_, P_hk⟩) (hFSc := ⟨_, W_hk⟩) (hEnc := ⟨_, E_hk, E_hcode, E_hcls, E_hmode, E_hdenv⟩)
    (hRel := ?hRel) (hLP := ?hLP) (hPE := ?hPE) (hFSs := ?hFSs) (hEn := ?hEn) (hfpE := ?hfpE) (hfpEp := ?hfpEp)
  case hfpE =>
    intro p hp
    simp only [ReactEnsureCall.fpEn, List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl <;> exact ⟨hG, fun _ => by simp (config := {{ decide := true }})⟩
  case hfpEp =>
    intro p hp
    simp [ReactEnsureCall.fpEn] at hp
  case hEn =>
    intro w h1 hw hfw
    obtain ⟨bw, hdw, hbw⟩ := declLike_frame hw hG hGe
    refine wp_mono (ReactEnsureCall.en_call (n := n) (s := w) (fo := fEn) (t := .undefined) (bG := bw) (oG := oG) (R := FR)
      {e_imp} (hlt := lt_heap_of_frame hw hEno) (hf := by omega) (hk := by rw [kind_frame hw hEno]; exact E_hk)
      (hcode := E_hcode) (hcls := E_hcls) (hmode := E_hmode)
      (hG := by rw [E_hdenv]; exact lt_envs_of_frame hw hG) (hGe := by rw [E_hdenv]; exact hdw)
      (hGF := by rw [hbw _ (by simp [FPA, FPS, Footprint.union])]; exact E_hGF) (hGFv := E_hGFv)
      (hGL := by rw [hbw _ (by simp [FPA, FPS, Footprint.union])]; exact E_hGL) (hGLv := E_hGLv)
      (hGM := by rw [hbw _ (by simp [FPA, FPS, Footprint.union])]; exact E_hGM) (hGMm := E_hGMm) (hGMv := E_hGMv)
      (hGD := by rw [hbw _ (by simp [FPA, FPS, Footprint.union])]; exact E_hGD) (hGDm := E_hGDm) (hGDv := E_hGDv)
      (hGS := by rw [hbw _ (by simp [FPA, FPS, Footprint.union])]; exact E_hGS) (hGSv := E_hGSv)
      (hSo := lt_heap_of_frame hw E_hSo) (hSk := by rw [kind_frame hw E_hSo]; exact E_hSk)
      (hScode := E_hScode) (hScls := E_hScls) (hSmode := E_hSmode) (hSenv := E_hSenv)
      (hGQ := by rw [hbw _ (by simp [FPA, FPS, Footprint.union])]; exact E_hGQ) (hGQv := E_hGQv)
      (hQo := lt_heap_of_frame hw E_hQo) (hQk := by rw [kind_frame hw E_hQo]; exact E_hQk) (hfn := E_hfn) (hq := E_hq)
      (hP := by rw [hw.realms_eq]; exact E_hP)
      (hR := lt_heap_of_frame hw hFR) (hRk := by rw [kind_frame hw hFR]; exact hFRk)) ?_
    rintro v w' h' ⟨-, hF, hfu, rfl, hSc⟩
    rw [E_hdenv] at hF hSc
    exact ⟨hF, frame_trans hw hF, by omega, rfl, hSc⟩
  case hRel =>
    intro w h1 hw hfw
    refine wp_mono (ReactSpawnedCallees.rrp_spec (s := w) (fo := fRel) (t := .undefined) (FR := FR) {l_imp}
      (hlt := lt_heap_of_frame hw hRelo) (hf := by omega) (hFR := lt_heap_of_frame hw hFR)
      (hFRk := by rw [kind_frame hw hFR]; exact hFRk) (hk := by rw [kind_frame hw hRelo]; exact L_hk)
      (hcode := L_hcode) (hcls := L_hcls) (hmode := L_hmode) (hpl := L_hpl)
      (hFRl := by rw [obj_eq_np hw rfl hFR]; exact L_hFRl) (hFRc := by rw [obj_eq_np hw rfl hFR]; exact L_hFRc)) ?_
    rintro v w' h' ⟨hF, hfu, rfl⟩
    exact ⟨hF, frame_mono (frame_trans hw hF) (fun p hp => by simpa [FPA, FP1, FPS, Footprint.union] using hp)
      (fun p hp => by simpa [FPA, FP1, FPS, Footprint.union] using hp) (fun hj => by simp [FPA, FP1, FPS, Footprint.union]),
      by omega, rfl⟩
  case hLP =>
    intro w h1 hw hfw
    refine wp_mono (ReactSpawnedCallees.ltep_sync (s := w) (fo := fLP) (t := .undefined)
      (hlt := lt_heap_of_frame hw hLPo) (hf := by omega) (hk := by rw [kind_frame hw hLPo]; exact T_hk)
      (hcode := T_hcode) (hcls := T_hcls) (hmode := T_hmode)) ?_
    rintro v w' h' ⟨-, hF, hfu, rfl⟩
    exact ⟨hF, by omega, rfl⟩
  case hPE =>
    intro w h1 hw hst hvt hfw
    obtain ⟨bw, hdw, hbw⟩ := declLike_frame hw hG hGe
    obtain ⟨bm1, o1, bd1, hd1, hb1, hv1, -⟩ := hst
    obtain ⟨bm2, o2, bd2, hd2, hb2, hv2, -⟩ := hvt
    rw [hdw] at hd1 hd2
    cases hd1; cases hd2
    refine wp_mono (Q := fun v w' h' => v = .bool false ∧ Frame {{}} w w' ∧ w.fuel ≤ w'.fuel + 60 ∧ h' = h1) ?_ ?_
    · apply ReactNoEffects.pending_none (s := w) (fo := fPE) (t := .undefined) (bG := bw) (oG := oG) (bdS := bd1)
        (bdV := bd2) {p_imp} (hf := by omega) (hlt := lt_heap_of_frame hw hPEo)
        (hG := by rw [P_hdenv]; exact lt_envs_of_frame hw hG) (hGe := by rw [P_hdenv]; exact hdw)
        (hGS := hb1) (hGSv := hv1) (hGV := hb2) (hGVv := hv2)
      all_goals {RB}
    · rintro v w' h' ⟨-, hF, hfu, rfl⟩
      exact ⟨hF, hfu, rfl⟩
  case hFSs =>
    intro w h1 hw hfw
    obtain ⟨bw, hdw, hbw⟩ := declLike_frame hw hG hGe
    refine wp_mono (ReactSpawnedCallees.fsw_flushing (s := w) (fo := fFS) (t := .undefined) (bG := bw) (oG := oG)
      {w_imp} (hlt := lt_heap_of_frame hw hFSo) (hf := by omega) (hk := by rw [kind_frame hw hFSo]; exact W_hk)
      (hcode := W_hcode) (hcls := W_hcls) (hmode := W_hmode)
      (hG := by rw [W_hdenv]; exact lt_envs_of_frame hw hG) (hGe := by rw [W_hdenv]; exact hdw)
      (gF := by
        rw [hbw _ (by simp [FPA, FPS, Footprint.union, ReactEnsureCall.fpEn])]; exact W_gF)
      (gFv := W_gFv)) ?_
    rintro v w' h' ⟨hF, hfu, rfl⟩
    exact ⟨hF, by omega, rfl⟩
"""
out = f'''import JSProofs.ReactSpawned
import JSProofs.ReactSpawnedCallees
import JSProofs.ReactEnsureCall

/-!
# flushSpawnedWork with its small callees (zippy docs/react-proofs.md)

`fsp_full`: `fsp_spec` with `releaseRootPooledCache`, `lanesToEventPriority`, `flushPendingEffects` and the inner
`flushSyncWorkAcrossRoots_impl` discharged at the call states (generated by `tools/react_commit/gen_fsp_full.py`).
`ensureRootIsScheduled` too (`ReactEnsureCall.en_call`: the root already scheduled, the next microtask queued
through the host's `queueMicrotask`). `requestPaint` (the scheduler's) stays a contract.
-/

open ES ES.M HostRuns Logic
open Std (HashMap)
open ReactFacts (BindIs)

namespace ReactSpawned

section
variable {{eng : Engine}} {{σ : Type}} {{answer : HostAnswer σ}} {{HI : σ → Prop}}

set_option maxRecDepth 40000 in
set_option maxHeartbeats 8000000 in
{stmt}
end

end ReactSpawned
'''
open("JSProofs/ReactSpawnedFull.lean", "w").write(out)
