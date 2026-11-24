"""Generates JSProofs/ReactFlushMutationFull.lean (zippy docs/react-proofs.md): fme_spec with its mutation-pass contract
discharged by cme_root_full (ReactCommitRootFull) at the call state. cme_root_full's premises are prefixed M_; its
module record is the call state's (FPRE's bindings differ), its other bindings and the objects' other properties carried
by the frame (rebase_fpre); its premises that quantify over frames from its entry state are stated here over frames
from fme's entry state with FPRE added (passed on with frame_trans). getActiveElementDeep stays a contract."""
import re, sys
sys.path.insert(0, "tools/react_commit")
from compose import binders, _rename, _theorem_header

FM = "JSProofs/ReactFlushMutation.lean"
CR = "JSProofs/ReactCommitRootFull.lean"
FPRE = "(FPRE d.env RSI RDSI)"
fb = binders(FM, "fme_spec")
drop_outer = {"hC", "KC", "fpC", "PC", "hfC", "hfpC", "hfpCp", "hCc", "hf"}
outer = [f"{k}{nm} : {t}{'}' if k == '{' else ')'}" for nm, k, t in fb if nm not in drop_outer]

cb = binders(CR, "cme_root_full")
subst = {"fo": "fC", "t": ".undefined", "R": "R", "FR": "FR", "lv": "lv", "bG": "bG", "oG": "oG"}
drop = {"n", "h", "s", "hf", "hlt", "hG", "hGe"}
ren = {}
for nm, k, t in cb:
    if nm in drop: continue
    ren[nm] = subst.get(nm, "M_" + nm)
QUANT = {"GH_hRN": 1, "GH_hCall": 2, "GH_hNT": 2, "CT_BT_CH_U_hI": 1, "CT_BT_CH_U_hOC": 2, "CT_BT_CH_U_hFC": 2,
         "CT_BT_CH_U_hLC": 2, "CT_BT_CH_U_hNT": 2, "CT_BT_CH_U_hNV": 2}

def widen(t):
    """Frames from the entry state `s` (or DomRead at `s`) widened by FPRE."""
    t2 = re.sub(r"Frame \((.*?)\) s w →", lambda m: f"Frame ({FPRE}.union ({m.group(1)})) s w →", t, count=1)
    if t2 == t:
        t2 = re.sub(r"DomRead eng answer HI (\S+(?: \+ \d+\))?) s \((.*)\) (\(?\(?M_CT_dom\)?\)?|M_GH_Doc|M_CT_BT_CH_U_T) ",
                    lambda m: f"DomRead eng answer HI {m.group(1)} s ({FPRE}.union ({m.group(2)})) {m.group(3)} ", t, count=1)
    assert t2 != t, t
    return t2

added = []; given = {}
for nm, k, t in cb:
    if nm in drop or nm in subst: continue
    tt = _rename(t, ren)
    if nm in QUANT:
        tt = widen(tt)
        given[nm] = (f"fun w' h1 hw' => M_{nm} w' h1 (frame_trans hw hw')" if QUANT[nm] == 2
                     else f"fun w' hw' => M_{nm} w' (frame_trans hw hw')")
    added.append(f"{k}M_{nm} : {tt}{'}' if k == '{' else ')'}")

hdr = _theorem_header(CR, "cme_root_full")
post = hdr[hdr.rindex("fun v w h' =>") + len("fun v w h' =>"):].strip()
# post: v = .undefined ∧ s.fuel ≤ w.fuel + 4700 ∧ PC w h' ∧ Frame FP s w
m = re.match(r"v = \.undefined ∧ s\.fuel ≤ w\.fuel \+ 4700 ∧ (\(fun w h => .*\)) w h' ∧ Frame (.*) s w$", post, re.S)
assert m, post
PC = _rename(m.group(1), ren).replace("(fun w h =>", "(fun (w : State) (h : σ) =>", 1)
FPC = _rename(m.group(2), ren)

extra = ["(hf : 5700 ≤ s.fuel)", "(M_hdenv : M_d.env = d.env)",
         "(dMS : M_CT_dom ≠ SI) (dMT : M_CT_dom ≠ RSI) (dMD : M_CT_dom ≠ RDSI) (dMF : M_CT_dom ≠ FR) (dMG : M_CT_dom ≠ fGD)",
         "(dLT : M_CT_BT_LP ≠ RSI) (dLD : M_CT_BT_LP ≠ RDSI) (dNT : M_CT_BT_NP ≠ RSI) (dND : M_CT_BT_NP ≠ RDSI)",
         "(dOT : M_CT_BT_CH_U_OP ≠ RSI) (dOD : M_CT_BT_CH_U_OP ≠ RDSI)"]
pat = re.compile(r"(?<![A-Za-z0-9_'.])fpC(?![A-Za-z0-9_'])")
late = [pat.sub(FPC, b).replace("WP eng answer (n + 1)", "WP eng answer (n + 9)") for b in outer if pat.search(b)]
outer = [b for b in outer if not pat.search(b)]
binds = "\n    ".join(outer + added + extra + late)
fargs = " ".join(f"({nm} := {nm})" for nm, k, t in fb if nm not in drop_outer and nm not in ("n", "h", "s"))
imp_args = " ".join(f"({nm} := {ren[nm]})" for nm, k, t in cb if k == "{" and nm not in drop and nm != "bG")
exp_args = " ".join(f"({nm} := {given[nm]})" for nm in given)
fpre_names = ["pendingEffectsStatus", "rootViewTransitionAffected", "inUpdateViewTransition", "executionContext"]

stmt = f"""theorem fme_full {binds} :
    WP eng answer (n + 10) h (callImpl eng (.obj fo) t #[]) s fun v w h' =>
      v = .undefined ∧ s.fuel ≤ w.fuel + 5700 ∧ (∃ w0, {PC} w0 h') ∧
      Frame ((({FPRE}.union {FPC})).union ⟨[(d.env, JSStr.ofString "selectionInformation"),
        (d.env, JSStr.ofString "eventsEnabled"), (d.env, JSStr.ofString "_enabled")],
        [(FR, .str (JSStr.ofString "current"))], false⟩) s w ∧
      BindIs w d.env (JSStr.ofString "pendingEffectsStatus") (.num (F64.fin false 4503599627370496 (-51))) ∧
      BindIs w d.env (JSStr.ofString "executionContext") (.num ec) ∧
      PropIs w RSI (JSStr.ofString "T") tv ∧ PropIs w RDSI (JSStr.ofString "p") pv := by
  refine fme_spec (n := n + 8) (KC := 5000) (fpC := {FPC}) (PC := {PC}) {fargs}
    (hf := by omega) (hfC := by omega) (hCc := ⟨_, M_hk⟩) (hC := ?hC) (hfpC := ?hfpC) (hfpCp := ?hfpCp)
  case hfpC =>
    intro p hp
    simp only [Footprint.union, ReactCommitRoot.F0, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with (hp | hp | hp) | hp | hp <;> subst hp <;> simp [M_hdenv, M_CT_BT_CH_hdenv]
  case hfpCp =>
    intro p hp
    have hp1 : p.1 = M_CT_dom := by
      simp [Footprint.union, ReactCommitRoot.F0] at hp
      first | exact hp.1 | exact congrArg Prod.fst hp | (subst hp; rfl)
    rw [hp1]
    exact ⟨dMS, dMT, dMD, dMF, dMG⟩
  case hC =>
    intro w h1 hw hfw
    obtain ⟨bw, hdw, hbw⟩ := declLike_frame hw hG hGe
    have hdw' : Scope.declLike? (w.envEntry M_d.env) = some (bw, oG) := by rw [M_hdenv]; exact hdw
    have hGw : M_d.env < w.envs.size := by rw [M_hdenv]; exact lt_envs_of_frame hw hG
    refine wp_mono (Q := fun v w' h' => v = .undefined ∧ w.fuel ≤ w'.fuel + 4700 ∧ {PC} w' h' ∧
      Frame {FPC} w w') ?_ ?_
    · apply ReactCommitRoot.cme_root_full (s := w) (n := n) (bG := bw) {imp_args}
        (hf := hfw) (hlt := lt_heap_of_frame hw hCo) (hG := hGw) (hGe := hdw') {exp_args}
      all_goals first | rebase_fpre hw, hbw |
        (simp only [M_T_hdenv, M_CT_T_hdenv, M_CT_BT_CH_hdenv]; first | exact hdw' | exact hGw) |
        (rw [hw.obj_eq _ (by with_reducible assumption) (fun k hk => by
          simp [FPRE] at hk; rcases hk with ⟨hh, -⟩ | ⟨hh, -⟩ <;> exact absurd hh (by assumption))] <;>
          with_reducible assumption)
    · rintro v w' h' ⟨rfl, hfu, hP, hF⟩
      exact ⟨rfl, by omega, hP, hF⟩
"""
out = f'''import JSProofs.ReactFlushMutation
import JSProofs.ReactCommitRootFull

/-!
# flushMutationEffects with the click's mutation pass (zippy docs/react-proofs.md)

`fme_full`: `fme_spec` with its contract for `commitMutationEffectsOnFiber(finishedWork, root, lanes)` discharged by
`ReactCommitRoot.cme_root_full` at the call state (generated by `tools/react_commit/gen_fme_full.py`; its premises
prefixed `M_`; those over frames from its entry state stated over frames from this one, widened by `FPRE`).
`getActiveElementDeep` stays a contract (`hGDC`).
-/

open ES ES.M HostRuns Logic
open Std (HashMap)
open ReactFacts (BindIs PropIs)

namespace ReactFlushMutation

/-- A premise at a state framed by `FPRE` from the entry state: its bindings outside `FPRE` (`hbw`), its objects'
properties other than `T` and `p`, its scope's record (`hdw`). -/
macro "rebase_fpre" hw:term "," hbw:term : tactic => `(tactic| first
  | rebase_quick $hw
  | (rw [$hbw _ (by simp [FPRE])] <;> with_reducible assumption)
  | (rw [props_frame $hw (by with_reducible assumption) (by
      simp [FPRE] <;> exact ⟨fun h => absurd h (by assumption), fun h => absurd h (by assumption)⟩)] <;>
      with_reducible assumption)
  | (rw [kind_frame $hw (by with_reducible assumption)] <;> with_reducible assumption))

section
variable {{eng : Engine}} {{σ : Type}} {{answer : HostAnswer σ}}

set_option maxRecDepth 40000 in
set_option maxHeartbeats 8000000 in
{stmt}
end

end ReactFlushMutation
'''
open("JSProofs/ReactFlushMutationFull.lean", "w").write(out)
print(len(added), "M_ premises;", len(given), "widened")
