"""Generates JSProofs/ReactCommitCounterFull.lean (zippy docs/react-proofs.md): cme_counter with its traversal
discharged by rtm_one (its child, the button, by cme_button_full) and its reconciliation by cre_spec."""
import sys
sys.path.insert(0, "tools/react_commit")
from compose import binders, compose

def fmt(bs, skip):
    return [f"{k}{nm} : {t}{'}' if k == '{' else ')'}" for nm, k, t in bs if nm not in skip]

def callargs(path, thm, prefix, subst, special, skip=("n", "h", "s")):
    out = []
    for nm, k, t in binders(path, thm):
        if nm in skip: continue
        if nm in special: out.append(f"({nm} := {special[nm]})"); continue
        if k == "{": out.append(f"({nm} := {subst.get(nm, prefix + nm)})")
        else: out.append(f"({nm} := ?_)")
    return " ".join(out)

FO = '⟨[(d.env, JSStr.ofString "offscreenDirectParentIsHidden")], [], false⟩'
FH = '⟨[(BT_CH_d.env, JSStr.ofString "viewTransitionMutationContext")], [(dom, .str BT_CH_kP)], false⟩'
FC = f"(Footprint.union {FO} {FH})"
PC = '(fun w h => (∃ w0 h0, BT_CH_U_R1 w0 h0) ∧ (∃ w0, BT_CH_U_R2 w0 h) ∧ HI h ∧ (∀ bm o, Scope.declLike? (w.envEntry d.env) = some (bm, o) → ∃ bd, bm[JSStr.ofString "viewTransitionMutationContext"]? = some bd ∧ bd.mutable = true ∧ bd.value.isSome = true))'

MONO = "(frame_mono (frame_trans hw0 hw') (fun p hp => by simpa [Footprint.union] using hp) (fun p hp => by simpa [Footprint.union] using hp) (fun hj => by simpa [Footprint.union] using hj))"

cc = binders("JSProofs/ReactCommitCounter.lean", "cme_counter")
outer = fmt(cc, {"hRT", "hRE", "hPCst", "fpC", "PC", "hRTc", "hREc", "hfpC", "hfpCp", "KR", "hf"})
outer.append("(hf : 4200 ≤ s.fuel)")
rt, _ = compose("JSProofs/ReactCommitTraverse.lean", "rtm_one", "T_",
    subst={"fo": "fRT", "t": ".undefined", "s": "s", "rv": "rv", "lv": "lv", "P": "K", "C": "B", "bG": "bG", "oG": "oG",
           "fC": "fo"},
    given={"hlt": "hRTo"}, drop=("n", "h", "hf", "hC", "hfpC", "hPCst", "fpC", "KC", "PC", "hCo", "hCc", "hHI"))
re_, _ = compose("JSProofs/ReactCommitRec.lean", "cre_spec", "RE_",
    subst={"fo": "fRE", "t": ".undefined", "s": "s", "F": "K", "fl": "fl", "fw": "fw", "fe": "fe", "fc": "fc"},
    given={"hlt": "hREo", "hF": "hK", "hFk": "hKk", "hFf": "hKf"}, drop=("n", "h", "hf"))
bt, _ = compose("JSProofs/ReactCommitButtonFull.lean", "cme_button_full", "BT_",
    subst={"fo": "fo", "d": "d", "t": ".undefined", "s": "s", "rv": "rv", "lv": "lv", "B": "B", "bG": "bG", "oG": "oG",
           "dom": "dom"},
    given={"hlt": "hlt", "hk": "hk", "hcode": "hcode", "hcls": "hcls", "hmode": "hmode", "hG": "hG", "hGe": "hGe"},
    drop=("n", "h", "hf", "hHI"))
extra = ["{B dom : ObjId}", "(T_hdenv : T_d.env = d.env)", "(hDK : dom ≠ K)", "(hDRE : dom ≠ fRE)", "(hDB : dom ≠ B)",
         "{bsw bse bsc : Bool} (hBsib : (s.objEntry B).props.get? (.str (JSStr.ofString \"sibling\")) = some (.data .null bsw bse bsc))"]
binds = "\n    ".join(outer + ["{B dom : ObjId}"] + rt + re_ + bt + extra[1:])

rt_call = callargs("JSProofs/ReactCommitTraverse.lean", "rtm_one", "T_",
    {"fo": "fRT", "t": ".undefined", "rv": "rv", "lv": "lv", "P": "K", "C": "B", "bG": "bG", "oG": "oG", "fC": "fo",
     "fpC": FC, "KC": "3500", "PC": PC},
    {"hf": "by omega", "hHI": "hHI1", "hC": "?hC", "hfpC": "?hfpCT", "hPCst": "fun w0 w' h hp _ hE => ⟨hp.1, hp.2.1, hp.2.2.1, fun bm o hd => hp.2.2.2 bm o (by rw [← hE _ (lt_envs_of_frame hw hG)]; exact hd)⟩", "hCo": "lt_heap_of_frame hw hlt",
     "hCc": "⟨_, by rw [objEntry_frame0 hw hlt]; exact hk⟩"})
re_call = callargs("JSProofs/ReactCommitRec.lean", "cre_spec", "RE_",
    {"fo": "fRE", "t": ".undefined", "F": "K", "fl": "fl", "fw": "fw", "fe": "fe", "fc": "fc"}, {"hf": "by omega"})
dom_names = ["CH_U_hOC", "CH_U_hNV", "CH_U_hFC", "CH_U_hLC", "CH_U_hNT"]
sp = {"hf": "by omega", "hHI": "hHI2"}
for nm in dom_names: sp[nm] = f"fun w' h1 hw' hi => BT_{nm} w' h1 {MONO} hi"
sp["CH_U_hI"] = f"fun w' hw' => BT_CH_U_hI w' {MONO}"
bt_call = callargs("JSProofs/ReactCommitButtonFull.lean", "cme_button_full", "BT_",
    {"fo": "fo", "d": "d", "t": ".undefined", "rv": "rv", "lv": "lv", "B": "B", "bG": "bG", "oG": "oG", "dom": "dom"}, sp)
cc_args = " ".join(f"({nm} := {nm})" for nm, k, t in cc if k == "(" and nm not in
    {"hRT", "hRE", "hPCst", "hRTc", "hREc", "hfpC", "hfpCp"})

stmt = f"""theorem cme_counter_full {binds} :
    WP eng answer (n + 7) h (callImpl eng (.obj fo) t #[.obj K, rv, lv]) s fun v w h' =>
      v = .undefined ∧ s.fuel ≤ w.fuel + 3700 ∧ {PC} w h' ∧ Frame {FC} s w := by
  refine cme_counter (n := n + 5) (KR := 3500) (PC := {PC}) (fpC := {FC}) {cc_args.replace("(hf := hf)", "(hf := by omega)")}
    (hRTc := ⟨_, T_hk⟩) (hREc := ⟨_, RE_hk⟩) (hRT := ?hRT) (hRE := ?hRE) (hfpC := ?hfpC) (hfpCp := ?hfpCp)
    (hPCst := fun w w' h hp _ hE => ⟨hp.1, hp.2.1, hp.2.2.1, fun bm o hd => hp.2.2.2 bm o (by rw [← hE _ hG]; exact hd)⟩)
  case hfpC =>
    intro p hp
    simp [Footprint.union] at hp
    rcases hp with rfl | rfl
    · exact ⟨rfl, by show JSStr.ofString "offscreenDirectParentIsHidden" ≠ JSStr.ofString "commitReconciliationEffects"; decide⟩
    · exact ⟨BT_CH_hdenv, by show JSStr.ofString "viewTransitionMutationContext" ≠ JSStr.ofString "commitReconciliationEffects"; decide⟩
  case hfpCp =>
    intro p hp
    simp [Footprint.union] at hp
    subst hp
    exact ⟨hDK, hDRE⟩
  case hRT =>
    intro w h1 hw hHI1 hfw
    refine wp_mono (ReactCommitTraverse.rtm_one (s := w) {rt_call}) (fun _ _ _ hq => hq)
    case hfpCT =>
      intro p hp
      simp [Footprint.union] at hp
      rcases hp with rfl | rfl
      · exact T_hdenv.symm
      · exact BT_CH_hdenv.trans T_hdenv.symm
    case hC =>
      intro w2 h2 hw2 hHI2 hfw2
      have hw0 := frame_empty_trans hw hw2
      refine wp_mono (ReactCommitButton.cme_button_full (s := w2) {bt_call}) ?postC
      case postC =>
        rintro v w' h' ⟨rfl, hfu, hPC, hF⟩
        have hB' : w'.objEntry B = s.objEntry B := by
          rw [hF.obj_eq B (lt_heap_of_frame hw0 BT_hB) (fun k hk => by simp [Footprint.union] at hk; exact hDB hk.1.symm),
            objEntry_frame0 hw0 BT_hB]
        exact ⟨hF, by omega, hPC, lt_heap_of_frame (frame_trans hw0 hF) BT_hB, by rw [hB']; exact BT_hBk, _, _, _,
          by rw [hB']; exact hBsib⟩
      all_goals rebase_tac hw0
    all_goals rebase_tac hw
  case hRE =>
    intro w h1 hw hfw
    refine wp_mono (ReactCommitRec.cre_spec (s := w) {re_call}) (fun _ _ _ ⟨_, hF, hfu, hh, hH⟩ => ⟨hF, hfu, hh, hH⟩)
    all_goals rebase_tac hw
"""
out = f'''import JSProofs.ReactCommitCounter
import JSProofs.ReactCommitButtonFull

/-!
# The counter's commit, composed (zippy docs/react-proofs.md)

`cme_counter_full`: `cme_counter` with its traversal discharged by `rtm_one` (the one child, the button, by
`cme_button_full`) and its reconciliation by `cre_spec` (generated by `tools/react_commit/gen_counter_full.py`).
-/

open ES ES.M HostRuns Logic
open Std (HashMap)

namespace ReactCommitCounter

section
variable {{eng : Engine}} {{σ : Type}} {{answer : HostAnswer σ}} {{HI : σ → Prop}}

set_option maxRecDepth 40000 in
set_option maxHeartbeats 8000000 in
{stmt}
end

end ReactCommitCounter
'''
open("JSProofs/ReactCommitCounterFull.lean", "w").write(out)
