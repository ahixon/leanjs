"""Generates JSProofs/ReactCommitRootFull.lean (zippy docs/react-proofs.md): cme_root with getHoistableRoot by
ghr_spec, its traversal by rtm_one (the one child, the counter, by cme_counter_full) and its reconciliation by
cre_spec."""
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

F0 = "(ReactCommitRoot.F0 d.env)"
FO = '⟨[(d.env, JSStr.ofString "offscreenDirectParentIsHidden")], [], false⟩'
FD = f"(Footprint.union {F0} {FO})"
FH = '⟨[(CT_BT_CH_d.env, JSStr.ofString "viewTransitionMutationContext")], [(CT_dom, .str CT_BT_CH_kP)], false⟩'
FC = f"(Footprint.union {FO} {FH})"
PCc = ('(fun w h => (∃ w0 h0, CT_BT_CH_U_R1 w0 h0) ∧ (∃ w0, CT_BT_CH_U_R2 w0 h) ∧ (∀ bm o, Scope.declLike? '
       '(w.envEntry d.env) = some (bm, o) → ∃ bd, bm[JSStr.ofString "viewTransitionMutationContext"]? = some bd ∧ '
       'bd.mutable = true ∧ bd.value.isSome = true))')
PCr = "(fun w h => (∃ w0 h0, CT_BT_CH_U_R1 w0 h0) ∧ (∃ w0, CT_BT_CH_U_R2 w0 h))"
def mono(a, b):
    return f"(frame_then_empty {a} {b})"

def monoS(a, b):
    return f"(frame_then_sub {a} {b} (fun p hp => by simp at hp; simp [Footprint.union, hp]) rfl rfl)"

cr = binders("JSProofs/ReactCommitRoot.lean", "cme_root")
outer = fmt(cr, {"hGHC", "hRT", "hRE", "hPCst", "fpC", "PC", "hGHc", "hRTc", "hREc", "hfpC", "hfpCp", "KR", "hf"})
outer.append("(hf : 5000 ≤ s.fuel)")
gh, _ = compose("JSProofs/ReactHoistable.lean", "ghr_spec", "GH_",
    subst={"fo": "fGH", "t": ".undefined", "s": "s", "Cont": "Cont", "n": "n + 7"}, given={"hlt": "hGHo"}, drop=("h", "hf"))
gh = [b.replace("Frame {} s w →", f"Frame {F0} s w →").replace(" (n + 7) s {} ", f" (n + 7) s {F0} ") for b in gh]
rt, _ = compose("JSProofs/ReactCommitTraverse.lean", "rtm_one", "T_",
    subst={"fo": "fRT", "t": ".undefined", "s": "s", "rv": ".obj FR", "lv": "lv", "P": "R", "C": "K", "bG": "bG",
           "oG": "oG", "fC": "fo"},
    given={"hlt": "hRTo"}, drop=("n", "h", "hf", "hC", "hfpC", "hPCst", "fpC", "KC", "PC", "hCo", "hCc"))
re_, _ = compose("JSProofs/ReactCommitRec.lean", "cre_spec", "RE_",
    subst={"fo": "fRE", "t": ".undefined", "s": "s", "F": "R", "fl": "fl", "fw": "fw", "fe": "fe", "fc": "fc"},
    given={"hlt": "hREo", "hF": "hR", "hFk": "hRk", "hFf": "hRf"}, drop=("n", "h", "hf"))
ct, _ = compose("JSProofs/ReactCommitCounterFull.lean", "cme_counter_full", "CT_",
    subst={"fo": "fo", "d": "d", "t": ".undefined", "s": "s", "rv": ".obj FR", "lv": "lv", "bG": "bG", "oG": "oG", "K": "K"},
    given={"hlt": "hlt", "hk": "hk", "hcode": "hcode", "hcls": "hcls", "hmode": "hmode", "hG": "hG", "hGe": "hGe"},
    drop=("n", "h", "hf", "BT_CH_U_bdV", "BT_CH_U_hGV", "BT_CH_U_hGVm", "BT_CH_U_hGVi"))
ct = [b.replace(f"Frame {FO} s w →", f"Frame {FD} s w →").replace(f" n s {FO} ", f" n s {FD} ") for b in ct]
extra = ["(T_hdenv : T_d.env = d.env)", "(hDR : CT_dom ≠ R)", "(hDRE : CT_dom ≠ fRE)",
         "{ksw kse ksc : Bool} (hKsib : (s.objEntry K).props.get? (.str (JSStr.ofString \"sibling\")) = some (.data .null ksw kse ksc))"]
binds = "\n    ".join(outer + ["{K : ObjId}"] + gh + rt + re_ + ct + extra)

dom_ct = ["BT_CH_U_hOC", "BT_CH_U_hNV", "BT_CH_U_hFC", "BT_CH_U_hLC", "BT_CH_U_hNT"]
sp = {"hf": "hfw2", "hG": "lt_envs_of_frame hw0 hG", "hGe": "hd2", "BT_CH_U_bdV": "bdV'", "BT_CH_U_hGV": "hbV'",
      "BT_CH_U_hGVm": "hbVm'", "BT_CH_U_hGVi": "hbVi'"}
for nm in dom_ct: sp[nm] = f"fun w' h1 hw' => CT_{nm} w' h1 {monoS('hw0', 'hw' + chr(39))}"
sp["BT_CH_U_hI"] = f"fun w' hw' => CT_BT_CH_U_hI w' {monoS('hw0', 'hw' + chr(39))}"
ct_call = callargs("JSProofs/ReactCommitCounterFull.lean", "cme_counter_full", "CT_",
    {"fo": "fo", "d": "d", "t": ".undefined", "rv": ".obj FR", "lv": "lv", "bG": "bw2", "oG": "oG", "K": "K"}, sp)
rt_call = callargs("JSProofs/ReactCommitTraverse.lean", "rtm_one", "T_",
    {"fo": "fRT", "t": ".undefined", "rv": ".obj FR", "lv": "lv", "P": "R", "C": "K", "bG": "bw", "oG": "oG", "fC": "fo",
     "fpC": FC, "KC": "4200", "PC": PCc},
    {"hf": "by omega", "hC": "?hC", "hfpC": "?hfpCT", "hG": "by rw [T_hdenv]; exact lt_envs_of_frame hw hG", "hGe": "hd",
     "hPCst": "fun w0 w' h hp _ hE => ⟨hp.1, hp.2.1, fun bm o hd' => hp.2.2 bm o (by rw [← hE _ (lt_envs_of_frame hw hG)]; exact hd')⟩",
     "hCo": "lt_heap_of_frame hw hlt", "hCc": "⟨_, by rw [hw.obj_eq fo hlt (fun _ hh => by simp at hh)]; exact hk⟩"})
gh_call = callargs("JSProofs/ReactHoistable.lean", "ghr_spec", "GH_", {"fo": "fGH", "t": ".undefined", "Cont": "Cont"},
    {"hf": "by omega", "hRN": f"fun w' hw' => GH_hRN w' {mono('hw', 'hw' + chr(39))}",
     "hCall": f"fun w' h1 hw' => GH_hCall w' h1 {mono('hw', 'hw' + chr(39))}",
     "hNT": f"fun w' h1 hw' => GH_hNT w' h1 {mono('hw', 'hw' + chr(39))}"})
re_call = callargs("JSProofs/ReactCommitRec.lean", "cre_spec", "RE_",
    {"fo": "fRE", "t": ".undefined", "F": "R", "fl": "fl", "fw": "fw", "fe": "fe", "fc": "fc"}, {"hf": "by omega"})
cr_args = " ".join(f"({nm} := {nm})" for nm, k, t in cr if k == "(" and nm not in
    {"hGHC", "hRT", "hRE", "hPCst", "hGHc", "hRTc", "hREc", "hfpC", "hfpCp", "hf"})

stmt = f"""theorem cme_root_full {binds} :
    WP eng answer (n + 9) h (callImpl eng (.obj fo) t #[.obj R, .obj FR, lv]) s fun v w h' =>
      v = .undefined ∧ s.fuel ≤ w.fuel + 4700 ∧ {PCr} w h' ∧ Frame ((ReactCommitRoot.F0 d.env).union {FC}) s w := by
  refine ReactCommitRoot.cme_root (n := n + 7) (KR := 4200) (PC := {PCr}) (fpC := {FC}) {cr_args}
    (hf := by omega) (hGHc := ⟨_, GH_hk⟩) (hRTc := ⟨_, T_hk⟩) (hREc := ⟨_, RE_hk⟩) (hGHC := ?hGHC) (hRT := ?hRT)
    (hRE := ?hRE) (hfpC := ?hfpC) (hfpCp := ?hfpCp) (hPCst := fun _ _ _ hp _ _ => hp)
  case hfpC =>
    intro p hp
    simp [Footprint.union] at hp
    rcases hp with rfl | rfl
    · exact ⟨rfl, by dsimp only; decide, by dsimp only; decide, by dsimp only; decide⟩
    · exact ⟨CT_BT_CH_hdenv, by dsimp only; decide, by dsimp only; decide, by dsimp only; decide⟩
  case hfpCp =>
    intro p hp
    simp [Footprint.union] at hp
    subst hp
    exact ⟨hDR, hDRE⟩
  case hGHC =>
    intro w h1 hw hfw
    refine wp_mono (ReactHoistable.ghr_spec (s := w) {gh_call}) (fun _ _ _ ⟨_, hF, hfu⟩ => ⟨hF, by omega⟩)
    all_goals rebase_tac hw
  case hRT =>
    intro w h1 hw hvt hfw
    obtain ⟨bw, hd, hbw⟩ := declLike_frame hw (e := d.env) hG hGe
    rw [← T_hdenv] at hd hbw
    refine wp_mono (ReactCommitTraverse.rtm_one (s := w) {rt_call}) ?postT
    case postT =>
      rintro v w' h' ⟨rfl, hfu, hPC, hF⟩
      refine ⟨rfl, hfu, ⟨hPC.1, hPC.2.1⟩, hF, fun bm o hd' => hPC.2.2 bm o hd'⟩
    case hfpCT =>
      intro p hp
      simp [Footprint.union] at hp
      rcases hp with rfl | rfl
      · exact T_hdenv.symm
      · exact CT_BT_CH_hdenv.trans T_hdenv.symm
    case hC =>
      intro w2 h2 hw2 hfw2
      have hw0 : Frame {FD} s w2 := frame_mono (frame_then_empty hw hw2)
        (fun p hp => List.mem_append.mpr (Or.inl hp)) (fun p hp => by simp at hp) (fun _ => rfl)
      obtain ⟨bw2, hd2, hbw2⟩ := declLike_frame (frame_then_empty hw hw2) (e := d.env) hG hGe
      obtain ⟨bdV', hbV', hbVm', hbVi'⟩ := hvt bw2 oG
        (by rw [← envEntry_frame0 hw2 (lt_envs_of_frame hw hG)]; exact hd2)
      refine wp_mono (ReactCommitCounter.cme_counter_full (s := w2) {ct_call}) ?postC
      case postC =>
        rintro v w' h' ⟨rfl, hfu, hPC, hF⟩
        have hK' : w'.objEntry K = s.objEntry K := by
          rw [hF.obj_eq K (lt_heap_of_frame hw0 CT_hK) (fun k hk => by simp [Footprint.union] at hk; exact CT_hDK hk.1.symm),
            hw0.obj_eq K CT_hK (fun _ hh => by simp [Footprint.union] at hh)]
        exact ⟨hF, by omega, hPC, lt_heap_of_frame (frame_trans hw0 hF) CT_hK, by rw [hK']; exact CT_hKk, _, _, _,
          by rw [hK']; exact hKsib⟩
      all_goals first | rebase_tac' hw0, hbw2 | (simp only [CT_T_hdenv, CT_BT_CH_hdenv, CT_BT_CH_U_hdenv]; first | exact hd2 | exact lt_envs_of_frame hw0 hG)
    all_goals first | rebase_tac' hw, hbw | (simp only [T_hdenv]; first | exact hd | exact lt_envs_of_frame hw hG)
  case hRE =>
    intro w h1 hw hfw
    have hRw : w.objEntry R = s.objEntry R :=
      hw.obj_eq R hR (fun k hk => by simp [Footprint.union] at hk; exact hDR hk.1.symm)
    have hREw : w.objEntry fRE = s.objEntry fRE :=
      hw.obj_eq fRE hREo (fun k hk => by simp [Footprint.union] at hk; exact hDRE hk.1.symm)
    refine wp_mono (ReactCommitRec.cre_spec (s := w) {re_call}) (fun _ _ _ ⟨_, hF, hfu, hh, hH⟩ => ⟨hF, hfu, hh, hH⟩)
    all_goals first | (rw [hRw] <;> with_reducible assumption) | (rw [hREw] <;> with_reducible assumption) | rebase_quick hw
"""
out = f'''import JSProofs.ReactCommitRoot
import JSProofs.ReactCommitCounterFull
import JSProofs.ReactHoistable

/-!
# The root's commit, composed (zippy docs/react-proofs.md)

`cme_root_full`: `cme_root` with `getHoistableRoot` by `ghr_spec`, its traversal by `rtm_one` (the one child, the
counter, by `cme_counter_full`) and its reconciliation by `cre_spec` (generated by
`tools/react_commit/gen_root_full.py`). The DOM's premises are quantified over the frame of the module bindings the
root and the button write around them.
-/

open ES ES.M HostRuns Logic
open Std (HashMap)

namespace ReactCommitRoot

section
variable {{eng : Engine}} {{σ : Type}} {{answer : HostAnswer σ}}

set_option maxRecDepth 40000 in
set_option maxHeartbeats 8000000 in
{stmt}
end

end ReactCommitRoot
'''
open("JSProofs/ReactCommitRootFull.lean", "w").write(out)
