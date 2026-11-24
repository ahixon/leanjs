"""Generates the crw_full part of JSProofs/ReactCommitEntryFull2.lean (zippy docs/react-proofs.md): crw_spec
(completeRootWhenReady) with its completeRoot contract discharged by cpr_full (premises CR_) at the call state."""
import re, sys
sys.path.insert(0, "tools/react_commit")
from compose import binders, compose, _rename, _theorem_header

CE = "JSProofs/ReactCommitEntry.lean"
CF = "JSProofs/ReactCommitEntryFull.lean"
Z = ".num (F64.fin false 0 (-1074))"
TWO = ".num (F64.fin false 4503599627370496 (-51))"
cb = binders(CE, "crw_spec")
outer_ren = {"A": "R", "x1": ".null", "x4": Z, "x5": Z, "x6": Z}
drop_outer = {"hCRf", "hCRc", "K", "hK", "P", "A", "x1", "x4", "x5", "x6"}
def ren_outer(t):
    pat = re.compile(r"(?<![A-Za-z0-9_'.$])(" + "|".join(re.escape(x) for x in outer_ren) + r")(?![A-Za-z0-9_'$])")
    return pat.sub(lambda m: outer_ren[m.group(1)] if " " not in outer_ren[m.group(1)] else "(" + outer_ren[m.group(1)] + ")", t)
outer = ["{R : ObjId}"] + [f"{k}{nm} : {ren_outer(t)}{'}' if k == '{' else ')'}" for nm, k, t in cb if nm not in drop_outer]
mb = binders(CF, "cpr_full")
csubst = {"fo": "fCR", "t": ".undefined", "FR": "FR", "R": "R", "bG": "bG", "oG": "oG", "tr": "x2", "di": "x3",
          "ds": "x7", "es": ".num (F64.fin false 5629499534213120 (-50))", "sst": ".null",
          # timeoutHandle: completeRootWhenReady writes -1 before completeRoot (hCRf's PropHas)
          "CM_SP_thw": "thw'", "CM_SP_the": "the'", "CM_SP_thc": "thc'"}
QUANT = [nm for nm, k, t in mb if k == "(" and t.strip().startswith("∀ s1")]
cr, _ = compose(CF, "cpr_full", "CR_", subst=csubst, given={}, drop=("n", "h", "s", "hf", "hlt", "hG", "hGe", "CM_SP_hfpE", "CM_SP_hFRt", "hHI"))
FPT = '⟨[], [(FR, .str (JSStr.ofString "timeoutHandle"))], false⟩'
qgiven = {}
for i, b in enumerate(cr):
    nm = b[1:b.index(" : ")]
    if nm[3:] in QUANT:
        body = b[b.index(" : ") + 3:-1]
        body = re.sub(r"(?<![A-Za-z0-9_'.])s(?![A-Za-z0-9_'])", "s2", body)
        cr[i] = f"({nm} : ∀ s2, Frame {FPT} s s2 → {body})"
        qgiven[nm[3:]] = f"{nm} w hw"
cren = {nm: csubst.get(nm, "CR_" + nm) for nm, k, t in mb if nm not in ("n", "h", "s")}
cr += ["(CR_hdenv : CR_d.env = d.env)"]
binds = "\n    ".join(outer + cr + ["(hf : 59500 ≤ s.fuel)"])
post_hdr = _theorem_header(CF, "cpr_full")
m = re.search(r"∃ w0, (\(fun \(w : State\) \(h : σ\) => .*\)) w0 h' ∧ Frame \{\} w0 w\s*$", post_hdr, re.S)
PCPR = _rename(m.group(1), cren)
_k = PCPR.rindex("∧ Frame (") + len("∧ Frame ")
_d = 0
for _j in range(_k, len(PCPR)):
    _d += {"(": 1, ")": -1}.get(PCPR[_j], 0)
    if _d == 0: break
FFF = PCPR[_k:_j + 1]
PCPR1 = re.sub(r"(?<![A-Za-z0-9_'.])s(?![A-Za-z0-9_'])", "s1", PCPR)
P = (f"(fun (w : State) (h : σ) => (∃ s1 w0, Frame {FPT} s s1 ∧ {PCPR1} w0 h ∧ Frame {{}} w0 w) ∧ "
     f"Frame (Footprint.union {FPT} ({FFF}.union {{}})) s w)")
fargs = " ".join(f"({nm} := {nm})" for nm, k, t in cb if nm not in drop_outer and nm not in ("n", "h", "s"))
fixed = " ".join(f"({nm} := {v})" for nm, v in outer_ren.items())
cimp = " ".join(f"({nm} := {csubst.get(nm, 'CR_' + nm)})" for nm, k, t in mb
                if k == "{" and nm not in ("n", "h", "s", "bG"))
qg = " ".join(f"({nm} := {v})" for nm, v in qgiven.items())
RB = ("first | rebase_quick hw | (rw [hbw _ (by simp)] <;> with_reducible assumption) | "
      "(rw [props_frame hw (by with_reducible assumption) (by simp [CR_CM_ME_dMF])] <;> with_reducible assumption) | "
      "(rw [kind_frame hw (by with_reducible assumption)] <;> with_reducible assumption) | "
      "(rw [hw.obj_eq _ (by with_reducible assumption) (fun _ hk => by simp [CR_dLPE, CR_dNPE, CR_dOPE] at hk)] <;> with_reducible assumption) | "
      "(simp only [CR_CM_ME_M_T_hdenv, CR_CM_ME_M_CT_T_hdenv, CR_CM_ME_M_CT_BT_CH_hdenv, CR_CM_ME_M_hdenv, CR_CM_hdenv, "
      "CR_CM_B_hdenv, CR_CM_ME_hdenv, CR_CM_LE_hdenv, CR_CM_SP_hdenv, CR_CM_MF_hdenv, CR_PN_hdenv, CR_hdenv]; "
      "first | exact hdw | exact lt_envs_of_frame hw hG)")
stmt = f"""theorem crw_full {binds} :
    WP eng answer (n + 13) h (callImpl eng (.obj fo) t #[.obj FR, .obj R, .null, x2, x3, {TWO}, {Z}, {Z}, {Z}, x7,
      .num (F64.fin false 5629499534213120 (-50)), c1, c2, c3]) s fun v w h' =>
      v = .undefined ∧ s.fuel ≤ w.fuel + 59400 + 100 ∧ ∃ w0, {P} w0 h' ∧ Frame {{}} w0 w := by
  refine crw_spec (n := n + 11) (K := 59400) (P := {P}) {fixed} {fargs} (hK := by omega)
    (hCRc := ⟨_, CR_hk⟩) (hCRf := ?hCRf)
  case hCRf =>
    intro w h1 hw hHI1 hTH hfw
    obtain ⟨thw', the', thc', hTH'⟩ := hTH
    obtain ⟨bw, hdw, hbw⟩ := declLike_frame hw hG hGe
    refine' wp_mono (cpr_full (s := w) (n := n) (bG := bw) {cimp} (hf := by omega) (hHI := hHI1)
      (hlt := lt_heap_of_frame hw hCRo) (hG := by rw [CR_hdenv]; exact lt_envs_of_frame hw hG)
      (hGe := by rw [CR_hdenv]; exact hdw) {qg}
      (CM_SP_E_hP := by rw [hw.realms_eq]; exact CR_CM_SP_E_hP) (CM_SP_hFRt := hTH') ..) ?rpost
    case rpost =>
      rintro v w' h' ⟨-, hfu, w0, hPc, hF0⟩
      exact ⟨by omega, ⟨w, w0, hw, hPc, hF0⟩, frame_trans hw (frame_trans hPc.2 hF0)⟩
    all_goals {RB}
"""
src = open(CF).read()
i = src.index("\nend\n\nend ReactCommitEntry")
src = src[:i] + "\nset_option maxRecDepth 40000 in\nset_option maxHeartbeats 8000000 in\n" + stmt + src[i:]
open(CF, "w").write(src)
print(len(binds.split("\n")), "binder lines")
