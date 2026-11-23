"""Generates JSProofs/ReactCommitRootFnFull.lean (zippy docs/react-proofs.md): cmr_spec with its callees' contracts
discharged by their composed specs at the call states. Stage list `DO` says which contracts are discharged so far (the
rest stay premises)."""
import re, sys
sys.path.insert(0, "tools/react_commit")
from compose import binders, compose, _rename, _theorem_header

DO = {"hMf", "hBf"}
CR = "JSProofs/ReactCommitRootFn.lean"
MF = "JSProofs/ReactMarkFinished.lean"
BMF = "JSProofs/ReactBeforeMutationFull.lean"
cb = binders(CR, "cmr_spec")
Z = ".num (F64.fin false 0 (-1074))"
drop_outer = {"sl", "ul", "srl", "K", "hK"}
if "hMf" in DO: drop_outer |= {"hMf", "hMc", "fpM", "hfpM", "hfpMp"}
outer_ren = {"sl": Z, "ul": Z, "srl": Z, "K": "5800"}
FPM = "(ReactMarkFinished.FPM FR MF_EA MF_XA)"
if "hMf" in DO: outer_ren["fpM"] = FPM
F1 = f"((FPC d.env FR RSI RDSI).union {FPM})"
if "hBf" in DO:
    drop_outer |= {"hBf", "hBc", "fpB", "hfpB", "hfpBp"}
    outer_ren["fpB"] = "(ReactBeforeMutation.FB d.env)"
LANE = "F64.fin false 4503599627370496 (-51)"
def widen(t, FP):
    t2 = re.sub(r"Frame \((.*?)\) s w →", lambda m: f"Frame ({FP}.union ({m.group(1)})) s w →", t, count=1)
    if t2 == t:
        t2 = re.sub(r"DomRead eng answer (\S+(?: \+ \d+\))?) s \((.*?)\) ", lambda m: f"DomRead eng answer {m.group(1)} s ({FP}.union ({m.group(2)})) ", t, count=1)
    assert t2 != t, t
    return t2
def ren_outer(t):
    pat = re.compile(r"(?<![A-Za-z0-9_'.$])(" + "|".join(re.escape(x) for x in outer_ren) + r")(?![A-Za-z0-9_'$])")
    return pat.sub(lambda m: outer_ren[m.group(1)] if outer_ren[m.group(1)].startswith("(") or " " not in outer_ren[m.group(1)] else "(" + outer_ren[m.group(1)] + ")", t)
outer = [f"{k}{nm} : {ren_outer(t).replace('WP eng answer (n + 1)', 'WP eng answer (n + 10)')}{'}' if k == '{' else ')'}"
         for nm, k, t in cb if nm not in drop_outer]
added = []
if "hMf" in DO:
    mf, _ = compose(MF, "mrf_spec", "MF_", subst={"fo": "fM", "t": ".undefined", "FR": "FR", "bG": "bG", "oG": "oG"},
                    given={}, drop=("n", "h", "s", "hf", "hlt", "hG", "hGe"))
    added += mf
    others = ["R", "RSI", "RDSI", "fB", "fME", "fLE", "fSP"]
    added += ["(MF_hdenv : MF_d.env = d.env)"] + [f"(dA{o} : MF_EA ≠ {o}) (dX{o} : MF_XA ≠ {o})" for o in others]
bgiven = {}
if "hBf" in DO:
    bb, _ = compose(BMF, "cbm_full", "B_", subst={"fo": "fB", "t": ".undefined", "FR": "FR", "R": "R", "bG": "bG",
                    "oG": "oG", "E": "E", "ev0": "ev0", "lanes": LANE}, given={}, drop=("n", "h", "s", "hf", "hlt", "hG", "hGe"))
    BQ = {"hGDC": 2, "S_hNN": 2, "S_hTL": 1, "S_hCE": 2}
    for i, b in enumerate(bb):
        nm = b[1:b.index(" : ")]
        if nm[2:] in BQ:
            bb[i] = b[0] + nm + " : " + widen(b[b.index(" : ") + 3:-1], F1) + b[-1]
            bgiven[nm[2:]] = (f"fun w' h1 hw' => {nm} w' h1 (frame_trans hw hw')" if BQ[nm[2:]] == 2
                              else f"fun w' hw' => {nm} w' (frame_trans hw hw')")
    bb = [re.sub(r"(?<![A-Za-z0-9_'.])FB(?= )", "ReactBeforeMutation.FB", b) for b in bb]
    bb = [re.sub(r"(?<![A-Za-z0-9_'.])n(?![A-Za-z0-9_'])", "(n + 8)", b) for b in bb]
    added += bb + ["(B_hdenv : B_d.env = d.env)"]
extra = ["(hf : 29400 ≤ s.fuel)"]
late = [b for b in outer if "MF_" in b or "ReactBeforeMutation.FB" in b]
outer = [b for b in outer if not ("MF_" in b or "ReactBeforeMutation.FB" in b)]
binds = "\n    ".join(outer + added + extra + late)
cargs = " ".join(f"({nm} := {ren_outer(nm) if nm in outer_ren else nm})" for nm, k, t in cb
                 if nm not in drop_outer and nm not in ("n", "h", "s") and k == "{")
eargs = " ".join(f"({nm} := {nm})" for nm, k, t in cb if nm not in drop_outer and k == "(")
fixed = " ".join(f"({nm} := {v})" for nm, v in outer_ren.items() if nm not in ("K",))
post_hdr = _theorem_header(CR, "cmr_spec")
POST = ren_outer(post_hdr[post_hdr.rindex("fun v w h' =>") + len("fun v w h' =>"):].strip())
CALL = ren_outer(post_hdr[post_hdr.rindex("WP eng answer"):post_hdr.rindex("fun v w h' =>")].strip())
UNF = "FPC, ReactMarkFinished.FPM, Footprint.union"
RB = (f"first | rebase_quick hw | (rw [hbw _ (by simp [{UNF}])] <;> with_reducible assumption) | "
      f"(rw [props_frame hw (by with_reducible assumption) (by simp [{UNF}])] <;> with_reducible assumption) | "
      f"(rw [kind_frame hw (by with_reducible assumption)] <;> with_reducible assumption)")
cases = []
if "hMf" in DO:
    mimp = " ".join(f"({nm} := MF_{nm})" for nm, k, t in binders(MF, "mrf_spec")
                    if k == "{" and nm not in ("n", "h", "s", "fo", "t", "FR", "bG", "oG"))
    cases.append(f"""  case hMf =>
    intro w h1 hw hfw
    obtain ⟨bw, hdw, hbw⟩ := declLike_frame hw hG hGe
    refine wp_mono (Q := fun v w' h' => v = .undefined ∧
      (w'.objEntry FR).props.get? (.str (JSStr.ofString "pendingLanes")) = some (.data ({Z}) true MF_pe MF_pc) ∧
      Frame {FPM} w w' ∧ w.fuel ≤ w'.fuel + 300 ∧ h' = h1) ?_ ?_
    · apply ReactMarkFinished.mrf_spec (s := w) (n := n + 8) (fo := fM) (t := .undefined) (FR := FR) (bG := bw)
        (oG := oG) {mimp} (hf := by omega) (hlt := lt_heap_of_frame hw hMo)
        (hG := by rw [MF_hdenv]; exact lt_envs_of_frame hw hG) (hGe := by rw [MF_hdenv]; exact hdw)
      all_goals {RB}
    · rintro v w' h' ⟨-, hpl, hF, hfu, rfl⟩
      exact ⟨hF, frame_trans hw hF, by omega, rfl, ⟨true, MF_pe, MF_pc, hpl⟩⟩
  case hfpM => intro p hp; simp [ReactMarkFinished.FPM] at hp
  case hfpMp =>
    intro p hp
    simp only [ReactMarkFinished.FPM, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp_all [Ne.symm dRF, Ne.symm dTF, Ne.symm dDF, Ne.symm dBF, Ne.symm dMF, Ne.symm dLF, Ne.symm dSF]""")
if "hBf" in DO:
    bimp = " ".join(f"({nm} := B_{nm})" for nm, k, t in binders(BMF, "cbm_full")
                    if k == "{" and nm not in ("n", "h", "s", "fo", "t", "FR", "R", "bG", "oG", "E", "ev0", "lanes"))
    bgv = " ".join(f"({nm} := {v})" for nm, v in bgiven.items())
    cases.append(f"""  case hBf =>
    intro w h1 hw hfw
    obtain ⟨bw, hdw, hbw⟩ := declLike_frame hw hG hGe
    refine' wp_mono (ReactBeforeMutation.cbm_full (s := w) (n := n + 8) (fo := fB) (t := .undefined) (FR := FR)
      (R := R) (bG := bw) (oG := oG) (E := E) (ev0 := ev0) (lanes := {LANE}) {bimp} (hf := by omega)
      (hlt := lt_heap_of_frame hw hBo) (hG := by rw [B_hdenv]; exact lt_envs_of_frame hw hG)
      (hGe := by rw [B_hdenv]; exact hdw) {bgv} ..) ?bpost
    case bpost =>
      rintro v w' h' ⟨-, rfl, hF, hfu, ⟨SI, hSI1, hSI2, hSI3, hSI4, hSI5, hSI6⟩, hev, hen⟩
      rw [B_hdenv] at hF hSI6 hev hen
      exact ⟨hF, frame_trans hw hF, by omega, rfl, ⟨SI, Nat.le_trans hw.heap_le hSI1, hSI2, hSI3, hSI4, hSI5, hSI6⟩,
        hev, hen⟩
    all_goals {RB}
  case hfpB =>
    intro p hp
    simp only [ReactBeforeMutation.FB, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl <;> exact ⟨hG, fun _ => by simp⟩
  case hfpBp => intro p hp; simp [ReactBeforeMutation.FB] at hp""")
hcall = []
if "hBf" in DO: hcall.append("(hBf := ?hBf) (hfpB := ?hfpB) (hfpBp := ?hfpBp) (hBc := ⟨_, B_hk⟩)")
if "hMf" in DO: hcall.append("(hMf := ?hMf) (hfpM := ?hfpM) (hfpMp := ?hfpMp) (hMc := ⟨_, MF_hk⟩)")
stmt = f"""theorem cmr_full {binds} :
    {CALL.replace("(n + 2)", "(n + 11)")} fun v w h' =>
      {POST} := by
  refine cmr_spec (n := n + 9) (K := 5800) {fixed} {cargs} {eargs} (hK := by omega)
    {" ".join(hcall)}
""" + "\n".join(cases) + "\n"
out = f'''import JSProofs.ReactCommitRootFn
import JSProofs.ReactMarkFinished
import JSProofs.ReactBeforeMutationFull

/-!
# commitRoot with the click's passes (zippy docs/react-proofs.md)

`cmr_full`: `cmr_spec` with its callees' contracts discharged at the call states (generated by
`tools/react_commit/gen_cmr_full.py`; so far: {", ".join(sorted(DO))}).
-/

open ES ES.M HostRuns Logic
open Std (HashMap)
open ReactFacts (BindIs PropIs SelInfo PropHas)

namespace ReactCommitRootFn

section
variable {{eng : Engine}} {{σ : Type}} {{answer : HostAnswer σ}}

set_option maxRecDepth 40000 in
set_option maxHeartbeats 8000000 in
{stmt}
end

end ReactCommitRootFn
'''
open("JSProofs/ReactCommitRootFnFull.lean", "w").write(out)
print(len(binds.split("\n")), "binder lines")
