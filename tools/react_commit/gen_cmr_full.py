"""Generates JSProofs/ReactCommitRootFnFull.lean (zippy docs/react-proofs.md): cmr_spec with its callees' contracts
discharged by their composed specs at the call states. Stage list `DO` says which contracts are discharged so far (the
rest stay premises)."""
import re, sys
sys.path.insert(0, "tools/react_commit")
from compose import binders, compose, _rename, _theorem_header

DO = {"hMf", "hBf", "hMEf"}
CR = "JSProofs/ReactCommitRootFn.lean"
MF = "JSProofs/ReactMarkFinished.lean"
BMF = "JSProofs/ReactBeforeMutationFull.lean"
FMF = "JSProofs/ReactFlushMutationFull.lean"
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
F2 = f"({F1}.union (ReactBeforeMutation.FB d.env))"
ME_SUPPLIED = ["SI", "hGSI", "hGSIv", "hGSIm", "hSI", "hSIk", "hSIf", "hSIr", "dTS", "dDS", "dFS", "dMS", "bdSI", "fw",
  "fe", "fc", "srv", "rw", "re", "rc", "hGS", "hGSv", "hGSm", "bdS", "hGE", "hGEv", "hGEm", "bdE", "hGEn", "hGEnm",
  "hGEni", "bdEn", "hGEv'", "hGEvv", "hGEvm", "bdEv", "evv", "hRSIt", "te", "tc", "hRDSIp", "pe", "pc"]
ME_SUBST = {"fo": "fME", "t": ".undefined", "bG": "bG", "oG": "oG", "FR": "FR", "R": "R", "RSI": "RSI", "RDSI": "RDSI",
  "E": "E", "ec": "ec", "tv": "tv", "pv": "pv"}
if "hMEf" in DO:
    drop_outer |= {"hMEf", "hMEc", "fpME", "hfpME", "hfpMEp", "Q1"}
    _h = _theorem_header(FMF, "fme_full")
    _post = _h[_h.rindex("fun v w h' =>") + len("fun v w h' =>"):].strip()
    _ren = {}
    for nm, k, t in binders(FMF, "fme_full"):
        if nm in ("n", "h", "s"): continue
        _ren[nm] = ME_SUBST.get(nm, "ME_" + nm)
    _pm = re.match(r"v = \.undefined ∧ s\.fuel ≤ w\.fuel \+ 5700 ∧ \(∃ w0, (.*?) w0 h'\) ∧\s*Frame (.*) s w ∧\s*BindIs w d\.env", _post, re.S)
    PCME = _rename(_pm.group(1), _ren)
    FME = _rename(_pm.group(2), _ren)
    outer_ren["fpME"] = FME
    Q1 = (f"(fun (w : State) (h : σ) => (∃ w0, {PCME} w0 h) ∧ BindIs w d.env (JSStr.ofString \"pendingEffectsStatus\") "
          f"(.num ({LANE})) ∧ BindIs w d.env (JSStr.ofString \"executionContext\") (.num ec) ∧ "
          f"PropIs w RSI (JSStr.ofString \"T\") tv ∧ PropIs w RDSI (JSStr.ofString \"p\") pv)")
    outer_ren["Q1"] = Q1
def _balanced(t, i):
    """index just after the parenthesised group starting at t[i] == '('"""
    d = 0
    for j in range(i, len(t)):
        if t[j] == "(": d += 1
        elif t[j] == ")":
            d -= 1
            if d == 0: return j + 1
    raise ValueError(t)
def widen(t, FP):
    m = re.search(r"Frame \(", t)
    if m and "→" in t[m.end():]:
        i = m.end() - 1; j = _balanced(t, i)
        if t[j:].startswith(" s w →"):
            return t[:i] + f"({FP}.union {t[i:j]})" + t[j:]
    m = re.search(r"DomRead eng answer (\(n \+ \d+\)|\S+) s \(", t)
    assert m, t
    i = m.end() - 1; j = _balanced(t, i)
    return t[:i] + f"({FP}.union {t[i:j]})" + t[j:]
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
megiven = {}
if "hMEf" in DO:
    mb, _ = compose(FMF, "fme_full", "ME_", subst=ME_SUBST, given={},
                    drop=tuple(["n", "h", "s", "hf", "hlt", "hG", "hGe"] + ME_SUPPLIED))
    MQ = ["hGDC", "M_GH_hRN", "M_GH_hCall", "M_GH_hNT", "M_CT_BT_CH_U_hI", "M_CT_BT_CH_U_hOC", "M_CT_BT_CH_U_hFC",
          "M_CT_BT_CH_U_hLC", "M_CT_BT_CH_U_hNT", "M_CT_BT_CH_U_hNV"]
    MQ1 = {"M_GH_hRN", "M_CT_BT_CH_U_hI"}
    for i, b in enumerate(mb):
        nm = b[1:b.index(" : ")]
        if nm[3:] in MQ:
            mb[i] = b[0] + nm + " : " + widen(b[b.index(" : ") + 3:-1], F2) + b[-1]
            megiven[nm[3:]] = (f"fun w' hw' => {nm} w' (frame_trans hw hw')" if nm[3:] in MQ1
                               else f"fun w' h1 hw' => {nm} w' h1 (frame_trans hw hw')")
    added += mb + ["(ME_hdenv : ME_d.env = d.env) (dDomH : ME_M_CT_dom < s.heap.size)",
                   "(dDomL : ME_M_CT_dom ≠ fLE) (dDomS : ME_M_CT_dom ≠ fSP) (dDomA : ME_M_CT_dom ≠ MF_EA) (dDomX : ME_M_CT_dom ≠ MF_XA)"] + \
             [f"(d{o}{x} : {e} ≠ {y})" for o, e in (("LP", "ME_M_CT_BT_LP"), ("NP", "ME_M_CT_BT_NP"), ("OP", "ME_M_CT_BT_CH_U_OP"))
              for x, y in (("F", "FR"), ("A", "MF_EA"), ("X", "MF_XA"))]
extra = ["(hf : 29400 ≤ s.fuel)"]
_islate = lambda b: "MF_" in b or "ReactBeforeMutation.FB" in b or "ME_" in b
late = [b for b in outer if _islate(b)]
outer = [b for b in outer if not _islate(b)]
binds = "\n    ".join(outer + added + extra + late)
cargs = " ".join(f"({nm} := {ren_outer(nm) if nm in outer_ren else nm})" for nm, k, t in cb
                 if nm not in drop_outer and nm not in ("n", "h", "s") and k == "{")
eargs = " ".join(f"({nm} := {nm})" for nm, k, t in cb if nm not in drop_outer and k == "(")
fixed = " ".join(f"({nm} := {v})" for nm, v in outer_ren.items() if nm not in ("K",))
post_hdr = _theorem_header(CR, "cmr_spec")
POST = ren_outer(post_hdr[post_hdr.rindex("fun v w h' =>") + len("fun v w h' =>"):].strip())
CALL = ren_outer(post_hdr[post_hdr.rindex("WP eng answer"):post_hdr.rindex("fun v w h' =>")].strip())
UNF = "FPC, ReactMarkFinished.FPM, ReactBeforeMutation.FB, Footprint.union"
RB = (f"first | rebase_quick hw | (rw [hbw _ (by simp [{UNF}])] <;> with_reducible assumption) | "
      f"(rw [props_frame hw (by with_reducible assumption) (by simp [{UNF}])] <;> with_reducible assumption) | "
      f"(rw [kind_frame hw (by with_reducible assumption)] <;> with_reducible assumption)")
WHOLE = ("dLPF, dLPA, dLPX, dNPF, dNPA, dNPX, dOPF, dOPA, dOPX, ME_dLT, ME_dLD, ME_dNT, ME_dND, ME_dOT, ME_dOD")
RBME = (f"first | rebase_quick hw | (rw [hbw _ (by simp [{UNF}])] <;> with_reducible assumption) | "
        f"(rw [props_frame hw (by with_reducible assumption) (by simp [{UNF}, ME_dMF, ME_dMT, ME_dMD, dDomA, dDomX])] <;> with_reducible assumption) | "
        f"(rw [kind_frame hw (by with_reducible assumption)] <;> with_reducible assumption) | "
        f"(rw [hw.obj_eq _ (by with_reducible assumption) (fun _ hk => by simp [{UNF}, {WHOLE}] at hk)] <;> with_reducible assumption)")
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
if "hMEf" in DO:
    meimp = " ".join(f"({nm} := ME_{nm})" for nm, k, t in binders(FMF, "fme_full")
                     if k == "{" and nm not in ["n", "h", "s"] + list(ME_SUBST) + ME_SUPPLIED)
    megv = " ".join(f"({nm} := {v})" for nm, v in megiven.items())
    BI = "obtain ⟨_, _, {bd}, {hd}, {hb}, {hv}, {hm}⟩ := {src}\n    rw [hdw] at {hd}; cases {hd}"
    cases.append(f"""  case hMEf =>
    intro w h1 hw hst hec hT hp hsel hfw
    obtain ⟨bw, hdw, hbw⟩ := declLike_frame hw hG hGe
    {BI.format(bd="bS'", hd="hd1", hb="hb1", hv="hv1", hm="hm1", src="hst")}
    {BI.format(bd="bE'", hd="hd2", hb="hb2", hv="hv2", hm="hm2", src="hec")}
    obtain ⟨⟨SI, hSI1, hSI2, hSI3, ⟨fw', fe', fc', hSIf'⟩, ⟨srv', rw', re', rc', hSIr'⟩, hsi⟩, hev, hen⟩ := hsel
    {BI.format(bd="bSI'", hd="hd3", hb="hb3", hv="hv3", hm="hm3", src="hsi")}
    {BI.format(bd="bEv'", hd="hd4", hb="hb4", hv="hv4", hm="hm4", src="hev")}
    {BI.format(bd="bEn'", hd="hd5", hb="hb5", hv="hv5", hm="hm5", src="hen")}
    obtain ⟨te', tc', hT'⟩ := hT
    obtain ⟨pe', pc', hp'⟩ := hp
    have hSIs : s.heap.size ≤ SI := hSI1
    refine' wp_mono (ReactFlushMutation.fme_full (s := w) (n := n) (fo := fME) (t := .undefined) (bG := bw) (oG := oG)
      (FR := FR) (R := R) (RSI := RSI) (RDSI := RDSI) (E := E) (ec := ec) (tv := tv) (pv := pv) (SI := SI)
      (bdS := bS') (bdE := bE') (bdSI := bSI') (bdEv := bEv') (bdEn := bEn') (evv := ev0) (te := te') (tc := tc')
      (pe := pe') (pc := pc') (fw := fw') (fe := fe') (fc := fc') (srv := srv') (rw := rw') (re := re') (rc := rc')
      {meimp} (hf := by omega) (hlt := lt_heap_of_frame hw hMEo)
      (hG := by rw [ME_hdenv]; exact lt_envs_of_frame hw hG) (hGe := by rw [ME_hdenv]; exact hdw)
      (hGS := hb1) (hGSv := hv1) (hGSm := hm1) (hGE := hb2) (hGEv := hv2) (hGEm := hm2)
      (hGSI := hb3) (hGSIv := hv3) (hGSIm := hm3) (hGEv' := hb4) (hGEvv := hv4) (hGEvm := hm4)
      (hGEn := hb5) (hGEnm := hm5) (hGEni := by rw [hv5]; rfl) (hRSIt := hT') (hRDSIp := hp')
      (hSI := hSI2) (hSIk := hSI3) (hSIf := hSIf') (hSIr := hSIr')
      (dTS := Nat.ne_of_lt (Nat.lt_of_lt_of_le hRSI hSIs)) (dDS := Nat.ne_of_lt (Nat.lt_of_lt_of_le hRDSI hSIs))
      (dFS := Nat.ne_of_lt (Nat.lt_of_lt_of_le hFR hSIs)) (dMS := Nat.ne_of_lt (Nat.lt_of_lt_of_le dDomH hSIs))
      {megv} ..) ?mpost
    case mpost =>
      rintro v w' h' ⟨-, hfu, hPC, hF, hst2, hec2, hT2, hp2⟩
      rw [ME_hdenv] at hst2 hec2
      exact ⟨hF, frame_trans hw hF, by omega, hPC, hst2, hec2, hT2, hp2⟩
    all_goals try (simp only [ME_M_T_hdenv, ME_M_CT_T_hdenv, ME_M_CT_BT_CH_hdenv, ME_M_hdenv, ME_hdenv]; first | exact hdw | exact lt_envs_of_frame hw hG)
    all_goals {RBME}
  case hfpME =>
    intro p hp
    simp only [Footprint.union, FPRE, ReactCommitRoot.F0, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at hp
    rcases hp with ((((hp | hp | hp | hp) | (hp | hp | hp) | hp | hp) | (hp | hp | hp))) <;> subst hp <;>
      simp [ME_hdenv, ME_M_hdenv, ME_M_CT_BT_CH_hdenv, hG]
  case hfpMEp =>
    intro p hp
    simp only [Footprint.union, FPRE, ReactCommitRoot.F0, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false, List.nil_append, List.append_nil] at hp
    rcases hp with ((hp | hp) | hp) | hp <;> subst hp <;>
      simp_all [Ne.symm dLT, Ne.symm dLD, Ne.symm dLF, Ne.symm dST, Ne.symm dSD, Ne.symm dSF]""")
hcall = []
if "hBf" in DO: hcall.append("(hBf := ?hBf) (hfpB := ?hfpB) (hfpBp := ?hfpBp) (hBc := ⟨_, B_hk⟩)")
if "hMEf" in DO: hcall.append("(hMEf := ?hMEf) (hfpME := ?hfpME) (hfpMEp := ?hfpMEp) (hMEc := ⟨_, ME_hk⟩)")
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
import JSProofs.ReactFlushMutationFull

/-!
# commitRoot with the click's passes (zippy docs/react-proofs.md)

`cmr_full`: `cmr_spec` with its callees' contracts discharged at the call states (generated by
`tools/react_commit/gen_cmr_full.py`; so far: {", ".join(sorted(DO))}).
-/

open ES ES.M HostRuns Logic
open Std (HashMap)
open ReactFacts (BindIs PropIs SelInfo PropHas)
open ReactFlushMutation (FPRE)

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
