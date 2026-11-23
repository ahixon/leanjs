"""Generates JSProofs/ReactCommitEntryFull.lean (zippy docs/react-proofs.md): cpr_spec (completeRoot) with its
commitRoot contract discharged by cmr_full (premises CM_) and flushPendingEffects by pending_none (PN_). cmr_full's
reads of the bindings completeRoot records come from the contract's antecedents; its premises over frames are stated
over states framed from completeRoot's entry by FPE."""
import re, sys
sys.path.insert(0, "tools/react_commit")
from compose import binders, compose, _rename, _theorem_header

CE = "JSProofs/ReactCommitEntry.lean"
CF = "JSProofs/ReactCommitRootFnFull.lean"
NE = "JSProofs/ReactNoEffects.lean"
Z = ".num (F64.fin false 0 (-1074))"
TWO = ".num (F64.fin false 4503599627370496 (-51))"
cb = binders(CE, "cpr_spec")
drop_outer = {"hPEf", "hCMf", "hPEc", "hCMc", "K", "hK", "P", "A", "lanes", "re", "sl", "ul", "srl"}
outer_ren = {"A": "R", "lanes": TWO, "re": ".null", "sl": Z, "ul": Z, "srl": Z}
def ren_outer(t):
    pat = re.compile(r"(?<![A-Za-z0-9_'.$])(" + "|".join(re.escape(x) for x in outer_ren) + r")(?![A-Za-z0-9_'$])")
    return pat.sub(lambda m: outer_ren[m.group(1)] if outer_ren[m.group(1)].startswith("(") or " " not in outer_ren[m.group(1)] else "(" + outer_ren[m.group(1)] + ")", t)
outer = [f"{k}{nm} : {ren_outer(t)}{'}' if k == '{' else ')'}" for nm, k, t in cb if nm not in drop_outer]
outer.insert(0, "{R : ObjId}")
outer = [b.replace("WP eng answer (n + 1)", "WP eng answer (n + 11)") for b in outer]
# cmr_full
mb = binders(CF, "cmr_full")
NAMES = {"pendingFinishedWork": "FW", "pendingEffectsRoot": "ER", "pendingEffectsLanes": "EL",
         "pendingRecoverableErrors": "RE"}
bdmap = {}
for nm, k, t in mb:
    m = re.match(r'bG\[JSStr\.ofString "(\w+)"\]\? = some (\w+)$', t.strip())
    if m and m.group(1) in NAMES: bdmap[m.group(2)] = (NAMES[m.group(1)], nm)
supplied = {}   # cmr_full binder -> term at application
for bd, (key, look) in bdmap.items():
    supplied[bd] = f"bd{key}'"; supplied[look] = f"hb{key}"
for nm, k, t in mb:
    for bd, (key, look) in bdmap.items():
        tt = t.strip()
        if tt.startswith(bd + ".value = some"): supplied[nm] = f"hv{key}"
        elif tt == bd + ".mutable = true": supplied[nm] = f"hm{key}"
        elif tt == bd + ".value.isSome = true": supplied[nm] = f"(by rw [hv{key}]; rfl)"
# cancelPendingCommit: completeRoot writes it null before commitRoot (hCMf's PropHas)
CPX = {"SP_cpw": "cpw'", "SP_cpe": "cpe'", "SP_cpc": "cpc'"}
supplied.update(CPX); supplied["SP_hFRc"] = "hCP'"
csubst = {"fo": "fCM", "t": ".undefined", "FR": "FR", "R": "R", "bG": "bG", "oG": "oG", "sst": "sst", "ME_lv": TWO}
QUANT = []
for nm, k, t in mb:
    if k == "(" and ("Frame" in t and t.strip().startswith("∀") or "DomRead" in t): QUANT.append(nm)
drop = ["n", "h", "s", "hf", "hlt", "hG", "hGe", "SP_hfpE"] + list(supplied)
cm, _ = compose(CF, "cmr_full", "CM_", subst=csubst, given={}, drop=tuple(drop))
FPE = "(FPE d.env FR)"
qgiven = {}
for i, b in enumerate(cm):
    nm = b[1:b.index(" : ")]
    if nm[3:] in QUANT:
        body = b[b.index(" : ") + 3:-1]
        body = re.sub(r"(?<![A-Za-z0-9_'.])s(?![A-Za-z0-9_'])", "s1", body)
        cm[i] = f"({nm} : ∀ s1, Frame {FPE} s s1 → {body})"
        qgiven[nm[3:]] = f"{nm} w hw"
cm += ["(CM_hdenv : CM_d.env = d.env)",
       "(dLPE : CM_ME_M_CT_BT_LP ≠ FR) (dNPE : CM_ME_M_CT_BT_NP ≠ FR) (dOPE : CM_ME_M_CT_BT_CH_U_OP ≠ FR)"]
pn, _ = compose(NE, "pending_none", "PN_", subst={"fo": "fPE", "t": ".undefined", "bG": "bG", "oG": "oG"}, given={},
                drop=("n", "h", "s", "hf", "hlt", "hG", "hGe", "hGS", "hGSv", "bdS"))
pn += ["(PN_hdenv : PN_d.env = d.env)"]
extra = ["(hf : 59200 ≤ s.fuel)"]
binds = "\n    ".join(outer + cm + pn + extra)
post_hdr = _theorem_header(CF, "cmr_full")
m = re.search(r"∧ \(∃ w0, (\(fun \(w : State\) \(h : σ\) => .*?\)) w0 h' ∧ Frame \{\} w0 w\) ∧ Frame (.*) s w\s*$", post_hdr, re.S)
_cren = {nm: csubst.get(nm, "CM_" + nm) for nm, k, t in mb if nm not in ("n", "h", "s")}
PCX = _rename(m.group(1), _cren)
FPCM = _rename(m.group(2), _cren)
P = f"(fun (w : State) (h : σ) => (∃ w0, {PCX} w0 h ∧ Frame {{}} w0 w) ∧ Frame ((FPE d.env FR).union {FPCM}) s w)"
fargs = " ".join(f"({nm} := {ren_outer(nm) if nm in outer_ren else nm})" for nm, k, t in cb
                 if nm not in drop_outer and nm not in ("n", "h", "s"))
fixed = " ".join(f"({nm} := {v})" for nm, v in outer_ren.items())
cimp = " ".join(f"({nm} := {supplied.get(nm, csubst.get(nm, 'CM_' + nm))})" for nm, k, t in mb
                if k == "{" and nm not in ("n", "h", "s", "bG"))
cexp = " ".join(f"({nm} := {v})" for nm, v in supplied.items() if nm not in [bd for bd in bdmap] and nm not in CPX)
qg = " ".join(f"({nm} := {v})" for nm, v in qgiven.items())
pimp = " ".join(f"({nm} := PN_{nm})" for nm, k, t in binders(NE, "pending_none")
                if k == "{" and nm not in ("n", "h", "s", "fo", "t", "bG", "oG", "bdS"))
UNF = "FPE, Footprint.union"
RB = (f"first | rebase_quick hw | (rw [hbw _ (by simp [{UNF}])] <;> with_reducible assumption) | "
      f"(rw [props_frame hw (by with_reducible assumption) (by simp [{UNF}, CM_ME_dMF])] <;> with_reducible assumption) | "
      f"(rw [kind_frame hw (by with_reducible assumption)] <;> with_reducible assumption) | "
      f"(rw [hw.obj_eq _ (by with_reducible assumption) (fun _ hk => by simp [{UNF}, dLPE, dNPE, dOPE] at hk)] <;> with_reducible assumption) | "
      f"(simp only [CM_ME_M_T_hdenv, CM_ME_M_CT_T_hdenv, CM_ME_M_CT_BT_CH_hdenv, CM_ME_M_hdenv, CM_hdenv, CM_B_hdenv, CM_ME_hdenv, CM_LE_hdenv, CM_SP_hdenv, CM_MF_hdenv]; first | exact hdw | exact lt_envs_of_frame hw hG)")
BI = "obtain ⟨_, _, {bd}, {hd}, {hb}, {hv}, {hm}⟩ := {src}\n    rw [hdw] at {hd}; cases {hd}"
stmt = f"""theorem cpr_full {binds} :
    WP eng answer (n + 12) h (callImpl eng (.obj fo) t #[.obj FR, .obj R, {TWO}, .null, tr, di, {Z}, {Z}, {Z}, ds, es, sst])
      s fun v w h' => v = .undefined ∧ s.fuel ≤ w.fuel + 2 * 29400 + 200 ∧ ∃ w0, {P} w0 h' ∧ Frame {{}} w0 w := by
  refine cpr_spec (n := n + 10) (K := 29400) (P := {P}) {fixed} {fargs} (hK := by omega)
    (hPEc := ⟨_, PN_hk⟩) (hCMc := ⟨_, CM_hk⟩) (hPEf := ?hPEf) (hCMf := ?hCMf)
  case hPEf =>
    intro w h1 hw hfw
    obtain ⟨bw, hdw, hbw⟩ := declLike_frame hw hG hGe
    refine' wp_mono (ReactNoEffects.pending_none (s := w) (n := n + 10) (fo := fPE) (t := .undefined) (bG := bw) (oG := oG)
      (bdS := bS) {pimp} (hf := by omega) (hlt := lt_heap_of_frame hw hPEo)
      (hG := by rw [PN_hdenv]; exact lt_envs_of_frame hw hG) (hGe := by rw [PN_hdenv]; exact hdw)
      (hGS := by rw [hbw _ (by simp [{UNF}])]; exact gS) (hGSv := gSv) ..) ?ppost
    case ppost =>
      rintro v w' h' ⟨-, hF, hfu, rfl⟩
      exact ⟨hF, by omega, rfl⟩
    all_goals {RB}
  case hCMf =>
    intro w h1 hw hFW hER hEL hRE hCP hfw
    obtain ⟨cpw', cpe', cpc', hCP'⟩ := hCP
    obtain ⟨bw, hdw, hbw⟩ := declLike_frame hw hG hGe
    {BI.format(bd="bdFW'", hd="hd1", hb="hbFW", hv="hvFW", hm="hmFW", src="hFW")}
    {BI.format(bd="bdER'", hd="hd2", hb="hbER", hv="hvER", hm="hmER", src="hER")}
    {BI.format(bd="bdEL'", hd="hd3", hb="hbEL", hv="hvEL", hm="hmEL", src="hEL")}
    {BI.format(bd="bdRE'", hd="hd4", hb="hbRE", hv="hvRE", hm="hmRE", src="hRE")}
    refine' wp_mono (ReactCommitRootFn.cmr_full (s := w) (n := n) (bG := bw) {cimp} (hf := by omega)
      (hlt := lt_heap_of_frame hw hCMo) (hG := by rw [CM_hdenv]; exact lt_envs_of_frame hw hG)
      (hGe := by rw [CM_hdenv]; exact hdw) {cexp} {qg}
      (SP_E_hP := by rw [hw.realms_eq]; exact CM_SP_E_hP) ..) ?cpost
    case cpost =>
      rintro v w' h' ⟨-, hfu, hP, hFc⟩
      exact ⟨by omega, hP, frame_trans hw hFc⟩
    all_goals {RB}
"""
out = f'''import JSProofs.ReactCommitEntry
import JSProofs.ReactCommitRootFnFull

/-!
# completeRoot with the click's commit (zippy docs/react-proofs.md)

`cpr_full`: `cpr_spec` with `commitRoot` discharged by `cmr_full` and `flushPendingEffects` by `pending_none` at the
call states (generated by `tools/react_commit/gen_cpr_full.py`).
-/

open ES ES.M HostRuns Logic
open Std (HashMap)
open ReactFacts (BindIs PropIs SelInfo PropHas)
open ReactFlushMutation (FPRE)
open ReactSpawned (FPS FPA FP1)
open ReactCommitRootFn (FPC)

namespace ReactCommitEntry

section
variable {{eng : Engine}} {{σ : Type}} {{answer : HostAnswer σ}}

set_option maxRecDepth 40000 in
set_option maxHeartbeats 8000000 in
{stmt}
end

end ReactCommitEntry
'''
open("JSProofs/ReactCommitEntryFull.lean", "w").write(out)
print(len(binds.split("\n")), "binder lines;", len(QUANT), "quantified;", len(supplied), "supplied")
