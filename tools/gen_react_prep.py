"""The click's microtask with prepareFreshStack's hypothesis (r_Prep) discharged by ReactPrepareFresh.call_spec
(zippy docs/react-proofs.md): `prep_hyp` carries its premises from the microtask's start to the call through the
frames in between; `microtask_render_prep` is `microtask_render_fin` with r_Prep proved by it."""
import sys, os, re
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from react_sig import sig, names_of_imp, hname
from react_compose import subst, concl_text, hyp_type
ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
PFS = ROOT + "/JSProofs/ReactPrepareFresh.lean"
TOP = ROOT + "/JSProofs/ReactMicrotaskFinish.lean"
pi, ph = sig(PFS, "call_spec", "    WP eng answer (n + 2)")
SET = {"n", "h", "fo", "d", "t", "s", "bG"}
KEEP = {"R", "oG"}
ren = {}; imps = []; passes = []
for b in pi:
    ty = b[b.index(":"):-1]
    keep = []
    for x in names_of_imp(b):
        if x in SET: continue
        nx = x if x in KEEP else "p_" + x
        ren[x] = nx
        if x not in KEEP: keep.append(nx)
        passes.append(f"({x} := {nx})")
    if keep: imps.append("{" + " ".join(keep) + " " + subst(ty, ren) + "}")
SELF = {"hlt": "heap_frame hT hPFo", "hk": "by rw [kind_frame hT hPFo, hPFk]; cases dPF; simp_all",
        "hf": "by omega", "hcode": "hPFcode", "hcls": "hPFcls", "hmode": "hPFmode",
        "hG": "envs_frame hT hG", "hGe": "hWd"}
FPS = "ReactMicrotaskClick.fpPerf, ReactSchedTaskRoot.fp, ReactRenderSync.fpPre, Logic.Footprint.union"
hyps = []; args = []
for b in ph:
    n = hname(b)
    if n in SELF: args.append(f"({n} := {SELF[n]})"); continue
    ty = subst(hyp_type(b), ren)
    ty = re.sub(r"(?<![\w.'])d\.(code|isClassCtor|thisMode)\b", r"dPF.\1", ty)
    nn = "p_" + n
    hyps.append(f"({nn} : {ty})")
    if re.search(r"\bbG\[", ty):
        args.append(f"({n} := by rw [hWx _ (by simp [{FPS}])]; exact {nn})")
    elif re.fullmatch(r"\S+ < s\.heap\.size", ty):
        args.append(f"({n} := heap_frame hT {nn})")
    elif ".kind" in ty and "s.objEntry" in ty:
        args.append(f"({n} := by rw [kind_frame hT]; exact {nn}; assumption)")
    elif ".props.get?" in ty and "s.objEntry" in ty:
        args.append(f"({n} := by rw [props_frame hT]; exact {nn}; all_goals first | assumption | simp [{FPS}, p_dA])")
    else:
        args.append(f"({n} := {nn})")
# r_Prep's type from the top theorem, instantiated
ti, th = sig(TOP, "microtask_render_fin", "    WP eng answer (j + 6)")
rp = hyp_type([b for b in th if hname(b) == "r_Prep"][0])
PFP = "(ReactPrepareFresh.fp d.env p_X p_A p_Qo p_U p_F p_Fa p_H)"
P1 = (f"(fun w' (_ : σ) => Frame (((((ReactMicrotaskClick.fpPerf d.env R A).union {{}}).union {{}}).union "
      f"(ReactRenderSync.fpPre d.env I)).union {PFP}) s w' ∧ ReactPrepareFresh.PrepBinds w' d.env oG p_X ∧ "
      f"ReactPrepareFresh.PrepFields w' p_X p_H p_F p_Fa p_Qo p_U p_vT p_vL p_vC p_vMP p_vMS p_vUQ p_vS p_vI p_vR p_vRC "
      f"p_fl p_hc p_fl' p_al)")
INST = {"P1": P1, "fpPF": PFP, "kP": "400", "j": "(j + 2)"}
rp_i = subst(rp, INST)
lemma = f"""set_option maxHeartbeats 8000000 in
set_option maxRecDepth 40000 in
/-- **`r_Prep` from facts at the microtask's start**: `prepareFreshStack`'s premises hold where it is called because
none of them is about what the steps before it write (`fpPerf`, `fpPre`). The work loop then starts from a state
framed from the microtask's start (`P1`). -/
theorem prep_hyp {{j : Nat}} {{s : State}} {{d dPF : FuncData}} {{R A I fPF : ObjId}} {{bG : HashMap JSStr Binding}}
    {{oG : Option EnvId}} {" ".join(imps)}
    (hPFo : fPF < s.heap.size) (hPFk : (s.objEntry fPF).kind = .func dPF)
    (hPFcode : dPF.code = PFSGen.prepareFreshStack_func) (hPFcls : dPF.isClassCtor = false)
    (hPFmode : dPF.thisMode = .strict) (hPFenv : dPF.env = d.env)
    (hG : d.env < s.envs.size) (hGe : Scope.declLike? (s.envEntry d.env) = some (bG, oG)) (hfu : 1000 ≤ s.fuel)
    (p_dA : p_A ≠ A)
    {chr(10).join("    " + x for x in hyps)} :
    {rp_i} := by
  intro sP hP fuP sW hW fuW sR hR fuR w h1 hpre fuw
  have hT := frame_trans (frame_trans (frame_trans hP hW) hR) hpre
  obtain ⟨bW, hWd, hWx⟩ := declLike_frame hT hG hGe
  refine wp_mono (ReactPrepareFresh.call_spec (n := j) (d := {{ dPF with env := d.env }}) (bG := bW)
    {" ".join(passes)}
    {" ".join(args)}) ?_
  intro v w' h' ⟨_, hF', hfu', hh, hAP, hPB, hPF⟩
  subst hh
  exact ⟨hF', by omega, hAP, frame_trans hT hF', hPB, hPF⟩
"""
# the top theorem with r_Prep discharged
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
imps2 = []; passes2 = []
for b in ti:
    ty = b[b.index(":"):-1]
    keep = [x for x in names_of_imp(b) if x not in INST or x == "j"]
    if keep: imps2.append("{" + " ".join(keep) + " " + subst(ty, {k: v for k, v in INST.items() if k != "j"}) + "}")
    for x in names_of_imp(b): passes2.append(f"({x} := {INST.get(x, x)})")
OBJ = ["p_X", "p_A", "p_Qo", "p_U", "p_F", "p_Fa", "p_H"]
TGT = ["I", "fWL", "fFQ", "fCR", "v_fE", "fG"]
dist = [f"(o_{a}_{b} : {a} ≠ {b})" for a in OBJ for b in TGT]
DN = ", ".join(f"o_{a}_{b}, Ne.symm o_{a}_{b}" for a in OBJ for b in TGT)
hyps2 = []; args2 = []
for b in th:
    n = hname(b); ty = subst(hyp_type(b), INST)
    if n == "r_Prep": continue
    if PFP in ty and "WP eng answer" not in ty: args2.append(f"({n} := by simp [ReactPrepareFresh.fp, ReactCreateWIP.fp, hG, {DN}])"); continue
    hyps2.append(f"({n} : {ty})"); args2.append(f"({n} := {n})")
# prep_hyp's own hypotheses (theirs, at the start state)
for b in ph:
    n = hname(b)
    if n in SELF: continue
    nn = "p_" + n
    ty = subst(hyp_type(b), ren)
    ty = re.sub(r"(?<![\w.'])d\.(code|isClassCtor|thisMode)\b", r"dPF.\1", ty)
    hyps2.append(f"({nn} : {ty})")
hyps2 += ["(hPFcode : dPF.code = PFSGen.prepareFreshStack_func) (hPFcls : dPF.isClassCtor = false)",
          "(hPFmode : dPF.thisMode = .strict) (hPFenv : dPF.env = d.env) (p_dA : p_A ≠ A)"] + dist
pargs = " ".join(f"(p_{hname(b)} := p_{hname(b)})" for b in ph if hname(b) not in SELF)
_src = open(TOP).read(); _i = _src.index("theorem microtask_render_fin"); _j = _src.index("    WP eng answer (j + 6)", _i)
c = subst(_src[_j:_src.index(" :=", _j)].strip(), INST)
top = (f"set_option maxHeartbeats 8000000 in\nset_option maxRecDepth 40000 in\n"
       f"/-- The click's microtask with `prepareFreshStack` proved (`prep_hyp`). -/\n"
       f"theorem microtask_render_prep " + " ".join(imps2) + " " + " ".join(imps) + "\n    " + "\n    ".join(hyps2) +
       " :\n    " + c + " :=\n  microtask_render_fin " + " ".join(passes2) + "\n    " + " ".join(args2) +
       f"\n    (r_Prep := prep_hyp (j := j) (s := s) (d := d) (dPF := dPF) (R := R) (A := A) (I := I) (fPF := fPF) "
       f"(bG := bG) (oG := oG) r_PFo r_PFk hPFcode hPFcls hPFmode hPFenv hG hGe (by omega) p_dA {pargs})\n")
hdr = '''import JSProofs.ReactMicrotaskFinish
import JSProofs.ReactPrepareFresh

/-!
# The click's microtask with `prepareFreshStack` proved (zippy docs/react-proofs.md)

Generated by `tools/gen_react_prep.py`.
-/

open ES ES.M HostRuns Logic
open Std (HashMap)

namespace ReactRenderClick

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ}

'''
open(ROOT + "/JSProofs/ReactMicrotaskPrep.lean", "w").write(hdr + lemma + "\nend\n\n" + top + "\nend ReactRenderClick\n")
