"""Generates ReactBeginRoot.lean: beginWork on the host root in a click's render (its early return: same props, no
scheduled update, so attemptEarlyBailoutIfNoScheduledUpdate). zippy docs/react-proofs.md"""
import os, re, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from react_sig import sig, names_of_imp, hname
from react_compose import subst, hyp_type
ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
J = lambda f: ROOT + "/JSProofs/" + f
TWO = "(F64.fin false 4503599627370496 (-51))"
ai, ah = sig(J("ReactEarlyBailout.lean"), "root_spec", "    WP eng answer")
ci, ch = sig(J("ReactRootBailout.lean"), "check_none", "    WP eng answer")
AEB_SET = {"n": "n", "h": None, "fo": "fAEB", "d": "dAEB", "t": ".undefined", "s": None}
imps = []; seen = set()
def add(names, ty):
    k = [x for x in names if x not in seen]; seen.update(k)
    if k: imps.append("{" + " ".join(k) + " " + ty + "}")
for b in ai:
    ty = b[b.index(":"):-1]
    add([x for x in names_of_imp(b) if x not in AEB_SET], ty)
add(["fAEB", "fCHK"], ": ObjId"); add(["dAEB", "dCHK"], ": FuncData"); add(["bdAEB", "bdCHK", "bdDRU"], ": Binding")
add(["hl0v"], ": F64"); add(["xf"], ": F64")
add(["hlw", "hle", "hlc", "hdw2", "hde2", "hdc2", "mpw", "mpe", "mpc", "ppw", "ppe", "ppc", "xfw", "xfe", "xfc"], ": Bool")
EXT = '(Logic.Footprint.union (ReactHostContainer.fp d.env VS a_RI a_CF a_CS) ⟨[(d.env, "didReceiveUpdate")], [], false⟩)'
hyps = []
AEB_SELF = {"hlt", "hk", "hf", "hcode", "hcls", "hmode", "hG", "hGe"}
for b in ah:
    n0 = hname(b)
    if n0 in AEB_SELF: continue
    ty = hyp_type(b)
    ty = re.sub(r"(?<![\w.'])dAEB\b", "dAEB", ty)
    if "ReactHostContainer.DomRead" in ty:
        ty = ty.replace("(ReactHostContainer.fp d.env VS a_RI a_CF a_CS)", EXT)
    hyps.append(f"({n0} : {ty})")
own = ["(hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : 700 ≤ s.fuel)",
       "(hcode : d.code = BWGen.beginWork_func) (hcls : d.isClassCtor = false) (hmode : d.thisMode = .strict)",
       "(hG : d.env < s.envs.size) (hGe : Scope.declLike? (s.envEntry d.env) = some (bG, oG))",
       "(g_CHK : bG[JSStr.ofString \"checkScheduledUpdateOrContext\"]? = some bdCHK) (g_CHKv : bdCHK.value = some (.obj fCHK))",
       "(h_CHK : fCHK < s.heap.size) (h_CHKk : (s.objEntry fCHK).kind = .func dCHK) (h_CHKcode : dCHK.code = CSUGen.checkScheduledUpdateOrContext_func)",
       "(h_CHKcls : dCHK.isClassCtor = false) (h_CHKmode : dCHK.thisMode = .strict)",
       "(g_AEB : bG[JSStr.ofString \"attemptEarlyBailoutIfNoScheduledUpdate\"]? = some bdAEB) (g_AEBv : bdAEB.value = some (.obj fAEB))",
       "(h_AEB : fAEB < s.heap.size) (h_AEBk : (s.objEntry fAEB).kind = .func dAEB) (h_AEBcode : dAEB.code = AEBGen.attemptEarlyBailoutIfNoScheduledUpdate_func)",
       "(h_AEBcls : dAEB.isClassCtor = false) (h_AEBmode : dAEB.thisMode = .strict) (h_AEBenv : dAEB.env = d.env)",
       "(g_DRU : bG[JSStr.ofString \"didReceiveUpdate\"]? = some bdDRU) (g_DRUm : bdDRU.mutable = true) (g_DRUv : bdDRU.value.isSome = true)",
       "(hHmp : (s.objEntry H).props.get? (.str \"memoizedProps\") = some (.data .null mpw mpe mpc))",
       "(hXpp : (s.objEntry X).props.get? (.str \"pendingProps\") = some (.data .null ppw ppe ppc))",
       "(hHl : (s.objEntry H).props.get? (.str \"lanes\") = some (.data (.num hl0v) hlw hle hlc))",
       "(hHd2 : (s.objEntry H).props.get? (.str \"dependencies\") = some (.data .null hdw2 hde2 hdc2))",
       f"(hl0 : isStrictlyEqual (.num (F64.fin false 0 (-1074))) (.num (numberBinOp .bitAnd hl0v {TWO})) = true)",
       "(hXf : (s.objEntry X).props.get? (.str \"flags\") = some (.data (.num xf) xfw xfe xfc))",
       "(hxf : isStrictlyEqual (.num (F64.fin false 0 (-1074))) (.num (numberBinOp .bitAnd xf (F64.fin false 4503599627370496 (-45)))) = true)",
       "(x_CHK_X : fCHK ≠ X) (x_CHK_H : fCHK ≠ H) (x_AEB_X : fAEB ≠ X) (x_AEB_H : fAEB ≠ H)"]
hyps = own + hyps
# objects: heap facts by object, from the statement
def split(lines):
    out = []
    for line in lines:
        dep = 0; cur = ""
        for c in line:
            if c == "(":
                if dep == 0: cur = ""
                dep += 1
            if dep > 0: cur += c
            if c == ")":
                dep -= 1
                if dep == 0: out.append(cur)
    return out
allh = split(hyps)
heaps = {}
for x in allh:
    m = re.match(r"\((\w+'?) : (\w+) < s\.heap\.size\)$", x)
    if m: heaps[m.group(2)] = m.group(1)
T = "(by first | assumption | (simp only [js_simp]; done) | (simp only [js_simp]; omega))"
JSF = ("hG, hGe, g_CHK, g_CHKv, h_CHK, h_CHKk, g_AEB, g_AEBv, h_AEB, h_AEBk, g_DRU, g_DRUm, g_DRUv, hHmp, hXpp, hHl, hHd2, "
       "hl0, hXf, hxf, e_hX, e_hXk, e_hH, e_hHk, x_CHK_X, x_CHK_H, x_AEB_X, x_AEB_H, Ne.symm x_CHK_X, Ne.symm x_CHK_H, "
       "Ne.symm x_AEB_X, Ne.symm x_AEB_H, hpn, hv, hl, ha, hne, Ne.symm hne, hG1, beq_self_eq_true, FDI.fdiCtx, Sem.inner")
DR = []
def aeb_arg(b):
    n0 = hname(b); ty = hyp_type(b)
    if n0 in ("hcode", "hcls", "hmode"): return f"h_AEB{n0[1:]}"
    if n0 == "hGe": return "?geA"
    if n0 == "hG": return "(by rw [h_AEBenv]; first | (simp only [js_simp]; omega) | (simp only [js_simp]; done) | omega)"
    if n0 in ("hlt", "hk", "hf"): return "?_"
    if "ReactHostContainer.DomRead" in ty:
        DR.append(n0)
        return f"?dr_{n0}"
    m = re.match(r"\(s\.objEntry (\w+)\)\.", ty)
    if m and m.group(1) in heaps:
        return f"(by simp only [js_simp]; rw [oo1 _ {heaps[m.group(1)]}]; exact {n0})"
    m = re.fullmatch(r"(\w+) < s\.heap\.size", ty)
    if m: return f"(by simp only [js_simp]; exact heap_frame hF1 (by simpa using {n0}))"
    m = re.match(r"bG\[JSStr\.ofString \"([^\"]+)\"\]\? = ", ty)
    if m: return f"(by simp only [Std.HashMap.getElem?_modify]; js_norm [{n0}])"
    if "d.env < s.envs.size" in ty: return "?_"
    if re.search(r"(?<![\w.'])s(?![\w'])", ty): return "?_"
    if "d.env" in ty: return f"(by rw [h_AEBenv]; exact {n0})"
    return n0
aimp = []
for b in ai:
    for x in names_of_imp(b):
        if x in AEB_SET:
            v = AEB_SET[x]
            if v: aimp.append(f"({x} := {v})")
        else: aimp.append(f"({x} := {x})")
aimp = [a for a in aimp if not a.startswith("(bG :=")]
RREC = '(bG.modify (JSStr.ofString "didReceiveUpdate") (fun bd => { bd with value := some (.bool false) }))'
aargs = " ".join(aeb_arg(b) for b in ah)
DRC = "".join(f"""    case dr_{x} =>
      intro w h1 hF
      refine {x} w h1 (frame_mono (frame_trans (fp1 := ⟨[(d.env, "didReceiveUpdate")], [], false⟩) ?h0 hF) ?_ ?_ ?_)
      case h0 => frame_go' [*, hne, Ne.symm hne, hG1]
      all_goals first | (simp [Logic.Footprint.union, ReactHostContainer.fp]; done) | (intro p hp; simp only [Logic.Footprint.union, List.mem_append, List.nil_append, List.append_nil, List.mem_cons, List.mem_nil_iff, or_false, h_AEBenv] at hp ⊢; first | (rcases hp with hp | hp <;> simp_all) | simp_all)
""" for x in DR)
proof = f'''  simp only [BWGen.beginWork]
  js [{JSF}]
  -- (`checkScheduledUpdateOrContext(current, renderLanes)`)
  refine ⟨by js_norm [CallableC, {JSF}], ?_⟩
  refine wp_mono (ReactRootBailout.check_none (d := dCHK) (H := H) (hl := hl0v) (lw := hlw) (le := hle) (lc := hlc) (dw := hdw2) (de := hde2) (dc := hdc2) ?_ ?_ ?_ h_CHKcode h_CHKcls h_CHKmode ?_ ?_ ?_ ?_ hl0) ?p1
  all_goals first | (simp only [js_simp]; omega) | (js_norm [{JSF}]; done) | skip
  case p1 =>
    intro v1 w1 h1 ⟨hv1, hF1, hfu1, hh1⟩
    subst hv1 hh1
    try simp only [js_simp] at hfu1
    have hE1 : s.envs.size < w1.envs.size := envs_frame hF1 {T}
    have hGk1 : d.env < w1.envs.size := envs_frame hF1 {T}
    have hEw1 := envEntry_frame0 hF1 (e := s.envs.size) {T}
    have hGw1 := envEntry_frame0 hF1 (e := d.env) {T}
    have oo1 : ∀ o, o < s.heap.size → w1.objEntry o = s.objEntry o := fun o ho => by
      rw [objEntry_frame0 hF1 (by simpa using ho)]; simp only [js_simp]
    have hX1 : X < w1.heap.size := heap_frame hF1 (by simpa using e_hX)
    have hH1 : H < w1.heap.size := heap_frame hF1 (by simpa using e_hH)
    have hA1 : fAEB < w1.heap.size := heap_frame hF1 (by simpa using h_AEB)
    have hT0 : Frame {{}} s w1 := frame_go_s0
    js [hE1, hGk1, hEw1, hGw1, hX1, hH1, hA1, oo1 _ e_hX, oo1 _ e_hH, oo1 _ h_AEB, Nat.ne_of_lt hE1, Nat.lt_succ_of_lt hE1, Nat.ne_of_lt hGk1, Nat.lt_succ_of_lt hGk1, {JSF}]
    -- (`attemptEarlyBailoutIfNoScheduledUpdate(current, workInProgress, renderLanes)`)
    refine ⟨by js_norm [CallableC, hX1, hH1, hA1, hE1, hGk1, hEw1, hGw1, oo1 _ e_hX, oo1 _ e_hH, oo1 _ h_AEB, {JSF}], ?_⟩
    refine wp_mono (ReactEarlyBailout.root_spec {" ".join(aimp)} (bG := {RREC}) {aargs}) ?p2
{DRC}    case geA => rw [h_AEBenv]; js_norm [hE1, hGk1, hEw1, hGw1, {JSF}]
    all_goals first | (simp only [js_simp]; omega) | (js_norm [hX1, hH1, hA1, hE1, hGk1, hEw1, hGw1, oo1 _ h_AEB, {JSF}]; done) | skip
    case p2 =>
      intro v2 w2 h2 ⟨hv2, hF2, hfu2, hh2⟩
      subst hv2 hh2
      try simp only [js_simp] at hfu2
      js [hE1, hGk1, {JSF}]
      all_goals (repeat' apply And.intro)
      all_goals first | omega | (simp only [js_simp] at *; omega) | skip
      simp only [fp, ReactEarlyBailout.fp, ReactHostContainer.fp, ReactBailout.fp, ReactCreateWIP.fp, Logic.Footprint.union, List.cons_append, List.nil_append, List.append_assoc, Bool.false_or] at hF2 ⊢
      rw [h_AEBenv] at hF2
      frame_go' [*, hne, Ne.symm hne, hG1]'''
out = f'''import JSProofs.ReactEarlyBailout
import JSProofs.BWGen

/-!
# React's `beginWork` on the host root in a click's render (zippy docs/react-proofs.md)

The root's work in progress has the same (null) props as the current root, no update in the render's lanes and no
forced update: `didReceiveUpdate` is cleared and `attemptEarlyBailoutIfNoScheduledUpdate` (its theorem) clones the
counter's fiber. Generated by `tools/gen_react_bw.py`.
-/

open ES ES.M HostRuns Logic
open Std (HashMap)

namespace ReactBeginRoot

section
variable {{eng : Engine}} {{σ : Type}} {{answer : HostAnswer σ}}

theorem simple (d : FuncData) (hc : d.code = BWGen.beginWork_func) : FDI.Simple d := by
  constructor <;> rw [hc] <;> try rfl
  simp [BWGen.beginWork_func, Func.params, Func.info]

/-- What it writes: `didReceiveUpdate` and what `attemptEarlyBailoutIfNoScheduledUpdate` writes. -/
def fp (g : EnvId) (VS RI CF CS Cu Cx X C1 : ObjId) : Footprint :=
  Logic.Footprint.union ⟨[(g, "didReceiveUpdate")], [], false⟩ (ReactEarlyBailout.fp g VS RI CF CS Cu Cx X C1)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
/-- **`beginWork(H, X, 2)`** on the host root: returns the counter's work in progress. -/
theorem root_spec {{n : Nat}} {{h : σ}} {{fo : ObjId}} {{d : FuncData}} {{t : Value}} {{s : State}} {" ".join(i for i in imps if not i.startswith("{n :") and not i.startswith("{h :") and not i.startswith("{fo :") and not i.startswith("{t :") and not i.startswith("{s :") and not i.startswith("{d :"))}
    {chr(10).join("    " + h for h in hyps)} :
    WP eng answer (n + 3) h (callImpl eng (.obj fo) t #[.obj H, .obj X, .num {TWO}]) s fun v w h' =>
      v = .obj e_C1 ∧ Frame (fp d.env VS a_RI a_CF a_CS b_Cu Cx X e_C1) s w ∧ s.fuel ≤ w.fuel + 700 ∧ h' = h := by
  apply wp_callGen BWGen.beginWork_eq (by decide) hlt hk (by omega) hcls hmode
    (by rw [hcode]; rfl) (by rw [hcode]; rfl) (simple d hcode) (by rw [hcode]; rfl) (by rw [hcode]; rfl)
  have hpn : d.code.info.fdi.paramNames = #[JSStr.ofString "current", JSStr.ofString "workInProgress",
    JSStr.ofString "renderLanes"] := by rw [hcode]; rfl
  have hv : d.code.info.fdi.varNames = #[JSStr.ofString "props", JSStr.ofString "$$typeof", JSStr.ofString "prevState",
    JSStr.ofString "nextState"] := by rw [hcode]; rfl
  have hl : FDI.lexDecls d = #[] := by simp [FDI.lexDecls, hcode, BWGen.beginWork_func, Func.info]
  have ha : d.code.isAsync = false := by rw [hcode]; rfl
  have hne : s.envs.size ≠ d.env := Nat.ne_of_gt hG
  have hG1 : d.env < s.envs.size + 1 := Nat.lt_succ_of_lt hG
  clear hcode
{proof}

end

end ReactBeginRoot
'''
out = out.replace("    have hT0 : Frame {} s w1 := frame_go_s0\n", "")
open(J("ReactBeginRoot.lean"), "w").write(out)
print(len(hyps), "hyp groups")
