"""Generates ReactUnitRoot.lean: performUnitOfWork on the host root's work in progress (beginWork by its theorem;
the next unit is the counter's fiber). zippy docs/react-proofs.md"""
import os, re, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from react_sig import sig, names_of_imp, hname
from react_compose import hyp_type
ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
J = lambda f: ROOT + "/JSProofs/" + f
TWO = "(F64.fin false 4503599627370496 (-51))"
bi, bh = sig(J("ReactBeginRoot.lean"), "root_spec", "    WP eng answer")
SET = {"n": "n", "h": None, "fo": "fBW", "d": "dBW", "t": ".undefined", "s": None}
imps = []; seen = set()
def add(names, ty):
    k = [x for x in names if x not in seen]; seen.update(k)
    if k: imps.append("{" + " ".join(k) + " " + ty + "}")
for b in bi:
    add([x for x in names_of_imp(b) if x not in SET], b[b.index(":"):-1])
add(["fBW"], ": ObjId"); add(["dBW"], ": FuncData"); add(["bdBW", "bdERL", "bdWIP"], ": Binding")
add(["mpv"], ": Value"); add(["aw", "ae", "ac", "mpe", "mpc"], ": Bool")
SELF = {"hlt", "hk", "hf", "hcode", "hcls", "hmode", "hG", "hGe"}
hyps = ["(hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : 800 ≤ s.fuel)",
        "(hcode : d.code = PUWGen.performUnitOfWork_func) (hcls : d.isClassCtor = false) (hmode : d.thisMode = .strict)",
        "(hG : d.env < s.envs.size) (hGe : Scope.declLike? (s.envEntry d.env) = some (bG, oG))",
        "(g_BW : bG[JSStr.ofString \"beginWork\"]? = some bdBW) (g_BWv : bdBW.value = some (.obj fBW))",
        "(h_BW : fBW < s.heap.size) (h_BWk : (s.objEntry fBW).kind = .func dBW) (h_BWcode : dBW.code = BWGen.beginWork_func)",
        "(h_BWcls : dBW.isClassCtor = false) (h_BWmode : dBW.thisMode = .strict) (h_BWenv : dBW.env = d.env)",
        f"(g_ERL : bG[JSStr.ofString \"entangledRenderLanes\"]? = some bdERL) (g_ERLv : bdERL.value = some (.num {TWO}))",
        "(g_WIP : bG[JSStr.ofString \"workInProgress\"]? = some bdWIP) (g_WIPm : bdWIP.mutable = true) (g_WIPv : bdWIP.value.isSome = true)",
        "(hXa : (s.objEntry X).props.get? (.str \"alternate\") = some (.data (.obj H) aw ae ac))",
        "(hXmp : (s.objEntry X).props.get? (.str \"memoizedProps\") = some (.data mpv true mpe mpc))",
        "(x_BW_X : fBW ≠ X) (x_BW_H : fBW ≠ H)"]
for b in bh:
    n0 = hname(b)
    if n0 in SELF: continue
    hyps.append(f"({n0} : {hyp_type(b)})")
# BW's heap facts by object
heaps = {}
for b in bh:
    m = re.fullmatch(r"(\w+) < s\.heap\.size", hyp_type(b))
    if m: heaps[m.group(1)] = hname(b)
DR = []
def arg(b):
    n0 = hname(b); ty = hyp_type(b)
    if n0 in ("hcode", "hcls", "hmode"): return f"h_BW{n0[1:]}"
    if n0 == "hGe": return "(by rw [h_BWenv]; js_norm [hG, hGe, hne, Ne.symm hne, hG1])"
    if n0 == "hG": return "(by rw [h_BWenv]; first | (simp only [js_simp]; omega) | omega)"
    if n0 in ("hlt", "hk", "hf"): return "?_"
    if "ReactHostContainer.DomRead" in ty: DR.append(n0); return f"?dr_{n0}"
    if re.match(r"\(s\.objEntry (\w+)\)\.", ty) or re.fullmatch(r"(\w+) < s\.heap\.size", ty):
        return f"(by first | (simp only [js_simp]; exact {n0}) | exact {n0})"
    if re.search(r"(?<![\w.'])s(?![\w'])", ty): return "?_"
    if "d.env" in ty: return f"(by rw [h_BWenv]; exact {n0})"
    return n0
args = " ".join(arg(b) for b in bh)
imp = []
for b in bi:
    for x in names_of_imp(b):
        if x in SET:
            if SET[x]: imp.append(f"({x} := {SET[x]})")
        else: imp.append(f"({x} := {x})")
DRC = "".join(f"""  case dr_{x} =>
    intro w h1 hF
    refine {x} w h1 (frame_mono (frame_trans (fp1 := {{}}) ?h0 hF) ?_ ?_ ?_)
    case h0 => frame_go' [*, hne, Ne.symm hne, hG1]
    all_goals first | (simp [Logic.Footprint.union, ReactHostContainer.fp]; done) | (intro p hp; simp only [Logic.Footprint.union, List.mem_append, List.nil_append, List.append_nil, List.mem_cons, List.mem_nil_iff, or_false, h_BWenv] at hp ⊢; first | (rcases hp with hp | hp <;> simp_all) | simp_all)
""" for x in DR)
T = "(by first | assumption | (simp only [js_simp]; done) | (simp only [js_simp]; omega))"
JSF = ("hG, hGe, g_BW, g_BWv, h_BW, h_BWk, g_ERL, g_ERLv, g_WIP, g_WIPm, g_WIPv, hXa, hXmp, e_hX, e_hXk, e_hH, e_hHk, "
       "x_BW_X, x_BW_H, Ne.symm x_BW_X, Ne.symm x_BW_H, hpn, hv, hl, ha, hne, Ne.symm hne, hG1, FDI.fdiCtx, Sem.inner")
FPU = '(Logic.Footprint.union (ReactBeginRoot.fp d.env VS a_RI a_CF a_CS b_Cu Cx X e_C1) ⟨[(d.env, "workInProgress")], [(X, .str "memoizedProps")], false⟩)'
proof = f'''  simp only [PUWGen.performUnitOfWork]
  js [{JSF}]
  -- (`beginWork(unitOfWork.alternate, unitOfWork, entangledRenderLanes)`)
  refine ⟨by js_norm [CallableC, {JSF}], ?_⟩
  refine wp_mono (ReactBeginRoot.root_spec {" ".join(imp)} {args}) ?p1
{DRC}  all_goals first | (simp only [js_simp]; omega) | (js_norm [{JSF}]; done) | skip
  case p1 =>
    intro v1 w1 h1 ⟨hv1, hF1, hfu1, hh1⟩
    subst hv1 hh1
    try simp only [js_simp] at hfu1
    simp only [ReactBeginRoot.fp, ReactEarlyBailout.fp, ReactHostContainer.fp, ReactBailout.fp, ReactCreateWIP.fp,
      Logic.Footprint.union, List.cons_append, List.nil_append, List.append_assoc, Bool.false_or] at hF1
    rw [h_BWenv] at hF1
    have hE1 : s.envs.size < w1.envs.size := envs_frame hF1 {T}
    have hGk1 : d.env < w1.envs.size := envs_frame hF1 {T}
    have hEw1 := envEntry_frame hF1 (e := s.envs.size) {T} (by simp [Nat.ne_of_lt hG])
    obtain ⟨bW, hWd, hWx⟩ := declLike_frame hF1 (e := d.env) (bs := bG) (o := oG) {T} (by js_norm [hG, hGe, hne, Ne.symm hne, hG1])
    have hWIP1 := hWx (JSStr.ofString "workInProgress") (by simp)
    have hX1 : X < w1.heap.size := heap_frame hF1 (by simpa using e_hX)
    have hXk1 : (w1.objEntry X).kind.isPlain = true := by rw [kind_frame hF1 (by simpa using e_hX)]; simpa using e_hXk
    have hXpp1 : (w1.objEntry X).props.get? (.str "pendingProps") = some (.data .null ppw ppe ppc) := by
      rw [props_frame hF1 (by simpa using e_hX) (by simp [x_VS_X, x_a_RI_X, x_a_CF_X, x_a_CS_X, x_b_Cu_X, x_Cx_X, e_n_X_C1, Ne.symm e_n_X_C1])]; simpa using hXpp
    have hXmp1 : (w1.objEntry X).props.get? (.str "memoizedProps") = some (.data mpv true mpe mpc) := by
      rw [props_frame hF1 (by simpa using e_hX) (by simp [x_VS_X, x_a_RI_X, x_a_CF_X, x_a_CS_X, x_b_Cu_X, x_Cx_X, e_n_X_C1, Ne.symm e_n_X_C1])]; simpa using hXmp
    js [hE1, hGk1, hEw1, hWd, hWIP1, g_WIP, g_WIPm, g_WIPv, hX1, hXk1, hXpp1, hXmp1, Nat.ne_of_lt hE1, Nat.lt_succ_of_lt hE1, Nat.ne_of_lt hGk1, Nat.lt_succ_of_lt hGk1, {JSF}]
    all_goals (repeat' apply And.intro)
    all_goals first | omega | (simp only [js_simp] at *; omega) | skip
    case' _ => skip
    all_goals first | (refine ⟨_, rfl, ?_⟩; simp [Std.HashMap.getElem?_modify, hWIP1, g_WIP]) | skip
    simp only [ReactBeginRoot.fp, ReactEarlyBailout.fp, ReactHostContainer.fp, ReactBailout.fp, ReactCreateWIP.fp,
      Logic.Footprint.union, List.cons_append, List.nil_append, List.append_assoc, Bool.false_or]
    frame_go' [*, Logic.Footprint.union, hne, Ne.symm hne, hG1]'''
IMPS = " ".join(i for i in imps if not re.match(r"\{(n|h|fo|d|t|s) :", i))
out = f'''import JSProofs.ReactBeginRoot
import JSProofs.PUWGen

/-!
# React's `performUnitOfWork` on the host root (zippy docs/react-proofs.md)

The root's unit of work in a click's render: `beginWork` (its theorem) returns the counter's work in progress, which
becomes the next unit (`workInProgress`); the root's props are memoized. Generated by `tools/gen_react_puw.py`.
-/

open ES ES.M HostRuns Logic
open Std (HashMap)

namespace ReactUnitRoot

section
variable {{eng : Engine}} {{σ : Type}} {{answer : HostAnswer σ}}

theorem simple (d : FuncData) (hc : d.code = PUWGen.performUnitOfWork_func) : FDI.Simple d := by
  constructor <;> rw [hc] <;> try rfl
  simp [PUWGen.performUnitOfWork_func, Func.params, Func.info]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
/-- **`performUnitOfWork(X)`**, `X` the host root's work in progress: the next unit is the counter's fiber. -/
theorem root_spec {{n : Nat}} {{h : σ}} {{fo : ObjId}} {{d : FuncData}} {{t : Value}} {{s : State}} {IMPS}
    {chr(10).join("    " + x for x in hyps)} :
    WP eng answer (n + 4) h (callImpl eng (.obj fo) t #[.obj X]) s fun v w h' =>
      v = .undefined ∧ Frame {FPU} s w ∧ s.fuel ≤ w.fuel + 800 ∧ h' = h ∧
      ∃ bm, Scope.declLike? (w.envEntry d.env) = some (bm, oG) ∧ ∃ bd, bm[JSStr.ofString "workInProgress"]? = some bd ∧
        bd.value = some (.obj e_C1) := by
  apply wp_callGen PUWGen.performUnitOfWork_eq (by decide) hlt hk (by omega) hcls hmode
    (by rw [hcode]; rfl) (by rw [hcode]; rfl) (simple d hcode) (by rw [hcode]; rfl) (by rw [hcode]; rfl)
  have hpn : d.code.info.fdi.paramNames = #[JSStr.ofString "unitOfWork"] := by rw [hcode]; rfl
  have hv : d.code.info.fdi.varNames = #[JSStr.ofString "next"] := by rw [hcode]; rfl
  have hl : FDI.lexDecls d = #[] := by simp [FDI.lexDecls, hcode, PUWGen.performUnitOfWork_func, Func.info]
  have ha : d.code.isAsync = false := by rw [hcode]; rfl
  have hne : s.envs.size ≠ d.env := Nat.ne_of_gt hG
  have hG1 : d.env < s.envs.size + 1 := Nat.lt_succ_of_lt hG
  clear hcode
{proof}

end

end ReactUnitRoot
'''
open(J("ReactUnitRoot.lean"), "w").write(out)
