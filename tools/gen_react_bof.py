"""Generates ReactBailout.lean: bailoutOnAlreadyFinishedWork on the host root in the steady state (its one child, the
counter's fiber, cloned by createWorkInProgress's theorem). zippy docs/react-proofs.md"""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from react_sig import sig, hname
ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
TWO = "(F64.fin false 4503599627370496 (-51))"; Z = "(F64.fin false 0 (-1074))"
RD = ["type", "childLanes", "lanes", "child", "memoizedProps", "memoizedState", "updateQueue", "sibling", "index",
      "ref", "refCleanup"]
VN = ["vT", "vCL", "vL", "vC", "vMP", "vMS", "vUQ", "vS", "vI", "vR", "vRC"]
WR = ["pendingProps", "type", "flags", "subtreeFlags", "deletions", "childLanes", "lanes", "child", "memoizedProps",
      "memoizedState", "updateQueue", "dependencies", "sibling", "index", "ref", "refCleanup"]
M = "(F64.fin false 5062151534280704 (-22))"
final = {"pendingProps": "pp", "flags": f".num (numberBinOp .bitAnd fl {M})", "subtreeFlags": f".num {Z}",
         "deletions": ".null", "dependencies": ".null"}
for k, v in zip(RD, VN): final[k] = v
final["sibling"] = ".null"
cw = [hname(b) for b in sig(ROOT + "/JSProofs/ReactCreateWIP.lean", "reuse_spec", "    WP eng answer")[1]]
bools = []
def B(p): bools.extend([p + "w", p + "e", p + "c"]); return f"{p}w {p}e {p}c"
hyps = []
hyps += ["(hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : 100 ≤ s.fuel)",
         "(hcode : d.code = BOFGen.bailoutOnAlreadyFinishedWork_func) (hcls : d.isClassCtor = false) (hmode : d.thisMode = .strict)",
         "(hG : d.env < s.envs.size) (hGe : Scope.declLike? (s.envEntry d.env) = some (bG, oG))",
         "(hGS : bG[JSStr.ofString \"workInProgressRootSkippedLanes\"]? = some bdS) (hGSm : bdS.mutable = true) (hGSv : bdS.value = some (.num sk))",
         "(hGC : bG[JSStr.ofString \"createWorkInProgress\"]? = some bdC) (hGCv : bdC.value = some (.obj fC))",
         "(hCo : fC < s.heap.size) (hCk : (s.objEntry fC).kind = .func dC) (hCcode : dC.code = CWIPGen.createWorkInProgress_func)",
         "(hCcls : dC.isClassCtor = false) (hCmode : dC.thisMode = .strict)"]
for o in ["H", "X", "C0", "C1"]:
    hyps.append(f"(h{o} : {o} < s.heap.size) (h{o}k : (s.objEntry {o}).kind.isPlain = true)")
hyps.append(f"(hHd : (s.objEntry H).props.get? (.str \"dependencies\") = some (.data .null {B('hd')}))")
hyps.append(f"(hHc : (s.objEntry H).props.get? (.str \"child\") = some (.data (.obj C0) {B('hc')}))")
hyps.append(f"(hXd : (s.objEntry X).props.get? (.str \"dependencies\") = some (.data xd true xde xdc))")
hyps.append(f"(hXl : (s.objEntry X).props.get? (.str \"lanes\") = some (.data (.num xl) {B('xl')}))")
hyps.append(f"(hXcl : (s.objEntry X).props.get? (.str \"childLanes\") = some (.data (.num xcl) {B('xcl')}))")
hyps.append(f"(hXc : (s.objEntry X).props.get? (.str \"child\") = some (.data (.obj C0) true xce xcc))")
hyps.append(f"(hlanes : isStrictlyEqual (.num {Z}) (.num (numberBinOp .bitAnd {TWO} xcl)) = false)")
# the counter fiber C0 and its alternate C1 (createWorkInProgress's premises)
hyps.append(f"(hC0p : (s.objEntry C0).props.get? (.str \"pendingProps\") = some (.data pp {B('cp')}))")
hyps.append(f"(hC0a : (s.objEntry C0).props.get? (.str \"alternate\") = some (.data (.obj C1) {B('ca')}))")
hyps.append(f"(hC0f : (s.objEntry C0).props.get? (.str \"flags\") = some (.data (.num fl) {B('cf')}))")
hyps.append(f"(hC0d : (s.objEntry C0).props.get? (.str \"dependencies\") = some (.data .null {B('cd')}))")
for k, v in zip(RD, VN):
    vv = ".null" if k == "sibling" else v
    hyps.append(f"(hC0_{k} : (s.objEntry C0).props.get? (.str \"{k}\") = some (.data {vv} {B('c_' + k)}))")
for i, k in enumerate(WR):
    hyps.append(f"(hC1_{k} : (s.objEntry C1).props.get? (.str \"{k}\") = some (.data o{i} true e{i} c{i}))")
hyps.append("(hC1r : (s.objEntry C1).props.get? (.str \"return\") = some (.data or true re rc))")
dist = [("H", "X"), ("H", "C0"), ("H", "C1"), ("X", "C0"), ("X", "C1"), ("C0", "C1"), ("fC", "X"), ("fC", "C1")]
hyps.append(" ".join(f"(n_{a}_{b} : {a} ≠ {b})" for a, b in dist))
DS = ", ".join([f"n_{a}_{b}" for a, b in dist] + [f"Ne.symm n_{a}_{b}" for a, b in dist])
bools += [f"e{i}" for i in range(16)] + [f"c{i}" for i in range(16)] + ["xde", "xdc", "xce", "xcc", "re", "rc"]
imps = ("{n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t : Value} {s : State} {bG : HashMap JSStr Binding} "
        "{oG : Option EnvId} {bdS bdC : Binding} {fC H X C0 C1 : ObjId} {dC : FuncData} {sk xl xcl fl : F64} "
        "{" + " ".join(VN) + " pp xd or " + " ".join(f"o{i}" for i in range(16)) + " : Value} {" + " ".join(bools) + " : Bool}")
fp = ("⟨[(g, \"workInProgressRootSkippedLanes\")], [(X, .str \"dependencies\"), (X, .str \"child\"), (C1, .str \"return\")] ++ "
      "(ReactCreateWIP.fp C1).props, false⟩")
post = [f"(w.objEntry C1).props.get? (.str \"{k}\") = some (.data ({final[k]}) true e{i} c{i})" for i, k in enumerate(WR)]
post += ["(w.objEntry C1).props.get? (.str \"return\") = some (.data (.obj X) true re rc)",
         "(w.objEntry X).props.get? (.str \"child\") = some (.data (.obj C1) true xce xcc)"]
# createWorkInProgress's implicits
cargs = ["(d := dC)", "(H := C0)", "(X := C1)", "(fl := fl)", "(pp := pp)"]
for k, v in zip(RD, VN):
    cargs.append(f"({v} := {'.null' if k == 'sibling' else v})")
for q, k in enumerate(RD): cargs += [f"(r{q}w := c_{k}w)", f"(r{q}e := c_{k}e)", f"(r{q}c := c_{k}c)"]
for q, pf in [(11, "ca"), (12, "cf"), (13, "cd")]: cargs += [f"(r{q}w := {pf}w)", f"(r{q}e := {pf}e)", f"(r{q}c := {pf}c)"]
for q in range(16): cargs += [f"(o{q} := o{q})", f"(e{q} := e{q})", f"(c{q} := c{q})"]
given = {"hcode": "hCcode", "hcls": "hCcls", "hmode": "hCmode"}
choles = " ".join(given.get(nm, "?_") for nm in cw)
F = ("hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGS, hGSm, hGSv, hGC, hGCv, hCo, hCk, hH, hHk, hX, hXk, hC0, hC0k, "
     "hC1, hC1k, hHd, hHc, hXd, hXl, hXcl, hXc, hlanes, hC0p, hC0a, hC0f, hC0d, " +
     ", ".join(f"hC0_{k}" for k in RD) + ", " + ", ".join(f"hC1_{k}" for k in WR) + ", hC1r, " + DS + ", beq_self_eq_true, FDI.fdiCtx, Sem.inner")
T = "(by first | assumption | (simp only [js_simp]; done) | (simp only [js_simp]; omega))"
WRq = ", ".join("q_" + k for k in WR)
out = f'''import JSProofs.ReactCreateWIP
import JSProofs.BOFGen
import JSProofs.Loops4

/-!
# React's `bailoutOnAlreadyFinishedWork` on the host root (zippy docs/react-proofs.md)

In a click's render the host root has no update of its own but its child does (lane 2 in `childLanes`): the root's
work in progress `X` takes the current root's `dependencies`, its lanes are skipped, and its one child (the counter's
fiber `C0`, no sibling) is cloned by `createWorkInProgress` into its alternate `C1`, which becomes `X.child` and
points back at `X`. Generated by `tools/gen_react_bof.py`.
-/

open ES ES.M HostRuns Logic
open Std (HashMap)

namespace ReactBailout

section
variable {{eng : Engine}} {{σ : Type}} {{answer : HostAnswer σ}} {{HI : σ → Prop}}

theorem simple (d : FuncData) (hc : d.code = BOFGen.bailoutOnAlreadyFinishedWork_func) : FDI.Simple d := by
  constructor <;> rw [hc] <;> try rfl
  simp [BOFGen.bailoutOnAlreadyFinishedWork_func, Func.params, Func.info]

/-- What it writes. -/
def fp (g : EnvId) (X C1 : ObjId) : Footprint := {fp}

set_option maxRecDepth 40000 in
set_option maxHeartbeats 8000000 in
/-- **`bailoutOnAlreadyFinishedWork(H, X, 2)`**: returns the counter's work in progress `C1`. -/
theorem root_spec {imps}
    {chr(10).join("    " + x for x in hyps)} :
    WP eng answer (n + 1) h (callImpl eng (.obj fo) t #[.obj H, .obj X, .num {TWO}]) s fun v w h' =>
      v = .obj C1 ∧ Frame (fp d.env X C1) s w ∧ s.fuel ≤ w.fuel + 100 ∧ h' = h ∧
      {(" ∧" + chr(10) + "      ").join(post)} := by
  apply wp_callGen BOFGen.bailoutOnAlreadyFinishedWork_eq (by decide) hlt hk (by omega) hcls hmode
    (by rw [hcode]; rfl) (by rw [hcode]; rfl) (simple d hcode) (by rw [hcode]; rfl) (by rw [hcode]; rfl)
  have hpn : d.code.info.fdi.paramNames = #[JSStr.ofString "current", JSStr.ofString "workInProgress",
    JSStr.ofString "renderLanes"] := by rw [hcode]; rfl
  have hv : d.code.info.fdi.varNames = #[] := by rw [hcode]; rfl
  have hl : FDI.lexDecls d = #[] := by simp [FDI.lexDecls, hcode, BOFGen.bailoutOnAlreadyFinishedWork_func, Func.info]
  have ha : d.code.isAsync = false := by rw [hcode]; rfl
  have hne : s.envs.size ≠ d.env := Nat.ne_of_gt hG
  have hG1 : d.env < s.envs.size + 1 := Nat.lt_succ_of_lt hG
  clear hcode
  simp only [BOFGen.bailoutOnAlreadyFinishedWork]
  js [{F}]
  -- (`createWorkInProgress(current, current.pendingProps)`)
  refine ⟨by js_norm [CallableC, {F}], ?_⟩
  refine wp_mono (ReactCreateWIP.reuse_spec {" ".join(cargs)} {choles}) ?p1
  all_goals first | omega | (simp only [js_simp]; omega) | (js_norm [{F}]; done) | skip
  case p1 =>
    intro v1 w1 h1 ⟨hv1, hF1, hfu1, hh1, {WRq}⟩
    subst hv1 hh1
    try simp only [js_simp] at hfu1
    have hE1 : s.envs.size < w1.envs.size := envs_frame hF1 {T}
    have hG2 : d.env < w1.envs.size := envs_frame hF1 {T}
    have hEw1 := envEntry_frame hF1 (e := s.envs.size) {T} (by simp [ReactCreateWIP.fp])
    have hGw1 := envEntry_frame hF1 (e := d.env) {T} (by simp [ReactCreateWIP.fp])
    have oX := objEntry_frame hF1 (o := X) (by simp only [js_simp]; exact hX) (by simp [ReactCreateWIP.fp, n_X_C1, Ne.symm n_X_C1])
    have oC0 := objEntry_frame hF1 (o := C0) (by simp only [js_simp]; exact hC0) (by simp [ReactCreateWIP.fp, n_C0_C1, Ne.symm n_C0_C1])
    have hC1' : C1 < w1.heap.size := heap_frame hF1 (by simp only [js_simp]; exact hC1)
    have hC1k' : (w1.objEntry C1).kind.isPlain = true := by rw [kind_frame hF1 (by simp only [js_simp]; exact hC1)]; js_norm [hC1k, n_X_C1, Ne.symm n_X_C1]
    have hC1r' : (w1.objEntry C1).props.get? (.str "return") = some (.data or true re rc) := by
      rw [props_frame hF1 (by simp only [js_simp]; exact hC1) (by simp [ReactCreateWIP.fp])]; js_norm [hC1r, n_X_C1, Ne.symm n_X_C1]
    have hX' : X < w1.heap.size := heap_frame hF1 (by simp only [js_simp]; exact hX)
    have hC0' : C0 < w1.heap.size := heap_frame hF1 (by simp only [js_simp]; exact hC0)
    js [hE1, hG2, hEw1, hGw1, oX, oC0, hC1', hC1k', hC1r', hX', hC0', {WRq}, Nat.ne_of_lt hE1, Nat.lt_succ_of_lt hE1, Nat.ne_of_lt hG2, Nat.lt_succ_of_lt hG2, {F}]
    refine wp_forExpr ?_
    js [hE1, hG2, hEw1, hGw1, oX, oC0, hC1', hC1k', hC1r', hX', hC0', {WRq}, Nat.ne_of_lt hE1, Nat.lt_succ_of_lt hE1, Nat.ne_of_lt hG2, Nat.lt_succ_of_lt hG2, {F}]
    all_goals (repeat' apply And.intro)
    all_goals first | omega | (simp only [js_simp] at *; omega) | (js_norm [*, {DS}]; done) | (simp only [fp, ReactCreateWIP.fp, List.cons_append, List.nil_append] at *; frame_go' [*, hne, Ne.symm hne, hG1]; done)

end

end ReactBailout
'''
open(ROOT + "/JSProofs/ReactBailout.lean", "w").write(out)
