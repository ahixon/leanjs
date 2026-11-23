"""Generates JSProofs/ReactUnitButton.lean: performUnitOfWork on the counter's button in the click's render — the
button's beginWork (ReactBeginButton.button_spec, returns null), its props memoized, completeUnitOfWork
(ReactCompleteUnit.unit_spec). The statement merges both callees' binders: the shared fibers, module record and
context cursor are identified, the button's others are prefixed `b_`; what beginWork writes (the button's lanes and
child) comes from its post. zippy docs/react-proofs.md"""
import os, re, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "react_cuw"))
import args as A
ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
J = lambda f: os.path.join(ROOT, "JSProofs", f)
BB = A.binders(J("ReactBeginButton.lean"), "button_spec")
UU = A.binders(J("ReactCompleteUnit.lean"), "unit_spec")
SKIP = {"n", "h", "s"}
SHARED = {"H": "H", "X": "X", "P0": "P0", "P1": "P1", "g": "g", "bG": "bG", "ln": "ln", "CS": "CS", "bdCSC": "bdCS"}
bren = {}
for imp, nm, ty in BB:
    if nm in SKIP: continue
    bren[nm] = SHARED.get(nm, "b_" + nm)
def sub(ty, ren):
    return re.sub(r"(?<![\w.'])([A-Za-z_][\w']*)", lambda m: ren.get(m.group(1), m.group(1)), ty)
U_FIXED = {"a": "(F64.fin false 0 (-1074))", "xlw": "true", "xle": "b_lw", "xlc": "b_lc", "cw": "true", "ce": "b_cw",
           "cc": "b_cc", "fU": "fCU", "dU": "dCU", "tU": ".undefined"}
U_DROP = {"hXla", "hXc", "hUo", "hUk", "hf", "hUcode", "hUcls", "hUmode", "hUenv"}
binds = []
seen = set()
binds += ["{n : Nat}", "{h : σ}", "{fo : ObjId}", "{d : FuncData}", "{t : Value}", "{s : State}",
          "{fCU : ObjId}", "{dCU : FuncData}", "{bdBW bdCU : Binding}"]
for imp, nm, ty in UU:
    if not imp or nm in SKIP or nm in U_FIXED: continue
    binds.append(f"{{{nm} : {ty}}}"); seen.add(nm)
for imp, nm, ty in BB:
    if not imp or nm in SKIP: continue
    n2 = bren[nm]
    if n2 in seen: continue
    binds.append(f"{{{n2} : {sub(ty, bren)}}}"); seen.add(n2)
own = ["(hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : 840 ≤ s.fuel)",
       "(hcode : d.code = PUWGen.performUnitOfWork_func) (hcls : d.isClassCtor = false) (hmode : d.thisMode = .strict)",
       "(henv : d.env = g)",
       "(hGBW : bG[JSStr.ofString \"beginWork\"]? = some bdBW) (hGBWv : bdBW.value = some (.obj b_fB))",
       "(hGCU : bG[JSStr.ofString \"completeUnitOfWork\"]? = some bdCU) (hGCUv : bdCU.value = some (.obj fCU))",
       "(hCUo : fCU < s.heap.size) (hCUk : (s.objEntry fCU).kind = .func dCU)",
       "(hCUcode : dCU.code = CUWGen.completeUnitOfWork_func) (hCUcls : dCU.isClassCtor = false)",
       "(hCUmode : dCU.thisMode = .strict) (hCUenv : dCU.env = g)",
       "(hXmp : (s.objEntry X).props.get? (.str \"memoizedProps\") = some (.data mpv true mpe' mpc'))",
       "(dCUX : fCU ≠ X) (dBWX : b_fB ≠ X)", "@@HDX@@"]
binds += ["{mpv : Value}", "{mpe' mpc' : Bool}"]
prem = list(own)
for imp, nm, ty in UU:
    if imp or nm in U_DROP: continue
    prem.append(f"({nm} : {sub(ty, U_FIXED)})")
for imp, nm, ty in BB:
    if imp: continue
    prem.append(f"(b_{nm} : {sub(ty, bren)})")
FP = ("Logic.Footprint.union (ReactBeginButton.fpBB g X) (Logic.Footprint.union "
      "⟨[], [(X, .str \"memoizedProps\")], false⟩ (ReactCompleteUnit.fpU g VS Cu Cx CS CF RI R C X))")
ubounds = A.caller_bounds(J("ReactCompleteUnit.lean"), "unit_spec")
XOBJ = sorted(o for o in ubounds if o not in ("X", "fU"))
prem = [p if p != "@@HDX@@" else f"(hdXall : ∀ Y ∈ [{', '.join(XOBJ)}], Y ≠ X)" for p in prem]
tmpl = open(os.path.join(ROOT, "tools", "react_puwb", "tmpl.lean.in")).read()
XO = "\n".join(f"  have xo_{o} : {o} ≠ X := hdXall {o} (by simp)" for o in XOBJ)
tmpl = tmpl.replace("@@XO@@", XO)
out = tmpl.replace("@@BINDERS@@", " ".join(binds)).replace("@@PREMISES@@", "\n    ".join(prem)).replace("@@FP@@", FP)
# stage args
bounds = A.caller_bounds_text = None
open(J("ReactUnitButton.lean"), "w").write(out)
# bounds from the written statement
bounds = A.caller_bounds(J("ReactUnitButton.lean"), "button_unit_spec")
dl = ["b_hHX", "dCUX", "dBWX"] + [f"xo_{o}" for o in XOBJ]
DS = ", ".join(["ReactBeginButton.fpBB", "ReactCompleteButton.fpCW", "ReactCompleteButton.fpCC", "ReactCompleteRoot.fpRC"] + dl + [f"Ne.symm {x}" for x in dl])
# stage 1: button beginWork at the call state (all objects as in s)
r1 = {nm: bren[nm] for nm in bren}
r1.update({nm: "b_" + nm for imp, nm, ty in BB if not imp})
r1["tB"] = ".undefined"
envb = A.caller_envbounds(J("ReactUnitButton.lean"), "button_unit_spec")
envren = {k: v for k, v in bren.items()}
a1 = A.transfer(J("ReactBeginButton.lean"), "button_spec", r1, {"hGe": "gG1"}, dict((k, v) for k, v in bren.items()), bounds, 1, DS, envbounds=envb)
# stage 2: completeUnitOfWork after beginWork and the memoized props
r2 = dict(U_FIXED); r2["bG"] = "bw"
ex2 = {"hGe": "gG2", "hXla": "hXla2", "hXc": "hXc2", "hUo": "(Nat.lt_of_lt_of_le hCUo gZ2)", "hUk": "(by rw [gK2 fCU hCUo]; exact hCUk)", "hUcode": "hCUcode", "hUcls": "hCUcls", "hUmode": "hCUmode", "hUenv": "hCUenv"}
a2 = A.transfer(J("ReactCompleteUnit.lean"), "unit_spec", r2, ex2, {}, bounds, 2, DS,
                bside="(by simp [ReactBeginButton.fpBB] <;> decide)")
out = open(J("ReactUnitButton.lean")).read().replace("@@ARGS1@@", a1).replace("@@ARGS2@@", a2)
open(J("ReactUnitButton.lean"), "w").write(out)
print("binders", len(binds), "premises", len(prem))
