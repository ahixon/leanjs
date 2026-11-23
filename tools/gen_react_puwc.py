"""Generates JSProofs/ReactUnitCounter.lean: performUnitOfWork on the counter's fiber in the click's render — the
counter's beginWork (ReactBeginCounter.click_spec) returns the button fiber, the counter's props are memoized and
the button becomes workInProgress. The statement is click_spec's binders plus performUnitOfWork's own; the post carries
the button fiber's state and the new props' text, which the button's unit of work needs. zippy docs/react-proofs.md"""
import os, re, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "react_cuw"))
import args as A
ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
J = lambda f: os.path.join(ROOT, "JSProofs", f)
BC = A.binders(J("ReactBeginCounter.lean"), "click_spec")
SKIP = {"n", "h", "s"}
binds = ["{n : Nat}", "{h : σ}", "{s : State}", "{fPU : ObjId}", "{dPU : FuncData}", "{tPU : Value}",
         "{bdBW bdEL bdWIP : Binding}", "{wv : Value}", "{aw' ae' ac' : Bool}"]
prem = ["(hPUo : fPU < s.heap.size) (hPUk : (s.objEntry fPU).kind = .func dPU) (hPUf : 560 ≤ s.fuel)",
        "(hPUcode : dPU.code = PUWGen.performUnitOfWork_func) (hPUcls : dPU.isClassCtor = false) (hPUmode : dPU.thisMode = .strict)",
        "(hPUenv : dPU.env = d.env)",
        "(hGBW : bG[JSStr.ofString \"beginWork\"]? = some bdBW) (hGBWv : bdBW.value = some (.obj fB))",
        "(hGEL : bG[JSStr.ofString \"entangledRenderLanes\"]? = some bdEL) (hGELv : bdEL.value = some two)",
        "(hGWIP : bG[JSStr.ofString \"workInProgress\"]? = some bdWIP) (hGWIPm : bdWIP.mutable = true)",
        "(hGWIPi : bdWIP.value = some wv) (hWIPfp : (d.env, JSStr.ofString \"workInProgress\") ∉ (fpB d.env C1 H0 Q RSI X).binds)",
        "(hC1alt : (s.objEntry C1).props.get? (.str \"alternate\") = some (.data (.obj C0) aw' ae' ac'))",
        "(hC1mp : (s.objEntry C1).props.get? (.str \"memoizedProps\") = some (.data mpv true mpe' mpc'))",
        "(hC1fp : ∀ k, k ∈ [PropKey.str (JSStr.ofString \"alternate\"), .str \"pendingProps\", .str \"memoizedProps\"] → (C1, k) ∉ (fpB d.env C1 H0 Q RSI X).props)",
        "(dXC1 : X ≠ C1) (dPC1 : fPU ≠ C1)"]
binds += ["{mpv : Value}", "{mpe' mpc' : Bool}"]
cur = {}; seenb = set()
def subn(ty):
    return re.sub(r"(?<![\w.'])([A-Za-z_][\w']*)", lambda m: cur.get(m.group(1), m.group(1)), ty)
for imp, nm, ty in BC:
    if nm in SKIP: continue
    ty2 = subn(ty)
    if nm in seenb:
        cur[nm] = nm + "_2"
    seenb.add(nm)
    n2 = cur.get(nm, nm)
    if imp: binds.append(f"{{{n2} : {ty2}}}")
    else: prem.append(f"({n2} : {ty2})")
src = open(J("ReactBeginCounter.lean")).read()
i = src.index("theorem click_spec"); j = src.index("∃ C : ObjId, v = .obj X ∧ Frame (fpB d.env C1 H0 Q RSI X) s w ∧", i)
k = src.index(":= by", j)
post = src[j:k]
# the button fiber's facts: as stated by click_spec (after `w.realm = s.realm ∧`)
facts = post[post.index("w.realm = s.realm ∧") + len("w.realm = s.realm ∧"):].rstrip()
facts = facts[:facts.index(" ∧\n      ∃ bm, Scope.declLike?")]
FP = ("Logic.Footprint.union (fpB d.env C1 H0 Q RSI X) ⟨[(d.env, \"workInProgress\")], [(C1, .str \"memoizedProps\")], false⟩")
tmpl = open(os.path.join(ROOT, "tools", "react_puwc", "tmpl.lean.in")).read()
out = (tmpl.replace("@@BINDERS@@", " ".join(binds)).replace("@@PREMISES@@", "\n    ".join(prem))
       .replace("@@FP@@", FP).replace("@@FACTS@@", facts))
open(J("ReactUnitCounter.lean"), "w").write(out)
bounds = A.caller_bounds(J("ReactUnitCounter.lean"), "counter_unit_spec")
envb = A.caller_envbounds(J("ReactUnitCounter.lean"), "counter_unit_spec")
ren = {"n": "n"}
a1 = A.transfer(J("ReactBeginCounter.lean"), "click_spec", {"tB": ".undefined", "oG": "none"}, {"hGe": "gG1", "hoG": "rfl"}, {}, bounds, 1, "",
                envbounds=envb, objall=True)
out = open(J("ReactUnitCounter.lean")).read().replace("@@ARGS1@@", a1)
open(J("ReactUnitCounter.lean"), "w").write(out)
print("binders", len(binds), "premises", len(prem))
