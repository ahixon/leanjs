"""Generates JSProofs/ReactUseFiber.lean: the child reconciler's useFiber (createWorkInProgress, then index and
sibling), its statement from ReactCreateWIP.reuse_spec's."""
import os, re
repo=os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
root=os.path.join(repo,"JSProofs")+"/"
u=open(root+"ReactCreateWIP.lean").read()
i=u.index("theorem reuse_spec {"); hd="WP eng answer n h (callImpl eng (.obj fo) t #[.obj H, pp]) s fun v w h' =>"
j=u.index(" :\n    "+hd)
prem=u[i+len("theorem reuse_spec "):j]
k=j+len(" :\n    "+hd); l=u.index(" := by",k)
post=u[k:l]
names=[m.group(1) for m in re.finditer(r"\((h[A-Za-z0-9_']*) :", prem)]
prem=prem.replace("{n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t pp : Value} {s : State}",
  "{n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {pp : Value} {s : State} {fU : ObjId} {dU : FuncData} {tU : Value}\n    {bR bG : HashMap JSStr Binding} {g : EnvId} {bdCW : Binding}")
prem=prem.replace("(hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : 20 ≤ s.fuel)",
"""(hU : fU < s.heap.size) (hUk : (s.objEntry fU).kind = .func dU) (hUcode : dU.code = CCRGen.useFiber_func)
    (hUcls : dU.isClassCtor = false) (hUmode : dU.thisMode = .strict)
    -- (useFiber's record: the reconciler's closure, whose outer record is the module's)
    (hE : dU.env < s.envs.size) (hEe : Scope.declLike? (s.envEntry dU.env) = some (bR, some g))
    (hEn : bR[JSStr.ofString "createWorkInProgress"]? = none)
    (hG : g < s.envs.size) (hGe : Scope.declLike? (s.envEntry g) = some (bG, oG))
    (hGC : bG[JSStr.ofString "createWorkInProgress"]? = some bdCW) (hGCv : bdCW.value = some (.obj fo))
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : 40 ≤ s.fuel)""")
post=post.replace("s.fuel ≤ w.fuel + 20","s.fuel ≤ w.fuel + 40").replace("Frame (fp X)","Logic.Frame (ReactCreateWIP.fp X)")
post=post.replace("""(w.objEntry X).props.get? (.str "sibling") = some (.data (vS) true e12 c12)""","""(w.objEntry X).props.get? (.str "sibling") = some (.data .null true e12 c12)""")
post=post.replace("""(w.objEntry X).props.get? (.str "index") = some (.data (vI) true e13 c13)""","""(w.objEntry X).props.get? (.str "index") = some (.data (.num (F64.fin false 0 (-1074))) true e13 c13)""")
tmpl=open(os.path.join(repo,"tools","react_reconcile","usefiber_tmpl.lean.in")).read()
units=[f"({x} := {x})" for x in names if x not in ("hf",)]+["(hf := by js_norm; omega)"]
lines=[];cur=""
for un in units:
    if len(cur)+len(un)+1>110 and cur: lines.append(cur); cur=un
    else: cur=(cur+" "+un).strip()
lines.append(cur)
out=tmpl.replace("@@PREM@@",prem).replace("@@POST@@",post).replace("@@ARGS@@","\n      ".join(lines))
open(root+"ReactUseFiber.lean","w").write(out)
