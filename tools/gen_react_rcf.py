"""Generates JSProofs/ReactReconcileFibers.lean: the reconciler's returned function (reconcileChildFibers) for the
click. Statement: ReactReconcileImpl.click_spec's premises plus its own (react_reconcile/rcf_extra.lean.in)."""
import os, re
repo=os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
root=os.path.join(repo,"JSProofs")+"/"
here=os.path.join(repo,"tools","react_reconcile")+"/"
u=open(root+"ReactReconcileImpl.lean").read()
hd="WP eng answer (n + 2) h (callImpl eng (.obj fI) tI #[.obj RF, .obj H, .obj El, ln]) s fun v w h' =>"
i=u.index("theorem click_spec {"); j=u.index(" :\n    "+hd)
prem=u[i+len("theorem click_spec "):j]
k=j+len(" :\n    "+hd); l=u.index(" := by",k)
post=u[k:l]
names=[m.group(1) for m in re.finditer(r"\((h[A-Za-z0-9_']*) :", prem)]
pt={}
for m in re.finditer(r"\((h[A-Za-z0-9_']*) :((?:[^()]|\((?:[^()]|\((?:[^()]|\([^()]*\))*\))*\))*)\)", prem):
    pt[m.group(1)]=m.group(2)
prem=prem.replace("{tI ln vEl vFr : Value}","{ln vEl vFr : Value}").replace("(hf : 120 ≤ s.fuel)","(hf : 150 ≤ s.fuel)")
post=post.replace("s.fuel ≤ w.fuel + 120","s.fuel ≤ w.fuel + 150").replace("Logic.Frame (fpI X) s w","Logic.Frame (fpR g X) s w")
post=post.rstrip()+""" ∧
      Scope.declLike? (w.envEntry g) = some ((bG.modify (JSStr.ofString "thenableIndexCounter$1")
        (fun bd => { bd with value := some (.num (F64.fin false 0 (-1074))) })).modify (JSStr.ofString "thenableState$1")
        (fun bd => { bd with value := some .null }), none)"""
extra=open(here+"rcf_extra.lean.in").read().rstrip("\n")
kk=prem.rindex(")")
prem=prem[:kk+1]+"\n"+extra+prem[kk+1:]
units=[]
for x in names:
    t=pt[x]
    if x=="hf": arg="(by rw [hStF]; omega)"
    elif x=="hGe": arg="hStg"
    elif x=="hEe": arg="(by rw [hStU]; exact hEe)"
    elif "s.envEntry" in t: raise Exception("env premise "+x)
    elif "< s.envs.size" in t: arg=f"(by rw [hStE]; exact Nat.lt_succ_of_lt {x})"
    elif re.search(r"s\.objEntry", t): arg=f"(by rw [hStO]; exact {x})"
    elif "< s.heap.size" in t: arg=f"(by rw [hStz]; exact {x})"
    elif re.search(r"\bbG\[", t): arg=f"(by js_norm [{x}])"
    else: arg=x
    units.append(f"({x} := {arg})")
lines=[];cur=""
for un in units:
    if len(cur)+len(un)+1>110 and cur: lines.append(cur); cur=un
    else: cur=(cur+" "+un).strip()
lines.append(cur)
args="\n      ".join(lines)
tmpl=open(here+"rcf_tmpl.lean.in").read()
open(root+"ReactReconcileFibers.lean","w").write(tmpl.replace("@@PREM@@",prem).replace("@@POST@@",post).replace("@@ARGS@@",args).replace("@@EF@@","hE, hG, hne, Ne.symm hne, hneG, Ne.symm hneG, hE1, hG1, hEe, hGe, hGT, hGTm, hGS, hGSm, hgU, Ne.symm hgU"))
