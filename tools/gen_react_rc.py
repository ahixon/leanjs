"""Generates JSProofs/ReactReconcileChildren.lean: reconcileChildren for the click (the current child reused).
Statement: ReactReconcileFibers.click_spec's premises plus its own (react_reconcile/rc_extra.lean.in)."""
import os, re
repo=os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
root=os.path.join(repo,"JSProofs")+"/"
here=os.path.join(repo,"tools","react_reconcile")+"/"
u=open(root+"ReactReconcileFibers.lean").read()
hd="WP eng answer (n + 3) h (callImpl eng (.obj fR) tR #[.obj RF, .obj H, .obj El, ln]) s fun v w h' =>"
i=u.index("theorem click_spec {"); j=u.index(" :\n    "+hd)
prem=u[i+len("theorem click_spec "):j]
k=j+len(" :\n    "+hd); l=u.index(" := by",k)
post=u[k:l]
names=[m.group(1) for m in re.finditer(r"\((h[A-Za-z0-9_']*|hdX|hgU) :", prem)]
pt={}
for m in re.finditer(r"\((h[A-Za-z0-9_']*) :((?:[^()]|\((?:[^()]|\((?:[^()]|\([^()]*\))*\))*\))*)\)", prem):
    pt[m.group(1)]=m.group(2)
prem=prem.replace("{tR : Value}","").replace("(hf : 150 ≤ s.fuel)","(hf : 170 ≤ s.fuel)")
post=post.replace("v = .obj X ∧","v = .undefined ∧").replace("s.fuel ≤ w.fuel + 150","s.fuel ≤ w.fuel + 170").replace("Logic.Frame (fpR g X) s w","Logic.Frame (fpC g X RF) s w")
post=post.rstrip()+""" ∧
      (w.objEntry RF).props.get? (.str "child") = some (.data (.obj X) true cw cc)"""
extra=open(here+"rc_extra.lean.in").read().rstrip("\n")
kk=prem.rindex(")")
prem=prem[:kk+1]+"\n"+extra+prem[kk+1:]
units=[]
for x in names:
    t=pt.get(x,"")
    if x=="hf": arg="(by rw [hStF]; omega)"
    elif x=="hGe": arg="hStg"
    elif x=="hEe": arg="(by rw [hStU]; exact hEe)"
    elif "s.envEntry" in t: raise Exception("env premise "+x)
    elif "< s.envs.size" in t: arg=f"(by rw [hStE]; exact Nat.lt_succ_of_lt {x})"
    elif re.search(r"s\.objEntry", t): arg=f"(by rw [hStO]; exact {x})"
    elif "< s.heap.size" in t: arg=f"(by rw [hStz]; exact {x})"
    else: arg=x
    units.append(f"({x} := {arg})")
lines=[];cur=""
for un in units:
    if len(cur)+len(un)+1>110 and cur: lines.append(cur); cur=un
    else: cur=(cur+" "+un).strip()
lines.append(cur)
tmpl=open(here+"rc_tmpl.lean.in").read()
open(root+"ReactReconcileChildren.lean","w").write(tmpl.replace("@@PREM@@",prem).replace("@@POST@@",post).replace("@@ARGS@@","\n      ".join(lines)))
