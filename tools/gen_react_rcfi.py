"""Generates JSProofs/ReactReconcileImpl.lean: reconcileChildFibersImpl for the click (the button element reusing the
current button fiber). Statement: ReactUseFiber.spec's premises plus its own (react_reconcile/rcfi_extra.lean.in)."""
import os, re
repo=os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
root=os.path.join(repo,"JSProofs")+"/"
here=os.path.join(repo,"tools","react_reconcile")+"/"
u=open(root+"ReactUseFiber.lean").read()
hd="WP eng answer (n + 1) h (callImpl eng (.obj fU) tU #[.obj H, pp]) s fun v w h' =>"
i=u.index("theorem spec {"); j=u.index(" :\n    "+hd)
prem=u[i+len("theorem spec "):j]
k=j+len(" :\n    "+hd); l=u.index(" := by",k)
post=u[k:l]
names=[m.group(1) for m in re.finditer(r"\((h[A-Za-z0-9_']*) :", prem)]
open(here+"uf_names.txt","w").write(" ".join(names))
# the useFiber call's this is undefined; pp is the element's props; the current child's sibling is null;
# vT renamed (it is the current fiber's type there; here vT is the element symbol)
prem=prem.replace("{pp : Value}","").replace("{fU : ObjId} {dU : FuncData} {tU : Value}","{fU : ObjId} {dU : FuncData}")
prem=re.sub(r"\bvT\b","vHT",prem)
prem=prem.replace("(.data vS r7w r7e r7c)","(.data .null r7w r7e r7c)").replace(" vS vI "," vI ")
prem=prem.replace("(hf : 40 ≤ s.fuel)","(hf : 120 ≤ s.fuel)")
post=re.sub(r"\bvT\b","vHT",post).replace("(pp)","(.obj C)").replace("s.fuel ≤ w.fuel + 40","s.fuel ≤ w.fuel + 120")
post=post.replace("Logic.Frame (ReactCreateWIP.fp X) s w","Logic.Frame (fpI X) s w")
post=post.replace("""(w.objEntry X).props.get? (.str "ref") = some (.data (vR) true e14 c14)""","""(w.objEntry X).props.get? (.str "ref") = some (.data .null true e14 c14)""")
post=post.rstrip()+""" ∧
      w.realm = s.realm ∧ (w.objEntry X).props.get? (.str "return") = some (.data (.obj RF) true rew rec)"""
extra=open(here+"rcfi_extra.lean.in").read().rstrip("\n")
kk=prem.rindex(")")
prem=prem[:kk+1]+"\n"+extra+prem[kk+1:]
# useFiber's premises at the call's state w1 (after deleteRemainingChildren): through hw1o / hw1eU / hw1eG
u2=open(root+"ReactUseFiber.lean").read()
i2=u2.index("theorem spec {"); j2=u2.index(" :\n    "+hd)
up=u2[i2+len("theorem spec "):j2]
pt={}
for m in re.finditer(r"\((h[A-Za-z0-9_']*) :((?:[^()]|\((?:[^()]|\((?:[^()]|\([^()]*\))*\))*\))*)\)", up):
    pt[m.group(1)]=m.group(2)
bound={}
for x,t in pt.items():
    mm=re.fullmatch(r"\s*(\w+) < s\.heap\.size\s*", t)
    if mm: bound[mm.group(1)]=x
units=[]
for x in [m.group(1) for m in re.finditer(r"\((h[A-Za-z0-9_']*) :", up)]:
    t=pt[x]
    if x=="hf": arg="(by omega)"
    elif re.search(r"s\.objEntry (\w+)\)", t):
        X=re.search(r"s\.objEntry (\w+)\)", t).group(1); arg=f"(by rw [hw1o {X} {bound[X]}]; exact {x})"
    elif re.fullmatch(r"\s*(\w+) < s\.heap\.size\s*", t): arg=f"(Nat.lt_of_lt_of_le {x} hw1z)"
    elif "s.envEntry dU.env" in t: arg=f"(by rw [hw1eU]; exact {x})"
    elif "s.envEntry g" in t: arg=f"(by rw [hw1eG]; exact {x})"
    elif re.search(r"< s\.envs\.size", t): arg=f"(Nat.lt_trans {x} (Nat.lt_of_succ_lt hw1E))"
    else: arg=x
    units.append(f"({x} := {arg})")
lines=[];cur=""
for un in units:
    if len(cur)+len(un)+1>110 and cur: lines.append(cur); cur=un
    else: cur=(cur+" "+un).strip()
lines.append(cur)
ufargs="\n      ".join(lines)
tmpl=open(here+"rcfi_tmpl.lean.in").read().replace("@@UFARGS@@",ufargs)
open(root+"ReactReconcileImpl.lean","w").write(tmpl.replace("@@PREM@@",prem).replace("@@POST@@",post))
