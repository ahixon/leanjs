"""Generates JSProofs/ReactRenderHooks.lean: renderWithHooks for the counter's click re-render. Its statement takes
ReactCounter.click_spec's premises (read from that file), less what renderWithHooks itself establishes, plus its own
(react_rwh/rwh_extra.lean.in), in react_rwh/rwh_tmpl.lean.in; the component's premises are passed by name."""
import os, re
repo=os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
root=os.path.join(repo,"JSProofs")+"/"
here=os.path.join(repo,"tools","react_rwh")+"/"
u=open(root+"ReactCounter.lean").read()
hd="WP eng answer (n + 5) h (callImpl eng (.obj fK) tK argsK) s fun v w h' =>"
i=u.index("theorem click_spec {"); j=u.index(" :\n    "+hd)
prem=u[i+len("theorem click_spec "):j]
names=[m.group(1) for m in re.finditer(r"\((h[A-Za-z0-9']*|d[A-Za-z0-9]+) :", prem)]
def sub(old,new):
    global prem
    assert old in prem, old
    prem=prem.replace(old,new)
# what renderWithHooks establishes
sub("(hGFv : bdF.value = some (.obj C1))","(hGFm : bdF.mutable = true) (hGFi : bdF.value.isSome = true)")
sub("(hGRLv : bdRL.value = some two)","(hGRLm : bdRL.mutable = true) (hGRLi : bdRL.value.isSome = true)")
sub("(hGSDv : bdSD.value = some (.bool false))","(hGSDm : bdSD.mutable = true) (hGSDi : bdSD.value.isSome = true)")
sub("(hC1m : (s.objEntry C1).props.get? (.str \"memoizedState\") = some (.data .null true me mc))",
    "(hC1m : (s.objEntry C1).props.get? (.str \"memoizedState\") = some (.data ms1 true me mc))")
sub("(hIH : (s.objEntry RSI).props.get? (.str \"H\") = some (.data (.obj HD) rw re rc))",
    "(hIH : (s.objEntry RSI).props.get? (.str \"H\") = some (.data vH0 true re rc))")
sub("{tK vT : Value} {argsK : Array Value}","{vT P ms1 vH0 vCO uq ln tRW : Value} {fF fRW : ObjId} {dF dRW : FuncData}\n    {bdHU bdRSd bdDP bdFR bdCO bdDS bdTI bdTS : Binding} {uw ue uc lw le lc nw' ne' nc' : Bool}")
sub("(hf : 200 ≤ s.fuel)","(hf : 300 ≤ s.fuel)")
extra=open(here+"rwh_extra.lean.in").read().rstrip("\n")
k=prem.rindex(")")
prem=prem[:k+1]+"\n"+extra+prem[k+1:]
# the component's premises at the call's state St (facts about St: hStO, hStz, hStE, hStEe, hStd, hStR, hStF)
special={"hC1k":"hC1k'","hC1a":"hC1a'","hC1m":"hC1m'","hIk":"hIk'","hIH":"hIH'","hGe":"hStd",
  "hGFv":"rfl","hGRLv":"rfl","hGSDv":"rfl","hf":"(by rw [hStF]; omega)"}
envs={"dS.env":("hSG","hSd"),"dK.env":("hAG","hKd"),"dJ.env":("hJG","hJd")}
objs=["fo","fW","fR","fIs","C0","H0","Q","U","fD","HD","fS","IR","IJ","fJ","AP","fV","AIP","fN","IP","OP","fK","fF"]
ptext={}
for m in re.finditer(r"\((h[A-Za-z0-9']*|d[A-Za-z0-9]+) :((?:[^()]|\((?:[^()]|\((?:[^()]|\([^()]*\))*\))*\))*)\)", prem):
    ptext[m.group(1)]=m.group(2)
units=[]
for x in names:
    t=ptext.get(x,"")
    if x in special: arg=special[x]
    elif re.search(r"s\.objEntry (\w+)\)", t):
        X=re.search(r"s\.objEntry (\w+)\)", t).group(1)
        arg=f"(by rw [hStO {X} d{X}1 d{X}2]; exact {x})" if X in objs else x
    elif re.search(r"< s\.heap\.size", t): arg=f"(by rw [hStz]; exact {x})"
    elif re.search(r"s\.envEntry (d[A-Z]\.env)\)", t):
        E=re.search(r"s\.envEntry (d[A-Z]\.env)\)", t).group(1)
        hE,hd=envs[E]; arg=f"(by rw [hStEe _ {hE} {hd}]; exact {x})"
    elif re.search(r"< s\.envs\.size", t): arg=f"(by rw [hStE]; exact Nat.lt_succ_of_lt {x})"
    elif "s.realms" in t: arg=f"(by rw [hStR]; exact {x})"
    elif re.search(r"bG\[", t): arg=f"(by js_norm [{x}])"
    else: arg=x
    units.append(f"({x} := {arg})")
lines=[];cur=""
for un in units:
    if len(cur)+len(un)+1>110 and cur: lines.append(cur); cur=un
    else: cur=(cur+" "+un).strip()
lines.append(cur)
args="\n      ".join(lines)
tmpl=open(here+"rwh_tmpl.lean.in").read()
dist="\n".join(f"  have d{X}1 : {X} ≠ C1 := (hdist {X} (by simp)).1\n  have d{X}2 : {X} ≠ RSI := (hdist {X} (by simp)).2" for X in objs)
out=tmpl.replace("@@PREM@@",prem).replace("@@CARGS@@",args).replace("@@DIST@@",dist)
open(root+"ReactRenderHooks.lean","w").write(out)
