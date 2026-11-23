"""Generates JSProofs/ReactBeginCounter.lean: beginWork for the counter fiber in the click's render.
Statement: ReactUpdateFunction.click_spec's premises plus its own (react_bwc/bwc_extra.lean.in)."""
import os, re
repo=os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
root=os.path.join(repo,"JSProofs")+"/"
here=os.path.join(repo,"tools","react_bwc")+"/"
u=open(root+"ReactUpdateFunction.lean").read()
hd="WP eng answer (n + 7) h (callImpl eng (.obj fUF) tUF #[.obj C0, .obj C1, .obj fK, P, two]) s fun v w h' =>"
i=u.index("theorem click_spec {"); j=u.index(" :\n    "+hd)
prem=u[i+len("theorem click_spec "):j]
k=j+len(" :\n    "+hd); l=u.index(" := by",k)
post=u[k:l]
pt={}; order=[]
depth=0; i=0
while i<len(prem):
    if prem[i]=="(":
        d=0; j=i
        while True:
            if prem[j]=="(": d+=1
            elif prem[j]==")": d-=1
            if d==0: break
            j+=1
        t=prem[i:j+1]
        m=re.match(r"\((\w[\w']*) :",t)
        if m: pt[m.group(1)]=t[t.index(" :")+2:-1]; order.append(m.group(1))
        i=j+1
    elif prem[i]=="{":
        i=prem.index("}",i)+1
    else: i+=1
bound={}
for x,t in pt.items():
    mm=re.fullmatch(r"\s*(\w+) < s\.heap\.size\s*", t)
    if mm: bound[mm.group(1)]=x
envs={"dS.env":("hSG","hSd"),"dK.env":("hAG","hKd"),"dJ.env":("hJG","hJd"),"dU.env":("rhE","hdUe")}
units=[]
for x in order:
    t=pt[x]
    if x=="hf" or re.fullmatch(r"\s*\d+ ≤ s\.fuel\s*", t): arg="(Nat.le_trans (by decide) gSF)"
    elif x=="hGe": arg="gSd"
    elif x=="hC1l": arg="gSC1l"
    elif x=="hGDR": arg="(by js_norm [hGDR])"
    elif x=="hGDRm": arg="hGDRm"
    elif x=="hGDRi": arg="rfl"
    elif re.search(r"\(s\.objEntry (\w+)\)\.props\.get\? ", t):
        X=re.search(r"\(s\.objEntry (\w+)\)", t).group(1)
        arg=f"(by rw [gSp {X} _ {bound[X]} (fun h => by first | decide | exact absurd h (by assumption) | exact absurd h (Ne.symm (by assumption)) | exact absurd h ((hdW _ (by simp)).1))]; exact {x})"
    elif re.search(r"\(s\.objEntry (\w+)\)\.kind", t):
        X=re.search(r"\(s\.objEntry (\w+)\)", t).group(1); arg=f"(by rw [gSk {X} {bound[X]}]; exact {x})"
    elif re.search(r"\(s\.objEntry (\w+)\)\.proto", t):
        X=re.search(r"\(s\.objEntry (\w+)\)", t).group(1); arg=f"(by rw [gSpr {X} {bound[X]}]; exact {x})"
    elif "s.objEntry" in t: raise Exception("obj "+x+t)
    elif re.fullmatch(r"\s*(\w+) < s\.heap\.size\s*", t): arg=f"(Nat.lt_of_lt_of_le {x} gSz)"
    elif re.search(r"s\.envEntry (d[A-Za-z]*\.env)\)", t):
        E=re.search(r"s\.envEntry (d[A-Za-z]*\.env)\)", t).group(1); hE,hd=envs[E]; arg=f"(by rw [gSe _ {hE} {hd}]; exact {x})"
    elif "s.envEntry" in t: raise Exception("env "+x+t)
    elif re.search(r"< s\.envs\.size", t): arg=f"(Nat.lt_of_lt_of_le {x} gSE)"
    elif "s.realms" in t: arg=f"(by rw [gSR]; exact {x})"
    elif re.search(r"\bbG\[", t): arg=f"(by js_norm [{x}])"
    else: arg=x
    units.append(f"({x} := {arg})")
lines=[];cur=""
for un in units:
    if len(cur)+len(un)+1>110 and cur: lines.append(cur); cur=un
    else: cur=(cur+" "+un).strip()
lines.append(cur)
prem=prem.replace("(hf : 500 ≤ s.fuel)","(hf : 520 ≤ s.fuel)").replace("{tUF : Value} ","").replace("{tUF : Value}","")
post=post.replace("s.fuel ≤ w.fuel + 500","s.fuel ≤ w.fuel + 530").replace("Frame (fpUF d.env C1 H0 Q RSI X) s w","Frame (fpB d.env C1 H0 Q RSI X) s w")
extra=open(here+"bwc_extra.lean.in").read().rstrip("\n")
kk=prem.rindex(")")
prem=prem[:kk+1]+"\n"+extra+prem[kk+1:]
tmpl=open(here+"bwc_tmpl.lean.in").read()
open(root+"ReactBeginCounter.lean","w").write(tmpl.replace("@@PREM@@",prem).replace("@@POST@@",post).replace("@@ARGS@@","\n      ".join(lines)))
