"""Generates JSProofs/ReactUpdateFunction.lean: updateFunctionComponent for the counter's click re-render.
Statement: ReactRenderHooks.click_spec's premises, ReactReconcileChildren.click_spec's (renamed: shared objects mapped,
the rest prefixed; what renderWithHooks' post provides dropped), and its own (react_ufc/ufc_extra.lean.in)."""
import os, re
repo=os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
root=os.path.join(repo,"JSProofs")+"/"
here=os.path.join(repo,"tools","react_ufc")+"/"
def get(f, hd):
    u=open(root+f).read()
    i=u.index("theorem click_spec {"); j=u.index(" :\n    "+hd)
    prem=u[i+len("theorem click_spec "):j]
    k=j+len(" :\n    "+hd); l=u.index(" := by",k)
    return prem,u[k:l]
wprem,wpost=get("ReactRenderHooks.lean","WP eng answer (n + 6) h (callImpl eng (.obj fRW) tRW #[.obj C0, .obj C1, .obj fK, P, .undefined, two]) s")
cprem,cpost=get("ReactReconcileChildren.lean","WP eng answer (n + 4) h (callImpl eng (.obj fC) tC #[.obj C0, .obj RF, .obj El, ln]) s fun v w h' =>")
def items(prem):
    """(kind, text) pieces: implicit binders {…} and hypotheses (…), comments dropped."""
    out=[]; i=0
    while i<len(prem):
        c=prem[i]
        if c in "{(":
            close="}" if c=="{" else ")"; depth=0; j=i
            while True:
                if prem[j] in "{(": depth+=1
                elif prem[j] in "})": depth-=1
                if depth==0: break
                j+=1
            out.append((c,prem[i:j+1])); i=j+1
        elif prem.startswith("--",i): i=prem.index("\n",i)
        else: i+=1
    return out
witems=items(wprem); citems=items(cprem)
wvars=set()
for k,t in witems:
    if k=="{": wvars|=set(t[1:t.index(":")].split())
shared={"C0":"C0","OP":"OP","bG":"bG","h":"h","n":"n","s":"s","eng":"eng","σ":"σ","answer":"answer"}
mapping={"g":"d.env","RF":"C1","vEl":"vT","ln":"two"}
drop_vars={"g","RF","vEl","ln","El","C","tC"}
drop_hyps={"hG","hGe","hEl","hElk","hEltyp","hElkey","hElty","hElp","hC","hCk","hCp","hCr","hRF","hRFk","hC0","hC0k","hOP","hOPk","hOPp","hOPr"}
ren={}
cvars=[]
for k,t in citems:
    if k=="{":
        vs=t[1:t.index(":")].split(); ty=t[t.index(":"):]
        keep=[]
        for v in vs:
            if v in shared or v in drop_vars: continue
            nv="r_"+v if v in wvars else v
            ren[v]=nv; keep.append(nv)
        if keep: cvars.append("{"+" ".join(keep)+" "+ty)
def rn(t):
    for v,nv in sorted(ren.items(),key=lambda x:-len(x[0])):
        if v!=nv: t=re.sub(r"(?<![\w.])"+re.escape(v)+r"(?![\w'])",nv,t)
    for v,nv in mapping.items(): t=re.sub(r"(?<![\w.])"+re.escape(v)+r"(?![\w'])",nv,t)
    return t
chyps=[]; cnames=[]
for k,t in citems:
    if k=="(":
        nm=t[1:t.index(" :")]
        if nm in drop_hyps: continue
        body=rn(t[t.index(" :"):])
        if nm=="hdX": body=body.replace("[fCR, fPl, El, C, OP]","[fCR, fPl, OP]")
        chyps.append("(r"+nm+body); cnames.append(nm)
open(here+"rc_names.txt","w").write(" ".join(cnames))
open(here+"rc_ren.txt","w").write(repr(ren))
wtext=wprem.rstrip()
extra=open(here+"ufc_extra.lean.in").read().rstrip("\n")
def wrap(xs):
    lines=[];cur=""
    for un in xs:
        if len(cur)+len(un)+1>110 and cur: lines.append(cur); cur=un
        else: cur=(cur+" "+un).strip()
    lines.append(cur); return "\n    ".join(lines)
prem=wtext.replace("(hf : 300 ≤ s.fuel)","(hf : 500 ≤ s.fuel)")+"\n    -- (reconcileChildren's premises, its objects renamed)\n    "+wrap(cvars)+"\n    "+wrap(chyps)+"\n"+extra
# renderWithHooks' premises at the call's state w1 (after prepareToReadContext)
wpt={}
for k,t in witems:
    if k=="(":
        wpt[t[1:t.index(" :")]]=t[t.index(" :")+2:-1]
wnames=[t[1:t.index(" :")] for k,t in witems if k=="("]
bound={}
for x,t in wpt.items():
    mm=re.fullmatch(r"\s*(\w+) < s\.heap\.size\s*", t)
    if mm: bound[mm.group(1)]=x
envs={"dS.env":("hSG","hSd"),"dK.env":("hAG","hKd"),"dJ.env":("hJG","hJd")}
units=[]
for x in wnames:
    t=wpt[x]
    if x=="hf": arg="(by omega)"
    elif x=="hGe": arg="hd1"
    elif re.search(r"s\.objEntry (\w+)\)", t):
        X=re.search(r"s\.objEntry (\w+)\)", t).group(1); arg=f"(by rw [hw1o {X} {bound[X]}]; exact {x})"
    elif re.fullmatch(r"\s*(\w+) < s\.heap\.size\s*", t): arg=f"(Nat.lt_of_lt_of_le {x} hw1z)"
    elif re.search(r"s\.envEntry (d[A-Z]\.env)\)", t):
        E=re.search(r"s\.envEntry (d[A-Z]\.env)\)", t).group(1); hE,hd=envs[E]; arg=f"(by rw [hw1s _ {hE} {hd}]; exact {x})"
    elif "s.envEntry" in t: raise Exception("env "+x+t)
    elif re.search(r"< s\.envs\.size", t): arg=f"(Nat.lt_of_lt_of_le (Nat.lt_succ_of_lt {x}) hw1E)"
    elif "s.realms" in t: arg=f"(by rw [hw1R]; exact {x})"
    elif re.search(r"\bbG\[", t): arg=f"(by js_norm [{x}])"
    else: arg=x
    units.append(f"({x} := {arg})")
rwargs="\n      ".join(wrap(units).split("\n    "))
# reconcileChildren's premises at its call's state St (facts hSo, hSo2, hSz, hSE, hSU, hSd, hSC1k, hSC1c, hSF)
cpt={}; corder=[]
for k,t in citems:
    if k=="(":
        nm=t[1:t.index(" :")]; corder.append(nm); cpt[nm]=t[t.index(" :")+2:-1]
cbound={}
for x,t in cpt.items():
    mm=re.fullmatch(r"\s*(\w+) < s\.heap\.size\s*", t)
    if mm: cbound[mm.group(1)]=x
dropped={"hG":"hGw3S","hGe":"hSd","hEl":"(Nat.lt_of_lt_of_le hEb hSz2)","hElk":"(by rw [hSo2 E hEb hEC1]; exact hEk)",
  "hEltyp":"(by rw [hSo2 E hEb hEC1]; exact hEt)","hElkey":"(by rw [hSo2 E hEb hEC1]; exact hEkey)",
  "hElty":"(by rw [hSo2 E hEb hEC1]; exact hEty)","hElp":"(by rw [hSo2 E hEb hEC1]; exact hEpr)",
  "hC":"(Nat.lt_of_lt_of_le hCb hSz2)","hCk":"(by rw [hSo2 C hCb hCC1, hCk]; rfl)","hCp":"(by rw [hSo2 C hCb hCC1]; exact hCp)",
  "hCr":"(by rw [hSo2 C hCb hCC1]; exact hCr)","hRF":"(Nat.lt_of_lt_of_le hC1 hSz)","hRFk":"hSC1k",
  "hC0":"(Nat.lt_of_lt_of_le hC0 hSz)","hC0k":"(by rw [hSo C0 hC0 dC01 dC02 dC03 dC04]; exact hC0k)",
  "hOP":"(Nat.lt_of_lt_of_le hOP hSz)","hOPk":"(by rw [hSo OP hOP dOP.1 dOP.2.1 dOP.2.2 dOPR]; exact hOPk)",
  "hOPp":"(by rw [hSo OP hOP dOP.1 dOP.2.1 dOP.2.2 dOPR]; exact hOPp)","hOPr":"(by rw [hSo OP hOP dOP.1 dOP.2.1 dOP.2.2 dOPR]; exact hOPref)"}
cunits=[]
for x in corder:
    if x in dropped: cunits.append(f"({x} := {dropped[x]})"); continue
    t=rn(cpt[x]); rx="r"+x
    if x=="hf": arg="(Nat.le_trans (by decide) hSF)"
    elif x=="hRFc": arg="hSC1c"
    elif x=="hdX": arg="hdX'"
    elif re.search(r"s\.objEntry (\w+)\)", t):
        Y=re.search(r"s\.objEntry (\w+)\)", t).group(1)
        b="r"+cbound[[k for k,v in ren.items() if v==Y][0] if Y in ren.values() else Y] if (Y in ren.values() or Y in cbound) else None
        arg=f"(by rw [hSo {Y} (by assumption) (hdW {Y} (by simp)).1 (hdW {Y} (by simp)).2.1 (hdW {Y} (by simp)).2.2.1 (hdW {Y} (by simp)).2.2.2]; exact {rx})"
    elif re.fullmatch(r"\s*(\w+) < s\.heap\.size\s*", t): arg=f"(Nat.lt_of_lt_of_le {rx} hSz)"
    elif "s.envEntry dU.env" in t: arg=f"(by rw [hSU]; exact {rx})"
    elif "s.envEntry" in t: raise Exception("env "+x+t)
    elif re.search(r"< s\.envs\.size", t): arg=f"(Nat.lt_of_lt_of_le (Nat.lt_succ_of_lt {rx}) hSE)"
    elif re.search(r"\bbG\[", t): arg=f"(by js_norm [{rx}, ReactFinishHooks.resetMap])"
    else: arg=rx
    cunits.append(f"({x} := {arg})")
rcargs="\n      ".join(wrap(cunits).split("\n    "))
xf=[l.strip() for l in cpost.split("\n") if "(w.objEntry X)" in l]
xfacts=" ∧\n      ".join(rn(l).rstrip(" ∧").replace("w.realm = s.realm ∧ ","") for l in xf)
post=f"""
      ∃ C : ObjId, v = .obj X ∧ Frame (fpUF d.env C1 H0 Q RSI X) s w ∧ s.fuel ≤ w.fuel + 500 ∧ h' = h ∧ w.realm = s.realm ∧
      {xfacts} ∧
      (w.objEntry C1).props.get? (.str "child") = some (.data (.obj X) true cw cc) ∧
      (w.objEntry C).props.get? (.str "children") =
        some (.data (.str (JSStr.ofString "Count: " ++ numberToJSStr xE ++ JSStr.ofString "")) true true true) ∧
      (w.objEntry C).kind.isPlain = true ∧ C < w.heap.size ∧ s.heap.size ≤ C ∧
      ∃ bm, Scope.declLike? (w.envEntry d.env) = some (bm, none) ∧
        (∃ bd, bm[JSStr.ofString "didReceiveUpdate"]? = some bd ∧ bd.mutable = true ∧ bd.value.isSome = true) ∧
        (∃ bd, bm[JSStr.ofString "thenableIndexCounter$1"]? = some bd ∧ bd.mutable = true ∧ bd.value.isSome = true) ∧
        ∃ bd, bm[JSStr.ofString "thenableState$1"]? = some bd ∧ bd.mutable = true ∧ bd.value.isSome = true"""
tmpl=open(here+"ufc_tmpl.lean.in").read().replace("@@RWARGS@@",rwargs).replace("@@RCARGS@@",rcargs).replace("@@POST@@",post)
allh=re.findall(r"\((h[A-Za-z0-9_']*|d[A-Za-z0-9]+|r[a-z][A-Za-z0-9_']*) :", prem)
import collections
dup=[x for x,c in collections.Counter(allh).items() if c>1]
assert not dup, dup
open(root+"ReactUpdateFunction.lean","w").write(tmpl.replace("@@PREM@@",prem))
