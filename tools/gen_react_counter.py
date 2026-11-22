"""Generates JSProofs/ReactCounter.lean: the counter component's statement takes ReactUseState.click_spec's
premises (read from that file) plus its own (react_counter/counter_extra.lean.in), in react_counter/counter_tmpl.lean.in."""
import re
import os
repo=os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
root=os.path.join(repo,"JSProofs")+"/"
here=os.path.join(repo,"tools","react_counter")+"/"
u=open(root+"ReactUseState.lean").read()
i=u.index("theorem click_spec {"); j=u.index(" :\n    WP eng answer (n + 4) h (callImpl eng (.obj fS) tS #[x]) s fun v w h' =>")
prem=u[i+len("theorem click_spec "):j]
names=[m.group(1) for m in re.finditer(r"\((h[A-Za-z0-9']*|d[0-9]+) :", prem)]
prem=prem.replace("{tS x : Value}","{tS : Value}")
prem=prem.replace("(hf : 120 ≤ s.fuel)","(hf : 200 ≤ s.fuel)")
prem=prem.replace("{oR : Option EnvId}","{oR : Option EnvId} {fK IR IJ fJ AP fV fN AIP IP OP : ObjId} {dK dJ : FuncData} {tK vT : Value} {argsK : Array Value}\n    {bA bJ : HashMap JSStr Binding} {oA oJ : Option EnvId} {bdIR bdIJ bdT : Binding} {bdV bdN : BuiltinData} {xE : F64}\n    {irw ire irc ijw ije ijc pw pe pc nnw nne nnc : Bool}")
extra=open(here+"counter_extra.lean.in").read().rstrip("\n")
k=prem.rindex(")")
prem=prem[:k+1]+"\n"+extra+prem[k+1:]
tmpl=open(here+"counter_tmpl.lean.in").read()
open(root+"ReactCounter.lean","w").write(tmpl.replace("@@PREM@@",prem))
