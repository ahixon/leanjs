"""Discharges one hypothesis of a React theorem: implicits instantiated, the hypothesis proved by a given term, the
hypotheses that become closed propositions proved by a tactic (zippy docs/react-proofs.md)."""
import re, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from react_sig import sig, names_of_imp, hname
from react_compose import subst, concl_text, hyp_type

def discharge(o):
    oi, oh = sig(o["path"], o["name"], o["marker"])
    imps = []; passes = []
    for b in oi:
        ty = b[b.index(":"):-1]
        keep = [x for x in names_of_imp(b) if x not in o["set"]]
        if keep: imps.append("{" + " ".join(keep) + " " + subst(ty, o["set"]) + "}")
    for b in oi:
        for x in names_of_imp(b):
            passes.append(f"({x} := {o['set'].get(x, x)})")
    hyps = []; args = []
    for b in oh:
        n = hname(b); ty = subst(hyp_type(b), o["set"])
        if n in o["prove"]: args.append(f"({n} := {o['prove'][n]})"); continue
        if re.search(o["auto_re"], ty): args.append(f"({n} := {o['auto_tac']})"); continue
        hyps.append(f"({n} : {ty})"); args.append(f"({n} := {n})")
    hyps += o.get("extra_hyps", [])
    c = subst(concl_text(o["path"], o["name"], o["marker"]), o["set"])
    return (f"theorem {o['newname']} " + " ".join(imps) + "\n    " + "\n    ".join(hyps) + " :\n    " + c +
            f" :=\n  {o['thm']} " + " ".join(passes) + "\n    " + " ".join(args) + "\n")
