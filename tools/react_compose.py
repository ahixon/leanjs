"""Composes two React call theorems: the outer one's hypothesis about a call discharged by the inner theorem (zippy docs/react-proofs.md)."""
import re, sys
import os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from react_sig import sig, names_of_imp, hname

def W(name):  # word-boundary pattern for a Lean identifier
    return r"(?<![\w.'])" + re.escape(name) + r"(?![\w'])"

def subst(text, mapping):
    """Simultaneous identifier substitution."""
    if not mapping: return text
    pat = re.compile("|".join(W(k) for k in sorted(mapping, key=len, reverse=True)))
    return pat.sub(lambda m: mapping[m.group(0)], text)

def concl_text(path, name, marker):
    src = open(path).read()
    i = src.index("theorem " + name); j = src.index(marker, i); k = src.index(":= by", j)
    return src[j:k].strip()

def hyp_type(b):
    return b[b.index(":") + 1:-1].strip()

def compose(o, i):
    oi, oh = sig(o["path"], o["name"], o["marker"])
    ii, ih = sig(i["path"], i["name"], i["marker"])
    # outer implicits kept
    oimps = []; onames = set(); okept = []
    for b in oi:
        ty = b[b.index(":"):-1]
        keep = [x for x in names_of_imp(b) if x not in o["set"] and x not in o.get("drop_imps", ()) and x not in (o["fp"], o["k"])]
        onames |= set(keep); okept.extend(keep)
        if keep: oimps.append("{" + " ".join(keep) + " " + ty + "}")
    shared = set(i.get("shared", ()))
    # inner implicits: rename on collision
    ren = {}; iimps = []; ipass = []
    for b in ii:
        ty = b[b.index(":"):-1]
        keep = []
        for x in names_of_imp(b):
            if x in i["set"]: continue
            if x in shared: ipass.append(f"({x} := {x})"); continue
            nx = i["pfx"] + x if x in onames or x in shared else x
            if nx != x: ren[x] = nx
            keep.append(x); ipass.append(f"({x} := {nx})")
        if keep: iimps.append(("{" + " ".join(keep) + " " + ty + "}", keep))
    # rename within implicit types too
    iimps_txt = []
    for t, keep in iimps:
        iimps_txt.append(subst(t, ren))
    ohn = {hname(b) for b in oh}
    hren = {}
    for b in ih:
        n = hname(b)
        if n in i["self"]: continue
        if n in ohn or n in o.get("fresh", ()): hren[n] = i["hpfx"] + n
    def itext(t):
        t = subst(t, ren)
        for a, b in i.get("pre", []): t = re.sub(a, b, t)
        return t
    ic = itext(concl_text(i["path"], i["name"], i["marker"]))
    m = re.search(r"Frame (.*) s w ∧\s*s\.fuel ≤ w\.fuel \+ (.*?) ∧ Q w h'", ic, re.S)
    FP, K = m.group(1).strip(), m.group(2).strip()
    FP = re.sub(r"\s+", " ", FP)
    oset = dict(o["set_txt"]); oset.update({o["fp"]: f"({FP})", o["k"]: f"({K})"})
    # outer hyps
    ohyps = []; oargs = []
    for b in oh:
        n = hname(b)
        if n == o["hole"] or n in o["prove"]: continue
        ohyps.append("(" + n + " : " + subst(hyp_type(b), oset) + ")")
        oargs.append(f"({n} := {n})")
    ohyps += o.get("extra_hyps", [])
    # inner hyps
    ihyps = []; iargs = []
    for b in ih:
        n = hname(b); ty = hyp_type(b); nn = hren.get(n, n)
        if n in i["self"]:
            iargs.append(f"({n} := {i['self'][n]})"); continue
        ty = itext(ty)
        if "WP eng answer" in ty:
            body = re.sub(W("s"), i["q"], ty)
            body = subst(body, i["set_txt"])
            ihyps.append(f"({nn} : ∀ {i['q']}, Frame {i['hop']} s {i['q']} → s.fuel ≤ {i['q']}.fuel + {i['hopk']} →\n      {body})")
            iargs.append(f"({n} := {nn} w hF hfu)")
        elif re.search(r"!= s\.envs\.size", ty):
            ty2 = ty.replace("q.1 != s.envs.size", "decide (q.1 < s.envs.size)")
            ihyps.append(f"({nn} : {subst(ty2, i['set_txt'])})")
            iargs.append(f"({n} := binds_avoid {nn} hF.envs_le)")
        elif re.search(r"decide \(q\.1 < s\.envs\.size\)", ty):
            ihyps.append(f"({nn} : {subst(ty, i['set_txt'])})")
            iargs.append(f"({n} := binds_lt_mono {nn} hF.envs_le)")
        elif i.get("bG_tac") and re.search(W("bG") + r"\[", ty):
            ihyps.append(f"({nn} : {subst(ty, i['set_txt'])})")
            iargs.append(f"({n} := " + i["bG_tac"].replace("{X}", nn) + ")")
        else:
            ihyps.append(f"({nn} : {subst(ty, i['set_txt'])})")
            if re.search(W("s"), ty): iargs.append(f"({n} := " + i.get("transfer", "by first | exact {X} | transfer hF, {X}").replace("{X}", nn) + ")")
            else: iargs.append(f"({n} := {nn})")
    ihyps += i.get("extra_hyps", [])
    # conclusion
    oc = subst(concl_text(o["path"], o["name"], o["marker"]), oset)
    oc = re.sub(r"WP eng answer \([^)]*\)", "WP eng answer " + o["level"], oc, count=1)
    osetargs = " ".join(f"({k} := {v})" for k, v in o["set"].items())
    osetargs += f" ({o['fp']} := {FP}) ({o['k']} := {K}) " + " ".join(f"({x} := {x})" for x in okept if x not in ("eng", "σ", "answer"))
    isetargs = " ".join(f"({k} := {v})" for k, v in i["set"].items())
    proves = "\n".join(f"  case {n} =>\n    {tac}" for n, tac in o["prove"].items())
    proof = f"""  refine {o['thm']} {osetargs}
    {" ".join(oargs)}
    ({o['hole']} := ?hole) {" ".join(f"({n} := ?{n})" for n in o["prove"])}
{proves}
  case hole =>
    intro w h1 hF hfu
{i.get('pre_tac', '')}
    refine wp_mono ({i['thm']} {isetargs}
      {" ".join(ipass)}
      {" ".join(iargs)}) ?_
    intro v w' h' ⟨hv, hFr, hfu', hQ⟩
    {o['post']}
"""
    stmt = (f"theorem {o['newname']} " + " ".join(oimps) + " " + " ".join(iimps_txt) + "\n    " +
            "\n    ".join(ohyps + ihyps) + " :\n    " + oc + " := by\n" + proof)
    return stmt, FP, K
