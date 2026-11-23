"""Composition helpers for the commit phase's specs (zippy docs/react-proofs.md).

A callee spec's binders, parsed from its Lean source, renamed with a prefix and with some of its variables replaced
by the caller's terms; from them the binders a composite theorem adds and the callee's call with named arguments.

  binders(path, thm)                 -> [(name, kind, type)]  kind '{' implicit or '(' explicit
  compose(path, thm, prefix, subst, given, drop)
      subst: callee variable -> caller term (dropped from the added binders, passed as that term)
      given: callee premise -> caller proof term (dropped, passed as that term)
      drop:  callee binders left out entirely (e.g. `s`, `h`, `n`: given in the call explicitly)
      -> (added binder text, named-argument text)
"""
import re, sys

def _theorem_header(path, thm):
    s = open(path).read()
    i = s.index("theorem " + thm + " ")
    j = s.index(":= by", i) if ":= by" in s[i:i+40000] else s.index(":=", i)
    return s[i + len("theorem " + thm):j]

def binders(path, thm):
    h = _theorem_header(path, thm)
    out = []; k = 0
    while k < len(h):
        c = h[k]
        if c in "({":
            close = ")" if c == "(" else "}"
            d = 0; m = k
            while True:
                if h[m] in "({[": d += 1
                elif h[m] in ")}]": d -= 1
                if d == 0: break
                m += 1
            inner = h[k+1:m]
            names, typ = inner.split(" : ", 1)
            for nm in names.split():
                out.append((nm, c, typ.strip()))
            k = m + 1
        elif c == ":":
            break
        else:
            k += 1
    return out

def _rename(text, ren):
    if not ren: return text
    pat = re.compile(r"(?<![A-Za-z0-9_'.$])(" + "|".join(re.escape(x) for x in sorted(ren, key=len, reverse=True)) + r")(?![A-Za-z0-9_'$])")
    return pat.sub(lambda m: ren[m.group(1)], text)

def compose(path, thm, prefix, subst, given, drop=()):
    bs = binders(path, thm)
    ren = {}
    for nm, kind, typ in bs:
        if nm in drop: continue
        ren[nm] = "(" + subst[nm] + ")" if nm in subst else prefix + nm
    added = []; args = []
    for nm, kind, typ in bs:
        if nm in drop: continue
        if nm in subst:
            args.append(f"({nm} := {subst[nm]})"); continue
        if nm in given:
            args.append(f"({nm} := {given[nm]})"); continue
        t = _rename(typ, ren)
        added.append(f"{kind}{prefix}{nm} : {t}{'}' if kind == '{' else ')'}")
        args.append(f"({nm} := {prefix}{nm})")
    return added, args

if __name__ == "__main__":
    for b in binders(sys.argv[1], sys.argv[2]): print(b)
