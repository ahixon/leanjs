"""Syntactic unification of Lean term texts (zippy docs/react-proofs.md): parse into parenthesised trees, match a
pattern with free variables against a term."""
import re

def parse(s):
    toks = re.findall(r"\(|\)|[^\s()]+", s); pos = 0
    def seq():
        nonlocal pos; out = []
        while pos < len(toks) and toks[pos] != ")":
            if toks[pos] == "(":
                pos += 1; out.append(seq()); pos += 1
            else:
                out.append(toks[pos]); pos += 1
        return out
    return seq()

def text(t):
    if isinstance(t, str): return t
    if len(t) == 1 and not (isinstance(t[0], str) and t[0].startswith("-")): return text(t[0])
    return "(" + " ".join(text(x) for x in t) + ")"

def match(pat, t, free, sub):
    """extend `sub` so that pat (with variables in `free`) equals t; False on a mismatch"""
    if isinstance(pat, list) and len(pat) == 1: pat = pat[0]
    if isinstance(t, list) and len(t) == 1: t = t[0]
    if isinstance(pat, str) and pat in free:
        tt = text(t)
        if pat in sub: return sub[pat] == tt
        sub[pat] = tt; return True
    if isinstance(pat, list) and isinstance(t, list) and len(pat) == len(t):
        return all(match(a, b, free, sub) for a, b in zip(pat, t))
    return text(pat) == text(t)

def subst(s, sub):
    def f(m):
        n = m.group(1)
        if n in sub:
            r = sub[n]; return r if re.fullmatch(r"[\w'.]+", r) else f"({r})"
        return n
    return re.sub(r"(?<![A-Za-z0-9_'.])([A-Za-z_][A-Za-z0-9_']*)(?![A-Za-z0-9_'])", f, s)
