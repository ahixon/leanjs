"""Argument lists for applying a callee spec at a named state (zippy docs/react-proofs.md).

`premises(path, thm)` parses a theorem's binders; `args(...)` builds `(name := term)` for each: implicits by name
(renamed), explicit premises transferred from the caller's facts by the shape of their type.
"""
import re

def binders(path, thm):
    s = open(path).read()
    i = s.index("theorem " + thm + " ")
    j = s.index(":\n    WP ", i)
    t = s[i + len("theorem " + thm):j]
    t = "\n".join(l.split("--")[0] for l in t.split("\n"))
    out = []; k = 0
    while k < len(t):
        c = t[k]
        if c in "({":
            close = ")" if c == "(" else "}"
            d = 0
            for e in range(k, len(t)):
                if t[e] in "({[": d += 1
                elif t[e] in ")}]":
                    d -= 1
                    if d == 0: break
            inner = t[k + 1:e]
            names, ty = inner.split(" : ", 1)
            for nm in names.split():
                out.append((c == "{", nm, " ".join(ty.split())))
            k = e + 1
        else:
            k += 1
    return out

def args(path, thm, ren, explicit, implicit_skip=()):
    """ren: callee name -> caller term (implicits and premises); explicit: callee premise name -> term overriding."""
    parts = []
    for imp, nm, ty in binders(path, thm):
        if imp:
            if nm in ("n", "h", "s", "eng", "σ", "answer") or nm in implicit_skip: continue
            parts.append(f"({nm} := {ren.get(nm, nm)})")
        else:
            parts.append(f"({nm} := {explicit.get(nm, ren.get(nm, nm))})")
    return " ".join(parts)

def caller_bounds(path, thm):
    """Object -> the caller's premise `O < s.heap.size`."""
    m = {}
    for imp, nm, ty in binders(path, thm):
        r = re.fullmatch(r"(\w+) < s\.heap\.size", ty)
        if not imp and r: m[r.group(1)] = nm
    return m

def transfer(path, thm, ren, explicit, objren, bounds, k, ds, written=()):
    """Premise terms at stage k: gZk (heap), gKk (kinds), gPk (props unless written), gEk (envs), gFk (fuel),
    gBk (bindings other than the loop's)."""
    ex = dict(explicit)
    for imp, nm, ty in binders(path, thm):
        if imp or nm in ex: continue
        src = ren.get(nm, nm)
        m = re.fullmatch(r"(\d+) ≤ s\.fuel", ty)
        if m: ex[nm] = f"(Nat.le_trans (by decide) gF{k})"; continue
        m = re.fullmatch(r"(\w+) < s\.heap\.size", ty)
        if m:
            o = objren.get(m.group(1), m.group(1)); ex[nm] = f"(Nat.lt_of_lt_of_le {bounds[o]} gZ{k})"; continue
        m = re.fullmatch(r"(\w+(?:\.\w+)?) < s\.envs\.size", ty)
        if m: ex[nm] = f"(by first | exact Nat.lt_of_lt_of_le {src} gE{k} | (rw [{ren.get('_envfix','hWenv')}] at *; exact Nat.lt_of_lt_of_le {src} gE{k}))"; continue
        m = re.match(r"\(s\.objEntry (\w+)\)\.kind", ty)
        if m:
            o = objren.get(m.group(1), m.group(1)); ex[nm] = f"(by rw [gK{k} {o} {bounds[o]}]; exact {src})"; continue
        m = re.match(r"\(s\.objEntry (\w+)\)\.props\.get\? \(\.str \"([^\"]*)\"\)", ty)
        if m:
            o = objren.get(m.group(1), m.group(1)); key = m.group(2)
            ex[nm] = (f"(by rw [gP{k} {o} (.str \"{key}\") (by simp [{ds}] <;> decide) {bounds[o]}]; exact {src})")
            continue
        m = re.match(r"\w+\[JSStr\.ofString \"([^\"]*)\"\]\? = ", ty)
        if m: ex[nm] = f"(by rw [gB{k} _ (by decide)]; exact {src})"; continue
    return args(path, thm, ren, ex)
