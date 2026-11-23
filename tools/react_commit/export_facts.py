"""Pass a callee's post facts up into its caller's post (zippy docs/react-proofs.md): the facts are the callee post's
conjuncts after `marker` (or a parenthesised group), renamed by the arguments the caller's `refine wp_mono (Callee ...`
passes."""
import re, sys
sys.path.insert(0, "tools/react_commit")
from compose import _theorem_header, _rename

def call_args(src, callee):
    """the named arguments `(name := value)` of the call `refine wp_mono (callee ...)` (the whole call, at depth 1)"""
    i = src.index(f"refine wp_mono ({callee} ")
    st = i + len("refine wp_mono ")
    d = 0
    for e in range(st, len(src)):
        d += {"(": 1, ")": -1}.get(src[e], 0)
        if d == 0: break
    body = src[st + 1:e]
    out = {}
    j = 0; d = 0
    while j < len(body):
        c = body[j]
        if c == "(" and d == 0:
            m = re.compile(r"\((\w+'?) := ").match(body, j)
            if m:
                k = m.end(); dd = 1
                while dd > 0:
                    dd += {"(": 1, ")": -1}.get(body[k], 0); k += 1
                out[m.group(1)] = body[m.end():k - 1]; j = k; continue
        d += {"(": 1, ")": -1}.get(c, 0)
        j += 1
    return out

def facts_group(path, thm):
    """the parenthesised facts group `(… ∧ …) ∧` that follows `h' = h ∧` in thm's post"""
    h = _theorem_header(path, thm)
    post = h[h.rindex("fun v w h' =>"):]
    i = post.index("h' = h ∧") + len("h' = h ∧")
    while post[i] in " \n": i += 1
    assert post[i] == "(", post[i:i + 80]
    d = 0
    for j in range(i, len(post)):
        if post[j] == "(": d += 1
        elif post[j] == ")":
            d -= 1
            if d == 0: return post[i:j + 1]

def renamed(caller_src, callee_path, callee_thm, callee_ref):
    return _rename(facts_group(callee_path, callee_thm), call_args(caller_src, callee_ref))
