"""Pass a callee's post facts up into its caller's post (zippy docs/react-proofs.md): the facts are the callee post's
conjuncts after `marker` (or a parenthesised group), renamed by the arguments the caller's `refine wp_mono (Callee ...`
passes."""
import re, sys
sys.path.insert(0, "tools/react_commit")
from compose import _theorem_header, _rename

def call_args(src, callee):
    i = src.index(f"refine wp_mono ({callee} ")
    j = i + len(f"refine wp_mono ({callee} ")
    out = {}
    while True:
        while src[j] in " \n": j += 1
        m = re.compile(r"\((\w+) := ").match(src, j)
        if not m: break
        k = m.end(); d = 1
        while d > 0:
            if src[k] == "(": d += 1
            elif src[k] == ")": d -= 1
            k += 1
        out[m.group(1)] = src[m.end():k - 1]; j = k
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
