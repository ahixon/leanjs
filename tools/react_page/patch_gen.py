"""Makes the `*Gen` modules' function syntax trees the page's own (zippy docs/react-proofs.md, Tests/react-counter).

A `*Gen` module was compiled from a snippet, so its `ES.Func`s carry the snippet's `FuncInfo.span` and `id`; the page
(React's CommonJS files verbatim, one classic script each) gives the same functions other ones, and premises
`d.code = XGen.f_func` must be true of the page's heap. For each `X_func` def, the page function whose syntax tree is
the same up to spans and ids is found (unique, else reported); every FuncInfo in the module inside that function's
source range is shifted by the difference (spans by the start offset, ids by the id difference: a function's subtree
gets consecutive ids), and the patched tree is checked equal to the page's, character for character.
Usage: python3 tools/react_page/patch_gen.py PAGE_DIR [--write] [Gen modules...]"""
import os, re, subprocess, sys
LEANJS = ".lake/build/bin/leanjs"
OUTD = ".lake/scratch/page"
SCRIPTS = ["cjs.js", "react.js", "react-jsx-runtime.js", "scheduler.js", "react-dom.js", "react-dom-client.js", "app.js"]
INFO = re.compile(r"span := \{ start := (\d+), stop := (\d+) : ((?:ES\.)?Span) \}((?:(?!span := ).)*?)id := (\d+)")
DEF = re.compile(r"^def (\w+)_func : ES\.Func := (.*)$", re.M)
def norm(rhs): return INFO.sub(lambda m: "span := S" + m.group(4) + "id := I", rhs)
def top(rhs):  # the function's own FuncInfo: the last one in its tree
    ms = list(INFO.finditer(rhs)); m = ms[-1]
    return int(m.group(1)), int(m.group(2)), int(m.group(5))
def funcs(text):
    """Every `(ES.Func.mk ...)` term in `text` (nested ones too), by balanced parentheses."""
    out, key = [], "(ES.Func.mk "
    i = text.find(key)
    while i >= 0:
        d, j = 0, i
        while True:
            c = text[j]
            if c == "(": d += 1
            elif c == ")":
                d -= 1
                if d == 0: break
            elif c == '"':  # skip string literals (they may hold parentheses)
                j += 1
                while text[j] != '"':
                    j += 2 if text[j] == "\\" else 1
            j += 1
        out.append(text[i:j + 1])
        i = text.find(key, i + 1)
    return out
def page_defs(page):
    os.makedirs(OUTD, exist_ok=True)
    defs = {}
    for sc in SCRIPTS:
        out = os.path.join(OUTD, sc.replace(".js", ".lean"))
        if not os.path.exists(out) or os.path.getmtime(out) < os.path.getmtime(os.path.join(page, sc)):
            subprocess.run([LEANJS, "compile", "--defs", os.path.join(page, sc), out], check=True, capture_output=True)
        text = open(out).read()
        text = text[text.index("def script_stmts"):]
        text = text[:text.index("\n")]
        seen = set()
        for f in funcs(text):
            if f in seen: continue
            seen.add(f)
            s0, e0, i0 = top(f)
            defs.setdefault(norm(f), []).append((sc, f"@{s0}", f))
    return defs
def main():
    args = sys.argv[1:]; page = args.pop(0); write = "--write" in args
    mods = [a for a in args if a != "--write"] or sorted(f[:-5] for f in os.listdir("JSProofs") if f.endswith("Gen.lean"))
    defs = page_defs(page)
    for mod in mods:
        path = f"JSProofs/{mod}.lean"; src = open(path).read()
        fs = [(m.group(1), m.group(2)) for m in DEF.finditer(src)]
        # outermost functions first: a function inside another is patched with it
        plan, report = [], []
        for name, rhs in fs:
            cands = defs.get(norm(rhs), [])
            if len(cands) != 1:
                report.append(f"{name}:{'none' if not cands else 'ambiguous ' + ','.join(c[0] + ':' + c[1] for c in cands)}")
                continue
            s0, e0, i0 = top(rhs); s1, e1, i1 = top(cands[0][2])
            plan.append((s0, e0, s1 - s0, i1 - i0, name, cands[0]))
        # matched trees are equal up to FuncInfos, so their FuncInfos correspond in textual order: map each of the
        # module's (start, stop, id) to the page's (the source text may differ in whitespace)
        mp = {}
        for *_, name, cand in plan:
            g = dict((m.group(1), m.group(2)) for m in DEF.finditer(src))[name]
            for x, y in zip(INFO.finditer(g), INFO.finditer(cand[2])):
                k = (int(x.group(1)), int(x.group(2)), int(x.group(5)))
                v = (int(y.group(1)), int(y.group(2)), int(y.group(5)))
                if mp.get(k, v) != v: report.append(f"{name}:conflict")
                mp[k] = v
        def shift(m):
            k = (int(m.group(1)), int(m.group(2)), int(m.group(5)))
            if k not in mp: return m.group(0)
            a, b, idv = mp[k]
            return f"span := {{ start := {a}, stop := {b} : {m.group(3)} }}{m.group(4)}id := {idv}"
        new = INFO.sub(shift, src)
        bad = []
        for name, rhs in ((m.group(1), m.group(2)) for m in DEF.finditer(new)):
            p = [x for x in plan if x[4] == name]
            if p and rhs != p[0][5][2]: bad.append(name)
        # every FuncInfo inside a patched function now names a page function: check the whole trees
        for name, rhs in ((m.group(1), m.group(2)) for m in DEF.finditer(new)):
            if name not in [x[4] for x in plan] and any(k in mp for k in
                    ((int(x.group(1)), int(x.group(2)), int(x.group(5))) for x in INFO.finditer(rhs))):
                if not any(rhs == c[2] for c in defs.get(norm(rhs), [])): bad.append(name + "(nested)")
        status = "OK" if not bad and not any("conflict" in r for r in report) else ("MISMATCH " + ",".join(bad))
        print(f"{mod}: {len(plan)}/{len(fs)} matched; {'unmatched ' + ' '.join(report) if report else ''} {status}".rstrip())
        if write and not bad and plan and new != src: open(path, "w").write(new)
main()
