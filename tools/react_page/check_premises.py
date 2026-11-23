"""Checks a theorem's premises against a real heap (zippy docs/react-proofs.md: the start-heap premise check).

The theorem (default `ReactMicrotaskAll.microtask_all`) is about `callImpl eng (.obj c) .undefined #[]` from a state
`s`; Zippy's Lean engine dumps the state each job is called from (`ZIPPY_DUMP_JOBS=DIR`, `ZippyHost/StateDump.lean`).
Each premise is parsed (the term shapes the React proofs use) and evaluated on that state. Equations are matched,
so a premise like `bG[JSStr.ofString "k"]? = some bd` *binds* `bd` to what the heap holds; the premises are
iterated to a fixed point from `s` and `c`. Every premise ends TRUE, FALSE (a false premise: the theorem says
nothing about this page) or UNCHECKED with the reason (contracts `∀ ...`, the engine's built-in table, footprint
side conditions, shapes not handled, variables nothing binds).
Usage: python3 tools/react_page/check_premises.py DUMP.json [--thm FILE:NAME] [-v]"""
import json, re, sys, os
from fractions import Fraction
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "react_commit"))
from compose import binders

class Unbound(Exception): pass
class Unknown(Exception): pass

# ---------------------------------------------------------------- terms
TOK = re.compile(r'\s*(?:(?P<str>"(?:[^"\\]|\\.)*")|(?P<num>\d+)|(?P<sym>≠|≤|≥|∧|∨|∉|∈|→|↔|¬|:=|[()\[\]⟨⟩,=<>!?+*-])|(?P<id>\.?[A-Za-z_$][\w$\'!?]*(?:\.[A-Za-z_$\d][\w$\'!?]*)*))')
def lex(t):
    out, i = [], 0
    while i < len(t):
        m = TOK.match(t, i)
        if not m or m.end() == i:
            if t[i:].strip() == "": break
            raise Unknown("lex " + t[i:i + 20])
        attached = m.start(m.lastgroup) == i  # no whitespace before the token
        kind = m.lastgroup; v = m.group(kind)
        out.append((kind, v, attached)); i = m.end()
    return out

class P:
    def __init__(s, toks): s.t, s.i = toks, 0
    def peek(s, k=0): return s.t[s.i + k] if s.i + k < len(s.t) else (None, None, False)
    def eat(s, v=None):
        tok = s.peek()
        if v is not None and tok[1] != v: raise Unknown(f"expected {v} got {tok[1]}")
        s.i += 1; return tok
    def expr(s):
        if s.peek()[1] == "∀": raise Unknown("forall")
        if s.peek()[0] == "id" and s.peek()[1] == "∃": pass
        e = s.rel()
        while s.peek()[1] in ("∧",):
            s.eat(); e = ("and", e, s.rel())
        return e
    def rel(s):
        if s.peek()[1] == "¬": s.eat(); return ("not", s.rel())
        e = s.add()
        op = s.peek()[1]
        if op in ("=", "≠", "<", "≤", "∉", "∈"):
            s.eat(); return (op, e, s.add())
        return e
    def add(s):
        e = s.app()
        while s.peek()[1] == "+":
            s.eat(); e = ("+", e, s.app())
        return e
    def app(s):
        f = s.post()
        args = []
        while True:
            k, v, att = s.peek()
            if k in ("str", "num") or (k == "id" and v not in ("∃",)) or v in ("(", "⟨"):
                if k == "id" and v.startswith(".") and att: break
                args.append(s.post())
            else: break
        return ("app", f, args) if args else f
    def post(s):
        e = s.atom()
        while True:
            k, v, att = s.peek()
            if k == "id" and v.startswith(".") and att:
                s.eat()
                for f in v[1:].split("."): e = ("proj", e, f)
            elif v == "[" and att:
                s.eat(); idx = s.expr(); s.eat("]")
                if s.peek()[1] == "?": s.eat(); e = ("idx?", e, idx)
                elif s.peek()[1] == "!": s.eat(); e = ("idx!", e, idx)
                else: raise Unknown("index")
            else: return e
    def atom(s):
        k, v, att = s.eat()
        if k == "str": return ("lit", json.loads(v))
        if k == "num": return ("lit", int(v))
        if v == "(":
            if s.peek()[1] == "-":
                s.eat(); n = s.eat()[1]; s.eat(")"); return ("lit", -int(n))
            e = s.expr()
            if s.peek()[1] == ",":
                items = [e]
                while s.peek()[1] == ",": s.eat(); items.append(s.expr())
                s.eat(")"); return ("tuple", items)
            s.eat(")"); return e
        if v == "⟨": raise Unknown("anonymous constructor")
        if k == "id": return ("id", v)
        raise Unknown("atom " + str(v))

def parse(t):
    t = re.sub(r"\s+", " ", t).strip()
    m = re.match(r"∃ ([\w' ]+?)( : [^,]+)?, (.*)$", t)
    if m: return ("exists", m.group(1).split(), parse(m.group(3)))
    p = P(lex(t)); e = p.expr()
    if p.i != len(p.t): raise Unknown("trailing " + str(p.peek()[1]))
    return e

# ---------------------------------------------------------------- the heap
class Heap:
    def __init__(h, d): h.d = d
    def obj(h, o):
        if not (0 <= o < len(h.d["heap"])): raise Unknown(f"object {o} out of range")
        return h.d["heap"][o]
    def env(h, e):
        if not (0 <= e < len(h.d["envs"])): raise Unknown(f"env {e} out of range")
        return h.d["envs"][e]

def jval(v):
    t = v["t"]
    if t in ("undefined", "null"): return (t,)
    if t == "bool": return ("bool", v["b"])
    if t == "num": return ("num", jf64(v["n"]))
    if t == "str": return ("str", v["s"])
    if t == "obj": return ("obj", v["o"])
    if t == "sym": return ("sym", v["id"])
    return ("other", t)
def jf64(n):
    if n["t"] == "fin": return ("fin", n["neg"], int(n["m"]), n["e"])
    if n["t"] == "inf": return ("inf", n["neg"])
    return ("nan",)
def jprop(p):
    if p is None: return ("none",)
    if p["t"] == "data": return ("some", ("data", jval(p["v"]), p["w"], p["e"], p["c"]))
    return ("some", ("acc",))
def jbinding(b): return ("binding", None if b["v"] is None else jval(b["v"]), b["m"], b["s"], b["d"])
def jkind(k):
    t = k["t"]
    if t == "func": return ("kfunc", ("fd", k["d"]))
    if t == "builtin": return ("kbuiltin", ("bd", k))
    return ("k" + t,)
def jrec(b): return ("rec", tuple(sorted((k, jbinding(x)) for k, x in b.items())))

def f64val(f):
    if f[0] != "fin": raise Unknown("non-finite")
    v = Fraction(f[2]) * (Fraction(2) ** f[3]) if f[3] >= 0 else Fraction(f[2], 2 ** (-f[3]))
    return -v if f[1] else v
def f64eq(a, b):
    if a[0] == "fin" and b[0] == "fin": return f64val(a) == f64val(b) and (f64val(a) != 0 or a[1] == b[1])
    return a == b
def to_int32(f):
    if f[0] != "fin": return 0
    v = f64val(f); n = int(v)  # truncation toward zero
    n %= 2 ** 32
    return n - 2 ** 32 if n >= 2 ** 31 else n
def from_int(n):
    if n == 0: return ("fin", False, 0, -1074)
    neg = n < 0; m = abs(n); e = 0
    while m < 2 ** 52: m *= 2; e -= 1
    return ("fin", neg, m, e)

def eq(a, b):
    if isinstance(a, tuple) and isinstance(b, tuple) and a and b and a[0] in ("fin", "nan", "inf") and b[0] in ("fin", "nan", "inf"):
        return f64eq(a, b)
    if isinstance(a, tuple) and isinstance(b, tuple) and len(a) == len(b):
        return all(eq(x, y) for x, y in zip(a, b))
    return a == b

# ---------------------------------------------------------------- evaluation
GENCODE = {}
INFO = re.compile(r"span := \{ start := (\d+), stop := (\d+) : (?:ES\.)?Span \}(?:(?!span := ).)*?id := (\d+)")
def gencode(name):
    if name in GENCODE: return GENCODE[name]
    mod, fn = name.split(".", 1)
    path = f"JSProofs/{mod}.lean"
    if not os.path.exists(path): raise Unknown("no " + path)
    m = re.search(r"^def " + re.escape(fn) + r" : ES\.Func := (.*)$", open(path).read(), re.M)
    if not m: raise Unknown("no def " + name)
    ms = list(INFO.finditer(m.group(1)))
    GENCODE[name] = ("code", int(ms[-1].group(1)), int(ms[-1].group(2)), int(ms[-1].group(3)))
    return GENCODE[name]

CTORS0 = {"EMPTYREC": ("rec", ()), ".null": ("null",), ".undefined": ("undefined",), "none": ("none",), "true": True, "false": False,
          ".strict": ("tm", "strict"), ".lexical": ("tm", "lexical"), ".global": ("tm", "global"),
          ".ordinary": ("kordinary",), ".array": ("karray",)}

class Ev:
    def __init__(s, heap, env, vars_):
        s.h, s.env, s.vars = heap, env, vars_
    def var(s, n):
        if n in s.env: return s.env[n]
        if n in s.vars: raise Unbound(n)
        raise Unknown("name " + n)
    def ev(s, e):
        t = e[0]
        if t == "lit": return e[1]
        if t == "tuple": return ("tuple",) + tuple(s.ev(x) for x in e[1])
        if t == "id":
            n = e[1]
            if n in CTORS0: return CTORS0[n]
            if n == "s": return ("state",)
            head, *rest = n.split(".")
            if not rest: return s.var(n)
            if n in s.env: return s.env[n]
            if len(rest) >= 1 and f"{head}.{rest[0]}" in s.env and head not in s.env:
                v = s.env[f"{head}.{rest[0]}"]
                for f in rest[1:]: v = s.proj(v, f)
                return v
            if head in s.env or head in s.vars or head == "s":
                v = s.ev(("id", head))
                for f in rest: v = s.proj(v, f)
                return v
            if n.endswith("_func") and "Gen." in n: return gencode(n)
            raise Unknown("const " + n)
        if t == "proj":
            if e[1][0] == "id" and e[1][1] in s.vars and e[1][1] not in s.env and f"{e[1][1]}.{e[2]}" in s.env:
                return s.env[f"{e[1][1]}.{e[2]}"]
            if e[1][0] == "proj" and e[1][1][0] == "id":  # X.2.1 of an unbound tuple
                key = f"{e[1][1][1]}.{e[1][2]}.{e[2]}"
                if key in s.env: return s.env[key]
            return s.proj(s.ev(e[1]), e[2])
        if t == "idx?":
            r = s.ev(e[1]); k = s.ev(e[2])
            if r[0] == "rec":
                for kk, b in r[1]:
                    if kk == k: return ("some", b)
                return ("none",)
            if r[0] == "intrinsics":
                return ("some", r[1][k]) if k in r[1] else ("none",)
            raise Unknown("index? on " + r[0])
        if t == "idx!":
            r = s.ev(e[1]); k = s.ev(e[2])
            if r == ("realms",): return ("realm", s.h.d["realms"][k])
            raise Unknown("index!")
        if t == "app": return s.app(e[1], e[2])
        if t == "+": return s.ev(e[1]) + s.ev(e[2])
        raise Unknown("eval " + t)
    def proj(s, v, f):
        if v == ("state",):
            if f in ("heap", "envs"): return ("arr", f)
            if f == "fuel": return s.h.d["fuel"]
            if f == "realms": return ("realms",)
        if v[0] == "arr" and f == "size": return len(s.h.d[v[1]])
        if v[0] == "objref":
            o = s.h.obj(v[1])
            if f == "kind": return jkind(o["kind"])
            if f == "props": return ("props", o)
            if f == "proto": return jval(o["proto"])
        if v[0] == "props" and f == "get?": return ("getfn", v[1])
        if v[0] == "binding":
            if f == "value": return ("none",) if v[1] is None else ("some", v[1])
            if f == "mutable": return v[2]
        if v[0] in ("some", "none") and f == "isSome": return v[0] == "some"
        if v[0] == "fd":
            d = v[1]
            if f == "code": return ("code", d["span"][0], d["span"][1], d["id"])
            if f == "env": return d["env"]
            if f == "isClassCtor": return d["classCtor"]
            if f == "thisMode": return ("tm", d["thisMode"])
            if f == "realm": return d["realm"]
        if v[0] == "bd":
            if f == "realm": return v[1]["realm"]
            if f == "id": return v[1]["id"]
        if v[0] == "kordinary" or v[0].startswith("k"):
            if f == "isPlain": return v[0] in ("kordinary", "kfunc", "kinternal")
            if f == "isReadPlain": return v[0] in ("kordinary", "kfunc", "kinternal", "karray", "kbuiltin")
        if v[0] == "realm":
            r = v[1]
            if f == "intrinsics": return ("intrinsics", r["intrinsics"])
            if f == "objectProto": return r["intrinsics"].get("%Object.prototype%")
            if f == "arrayProto": return r["intrinsics"].get("%Array.prototype%")
        if v[0] == "fin" and f == "neg": return ("fin", not v[1], v[2], v[3])
        if v[0] == "tuple" and f in ("1", "2"): return v[1] if f == "1" else (v[2] if len(v) == 3 else ("tuple",) + v[2:])
        raise Unknown(f"projection .{f} of {v[0]}")
    def app(s, f, args):
        if f[0] == "id":
            n = f[1]
            if n == "s.objEntry": return ("objref", s.ev(args[0]))
            if n == "s.envEntry": return ("envref", s.ev(args[0]))
            if n == "some": return ("some", s.ev(args[0]))
            if n == "JSStr.ofString": return s.ev(args[0])
            if n == "F64.fin": return ("fin", s.ev(args[0]), s.ev(args[1]), s.ev(args[2]))
            if n in (".obj", ".num", ".bool", ".str", ".sym"): return (n[1:], s.ev(args[0]))
            if n == ".data": return ("data",) + tuple(s.ev(a) for a in args)
            if n == ".func": return ("kfunc", s.ev(args[0]))
            if n == ".builtin": return ("kbuiltin", s.ev(args[0]))
            if n == "Scope.declLike?":
                r = s.ev(args[0])
                if r[0] != "envref": raise Unknown("declLike? of " + r[0])
                en = s.h.env(r[1])
                if en["t"] in ("decl", "func"):
                    return ("some", ("tuple", jrec(en["b"]), ("none",) if en["outer"] is None else ("some", en["outer"])))
                return ("none",)
            if n == "numberBinOp":
                op = args[0][1]; a, b = s.ev(args[1]), s.ev(args[2])
                if op == ".bitAnd": return from_int(to_int32(a) & to_int32(b))
                if op == ".bitOr": return from_int(to_int32(a) | to_int32(b))
                raise Unknown("numberBinOp " + op)
            if n == "isStrictlyEqual":
                a, b = s.ev(args[0]), s.ev(args[1])
                if a[0] == "num" and b[0] == "num": return f64eq(a[1], b[1]) and a[1][0] == "fin"
                return eq(a, b)
        if f[0] == "proj" and f[2] in ("objEntry", "envEntry") and s.ev(f[1]) == ("state",):
            return ("objref" if f[2] == "objEntry" else "envref", s.ev(args[0]))
        if f[0] == "proj" and f[2] == "get?":
            props = s.ev(f[1])
            if props[0] != "props": raise Unknown("get? on " + props[0])
            k = s.ev(args[0])
            if k[0] != "str": raise Unknown("key " + k[0])
            for kk, p in props[1]["props"]:
                if kk["t"] == "str" and kk["s"] == k[1]: return jprop(p)
            return ("none",)
        if f[0] == "proj":
            fn = s.ev(f)
            if isinstance(fn, tuple) and fn[0] == "getfn":
                k = s.ev(args[0])
                for kk, p in fn[1]["props"]:
                    if kk["t"] == "str" and kk["s"] == k[1]: return jprop(p)
                return ("none",)
        raise Unknown("apply " + (f[1] if f[0] == "id" else f[0]))

    # matching: a pattern against a value, binding unbound variables
    def match(s, p, v, new):
        if p[0] == "id" and "." in p[1]:
            head, *rest = p[1].split(".")
            if head in s.vars and head not in s.env:
                q = ("id", head)
                for f in rest: q = ("proj", q, f)
                p = q
        t = p[0]
        if t == "id" and p[1] in s.vars and p[1] not in s.env and p[1] not in new:
            new[p[1]] = v; return True
        if t == "proj" and p[1][0] == "id" and p[1][1] in s.vars and p[1][1] not in s.env:
            key = f"{p[1][1]}.{p[2]}"
            if key in s.env or key in new: return eq((s.env.get(key) if key in s.env else new[key]), v)
            new[key] = v; return True
        if t == "proj" and p[1][0] == "proj" and p[1][1][0] == "id" and p[1][1][1] in s.vars and p[1][1][1] not in s.env:
            key = f"{p[1][1][1]}.{p[1][2]}.{p[2]}"
            if key in s.env or key in new: return eq((s.env.get(key) if key in s.env else new[key]), v)
            new[key] = v; return True
        if t == "app" and p[1][0] == "id":
            n, args = p[1][1], p[2]
            if n == "some":
                return v[0] == "some" and s.match(args[0], v[1], new)
            if n in (".obj", ".num", ".bool", ".str", ".sym"):
                return v[0] == n[1:] and s.match(args[0], v[1], new)
            if n == ".data":
                return v[0] == "data" and all(s.match(a, x, new) for a, x in zip(args, v[1:]))
            if n == ".func": return v[0] == "kfunc" and s.match(args[0], v[1], new)
            if n == ".builtin": return v[0] == "kbuiltin" and s.match(args[0], v[1], new)
        if t == "tuple":
            return v[0] == "tuple" and len(v) == len(p[1]) + 1 and all(s.match(a, x, new) for a, x in zip(p[1], v[1:]))
        # otherwise the pattern must evaluate (with what this match bound so far)
        old = s.env; s.env = {**old, **new}
        try: return eq(s.ev(p), v)
        finally: s.env = old

    def check(s, e):
        """True/False, binding variables in self.env; raises Unbound/Unknown."""
        t = e[0]
        if t == "and":
            return s.check(e[1]) and s.check(e[2])
        if t == "not": return not s.check(e[1])
        if t == "=":
            for a, b in ((e[1], e[2]), (e[2], e[1])):
                try: v = s.ev(a)
                except Unbound: continue
                new = {}
                ok = s.match(b, v, new)
                if ok: s.env.update(new)
                return ok
            raise Unbound("both sides")
        if t == "≠": return not eq(s.ev(e[1]), s.ev(e[2]))
        if t == "<": return s.ev(e[1]) < s.ev(e[2])
        if t == "≤": return s.ev(e[1]) <= s.ev(e[2])
        if t == "exists":
            names = e[1]
            saved = dict(s.env); s.vars = s.vars | set(names)
            try:
                r = s.check(e[2])
            finally:
                for n in names: s.env.pop(n, None)
            return r
        if t in ("id", "proj", "app"):
            v = s.ev(e)
            if isinstance(v, bool): return v
        raise Unknown("premise shape " + t)

def main():
    args = sys.argv[1:]
    dump = args.pop(0)
    thm = "JSProofs/ReactMicrotaskAll.lean:microtask_all"
    if "--thm" in args: thm = args[args.index("--thm") + 1]
    verbose = "-v" in args
    path, name = thm.split(":")
    bs = binders(path, name)
    d = json.load(open(dump))
    h = Heap(d)
    vars_ = {n for n, k, t in bs if k == "{"}
    env = {}
    call = d["call"]["f"]
    if call["t"] != "obj": sys.exit("the job is not a function object")
    env["c"] = call["o"]
    ev = Ev(h, env, vars_)
    prem = [(n, t) for n, k, t in bs if k == "("]
    status = {}
    parsed = {}
    for n, t in prem:
        tt = re.sub(r"\s+", " ", t).strip()
        if tt.startswith("∀"): status[n] = ("UNCHECKED", "contract (∀)"); continue
        if "eng.builtins" in tt: status[n] = ("UNCHECKED", "engine built-in table"); continue
        if "Footprint" in tt or "⟨" in tt or ".binds" in tt or ".props.all" in tt: status[n] = ("UNCHECKED", "footprint side condition"); continue
        m = re.fullmatch(r"ReactSchedTask\.Callback s (\w+) (\w+) ([\w.]+)", tt)
        if m:  # its definition (JSProofs/ReactSchedTask.lean), the closure's record empty
            c_, e_, g_ = m.groups()
            tt = (f"∃ dc, {c_} < s.heap.size ∧ (s.objEntry {c_}).kind = .func dc ∧ dc.code = SIRGen.fn5_func ∧ "
                  f"dc.thisMode = .strict ∧ dc.isClassCtor = false ∧ dc.env = {e_} ∧ {e_} < s.envs.size ∧ "
                  f"Scope.declLike? (s.envEntry {e_}) = some (EMPTYREC, some {g_})")
        try: parsed[n] = parse(tt)
        except Unknown as x: status[n] = ("UNCHECKED", "parse: " + str(x))
    pending = dict(parsed)
    progress = True
    while progress:
        progress = False
        for n in list(pending):
            try:
                r = ev.check(pending[n])
                status[n] = ("TRUE",) if r else ("FALSE",)
                del pending[n]; progress = True
            except Unbound: pass
            except Unknown as x:
                status[n] = ("UNCHECKED", str(x)); del pending[n]; progress = True
            except (KeyError, IndexError, TypeError) as x:
                status[n] = ("UNCHECKED", f"error {type(x).__name__}: {x}"); del pending[n]; progress = True
    for n in pending: status[n] = ("UNCHECKED", "unbound variables")
    import collections
    c = collections.Counter(v[0] for v in status.values())
    print(f"premises {len(prem)}: " + ", ".join(f"{k} {c[k]}" for k in ("TRUE", "FALSE", "UNCHECKED")))
    reasons = collections.Counter(v[1].split(":")[0] if len(v) > 1 else "" for v in status.values() if v[0] == "UNCHECKED")
    print("unchecked by reason:", dict(reasons.most_common(12)))
    texts = dict(prem)
    for n, v in status.items():
        if v[0] == "FALSE": print("FALSE", n, ":", re.sub(r"\s+", " ", texts[n])[:220])
    if verbose:
        for n, v in status.items():
            if v[0] == "UNCHECKED": print("UNCHECKED", n, v[1], ":", re.sub(r"\s+", " ", texts[n])[:160])
    print("bound variables:", len([k for k in env if k in vars_]), "of", len(vars_))

if __name__ == "__main__":
    main()
