"""Generates JSProofs/ReactMicrotaskComplete.lean (zippy docs/react-proofs.md): `complete_hyp`, the microtask's
`hComplete` (the commit's contract) from `ReactCommitOne.crw_one`, with PRu := loop_hyp's handoff, fpC := the
commit's frame, PC := its post. crw_one's parameters are renamed (the commit's objects identified with the render's
and the microtask's, the rest prefixed `c_`); its premises at the commit's start come from the handoff, RenderDone and
MicroFacts through performWorkOnRoot's locals' frame, the rest from the microtask's start through the handoff's frame."""
import re, sys
sys.path.insert(0, "tools/react_commit")
from compose import binders, _theorem_header
from unify import parse, text, subst as usubst

TOP, TOPT = "JSProofs/ReactMicrotaskPrep.lean", "microtask_render_prep"
CO, COT = "JSProofs/ReactCommitOne.lean", "crw_one"
LH = "JSProofs/ReactMicrotaskLoop.lean"
tb = binders(TOP, TOPT); td = {n: (k, t) for n, k, t in tb}
cb = binders(CO, COT); cd = {n: (k, t) for n, k, t in cb}
lb = binders(LH, "loop_hyp"); ld = {n: (k, t) for n, k, t in lb}
ID = re.compile(r"(?<![A-Za-z0-9_'.])([A-Za-z_][A-Za-z0-9_']*)(?![A-Za-z0-9_'])")
def ws(x): return re.sub(r"\s+", " ", x)
# the handoff, as loop_hyp states it
lt = ws(open(LH).read())
i = lt.index("(fun x (_ : σ) => ∃ eR eE,"); d0 = 0
for j in range(i, len(lt)):
    d0 += {"(": 1, ")": -1}.get(lt[j], 0)
    if d0 == 0: break
HANDOFF = lt[i:j + 1]
# crw_one's names
IDN = {"fo": "fCR", "FR": "R", "R": "p_X", "CR_CM_B_K": "p_Fa", "CR_CM_ME_M_CT_B": "l_X", "CR_CM_MF_XA": "A",
       "CR_CM_RSI": "I", "oG": "oG", "s": "s", "w": "w", "n": "n", "h": "h", "eng": "eng", "σ": "σ", "answer": "answer"}
SUBV = {"t": ".undefined", "c1": ".null", "c2": ".num (F64.fin false 0 (-1074)).neg", "c3": ".num (F64.fin false 0 (-1074))"}
DROP = {"fpA", "bW", "hFA", "hGw", "hcb", "hcp", "hco"}
REN = {}
for n, k, t in cb:
    if n in DROP: continue
    REN[n] = IDN.get(n, "c_" + n)
def ren(t):
    parts = re.split(r'("[^"]*")', t)
    return "".join(x if x.startswith('"') else ID.sub(lambda m: REN.get(m.group(1), m.group(1)), x) for x in parts)
# the conclusion
hc = ws(td["hComplete"][1])
FC_post = ws(_theorem_header(CO, COT))
post = FC_post[FC_post.rindex("fun v w' h' =>"):]
m = re.search(r"∃ w0, (\(fun \(w'? : State\) \(h : σ\) => .*\)) w0 h' ∧ Frame \{\} w0 w'\s*$", post)
PCRW = m.group(1)
k = PCRW.rindex("∧ Frame (") + len("∧ Frame "); d0 = 0
for j in range(k, len(PCRW)):
    d0 += {"(": 1, ")": -1}.get(PCRW[j], 0)
    if d0 == 0: break
FFF = PCRW[k:j + 1]
def full(t): return ren(usubst(t, SUBV))
FC = f"(Logic.Footprint.union {full(FFF)} {{}})"
PCRWr = re.sub(r"(?<![A-Za-z0-9_'.])w(?![A-Za-z0-9_'])", "ws", full(PCRW))
PC = f"(fun (w' : State) (h' : σ) => ∃ ws w0, {PCRWr} w0 h' ∧ Frame {{}} w0 w')"
concl = hc.replace("((j + 2) + 1)", "(n + 13)")
for a, b in [("PRu", HANDOFF), ("fpC", FC), ("kC", "59500"), ("PC", PC), ("kW", "2400")]:
    concl = re.sub(r"(?<![\w'])" + a + r"(?![\w'])", lambda _m: b, concl)
print("concl", len(concl))
open(".lake/scratch/complete_concl.txt", "w").write(concl)
