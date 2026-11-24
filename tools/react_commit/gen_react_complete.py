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
# ---- premises ----
def norm(x):
    x = ws(x)
    while True:
        y = re.sub(r"\((\w+)\)", r"\1", x)
        if y == x: return x
        x = y
IDN.update({"CR_CM_ME_M_CT_BT_CH_U_OP": "l_OP"})
REN.update({k: v for k, v in IDN.items() if k in REN})
NP, F1, T1 = "CR_CM_ME_M_CT_BT_NP", "CR_CM_ME_M_CT_BT_CH_U_f1", "CR_CM_ME_M_CT_BT_CH_U_t1"
HS = {}
for m in re.finditer(r'\(∃ fa fb, \(x\.objEntry (\w+)\)\.props\.get\? \(\.str "(\w+)"\) = some \(\.data ', HANDOFF):
    j = m.end(); d0 = 1
    while d0: d0 += {"(": 1, ")": -1}.get(HANDOFF[j], 0); j += 1
    HS[(m.group(1), m.group(2))] = "some (.data " + HANDOFF[m.end():j - 1] + ")"
BSRC = {"executionContext", "workInProgressRoot", "pendingEffectsLanes", "concurrentlyUpdatedLanes", "isFlushingWork",
        "mightHavePendingSyncWork", "didScheduleMicrotask", "workInProgressRootRenderLanes"}
MFK = {("R", "callbackNode"), ("R", "callbackPriority"), ("A", "1")}
cimp = {n for n, k, t in cb if k == "{"}
lfree = {n for n, k, t in lb if k == "{"}
sup, rest_s, quant, kept = [], [], [], []
sub, eqs = {}, []
free = {REN[v] for v in cimp if v in REN} - set(IDN.values())
def walk(a, b, n):
    if isinstance(a, list) and len(a) == 1: a = a[0]
    if isinstance(b, list) and len(b) == 1: b = b[0]
    if isinstance(a, str) and a in free and text(b) in ("fa", "fb"): return
    if isinstance(a, str) and a in free:
        if a in sub and sub[a] != text(b): eqs.append((text(b), sub[a], n))
        else: sub[a] = text(b)
        return
    if isinstance(b, str) and b in lfree and not b.startswith("fa") and b not in ("fa", "fb"):
        if b in sub and sub[b] != text(a): eqs.append((sub[b], text(a), n))
        else: sub[b] = text(a)
        return
    if isinstance(a, list) and isinstance(b, list) and len(a) == len(b) and \
            (not isinstance(a[0], str) or not isinstance(b[0], str) or a[0] == b[0]):
        for x, y in zip(a, b): walk(x, y, n)
        return
    if text(a) != text(b): eqs.append((text(b), text(a), n))
for n, k, t in cb:
    if k != "(" or n in DROP: continue
    tt = norm(ren(usubst(t, SUBV)))
    if tt.startswith("∀"): quant.append(n); continue
    if re.search(r"(?<![\w'])c_" + NP + r"(?![\w'])", tt) or re.search(r"(?<![\w'])c_" + F1 + r"(?![\w'])", tt):
        sup.append(n); continue
    atw = re.search(r"(?<![\w'.])w\.", tt) or "bW[" in tt
    if not atw: kept.append(n); continue
    m = re.match(r'\(w\.objEntry (\w+)\)\.props\.get\? \(\.str \(?(?:JSStr\.ofString )?"(\w+)"\)?\) = (.*)$', tt)
    if m and (m.group(1), m.group(2)) in HS:
        sup.append(n); walk(parse(m.group(3)), parse(HS[(m.group(1), m.group(2))]), n); continue
    if m and (m.group(1), m.group(2)) in MFK: sup.append(n); continue
    b = re.match(r'bW\[JSStr\.ofString "([\w$]+)"\]', tt)
    if b and b.group(1) in BSRC: sup.append(n); continue
    if re.match(r"\d+ ≤ w\.fuel$", tt): sup.append(n); continue
    rest_s.append(n)
# binding-value premises on supplied bindings' variables
supvars = {v for n in sup for v in ID.findall(ren(cd[n][1])) if v in free}
for n, k, t in cb:
    mm = re.match(r"(\w+)\.(value|mutable)", ren(t).strip())
    if k == "(" and n in kept and mm and mm.group(1) in supvars: kept.remove(n); sup.append(n)
sub = {k: v for k, v in sub.items() if k != v}
for _v in ("c_CR_ec", "c_CR_CM_ec"):
    if _v in free: sub[_v] = "v_ec"
_np = re.search(r"ReactNewProps\.NewProps x Cn F \w+ (\(JSStr\.ofString \"Count: \" \+\+ numberToJSStr \w+ \+\+ JSStr\.ofString \"\"\))", HANDOFF)
sub["c_" + T1] = _np.group(1)[1:-1]
print("supplied", len(sup), "at s (restated)", len(rest_s), "kept", len(kept), "quantified", len(quant), "unified", len(sub))
for e in eqs: print("EQ", e)
print("REST_S", rest_s)
# ---- the statement ----
def S(t): return usubst(full(t), sub)
FALLM = re.search(r"Frame (\(.*?\)) s x ∧ ∃ Cn F,", HANDOFF).group(1)
FPA = f"({FALLM}.union (ReactPerformWork.fpOwn eW))"
ebinds, ibinds = [], []
for n, k, t in cb:
    if n in DROP or n in IDN or n in SUBV or REN.get(n) in sub: continue
    if k == "{":
        ibinds.append((REN[n], f"{{{REN[n]} : {S(t)}}}")); continue
    if n in kept: ebinds.append(f"({REN[n]} : {S(t)})")
    elif n in rest_s:
        ebinds.append(f"({REN[n]} : {re.sub(r'(?<![A-Za-z0-9_.])w(?![A-Za-z0-9_])', 's', S(t))})")
    elif n in quant:
        body = S(t).strip()
        body = re.sub(r"^∀ s3, Frame fpA s s3 →", f"∀ eR eE eW, ∀ s3, Frame {FPA} s s3 →", body)
        ebinds.append(f"({REN[n]} : {body})")
concl2 = usubst(concl, sub)
extra = ["(hcdenv : c_d.env = d.env)"] + [f"(eq_{i} : {a} = {b})" for i, (a, b, nn) in enumerate(eqs)]
text_all = " ".join(ebinds) + " " + concl2 + " " + " ".join(extra)
used = set(ID.findall(text_all))
for _ in range(3):
    used |= set(ID.findall(" ".join(b for nm, b in ibinds if nm in used)))
ib = [b for nm, b in ibinds if nm in used]
tbn = [f"{{{n} : {usubst(t, sub)}}}" for n, k, t in tb if k == "{" and n in used and n not in sub]
have = {n for n, k, t in tb if k == "{"} | {nm for nm, b in ibinds}
lbn = [f"{{{n} : {usubst(t, sub)}}}" for n, k, t in lb if k == "{" and n in used and n not in sub and n not in have]
stmt = ("theorem complete_hyp {n : Nat} " + " ".join(tbn) + "\n    " + " ".join(lbn) + "\n    " + " ".join(ib) + "\n    " +
        "\n    ".join(ebinds) + "\n    " + " ".join(extra) + " :\n    " + concl2 + " := by\n  sorry\n")
OPENS = "\n".join(l for l in open("JSProofs/ReactWorkLoop.lean").read().split("\n") if l.startswith("open "))
COPENS = "\n".join(l for l in open(CO).read().split("\n") if l.startswith("open ") and "ES ES.M" not in l)
out = f'''import JSProofs.ReactMicrotaskLoop
import JSProofs.ReactCommitOne

/-!
# The click's commit as the microtask's `hComplete` (zippy docs/react-proofs.md)

Generated by `tools/react_commit/gen_react_complete.py`.
-/

{OPENS}
{COPENS}

namespace ReactMicrotaskComplete

section
variable {{eng : Engine}} {{σ : Type}} {{answer : HostAnswer σ}} {{HI : σ → Prop}}

set_option maxRecDepth 40000 in
set_option maxHeartbeats 8000000 in
{stmt}
end

end ReactMicrotaskComplete
'''
open("JSProofs/ReactMicrotaskComplete.lean", "w").write(out)
print("binders: tb", len(tbn), "lb", len(lbn), "crw implicit", len(ib), "premises", len(ebinds))
# ---- the proof ----
# the handoff's conjuncts after `∃ Cn F,`
hb = HANDOFF[HANDOFF.index("∃ Cn F, ") + len("∃ Cn F, "):-1]
parts, d0, cur = [], 0, ""
i = 0
while i < len(hb):
    c = hb[i]
    d0 += {"(": 1, ")": -1, "⟨": 1, "⟩": -1}.get(c, 0)
    if d0 == 0 and hb.startswith(" ∧ ", i):
        parts.append(cur); cur = ""; i += 3; continue
    cur += c; i += 1
parts.append(cur)
HN = [f"H{i}" for i in range(len(parts))]
PIDX = {}
for i, p in enumerate(parts):
    m = re.match(r'\(∃ fa fb, \(x\.objEntry (\w+)\)\.props\.get\? \(\.str "(\w+)"\)', p)
    if m: PIDX[(m.group(1), m.group(2))] = i
    elif p.startswith("ReactNewProps.NewProps"): PIDX["NP"] = i
    elif p.startswith("ReactRenderSync.EndBinds"): PIDX["EB"] = i
    elif p.startswith("ReactFinishQueueing.QueuesDone"): PIDX["QD"] = i
    elif "pendingEffectsLanes" in p: PIDX["PE"] = i
    elif p.startswith("s.heap.size ≤ Cn"): PIDX["CN"] = i
    elif p.startswith("ReactMicrotaskClick.MicroFacts"): PIDX["MF"] = i
    elif "workInProgressRootRecoverableErrors" in p: PIDX["RV"] = i
print("handoff parts", len(parts), sorted(k for k in PIDX if isinstance(k, str)))
cwd = {n: t for n, k, t in cb}
# bounds at the start (premise names) for objects
allp = {}
for b in ebinds + ["(hRo : R < s.heap.size)", "(hAo : A < s.heap.size)", "(hH : p_H < s.heap.size)", "(hf0o : c_CR_CM_ME_M_CT_BT_CH_U_f0 < s.heap.size)"]:
    mm = re.match(r"\((\w+) : \(?(\w+)\)? < \(?s\)?\.heap\.size\)$", ws(b))
    if mm: allp.setdefault(mm.group(2), mm.group(1))
def B(o): return f"(Nat.lt_of_lt_of_le {allp[o]} hFA2.heap_le)"
pre, args = [], []
for (o, k), i in [(k, v) for k, v in PIDX.items() if isinstance(k, tuple)]:
    pre.append(f"obtain ⟨_, _, P{i}⟩ := H{i}")
pre.append(f"obtain ⟨⟨bmF, hbmF, bdF, hbdF, hbdFv⟩, ⟨⟨_, _, _, hA1⟩, ⟨_, _, _, hCP⟩, ⟨_, _, _, hCN⟩⟩, ⟨bmG, hbmG, ⟨_, gMS, gMSm, gMSv⟩, ⟨_, gDS, gDSm, gDSv⟩⟩⟩ := H{PIDX['MF']}")
pre.append(f"obtain ⟨bmE, hbmE, ⟨_, gEC, gECv, gECm⟩, ⟨_, gWR, gWRv⟩, ⟨_, gRL, gRLv⟩⟩ := H{PIDX['EB']}")
pre.append(f"obtain ⟨bmQ, oQ, hbmQ, _, gCU, gCUv⟩ := H{PIDX['QD']}")
pre.append(f"obtain ⟨bmP, hbmP, _, gPE, gPEm, gPEv⟩ := H{PIDX['PE']}")
pre.append(f"obtain ⟨bmV, hbmV, ⟨_, r1, r1v⟩, ⟨_, r4, r4v⟩, ⟨_, r5, r5v⟩, ⟨_, r6, r6v⟩⟩ := H{PIDX['RV']}")
for v in ["bmF", "bmG", "bmE", "bmP", "bmV"]:
    pre.append(f"have e_{v} : bm = {v} := by rw [hRD.record] at h{v}; cases h{v}; rfl")
    pre.append(f"subst e_{v}")
pre.append("have e_bmQ : bm = bmQ := by rw [hRD.record] at hbmQ; cases hbmQ; rfl")
pre.append("subst e_bmQ")
for xi, (r, rv) in [("x1", ("r1", "r1v")), ("x4", ("r4", "r4v")), ("x5", ("r5", "r5v")), ("x6", ("r6", "r6v"))]:
    fld = {"x1": "v1", "x4": "v4", "x5": "v5", "x6": "v6"}[xi]
    pre.append(f"obtain ⟨_, g{xi}, g{xi}v⟩ := hRD.{fld}")
    pre.append(f"rw [{r}] at g{xi}; cases g{xi}")
    pre.append(f"rw [{rv}] at g{xi}v; cases g{xi}v")
pre.append("obtain ⟨_, _, _, _, _, hRC⟩ := hRD.root")
pre.append("rw [props_frame hFA2 hRo (by simp (config := { decide := true }) [@@ALLDEFS@@, dr_RI, dr_CF, dr_CS, dr_Cu, @@DLN@@]), hRcur] at hRC; cases hRC")
pre.append("obtain ⟨_, _, _, _, _, hCA⟩ := hRD.cur")
pre.append("rw [props_frame hFA2 hH (by simp (config := { decide := true }) [@@ALLDEFS@@, @@DLN@@]), hHa] at hCA; cases hCA")
pre.append(f"have hNPw := ReactNewProps.NewProps.frame hOwn H{PIDX['NP']} (fun k hk => by simp [ReactPerformWork.fpOwn] at hk)")
PRE = "\n  ".join(pre)
# supplied premises' proofs
BIND = {"executionContext": {"get": "gEC", "value": "gECv", "mutable": "gECm"}, "workInProgressRoot": {"get": "gWR", "value": "gWRv"},
        "workInProgressRootRenderLanes": {"get": "gRL", "value": "gRLv"},
        "pendingEffectsLanes": {"get": "gPE", "mutable": "gPEm", "value": "gPEv"},
        "concurrentlyUpdatedLanes": {"get": "gCU", "value": "gCUv"}, "isFlushingWork": {"get": "hbdF", "value": "hbdFv"},
        "mightHavePendingSyncWork": {"get": "gMS", "mutable": "gMSm", "value": "gMSv"},
        "didScheduleMicrotask": {"get": "gDS", "mutable": "gDSm", "value": "gDSv"}}
bvar = {}
for n in sup:
    t = norm(ren(usubst(cwd[n], SUBV)))
    mm = re.match(r'bW\[JSStr\.ofString "([\w$]+)"\]\? = some (\w+)$', t)
    if mm: bvar[mm.group(2)] = mm.group(1); args.append(f"({n} := {BIND[mm.group(1)]['get']})")
NPF = {"hNPlt": "hNPw.1", "hNPk": "(by rw [hNPw.2.1]; rfl)", "hNPp": "hNPw.2.2.1", "hNPkeys": "hNPw.2.2.2.1",
       "hNPon": "hNPw.2.2.2.2.1", "hNPch": "hNPw.2.2.2.2.2.1", "hNPh": "hNPw.2.2.2.2.2.2.1"}
for n in sup:
    t = norm(ren(usubst(cwd[n], SUBV)))
    if t.startswith("bW["): continue
    if re.match(r"\d+ ≤ w\.fuel$", t): args.append(f"({n} := by omega)"); continue
    mm = re.match(r"(\w+)\.(value|mutable)", t)
    if mm and mm.group(1) in bvar:
        f = "mutable" if mm.group(2) == "mutable" else "value"
        src_ = BIND[bvar[mm.group(1)]].get(f, BIND[bvar[mm.group(1)]]["value"])
        args.append(f"({n} := by first | exact {src_} | simpa using {src_} | simp [{src_}])"); continue
    short = n.split("_")[-1]
    if short in NPF and "NP" in n: args.append(f"({n} := {NPF[short]})"); continue
    if re.match(rf"c_{NP} ≠ (\w+)$", t) or re.match(rf"(\w+) ≠ c_{NP}$", t):
        o = re.findall(r"\w+", t.replace(f"c_{NP}", ""))[0]
        nm = f"Nat.ne_of_gt (Nat.lt_of_lt_of_le {allp.get(o, 'MISSING_' + o)} H{PIDX['CN']})"
        args.append(f"({n} := {nm if t.startswith('c_' + NP) else '(' + nm + ').symm'})"); continue
    if f"c_{F1}" in t:
        args.append(f"({n} := Nat.ne_of_gt (Nat.lt_of_lt_of_le hf0o (Nat.le_trans H{PIDX['CN']} (Nat.le_of_lt hNPw.2.2.2.2.2.2.2.2))))"); continue
    mm = re.match(r'\(w\.objEntry (\w+)\)\.props\.get\? \(\.str \(?(?:JSStr\.ofString )?"(\w+)"\)?\) = ', t)
    if mm:
        o, k = mm.group(1), mm.group(2)
        if (o, k) in PIDX: args.append(f"({n} := by rw [hO2 _ {B(o)}]; exact P{PIDX[(o, k)]})"); continue
        if (o, k) in MFK:
            h_ = {"1": "hA1", "callbackPriority": "hCP", "callbackNode": "hCN"}[k]
            args.append(f"({n} := by rw [hO2 _ {B(o)}]; exact {h_})"); continue
    args.append(f"({n} := sorry)"); print("UNSOURCED", n, t[:100])
print("args", len(args))
# ---- the call, side conditions, post ----
ALLDEFS = ("Logic.Footprint.union, ReactMicrotaskClick.fpPerf, ReactSchedTaskRoot.fp, ReactRenderSync.fpPre, "
           "ReactPrepareFresh.fp, ReactCreateWIP.fp, ReactRenderSync.fpOwn, ReactBeginRoot.fp, ReactEarlyBailout.fp, "
           "ReactHostContainer.fp, ReactBailout.fp, fpB, ReactUpdateFunction.fpUF, ReactReconcileImpl.fpI, "
           "ReactBeginButton.fpBB, ReactCompleteUnit.fpU, ReactCompleteButton.fpCW, ReactCompleteButton.fpCC, "
           "ReactCompleteRoot.fpRC, ReactRenderSync.fpEnd, ReactFinishQueueing.fp, ReactPerformWork.fpOwn")
SPECIAL = {"s": "s", "w": "w", "n": "n", "h": "h1"}
alltext = " ".join(t for n, k, t in cb if k == "(") + " " + post
impl = []
for n, k, t in cb:
    if k != "{" or n in DROP or n in ("eng", "σ", "answer"): continue
    if n in SPECIAL: impl.append(f"({n} := {SPECIAL[n]})"); continue
    if n in ("x2", "x3", "x7"): impl.append(f"({n} := {n})"); continue
    if n in SUBV: impl.append(f"({n} := {SUBV[n]})"); continue
    if n == NP: impl.append(f"({n} := Cn)"); continue
    if n == F1: impl.append(f"({n} := F)"); continue
    if n in IDN: impl.append(f"({n} := {IDN[n]})"); continue
    r = REN[n]
    if r in sub:
        v = sub[r]; v = v if re.fullmatch(r"[\w.]+", v) else "(" + v + ")"; impl.append(f"({n} := {v})"); continue
    if r in used: impl.append(f"({n} := {r})"); continue
    if not re.search(r"(?<![\w'.])" + re.escape(n) + r"(?![\w'])", alltext): impl.append(f"({n} := default)")
qargs = [f"({n} := {REN[n]} eR eE sW.envs.size)" for n in quant if norm(cwd[n]).startswith("∀ s3, Frame fpA s s3")]
wtxt = ws(_theorem_header(CO, COT))
KN = re.search(r"\(hcb : ∀ x, x ∈ \[(.*?)\] →", wtxt).group(1).split(", ")
KP = re.search(r"\(hcp : ∀ o k, \(o, k\) ∈ \(\[(.*?)\] : List \(ObjId × PropKey\)\)", wtxt).group(1)
kpairs = re.findall(r"\((\w+), \.(?:str|sym) (?:\(JSStr\.ofString \"[\w$]+\"\)|[\w.]+)\)", KP)
assert len(kpairs) == KP.count("), (") + 1, (len(kpairs), KP.count("), (") + 1)
WH = re.search(r"\(hco : ∀ o, o ∈ \(\[(.*?)\] : List ObjId\)", wtxt).group(1).split(", ")
FPAe = FPA.replace("eW", "sW.envs.size")
DLN = "@@DLN@@"
proof = f"""  intro sP hP hMF fuP sW hW fuW w2 w h1 C alt bm x1 x2 x3 x4 x5 x6 x7 hRD ⟨eR, eE, hFA2, Cn, F, {', '.join(HN)}⟩ hOwn fuw
  have heW : d.env ≠ sW.envs.size := Nat.ne_of_lt (Nat.lt_of_lt_of_le hG (Nat.le_trans hP.envs_le hW.envs_le))
  have hT := frame_trans hFA2 hOwn
  have hO2 : ∀ o, o < w2.heap.size → w.objEntry o = w2.objEntry o :=
    fun o ho => hOwn.obj_eq o ho (fun k hk => by simp [ReactPerformWork.fpOwn] at hk)
  have hE2 : w.envEntry d.env = w2.envEntry d.env :=
    hOwn.env_eq _ (Nat.lt_of_lt_of_le hG hFA2.envs_le) (by simp [ReactPerformWork.fpOwn, heW])
  {PRE}
  refine' wp_mono (ReactCommitOne.crw_one (fpA := {FPAe}) (bW := bm) {' '.join(impl)}
    {' '.join(args)} {' '.join(qargs)}
    (hFA := hT) (hGw := by rw [hcdenv, hE2]; exact hRD.record)
    (hcb := fun x hx => by
      rw [hcdenv]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with {' | '.join(['rfl'] * len(KN))} <;> simp (config := {{ decide := true }}) [{ALLDEFS}, heW])
    (hcp := fun o k hk => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hk
      rcases hk with {' | '.join(['⟨rfl, rfl⟩'] * len(kpairs))} <;> simp (config := {{ decide := true }}) [{ALLDEFS}, {DLN}])
    (hco := fun o ho k => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with {' | '.join(['rfl'] * len(WH))} <;> simp [{ALLDEFS}, {DLN}])
    ..) ?post
  case post =>
    rintro v w' h' ⟨-, hfu, w0, hPc, hF0⟩
    exact ⟨frame_trans hPc.2 hF0, by omega, w, w0, hPc, hF0⟩
  all_goals first | with_reducible assumption | (rw [props_frame hT (by with_reducible assumption) (by simp (config := {{ decide := true }}) [{ALLDEFS}, {DLN}])] <;> with_reducible assumption) | (rw [kind_frame hT (by with_reducible assumption)] <;> with_reducible assumption)
"""
EXTRA2 = ["(hG : d.env < s.envs.size)", "(hRo : R < s.heap.size)", "(hH : p_H < s.heap.size)",
          "(hRcur : (s.objEntry R).props.get? (.str \"current\") = some (.data (.obj p_H) p_ruw p_rue p_ruc))",
          "(hHa : (s.objEntry p_H).props.get? (.str \"alternate\") = some (.data (.obj p_X) p_haw p_hae p_hac))",
          "(hf0o : c_CR_CM_ME_M_CT_BT_CH_U_f0 < s.heap.size)",
          "(dr_RI : R ≠ l_RI) (dr_CF : R ≠ l_CF) (dr_CS : R ≠ l_CS) (dr_Cu : R ≠ l_Cu) (dr_U : R ≠ p_U)", "(hfu : 64000 ≤ s.fuel)"]
# objects whose same-key entries in the microtask's and render's footprints need telling apart: generated on demand
DLP = [l for l in open("tools/react_commit/complete_dl.txt").read().split("\n") if l.strip()] if __import__("os").path.exists("tools/react_commit/complete_dl.txt") else []
_dn = [re.match(r".(\w+) :", l).group(1) for l in DLP]
DLNv = ", ".join(f"{x}, Ne.symm {x}" for x in _dn + ["dr_RI", "dr_CF", "dr_CS", "dr_Cu", "dr_U"])
proof = proof.replace("@@DLN@@", DLNv).replace("{PRE}", PRE)
proof = proof.replace("@@ALLDEFS@@", ALLDEFS)
text_all2 = text_all + " " + " ".join(EXTRA2 + DLP)
used2 = set(ID.findall(text_all2))
for _ in range(3):
    used2 |= set(ID.findall(" ".join(b for nm, b in ibinds if nm in used2)))
ib2 = [b for nm, b in ibinds if nm in used2]
tbn2 = [f"{{{n} : {usubst(t, sub)}}}" for n, k, t in tb if k == "{" and n in used2 and n not in sub]
lbn2 = [f"{{{n} : {usubst(t, sub)}}}" for n, k, t in lb if k == "{" and n in used2 and n not in sub and n not in have]
stmt2 = ("theorem complete_hyp {n : Nat} " + " ".join(tbn2) + "\n    " + " ".join(lbn2) + "\n    " + " ".join(ib2) + "\n    " +
         "\n    ".join(ebinds) + "\n    " + " ".join(extra + EXTRA2 + DLP) + " :\n    " + concl2 + " := by\n" + proof)
out2 = out.replace(out[out.index("theorem complete_hyp"):out.index("\nend\n")], stmt2)
open("JSProofs/ReactMicrotaskComplete.lean", "w").write(out2)
print("written; impl", len(impl), "quant", len(qargs), "kn", len(KN), "kp", len(kpairs), "wh", len(WH))
