"""Generates JSProofs/ReactMicrotaskLoop.lean (zippy docs/react-proofs.md): `loop_hyp`, the microtask's `r_Loop` from
`ReactWorkLoopTop.wls_top`. Its parameters are wls_top's, renamed (the loop's objects identified with
prepareFreshStack's, the rest prefixed `l_`); the premises wls_top states at the loop's start come from `P1` (the
work loop's start: prepareFreshStack's post) through renderRootSync's locals' frame; where a value the loop assumes is
not syntactically prep's, an equation premise (`eq_…`) says they agree; distinctness premises (`dl_…`) give the side
conditions on the microtask's footprint."""
import re, sys
sys.path.insert(0, "tools/react_commit")
from compose import binders, _theorem_header
from unify import parse, match, text, subst as usubst

TOP, TOPT = "JSProofs/ReactMicrotaskPrep.lean", "microtask_render_prep"
WLT, WLTT = "JSProofs/ReactWorkLoopTop.lean", "wls_top"
tb = binders(TOP, TOPT); td = {n: (k, t) for n, k, t in tb}
wb = binders(WLT, WLTT)
ID = re.compile(r"(?<![A-Za-z0-9_'.])([A-Za-z_][A-Za-z0-9_']*)(?![A-Za-z0-9_'])")
def norm(x):
    x = re.sub(r"\s+", " ", x)
    while True:
        y = re.sub(r"\((\w+)\)", r"\1", x)
        if y == x: return x
        x = y
IDN = {"Rw": "p_X", "Rc": "p_H", "C0": "p_F", "C1": "p_Fa", "Q": "p_Qo", "U": "p_U", "RSI": "I", "fWL": "fWL",
       "dWL": "dWL", "oG": "oG", "s": "s", "n": "n", "h": "h", "eng": "eng", "σ": "σ", "answer": "answer"}
DROP = {"w", "fpA", "bW", "hFA", "hGw", "hcb", "hcp", "hco", "hce"}
wnames = [n for n, k, t in wb]
REN = {n: IDN.get(n, "l_" + n) for n in wnames if n not in DROP}
def ren(t):
    parts = re.split(r'("[^"]*")', t)
    return "".join(x if x.startswith('"') else re.sub(r"(?<![A-Za-z0-9_'.])([A-Za-z_][A-Za-z0-9_']*)(?![A-Za-z0-9_'])",
                   lambda m: REN.get(m.group(1), m.group(1)), x) for x in parts)
wimp = {n for n, k, t in wb if k == "{"}
# supplied premises: about w (or bW), and the binding-value premises on their bindings
sup = [n for n, k, t in wb if k == "(" and n not in DROP and (re.search(r"(?<![\w'.])w\.", t) or "bW[" in t)]
supvars = {v for n, k, t in wb if n in sup for v in ID.findall(t) if v in wimp}
for n, k, t in wb:
    m = re.match(r"(\w+)\.(value|mutable)", t.strip())
    if k == "(" and n not in sup and m and m.group(1) in supvars: sup.append(n)
supvars = {v for n, k, t in wb if n in sup for v in ID.findall(t) if v in wimp} - {"w", "s"}
kept = [n for n, k, t in wb if k == "(" and n not in DROP and n not in sup]
keptvars = {v for n, k, t in wb if n in kept for v in ID.findall(t)}
# P1's facts at the loop's start (prep's names), by (object, key)
P1 = td["r_Loop"][1]
p1 = P1[P1.index("(fun w' (_ : σ) =>"):]
pf_args = re.search(r"ReactPrepareFresh\.PrepFields w' ([^∧]*?) ∧", p1).group(1).split()
src = open("JSProofs/ReactPrepareFresh.lean").read()
pdef = src[src.index("def PrepFields"):src.index("\n\n", src.index("def PrepFields"))]
pparams = re.search(r"def PrepFields \(w : State\) (.*?) : Prop :=", pdef, re.S).group(1)
pnames = [x for grp in re.findall(r"\(([^:()]*) :", pparams) for x in grp.split()]
pmap = dict(zip(pnames, pf_args))
SRC = {}
for m in re.finditer(r'\(\(w\.objEntry (\w+)\)\.props\.get\? \(\.str "(\w+)"\) = (some \(\.data .*?\))\)(?: ∧|$)', re.sub(r"\s+", " ", pdef)):
    SRC[(pmap[m.group(1)], m.group(2))] = usubst(m.group(3), pmap)
sub, eqs = {}, []
free = {REN[v] for v in supvars if v in REN and v not in IDN}
timp = {n for n, k, t in tb if k == "{"}
pfree = {x for a in pf_args for x in ID.findall(a) if x in timp and x.startswith("p_")}
for n in sup:
    t = norm(ren(dict((a, c) for a, b, c in wb)[n].strip()))
    m = re.match(r'\(w\.objEntry (\w+)\)\.props\.get\? \(\.str (?:\(JSStr\.ofString )?"(\w+)"\)?\) = (.*)$', t)
    if not m: continue
    key = (m.group(1), m.group(2))
    if key not in SRC:
        if key != ("I", "H"): print("NO SOURCE", n, key)
        continue
    a, b = parse(m.group(3)), parse(SRC[key])
    def walk(a, b):
        if isinstance(a, list) and len(a) == 1: a = a[0]
        if isinstance(b, list) and len(b) == 1: b = b[0]
        if isinstance(a, str) and a in free:
            if a in sub and sub[a] != text(b): eqs.append((text(b), sub[a], n))
            else: sub[a] = text(b)
            return
        if isinstance(b, str) and b in pfree:
            if b in sub and sub[b] != text(a): eqs.append((sub[b], text(a), n))
            else: sub[b] = text(a)
            return
        if isinstance(a, list) and isinstance(b, list) and len(a) == len(b):
            for x, y in zip(a, b): walk(x, y)
            return
        if text(a) != text(b): eqs.append((text(b), text(a), n))
    walk(a, b)
shared = sorted(v for v in sub if v in {REN.get(x, x) for x in keptvars})
print("supplied", len(sup), "kept", len(kept), "unified", len(sub), "shared with kept", shared)
for e in eqs: print("EQ", e)
sub = {k: v for k, v in sub.items() if k != v}
def S(t): return usubst(ren(t), sub)
# the conclusion: r_Loop with the loop's footprint, its fuel, PRu trivial for now
wh = re.sub(r"\s+", " ", _theorem_header(WLT, WLTT))
wpost = wh[wh.rindex("fun v w' h' =>"):]
FPW = re.search(r"Frame \((.*)\) w w' ∧ w\.fuel ≤ w'\.fuel \+ 2400", wpost).group(1)
concl = re.sub(r"\s+", " ", P1.strip())
concl = concl.replace("(j + 2)", "(n + 10)")
concl = re.sub(r"(?<![\w'])fpWL(?![\w'])", f"({S(FPW)})", concl)
concl = re.sub(r"(?<![\w'])kW(?![\w'])", "2400", concl)
concl = re.sub(r"(?<![\w'])PRu(?![\w'])", "(fun _ _ => True)", concl)
concl = usubst(concl, sub)
used = set(ID.findall(concl))
ebinds, ibinds = [], []
DOMR = []
wd = {n: (k, t) for n, k, t in wb}
for n, k, t in wb:
    if n in DROP or n in IDN or REN.get(n, n) in sub: continue
    if k == "{":
        ibinds.append((REN[n], f"{{{REN[n]} : {S(t)}}}"))
    elif n in kept:
        tt = S(t).strip()
        if tt.startswith("ReactHostContainer.DomRead"):
            m = re.match(r"ReactHostContainer\.DomRead eng answer (\(n \+ \d+\)|n) w (.*)$", re.sub(r"\s+", " ", tt))
            assert m, tt[:120]
            rest = m.group(2)
            # the footprint argument: the first balanced (...) group
            d0 = 0
            for j, ch in enumerate(rest):
                d0 += {"(": 1, ")": -1}.get(ch, 0)
                if d0 == 0: break
            fp, tail = rest[:j + 1], rest[j + 1:]
            tt = f"∀ e, ReactHostContainer.DomRead eng answer {m.group(1)} s ((FAE e).union {fp}){tail}"
            DOMR.append(REN[n])
        ebinds.append(f"({REN[n]} : {tt})")
extra0 = ["(hPUenv : l_dPU.env = d.env)"] + [f"(eq_{i} : {b} = {a})" for i, (a, b, n) in enumerate(eqs)]
usedw = set(ID.findall(" ".join(ebinds) + " " + concl + " " + " ".join(extra0)))
for _ in range(3):
    usedw |= set(ID.findall(" ".join(b for nm, b in ibinds if nm in usedw)))
ibinds = [b for nm, b in ibinds if nm in usedw]
extra = ["(hoG : oG = none)", "(hG : d.env < s.envs.size)",
         "(hRo : R < s.heap.size) (hRk : (s.objEntry R).kind.isPlain = true)",
         "(hRcur : (s.objEntry R).props.get? (.str \"current\") = some (.data (.obj p_H) p_ruw p_rue p_ruc))",
         "(hH : p_H < s.heap.size) (hHk : (s.objEntry p_H).kind.isPlain = true)",
         "(hHa : (s.objEntry p_H).props.get? (.str \"alternate\") = some (.data (.obj p_X) p_haw p_hae p_hac))",
         "(hFQo : fFQ < s.heap.size) (hFQk : (s.objEntry fFQ).kind = .func dFQ)",
         "(dr_RI : R ≠ l_RI) (dr_CF : R ≠ l_CF) (dr_CS : R ≠ l_CS) (dr_Cu : R ≠ l_Cu)", "(hPUenv : l_dPU.env = d.env)", "(hfu : 4000 ≤ s.fuel)"]
allw = " ".join(ebinds) + " " + " ".join(ibinds) + " " + concl + " " + " ".join(extra)
need = set(ID.findall(allw))
tbinds = []
for n, k, t in tb:
    if k == "{" and n in need and n not in sub: tbinds.append(f"{{{n} : {S(t) if False else usubst(t, sub)}}}")
for i, (a, b, n) in enumerate(eqs):
    extra.append(f"(eq_{i} : {b} = {a})")
FAE = re.search(r"Frame \((\(\(\(\(ReactMicrotaskClick\.fpPerf.*?ReactPrepareFresh\.fp d\.env p_X p_A p_Qo p_U p_F p_Fa p_H\))\) s w'", concl).group(1)
ebinds = [b.replace("(FAE e)", f"(({FAE}).union (ReactRenderSync.fpOwn e))") for b in ebinds]
stmt = ("theorem loop_hyp {n : Nat} " + " ".join(tbinds) + "\n    " + " ".join(ibinds) + "\n    " + "\n    ".join(ebinds) +
        "\n    " + " ".join(extra) + " :\n    " + concl + " := by\n  sorry\n")
OPENS = "\n".join(l for l in open("JSProofs/ReactWorkLoop.lean").read().split("\n") if l.startswith("open "))
out = f'''import JSProofs.ReactWorkLoopTop
import JSProofs.ReactMicrotaskPrep

/-!
# The click's work loop as the microtask's `r_Loop` (zippy docs/react-proofs.md)

Generated by `tools/react_commit/gen_react_loop.py`.
-/

{OPENS}

namespace ReactMicrotaskLoop

section
variable {{eng : Engine}} {{σ : Type}} {{answer : HostAnswer σ}}

set_option maxRecDepth 40000 in
set_option maxHeartbeats 8000000 in
{stmt}
end

end ReactMicrotaskLoop
'''
open("JSProofs/ReactMicrotaskLoop.lean", "w").write(out)
print("binders: microtask", len(tbinds), "implicit", len(ibinds), "premises", len(ebinds), "extra", len(extra))
# ---- the proof (part 1: wls_top applied; its post left open) ----
FAKEYS = [("A", "1"), ("R", "callbackPriority"), ("R", "callbackNode"), ("I", "H"), ("I", "A")] + \
    [("p_X", k) for k in ["pendingProps", "type", "flags", "subtreeFlags", "deletions", "childLanes", "lanes", "child",
                          "memoizedProps", "memoizedState", "updateQueue", "dependencies", "sibling", "index", "ref",
                          "refCleanup"]] + \
    [("p_A", k) for k in "0123"] + [("p_Qo", "pending"), ("p_U", "next"), ("p_F", "lanes"), ("p_Fa", "lanes"),
                                     ("p_H", "childLanes")]
FAOBJ = sorted({o for o, k in FAKEYS})
wtxt = re.sub(r"\s+", " ", _theorem_header(WLT, WLTT))
KP = re.search(r"\(hcp : ∀ o k, \(o, k\) ∈ \(\[(.*?)\] : List \(ObjId × PropKey\)\)", wtxt).group(1)
kpairs = re.findall(r"\((\w+), \.(?:str|sym) (\(JSStr\.ofString \"[\w$]+\"\)|[\w.]+)\)", KP)
WH = re.search(r"\(hco : ∀ o, o ∈ \(\[(.*?)\] : List ObjId\)", wtxt).group(1).split(", ")
OE = re.search(r"\(hce : ∀ e, e ∈ \(\[(.*?)\] : List EnvId\)", wtxt).group(1).split(", ")
dl = set()
for o, k in kpairs:
    o = REN.get(o, o)
    kk = re.search(r'"([\w$]+)"', k).group(1) if '"' in k else None
    for O, K in FAKEYS:
        if kk == K and o != O: dl.add((o, O))
for o in WH:
    for O in FAOBJ:
        if REN.get(o, o) != O: dl.add((REN.get(o, o), O))
dle = [REN.get(e.split(".")[0], e.split(".")[0]) + ".env" for e in OE]
ebnd = {}
for b in ebinds:
    m = re.match(r"\((\w+) : (\w+\.env) < s\.envs\.size\)$", b)
    if m: ebnd.setdefault(m.group(2), m.group(1))
DLP = [f"(dl_{a}_{b} : {a} ≠ {b})" for a, b in sorted(dl)] + [f"(dle_{i} : {e} ≠ d.env)" for i, e in enumerate(dle)]
DLN = ", ".join(f"dl_{a}_{b}, Ne.symm dl_{a}_{b}" for a, b in sorted(dl))
# bounds of objects at the start (premise names)
allp = {}
for b in ebinds + [f"({n} : {t})" for n, k, t in tb if k == "("]:
    m = re.match(r"\((\w+) : \(?(\w+)\)? < \(?s\)?\.heap\.size\)$", b)
    if m: allp.setdefault(m.group(2), m.group(1))
PF = ["X.pendingProps", "X.type", "X.flags", "X.subtreeFlags", "X.deletions", "X.lanes", "X.child", "X.memoizedProps",
      "X.memoizedState", "X.updateQueue", "X.dependencies", "X.sibling", "X.index", "X.ref", "X.refCleanup",
      "X.childLanes", "H.childLanes", "F.lanes", "Fa.lanes", "Qo.pending", "U.next"]
pfn = {("p_" + x.split(".")[0], x.split(".")[1]): "pf_" + x.replace(".", "_") for x in PF}
PFPAT = "⟨" + ", ".join(pfn[("p_" + x.split(".")[0], x.split(".")[1])] for x in PF) + "⟩"
PBPAT = ("⟨bm1, hbm1, ⟨_, gW, gWv, gWm⟩, ⟨_, gE, gEv⟩, ⟨_, gS, gSv, gSm⟩, ⟨_, gX, gXv, gXm⟩, ⟨_, gR, gRv, gRm⟩, "
         "⟨_, gL, gLv, gLm⟩, ⟨_, g1, g1v⟩, ⟨_, g3, g3v⟩, ⟨_, g4, g4v⟩, ⟨_, g5, g5v⟩, ⟨_, g6, g6v⟩, ⟨_, g7, g7v⟩, "
         "⟨_, gQ, gQm, gQv⟩, ⟨_, gU, gUm, gUv⟩⟩")
BSRC = {"workInProgress": ("gW", {"value": "gWv", "mutable": "gWm"}),
        "entangledRenderLanes": ("gE", {"value": "gEv"}),
        "workInProgressRootSkippedLanes": ("gS", {"value": "gSv", "mutable": "gSm"}),
        "workInProgressRootExitStatus": ("gX", {"value": "gXv", "mutable": "gXm"})}
wd = {n: t for n, k, t in wb}
args = []
bvar = {}
for n in sup:
    t = norm(S(wd[n]).strip())
    m = re.match(r"bW\[JSStr\.ofString \"([\w$]+)\"\]\? = some (\w+)$", t)
    if m:
        bvar[m.group(2)] = m.group(1); args.append(f"({n} := {BSRC[m.group(1)][0]})"); continue
for n in sup:
    t = norm(S(wd[n]).strip())
    if t.startswith("bW["): continue
    if re.search(r"≤ w\.fuel$", t): args.append(f"({n} := by omega)"); continue
    m = re.match(r"(\w+)\.(value|mutable)", t)
    if m and m.group(1) in bvar:
        f = "mutable" if m.group(2) == "mutable" else "value"
        args.append(f"({n} := by first | exact {BSRC[bvar[m.group(1)]][1][f]} | simpa using {BSRC[bvar[m.group(1)]][1][f]} | simp [{BSRC[bvar[m.group(1)]][1][f]}])"); continue
    m = re.match(r'\(w\.objEntry (\w+)\)\.props\.get\? \(\.str (?:\(JSStr\.ofString )?"(\w+)"', t)
    o, k = m.group(1), m.group(2)
    bnd = allp.get(o)
    pre = f"rw [hO _ (lt_heap_of_frame hFA1 {bnd})]"
    if (o, k) == ("I", "H"): args.append(f"({n} := by {pre}; exact hIHv)"); continue
    eqr = [f"eq_{i}" for i, (a, b, nn) in enumerate(eqs) if nn == n]
    rw2 = f"; rw [{', '.join(eqr)}]" if eqr else ""
    args.append(f"({n} := by {pre}{rw2}; exact {pfn[(o, k)]})")
for n, k, t in wb:
    if n in DROP or n in IDN: continue
    if k == "{":
        r = REN[n]
        if r in sub:
            v = sub[r] if re.fullmatch(r"[\w.]+", sub[r]) else "(" + sub[r] + ")"
            args.append(f"({n} := {v})")
        elif r in usedw: args.append(f"({n} := {r})")
    elif n in kept:
        r = REN[n]
        if r in DOMR: args.append(f"({n} := fun w' h1' hf' => {r} sR.envs.size w' h1' (frame_trans hT hf'))")
        else: args.append(f"({n} := {r})")
for o in IDN:
    if o in wnames and o not in ("s", "n", "h", "eng", "σ", "answer") and wd[o] is not None and dict((a, b) for a, b, c in wb)[o] == "{":
        args.append(f"({o} := {'none' if o == 'oG' else IDN[o]})")
NKN = len(re.search(r"\(hcb : ∀ x, x ∈ \[(.*?)\] →", wtxt).group(1).split(", "))
alltext = " ".join(t for n, k, t in wb if k == "(") + " " + wtxt[wtxt.rindex("fun v w' h' =>"):]
phantom = [n for n, k, t in wb if k == "{" and n not in DROP and n not in IDN and
           not re.search(r"(?<![\w'.])" + re.escape(n) + r"(?![\w'])", alltext)]
args += [f"({n} := default)" for n in phantom]
FADEFS = ("Logic.Footprint.union, ReactMicrotaskClick.fpPerf, ReactSchedTaskRoot.fp, ReactRenderSync.fpPre, "
          "ReactPrepareFresh.fp, ReactCreateWIP.fp, ReactRenderSync.fpOwn")
FPD = ("Logic.Footprint.union, ReactBeginRoot.fp, ReactEarlyBailout.fp, ReactHostContainer.fp, ReactBailout.fp, "
       "ReactCreateWIP.fp, fpB, ReactUpdateFunction.fpUF, ReactReconcileImpl.fpI, ReactBeginButton.fpBB, "
       "ReactCompleteUnit.fpU, ReactCompleteButton.fpCW, ReactCompleteButton.fpCC, ReactCompleteRoot.fpRC")
POST = """  case post =>
  rintro v w' h' ⟨hv, hFw, hfuw, hh, Cn, F, -, -, -, -, -, -, -, -, bmL, hbmL, ⟨_, gWn, gWnv⟩, ⟨_, gXs, gXsv, gXsm⟩,
    ⟨_, gLc, gLcm, gLci⟩, ⟨_, gCr, gCrm, gCri⟩⟩
  subst hh
  have hGw : l_dPU.env < w.envs.size := by rw [hPUenv]; exact Nat.lt_of_lt_of_le hGs hT.envs_le
  obtain ⟨bw, hbw, NB⟩ := declLike_frame hFw hGw hbmw
  have hbL : bmL = bw := by rw [hbw] at hbmL; cases hbmL; rfl
  subst hbL
  obtain ⟨bmR, hbmR, ⟨_, gEC, gECm, gECi⟩, ⟨_, gTr, gTrv⟩⟩ := hRec
  have hbR : bmR = bm1 := by rw [hbm1] at hbmR; cases hbmR; rfl
  rw [hbR] at gEC gTr
  have hbmL' : Scope.declLike? (w'.envEntry d.env) = some (bmL, none) := by rw [← hPUenv]; exact hbmL
  refine ⟨hFw, hfuw, ?AL, ?RY, ?RD⟩
  case AL =>
    unfold ReactRenderSync.AfterLoop ReactRenderSync.Writable
    exact ⟨bmL, _, _, hbmL', gXs, gXsv, gWn, gWnv, ⟨_, gLc, gLcm, gLci⟩, ⟨_, gCr, gCrm, gCri⟩,
      ⟨_, by rw [NB (JSStr.ofString "executionContext") (by simp (config := { decide := true }) [@@FPD@@])]; exact gEC, gECm, gECi⟩,
      ⟨_, by rw [NB (JSStr.ofString "workInProgressRoot") (by simp (config := { decide := true }) [@@FPD@@])]; exact gR, gRm, by simp [gRv]⟩,
      ⟨_, by rw [NB (JSStr.ofString "workInProgressRootRenderLanes") (by simp (config := { decide := true }) [@@FPD@@])]; exact gL, gLm, by simp [gLv]⟩⟩
  case RY =>
    exact ⟨Nat.lt_of_lt_of_le hGs (Nat.le_trans hT.envs_le hFw.envs_le), Nat.lt_of_lt_of_le hFQo (Nat.le_trans hT.heap_le hFw.heap_le),
      by rw [kind_frame (frame_trans hT hFw) hFQo]; exact hFQk,
      ⟨bmL, none, _, _, hbmL', by rw [NB (JSStr.ofString "concurrentQueuesIndex") (by simp (config := { decide := true }) [@@FPD@@])]; exact gQ, gQm, gQv,
        by rw [NB (JSStr.ofString "concurrentlyUpdatedLanes") (by simp (config := { decide := true }) [@@FPD@@])]; exact gU, gUm, gUv⟩⟩
  case RD =>
    intro e w2 w3 hEnd hFQ c
    have hG2 : d.env < w'.envs.size := Nat.lt_of_lt_of_le hGs (Nat.le_trans hT.envs_le hFw.envs_le)
    obtain ⟨b2, hb2, B2⟩ := declLike_frame hEnd hG2 hbmL'
    obtain ⟨b3, hb3, B3⟩ := declLike_frame hFQ (Nat.lt_of_lt_of_le hG2 hEnd.envs_le) hb2
    have TOT := frame_trans (frame_trans (frame_trans hT hFw) hEnd) hFQ
    have V : ∀ x : String, (d.env, JSStr.ofString x) ∉ (ReactFinishQueueing.fp d.env).binds →
        (d.env, JSStr.ofString x) ∉ (ReactRenderSync.fpEnd e d.env I).binds →
        (l_dPU.env, JSStr.ofString x) ∉ (@@FPW@@).binds → b3[JSStr.ofString x]? = bm1[JSStr.ofString x]? :=
      fun x h3 h2 h1 => by rw [B3 _ h3, B2 _ h2, NB _ h1]
    have nb : ∀ x : String, x ∈ ["workInProgressRootRecoverableErrors", "workInProgressTransitions",
        "workInProgressRootDidIncludeRecursiveRenderUpdate", "workInProgressDeferredLane",
        "workInProgressRootInterleavedUpdatedLanes", "workInProgressSuspendedRetryLanes",
        "workInProgressRootDidSkipSuspendedSiblings"] → b3[JSStr.ofString x]? = bm1[JSStr.ofString x]? := by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact V _ (by simp (config := { decide := true }) [ReactFinishQueueing.fp])
          (by simp (config := { decide := true }) [ReactRenderSync.fpEnd, ReactRenderSync.fpOwn])
          (by simp (config := { decide := true }) [@@FPD@@])
    refine ⟨⟨p_H, .obj p_X, b3, .null, .null, .bool false, .num (F64.fin false 0 (-1074)), .num (F64.fin false 0 (-1074)),
      .num (F64.fin false 0 (-1074)), .bool false, ⟨hb3, ⟨_, (nb _ (by simp)).trans g1, g1v⟩, ⟨_, (nb _ (by simp)).trans gTr, gTrv⟩,
      ⟨_, (nb _ (by simp)).trans g3, g3v⟩, ⟨_, (nb _ (by simp)).trans g4, g4v⟩, ⟨_, (nb _ (by simp)).trans g5, g5v⟩,
      ⟨_, (nb _ (by simp)).trans g6, g6v⟩, ⟨_, (nb _ (by simp)).trans g7, g7v⟩,
      ⟨Nat.lt_of_lt_of_le hRo TOT.heap_le, by show (w3.objEntry R).kind.isPlain = true; rw [kind_frame TOT hRo]; exact hRk,
        _, _, _, by show (w3.objEntry R).props.get? _ = _; rw [props_frame TOT hRo (by simp (config := { decide := true }) [@@FPD@@, @@FADEFS@@, ReactRenderSync.fpEnd, ReactRenderSync.fpOwn, ReactFinishQueueing.fp, dr_RI, dr_CF, dr_CS, dr_Cu, @@DLN@@])]; exact hRcur⟩,
      ⟨Nat.lt_of_lt_of_le hH TOT.heap_le, by show (w3.objEntry p_H).kind.isPlain = true; rw [kind_frame TOT hH]; exact hHk,
        _, _, _, by show (w3.objEntry p_H).props.get? _ = _; rw [props_frame TOT hH (by simp (config := { decide := true }) [@@FPD@@, @@FADEFS@@, ReactRenderSync.fpEnd, ReactRenderSync.fpOwn, ReactFinishQueueing.fp, @@DLN@@])]; exact hHa⟩⟩⟩, trivial⟩
""".replace("@@FPD@@", FPD).replace("@@FPW@@", S(FPW)).replace("@@FADEFS@@", FADEFS).replace("@@DLN@@", DLN)
proof = f"""  intro sP hP fuP sW hW fuW sR hR fuR w1 w h1 ⟨hFA1, hPB, hPF, ⟨iv, ia, ib, hIHv⟩, hRec⟩ hOwn fuw
  subst hoG
  have hsR : s.envs.size ≤ sR.envs.size := Nat.le_trans hP.envs_le (Nat.le_trans hW.envs_le hR.envs_le)
  have hT := frame_trans hFA1 hOwn
  have hGs : d.env < s.envs.size := hG
  have hdne : d.env ≠ sR.envs.size := Nat.ne_of_lt (Nat.lt_of_lt_of_le hGs hsR)
  have hO : ∀ o, o < w1.heap.size → w.objEntry o = w1.objEntry o := fun o ho => obj_eq_np hOwn rfl ho
  have hE : w.envEntry d.env = w1.envEntry d.env :=
    hOwn.env_eq _ (Nat.lt_of_lt_of_le hGs hFA1.envs_le) (by simp [ReactRenderSync.fpOwn, hdne])
  unfold ReactPrepareFresh.PrepBinds at hPB
  unfold ReactPrepareFresh.PrepFields at hPF
  obtain {PBPAT} := hPB
  obtain {PFPAT} := hPF
  have hbmw : Scope.declLike? (w.envEntry l_dPU.env) = some (bm1, none) := by rw [hPUenv, hE]; exact hbm1
  refine wp_mono (ReactWorkLoopTop.wls_top (s := s) (w := w) (bW := bm1) {' '.join(args)}
    (hFA := hT) (hGw := hbmw)
    (hcb := fun x hx => by
      rw [hPUenv]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with {' | '.join(['rfl'] * NKN)} <;>
        simp (config := {{ decide := true }}) [{FADEFS}, hdne])
    (hcp := fun o k hk => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hk
      rcases hk with {' | '.join(['⟨rfl, rfl⟩'] * len(kpairs))} <;>
        simp (config := {{ decide := true }}) [{FADEFS}, {DLN}])
    (hco := fun o ho k => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with {' | '.join(['rfl'] * len(WH))} <;> simp [{FADEFS}, {DLN}])
    (hce := fun e he x => by
      {'; '.join(f'have ne_{i} : {e} ≠ sR.envs.size := Nat.ne_of_lt (Nat.lt_of_lt_of_le {ebnd[e]} hsR)' for i, e in enumerate(dle))}
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with {' | '.join(['rfl'] * len(OE))} <;>
        simp [{FADEFS}, {', '.join(f'dle_{i}' for i in range(len(OE)))}, {', '.join(f'ne_{i}' for i in range(len(OE)))}])) ?post
""" + POST

stmt = stmt.replace(" := by\n  sorry\n", " := by\n" + proof)
stmt = stmt.replace("(hfu : 4000 ≤ s.fuel)", "(hfu : 4000 ≤ s.fuel) " + " ".join(DLP))
out = out.replace(out[out.index("theorem loop_hyp"):out.index("\nend\n")], stmt)
open("JSProofs/ReactMicrotaskLoop.lean", "w").write(out)
print("dl", len(dl), "dle", len(dle), "bounds", len(allp), [o for o in FAOBJ if o not in allp])
