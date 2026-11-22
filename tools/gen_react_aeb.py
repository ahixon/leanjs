"""Generates ReactEarlyBailout.lean: attemptEarlyBailoutIfNoScheduledUpdate on the host root (its switch's case 3:
pushHostContainer, pushProvider, resetHydrationState, then bailoutOnAlreadyFinishedWork, each by its theorem).
zippy docs/react-proofs.md"""
import os, re, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from react_sig import sig, names_of_imp, hname
from react_compose import subst, hyp_type
ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
J = lambda f: ROOT + "/JSProofs/" + f
TWO = "(F64.fin false 4503599627370496 (-51))"; THREE = "(F64.fin false 6755399441055744 (-51))"
Z = "(F64.fin false 0 (-1074))"
CALLEES = [
  dict(key="phc", file="ReactHostContainer.lean", thm="ReactHostContainer.call_spec", name="call_spec", pfx="a_",
       share={"bG": "bG", "oG": "oG", "X": "X", "C": "C", "VS": "VS", "bdI": "bdI", "bdV": "bdV", "fP": "fP", "dP": "dP",
              "L": "L", "lw": "lw", "le": "le", "lc": "lc", "bdP": "bdP"},
       set={"n": "n", "h": "_", "fo": "fPHC", "d": "dPHC", "t": ".undefined", "s": "_"},
       self=["hlt", "hk", "hf", "hcode", "hcls", "hmode", "hG", "hGe"], drop=[], fn=("fPHC", "dPHC")),
  dict(key="ppr", file="ReactRootBailout.lean", thm="ReactRootBailout.provider_spec", name="provider_spec", pfx="b_",
       share={"bG": "bG", "oG": "oG", "VS": "VS", "bdI": "bdI", "bdV": "bdV", "fP": "fP", "dP": "dP", "L": "L",
              "lw": "lw", "le": "le", "lc": "lc", "bdP": "bdP", "Cx": "Cx"},
       set={"n": "n", "h": "_", "fo": "fPPR", "d": "dPPR", "t": ".undefined", "s": "_", "fib": "(.obj X)",
            "value": "cache", "iv": TWO, "nv": THREE, "i": "3"},
       self=["hlt", "hk", "hf", "hcode", "hcls", "hmode", "hG", "hGe", "hGI", "hGIm", "hGIv", "hnv", "hidx", "hnl"],
       drop=["hGP", "hGPv", "hPo", "hPk", "hPcode", "hPcls", "hPmode", "hPenv", "hGV", "hGVv", "hVS", "hVSk", "hlen"],
       fn=("fPPR", "dPPR")),
  dict(key="rhs", file="ReactRootBailout.lean", thm="ReactRootBailout.reset_spec", name="reset_spec", pfx="c_",
       share={"bG": "bG", "oG": "oG"}, set={"n": "n + 1", "h": "_", "fo": "fRHS", "d": "dRHS", "t": ".undefined", "s": "_"},
       self=["hlt", "hk", "hf", "hcode", "hcls", "hmode", "hG", "hGe"], drop=[], fn=("fRHS", "dRHS")),
  dict(key="bof", file="ReactBailout.lean", thm="ReactBailout.root_spec", name="root_spec", pfx="e_",
       share={"bG": "bG", "oG": "oG", "H": "H", "X": "X"},
       set={"n": "n", "h": "_", "fo": "fBOF", "d": "dBOF", "t": ".undefined", "s": "_"},
       self=["hlt", "hk", "hf", "hcode", "hcls", "hmode", "hG", "hGe"], drop=[], fn=("fBOF", "dBOF")),
]
imps = []; hyps = []; seen_imps = set()
def add_imp(names, ty):
    keep = [x for x in names if x not in seen_imps]
    seen_imps.update(keep)
    if keep: imps.append("{" + " ".join(keep) + " " + ty + "}")
add_imp(["n"], ": Nat"); add_imp(["h"], ": σ"); add_imp(["fo"], ": ObjId"); add_imp(["d"], ": FuncData")
add_imp(["t"], ": Value"); add_imp(["s"], ": State"); add_imp(["bG"], ": HashMap JSStr Binding")
add_imp(["oG"], ": Option EnvId")
for c in CALLEES:
    ci, ch = sig(J(c["file"]), c["name"], "    WP eng answer")
    ren = {}
    for b in ci:
        for x in names_of_imp(b):
            if x in c["set"]: continue
            ren[x] = c["share"].get(x, c["pfx"] + x)
    c["ren"] = ren
    sub = dict(ren); sub.update({k: v for k, v in c["set"].items() if k not in ("s", "h")})
    for b in ci:
        ty = b[b.index(":"):-1]
        nm = [ren[x] for x in names_of_imp(b) if x in ren]
        if nm: add_imp(nm, subst(ty, sub))
    c["hyps"] = []
    for b in ch:
        n0 = hname(b)
        if n0 in c["self"] or n0 in c["drop"]: continue
        ty = subst(hyp_type(b), sub)
        if re.search(r"(?<![\w.'])" + c["set"]["d"] + r"\.env\b", ty): c.setdefault("envhyps", []).append(n0)
        ty = re.sub(r"(?<![\w.'])" + c["set"]["d"] + r"\.env\b", "d.env", ty)
        if c["key"] == "phc":
            ty = re.sub(r"(?<![\w.'])DomRead\b", "ReactHostContainer.DomRead", ty)
            ty = re.sub(r"(?<![\w.'])fp\b", "ReactHostContainer.fp", ty)
        nn = c["pfx"] + n0
        ty = ty.replace("numberToJSStr (F64.fin false 6755399441055744 (-51))", "JSStr.ofString \"3\"")
        ty = ty.replace("(.str (JSStr.ofString \"3\"))", "(.str \"3\")")
        hyps.append(f"({nn} : {ty})"); c["hyps"].append((n0, nn, ty))
# AEB's own premises
add_imp(["fPHC", "fPPR", "fRHS", "fBOF", "Cx", "Rt", "MS", "Cu0"], ": ObjId")
add_imp(["dPHC", "dPPR", "dRHS", "dBOF"], ": FuncData")
add_imp(["bdPHC", "bdPPR", "bdRHS", "bdBOF", "bdCC"], ": Binding")
add_imp(["cache"], ": Value")
add_imp(["tw", "te", "tc", "sw", "se", "sc", "kw", "ke", "kc", "mw", "me", "mc", "cw", "ce2", "cc2"], ": Bool")
own = ["(hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : 500 ≤ s.fuel)",
       "(hcode : d.code = AEBGen.attemptEarlyBailoutIfNoScheduledUpdate_func) (hcls : d.isClassCtor = false) (hmode : d.thisMode = .strict)",
       "(hG : d.env < s.envs.size) (hGe : Scope.declLike? (s.envEntry d.env) = some (bG, oG))"]
for nm, f, dd, code in [("pushHostContainer", "fPHC", "dPHC", "PHCGen.pushHostContainer_func"),
                        ("pushProvider", "fPPR", "dPPR", "PPRGen.pushProvider_func"),
                        ("resetHydrationState", "fRHS", "dRHS", "RHSGen.resetHydrationState_func"),
                        ("bailoutOnAlreadyFinishedWork", "fBOF", "dBOF", "BOFGen.bailoutOnAlreadyFinishedWork_func")]:
    b = "bd" + f[1:]
    own.append(f"(g_{f} : bG[JSStr.ofString \"{nm}\"]? = some {b}) (g_{f}v : {b}.value = some (.obj {f}))")
    own.append(f"(h_{f} : {f} < s.heap.size) (h_{f}k : (s.objEntry {f}).kind = .func {dd}) (h_{f}code : {dd}.code = {code})")
    own.append(f"(h_{f}cls : {dd}.isClassCtor = false) (h_{f}mode : {dd}.thisMode = .strict) (h_{f}env : {dd}.env = d.env)")
own.append("(g_CC : bG[JSStr.ofString \"CacheContext\"]? = some bdCC) (g_CCv : bdCC.value = some (.obj Cx))")
own.append("(hRt : Rt < s.heap.size) (hRtk : (s.objEntry Rt).kind.isPlain = true) (hMS : MS < s.heap.size) (hMSk : (s.objEntry MS).kind.isPlain = true)")
own.append("(hXt : (s.objEntry X).props.get? (.str \"tag\") = some (.data (.num (F64.fin false 6755399441055744 (-51))) tw te tc))")
own.append("(hXs : (s.objEntry X).props.get? (.str \"stateNode\") = some (.data (.obj Rt) sw se sc))")
own.append("(hRtc : (s.objEntry Rt).props.get? (.str \"containerInfo\") = some (.data (.obj C) kw ke kc))")
own.append("(hHm : (s.objEntry H).props.get? (.str \"memoizedState\") = some (.data (.obj MS) mw me mc))")
own.append("(hMSc : (s.objEntry MS).props.get? (.str \"cache\") = some (.data cache cw ce2 cc2))")
hyps = own + hyps
open(ROOT + "/.lake/scratch/aeb_stmt.txt", "w").write("\n".join(imps) + "\n\n" + "\n".join(hyps))
print(len(hyps), "hyps")

# ---------- objects: distinctness between what the callees write and what is read later ----------
W = ["VS", "a_RI", "a_CF", "a_CS", "b_Cu", "Cx"]
R = ["X", "H", "e_C0", "e_C1", "e_fC", "Rt", "MS", "fPHC", "fPPR", "fRHS", "fBOF", "fP", "a_fO", "a_fGO", "a_fGC"] + W
pairs = []
for a in W:
    for b in R:
        if a != b and (b, a) not in pairs and (a, b) not in pairs: pairs.append((a, b))
dist = [f"(x_{a}_{b} : {a} ≠ {b})" for a, b in pairs]
DS = ", ".join([f"x_{a}_{b}, Ne.symm x_{a}_{b}" for a, b in pairs])
hyps = [h for h in hyps if "Cu0" not in h]
imps = [i.replace(" Cu0", "") for i in imps]
hyps.append(" ".join(dist))
# ---------- parse facts about objects ----------
def split_hyps(lines):
    out = []
    for line in lines:
        depth = 0; cur = ""
        for ch in line:
            if ch == "(":
                if depth == 0: cur = ""
                depth += 1
            if depth > 0: cur += ch
            if ch == ")":
                depth -= 1
                if depth == 0: out.append(cur)
    return out
allh = split_hyps(hyps)
props, kinds, heaps = {}, {}, {}
for hh in allh:
    m = re.match(r"\((\w+'?) : \(s\.objEntry (\w+)\)\.props\.get\? \(\.str \"([^\"]+)\"\) = some \(\.data (.+) (\S+) (\S+) (\S+)\)\)$", hh)
    if m:
        nm, o, k, v, w, e, c = m.groups()
        props[(o, k)] = (nm, v, w, e, c); continue
    m = re.match(r"\((\w+'?) : \(s\.objEntry (\w+)\)(\.kind.*)\)$", hh)
    if m: kinds[m.group(2)] = (m.group(1), m.group(3)); continue
    m = re.match(r"\((\w+'?) : (\w+) < s\.heap\.size\)$", hh)
    if m: heaps[m.group(2)] = m.group(1)
OBJS = sorted(set(list(heaps.keys())))
others = [hname("(" + h[1:]) for h in allh if not any(h.startswith("(" + v[0] + " ") for v in props.values())]
T = "(by first | assumption | (simp only [js_simp]; done) | (simp only [js_simp]; omega))"
def dso(o):
    ps = [f"x_{a}_{b}, Ne.symm x_{a}_{b}" for a, b in pairs if o in (a, b)]
    return ", ".join(ps) if ps else "nts3"
NAMES = ", ".join(hname(h) for h in allh if hname(h) != "hcode")
extra = []
def allf():
    return ", ".join([NAMES, DS] + [v[0] for v in props.values()] + [v[0] for v in kinds.values()] + list(heaps.values()) + extra +
                     ["hpn, hv, hl, ha, hne, Ne.symm hne, hG1, hG2, hGn2, Ne.symm hGn2, nts3, beq_self_eq_true, FDI.fdiCtx, Sem.inner"])
OWNF = ["hG", "hGe", "hXt", "hXs", "hRtc", "hHm", "hMSc", "g_CC", "g_CCv"] + [f"{a}{f}{b}" for f in ["fPHC", "fPPR", "fRHS", "fBOF"] for a, b in [("g_", ""), ("g_", "v"), ("h_", ""), ("h_", "k")]]
def jsf():
    return ", ".join(OWNF + [v[0] for (o, k), v in props.items() if o in ("X", "Rt", "H", "MS")] +
                     [v[0] for o, v in kinds.items() if o in ("X", "Rt", "H", "MS", "fPHC", "fPPR", "fRHS", "fBOF")] +
                     [heaps[o] for o in heaps if o in ("X", "Rt", "H", "MS", "fPHC", "fPPR", "fRHS", "fBOF")] + extra +
                     ["hpn, hv, hl, ha, hne, Ne.symm hne, hG1, hG2, hGn2, Ne.symm hGn2, nts3, beq_self_eq_true, FDI.fdiCtx, Sem.inner"])
lines = []; ind = 2
def emit(t):
    for l in t.split("\n"): lines.append(" " * ind + l)
def after(k, wrote):
    global extra
    emit(f"have hE{k} : s.envs.size < w{k}.envs.size := envs_frame hF{k} {T}")
    emit(f"have hEw{k} := envEntry_frame hF{k} (e := s.envs.size) {T} (by simp [Nat.ne_of_lt hG])")
    emit(f"have hGk{k} : d.env < w{k}.envs.size := envs_frame hF{k} {T}")
    emit(f"have hEa{k} : s.envs.size < w{k}.envs.size + 1 := Nat.lt_succ_of_lt hE{k}")
    emit(f"have hEb{k} : s.envs.size ≠ w{k}.envs.size := Nat.ne_of_lt hE{k}")
    emit(f"have hGb{k} : d.env ≠ w{k}.envs.size := Nat.ne_of_lt hGk{k}")
    emit(f"have hBl{k} : s.envs.size + 1 < w{k}.envs.size := envs_frame hF{k} {T}")
    emit(f"have hBw{k} := envEntry_frame hF{k} (e := s.envs.size + 1) {T} (by simp <;> omega)")
    emit(f"have hBa{k} : s.envs.size + 1 < w{k}.envs.size + 1 := Nat.lt_succ_of_lt hBl{k}")
    emit(f"have hBb{k} : s.envs.size + 1 ≠ w{k}.envs.size := Nat.ne_of_lt hBl{k}")
    nh, nk, np = {}, {}, {}
    for o in OBJS:
        emit(f"have hh{k}_{o} : {o} < w{k}.heap.size := heap_frame hF{k} (by first | exact {heaps[o]} | (simp only [js_simp]; exact {heaps[o]}))")
        nh[o] = f"hh{k}_{o}"
        if o in kinds:
            kn, kty = kinds[o]
            emit(f"have kk{k}_{o} : (w{k}.objEntry {o}){kty} := by rw [kind_frame hF{k} (by first | exact {heaps[o]} | (simp only [js_simp]; exact {heaps[o]}))]; first | (simp only [js_simp]; exact {kn}) | js_norm [{allf()}]")
            nk[o] = (f"kk{k}_{o}", kty)
    for (o, key), (nm, v, w, e, c) in props.items():
        if (o, key) in wrote: continue
        if o not in heaps: continue
        emit(f"have pp{k}_{o}_{re.sub(r'[^A-Za-z0-9]', '_', key)} : (w{k}.objEntry {o}).props.get? (.str \"{key}\") = some (.data {v} {w} {e} {c}) := by rw [props_frame hF{k} (by first | exact {heaps[o]} | (simp only [js_simp]; exact {heaps[o]})) (by simp [nts3, {dso(o)}])]; first | (simp only [js_simp]; exact {nm}) | js_norm [{allf()}]")
        np[(o, key)] = (f"pp{k}_{o}_{re.sub(r'[^A-Za-z0-9]', '_', key)}", v, w, e, c)
    np.update(wrote)
    heaps.clear(); heaps.update(nh); kinds.clear(); kinds.update(nk); props.clear(); props.update(np)
    extra += [f"hBl{k}", f"hBw{k}", f"hBa{k}", f"hBb{k}", f"Ne.symm hBb{k}", f"hE{k}", f"hEw{k}", f"hGk{k}", f"hEa{k}", f"hEb{k}", f"hGb{k}", f"Ne.symm hEb{k}", f"Ne.symm hGb{k}"]
def targeted(c, n0, k):
    for (n1, nn, ty) in c["hyps"]:
        if n1 != n0: continue
        m = re.match(r"\(s\.objEntry (\w+)\)\.props\.get\? \(\.str \"([^\"]+)\"\) = ", ty)
        if m and (m.group(1), m.group(2)) in props:
            return f"(by first | (simp only [js_simp]; exact {props[(m.group(1), m.group(2))][0]}) | exact {props[(m.group(1), m.group(2))][0]})"
        m = re.match(r"\(s\.objEntry (\w+)\)\.kind", ty)
        if m and m.group(1) in kinds: return f"(by first | (simp only [js_simp]; exact {kinds[m.group(1)][0]}) | exact {kinds[m.group(1)][0]})"
        m = re.fullmatch(r"(\w+) < s\.heap\.size", ty)
        if m and m.group(1) in heaps: return f"(by first | (simp only [js_simp]; exact {heaps[m.group(1)]}) | exact {heaps[m.group(1)]})"
        m = re.match(r"bG\[JSStr\.ofString \"([^\"]+)\"\]\? = ", ty)
        if m:
            if k == 1: return nn
            if k == 2: return f"(by rw [hbmx _ (by decide)]; exact {nn})"
            return f"(by simp only [Std.HashMap.getElem?_modify]; js_norm [bmx_{m.group(1)}, {nn}])"
        if c.get("envhyps") and n0 in c["envhyps"]: return f"(by rw [h_{c['fn'][0]}env]; exact {nn})"
        if not re.search(r"(?<![\w.'])s(?![\w'])", ty): return nn
        return None
    return None
def callee_args(c, extra_given, k=1):
    ci, ch = sig(J(c["file"]), c["name"], "    WP eng answer")
    imp = []
    for b in ci:
        for x in names_of_imp(b):
            if x in c["set"]:
                if c["set"][x] != "_": imp.append(f"({x} := {c['set'][x]})")
            else: imp.append(f"({x} := {c['ren'][x]})")
    holes = []
    for b in ch:
        n0 = hname(b)
        if n0 in extra_given: holes.append(extra_given[n0])
        elif n0 in ("hcode", "hcls", "hmode"): holes.append(f"h_{c['fn'][0]}{n0[1:]}")
        else:
            tg = targeted(c, n0, k)
            holes.append(tg if tg else "?_")
    return " ".join(imp), " ".join(holes)
CLOSE = ("all_goals first | omega | (simp only [js_simp]; done) | (simp only [js_simp]; omega) | decide | "
         "(simp only [Std.HashMap.getElem?_modify]; js_norm [{F}]; done) | "
         "(rw [hbmx _ (by decide)]; assumption) | (simp only [Std.HashMap.getElem?_modify, beq_iff_eq]; simp only [JSStr.ofString.injEq]; rw [hbmx _ (by decide)]; first | assumption | simp [*]) | "
         "(js_norm [{F}]; done) | skip")
def close(): emit(CLOSE.replace("{F}", allf()))
c_phc, c_ppr, c_rhs, c_bof = CALLEES
emit('have nts3 : numberToJSStr (F64.fin false 6755399441055744 (-51)) = JSStr.ofString "3" := by decide')
emit("have hG2 : d.env < s.envs.size + 1 + 1 := Nat.lt_succ_of_lt hG1")
emit("have hGn2 : d.env ≠ s.envs.size + 1 := Nat.ne_of_lt hG1")
emit("simp only [AEBGen.attemptEarlyBailoutIfNoScheduledUpdate]")
emit(f"js [{jsf()}]")
# 1. pushHostContainer
dr = {nm: f"?dr_{nm}" for nm in ("hNT", "hTN", "hNS")}
imp, holes = callee_args(c_phc, dict(dr, hG="?_", hGe="?_"))
emit("-- (`pushHostContainer(workInProgress, workInProgress.stateNode.containerInfo)`)")
emit(f"refine ⟨by js_norm [CallableC, {jsf()}], ?_⟩")
emit(f"refine wp_mono (ReactHostContainer.call_spec {imp} {holes}) ?p1")
for nm in ("hNT", "hTN", "hNS"):
    emit(f"case dr_{nm} =>\n  intro w h1 hF\n  refine a_{nm} w h1 (frame_mono (frame_trans (fp1 := {{}}) ?h0 hF) ?_ ?_ ?_)\n  case h0 => frame_go' [*, hne, Ne.symm hne, hG1]\n  all_goals simp [Footprint.union, h_fPHCenv]")
emit("have hbmx : ∀ x, x ≠ JSStr.ofString \"index\" → bG[x]? = bG[x]? := fun _ _ => rfl")
close()
emit("case p1 =>"); ind += 2
emit("intro v1 w1 h1 ⟨hv1, hF1, hfu1, hh1, ⟨bm, hbm, ⟨bd, hbd, hbdv, hbdm⟩, hbmx⟩, q0, q1, q2, qRI, qCF, qCS⟩\nsubst hv1 hh1\nrw [h_fPHCenv] at hF1 hbm\ntry simp only [js_simp] at hfu1\nsimp only [ReactHostContainer.fp, List.cons_append, List.nil_append] at hF1")
after(1, {("VS", "0"): ("q0", "a_vr", "true", "a_e0", "a_c0"), ("VS", "1"): ("q1", "a_vf", "true", "a_e1", "a_c1"),
          ("VS", "2"): ("q2", "a_vc", "true", "a_e2", "a_c2"), ("a_RI", "current"): ("qRI", "(.obj C)", "true", "a_re", "a_rc"),
          ("a_CF", "current"): ("qCF", "(.obj X)", "true", "a_fe", "a_fc"),
          ("a_CS", "current"): ("qCS", f"(.num {Z})", "true", "a_ce", "a_cc")})
extra.append("hbm")
for x in ["nextHydratableInstance", "hydrationParentFiber", "isHydrating", "workInProgressRootSkippedLanes",
          "createWorkInProgress", "valueCursor", "push", "valueStack", "resetHydrationState",
          "bailoutOnAlreadyFinishedWork", "pushProvider", "CacheContext"]:
    emit(f"have bmx_{x} : bm[JSStr.ofString \"{x}\"]? = bG[JSStr.ofString \"{x}\"]? := hbmx _ (by decide)")
    extra.append(f"bmx_{x}")
emit(f"js [{jsf()}]")
# 2. pushProvider
imp, holes = callee_args(c_ppr, {"hGI": "hbd", "hGIm": "hbdm", "hGIv": "hbdv", "hnv": "(by decide)", "hidx": "(by simp only [js_simp, nts3])",
                                 "hnl": "(by rw [nts3]; decide)", "hGe": "?ge2", "hGP": "(by rw [hbmx _ (by decide)]; exact a_hGP)",
                                 "hGPv": "a_hGPv", "hPo": "?_", "hPk": "?_", "hPcode": "a_hPcode", "hPcls": "a_hPcls",
                                 "hPmode": "a_hPmode", "hPenv": "(by rw [a_hPenv, h_fPPRenv])", "hGV": "(by rw [hbmx _ (by decide)]; exact a_hGV)",
                                 "hGVv": "a_hGVv", "hVS": "?_", "hVSk": "?_", "hlen": "?_"}, 2)
imp = imp.replace("(bG := bG)", "(bG := bm)").replace("(bdI := bdI)", "(bdI := bd)")
emit("-- (`pushProvider(workInProgress, CacheContext, current.memoizedState.cache)`)")
emit(f"refine ⟨by js_norm [CallableC, {jsf()}], ?_⟩")
emit(f"refine wp_mono (ReactRootBailout.provider_spec {imp} {holes}) ?p2")
emit(f"case ge2 => rw [h_fPPRenv]; js_norm [{jsf()}]")
close()
emit("case p2 =>"); ind += 2
emit("intro v2 w2 h2 ⟨hv2, hF2, hfu2, hh2, hR2, q3, qCu, qCx⟩\nsubst hv2 hh2\nrw [nts3] at q3\nrw [h_fPPRenv] at hF2 hR2\ntry simp only [js_simp] at hfu2\nsimp only [ReactRootBailout.fpP, List.cons_append, List.nil_append] at hF2")
(_, cur, _, ce, cc) = props[("b_Cu", "current")]
(_, cv, _, xe, xc) = props[("Cx", "_currentValue")]
(_, old, _, oe, oc) = ("", "b_old", "", "b_oe", "b_oc")
after(2, {("b_Cu", "current"): ("qCu", cv, "true", ce, cc), ("Cx", "_currentValue"): ("qCx", "cache", "true", xe, xc),
          ("VS", "3"): ("q3", cur, "true", "b_oe", "b_oc")})
extra.append("hR2")
emit(f"js [{jsf()}]")
# 3. resetHydrationState
imp, holes = callee_args(c_rhs, {"hGe": "?ge3"}, 3)
imp = imp.replace("(bG := bG)", "(bG := (bm.modify (JSStr.ofString \"index\") (fun bd => { bd with value := some (.num (F64.fin false 6755399441055744 (-51))) })))")
emit("-- (`resetHydrationState()`)")
emit(f"refine ⟨by js_norm [CallableC, {jsf()}], ?_⟩")
emit(f"refine wp_mono (ReactRootBailout.reset_spec {imp} {holes}) ?p3")
emit(f"case ge3 => rw [h_fRHSenv]; js_norm [{jsf()}]")
close()
emit("case p3 =>"); ind += 2
emit("intro v3 w3 h3 ⟨hv3, hF3, hfu3, hh3, hR3⟩\nsubst hv3 hh3\nrw [h_fRHSenv] at hF3 hR3\ntry simp only [js_simp] at hfu3\nsimp only [ReactRootBailout.fpR, List.cons_append, List.nil_append] at hF3")
after(3, {})
extra.append("hR3")
emit(f"js [{jsf()}]")
# 4. bailoutOnAlreadyFinishedWork
imp, holes = callee_args(c_bof, {"hGe": "?ge4"}, 4)
imp = imp.replace("(bG := bG)", "(bG := ((((bm.modify (JSStr.ofString \"index\") (fun bd => { bd with value := some (.num (F64.fin false 6755399441055744 (-51))) })).modify (JSStr.ofString \"hydrationParentFiber\") (fun bd => { bd with value := some .null })).modify (JSStr.ofString \"nextHydratableInstance\") (fun bd => { bd with value := some .null })).modify (JSStr.ofString \"isHydrating\") (fun bd => { bd with value := some (.bool false) })))")
emit("-- (`bailoutOnAlreadyFinishedWork(current, workInProgress, renderLanes)`)")
emit(f"refine ⟨by js_norm [CallableC, {jsf()}], ?_⟩")
emit(f"refine wp_mono (ReactBailout.root_spec {imp} {holes}) ?p4")
emit(f"case ge4 => rw [h_fBOFenv]; js_norm [{jsf()}]")
close()
emit("case p4 =>"); ind += 2
emit("intro v4 w4 h4 ⟨hv4, hF4, hfu4, hh4, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18⟩\nsubst hv4 hh4\nrw [h_fBOFenv] at hF4\ntry simp only [js_simp] at hfu4\nsimp only [ReactBailout.fp, ReactCreateWIP.fp, List.cons_append, List.nil_append] at hF4")
emit(f"js [{jsf()}, hF4]")
emit("all_goals (repeat' apply And.intro)")
emit("all_goals first | omega | (simp only [js_simp] at *; omega) | skip")
emit("simp only [fp, ReactHostContainer.fp, ReactBailout.fp, ReactCreateWIP.fp, List.cons_append, List.nil_append]")
emit("frame_go' [*, nts3, hne, Ne.symm hne, hG1, hG2, hGn2]")
FP = ("⟨[(g, \"index\"), (g, \"hydrationParentFiber\"), (g, \"nextHydratableInstance\"), (g, \"isHydrating\"), "
      "(g, \"workInProgressRootSkippedLanes\")], (ReactHostContainer.fp g VS RI CF CS).props ++ "
      "[(VS, .str \"3\"), (Cu, .str \"current\"), (Cx, .str \"_currentValue\")] ++ (ReactBailout.fp g X C1).props, false⟩")
out = f'''import JSProofs.ReactHostContainer
import JSProofs.ReactRootBailout
import JSProofs.ReactBailout
import JSProofs.AEBGen

/-!
# React's `attemptEarlyBailoutIfNoScheduledUpdate` on the host root (zippy docs/react-proofs.md)

The host root has no update of its own in a click's render: its case of the switch pushes the host container (the
container's DOM reads are `pushHostContainer`'s hypotheses), the cache provider and resets hydration, then
`bailoutOnAlreadyFinishedWork` clones the counter's fiber. Each callee by its theorem; their premises are this
theorem's, at its start (those about what an earlier callee writes come from that callee's post). Generated by
`tools/gen_react_aeb.py`.
-/

open ES ES.M HostRuns Logic
open Std (HashMap)

namespace ReactEarlyBailout

section
variable {{eng : Engine}} {{σ : Type}} {{answer : HostAnswer σ}}

theorem simple (d : FuncData) (hc : d.code = AEBGen.attemptEarlyBailoutIfNoScheduledUpdate_func) : FDI.Simple d := by
  constructor <;> rw [hc] <;> try rfl
  simp [AEBGen.attemptEarlyBailoutIfNoScheduledUpdate_func, Func.params, Func.info]

/-- What it writes. -/
def fp (g : EnvId) (VS RI CF CS Cu Cx X C1 : ObjId) : Footprint := {FP}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
/-- **`attemptEarlyBailoutIfNoScheduledUpdate(H, X, 2)`** on the host root: returns the counter's work in progress. -/
theorem root_spec {" ".join(imps)}
    {chr(10).join("    " + h for h in hyps)} :
    WP eng answer (n + 2) h (callImpl eng (.obj fo) t #[.obj H, .obj X, .num {TWO}]) s fun v w h' =>
      v = .obj e_C1 ∧ Frame (fp d.env VS a_RI a_CF a_CS b_Cu Cx X e_C1) s w ∧ s.fuel ≤ w.fuel + 500 ∧ h' = h := by
  apply wp_callGen AEBGen.attemptEarlyBailoutIfNoScheduledUpdate_eq (by decide) hlt hk (by omega) hcls hmode
    (by rw [hcode]; rfl) (by rw [hcode]; rfl) (simple d hcode) (by rw [hcode]; rfl) (by rw [hcode]; rfl)
  have hpn : d.code.info.fdi.paramNames = #[JSStr.ofString "current", JSStr.ofString "workInProgress",
    JSStr.ofString "renderLanes"] := by rw [hcode]; rfl
  have hv : d.code.info.fdi.varNames = #[JSStr.ofString "state$108", JSStr.ofString "primaryChildLanes"] := by rw [hcode]; rfl
  have hl : FDI.lexDecls d = #[] := by simp [FDI.lexDecls, hcode, AEBGen.attemptEarlyBailoutIfNoScheduledUpdate_func, Func.info]
  have ha : d.code.isAsync = false := by rw [hcode]; rfl
  have hne : s.envs.size ≠ d.env := Nat.ne_of_gt hG
  have hG1 : d.env < s.envs.size + 1 := Nat.lt_succ_of_lt hG
  clear hcode
{chr(10).join(lines)}

end

end ReactEarlyBailout
'''
open(ROOT + "/JSProofs/ReactEarlyBailout.lean", "w").write(out)
print("written", len(lines), "proof lines")
