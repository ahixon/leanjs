"""Generates JSProofs/ReactWorkLoop.lean: workLoopSync in the click's render — performUnitOfWork on the root
(ReactUnitRoot), the counter (ReactUnitCounter) and the button (ReactUnitButton), the loop's test reading
workInProgress (the root fiber, the counter fiber, the button fiber, then null). The statement merges the three units'
binders: the counter's unprefixed, the root's `R_`, the button's `B_`, with the fibers, the unit function, the stack
and the module record identified; each later premise about a property or binding an earlier unit writes is dropped
and supplied by that unit's post (its generic values substituted into the rest); the others go through the frames.
zippy docs/react-proofs.md"""
import os, re, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "react_cuw"))
import args as A
ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
J = lambda f: os.path.join(ROOT, "JSProofs", f)
RB = A.binders(J("ReactUnitRoot.lean"), "root_spec")
KB = A.binders(J("ReactUnitCounter.lean"), "counter_unit_spec")
BB = A.binders(J("ReactUnitButton.lean"), "button_unit_spec")
SKIP = {"n", "h", "s"}
L22 = "(F64.fin false 5062151534280704 (-22))"; ONE = "(F64.fin false 4503599627370496 (-52))"; Z = "(F64.fin false 0 (-1074))"
# --- the counter: base names, its d separate, values its root-supplied premises fix
KMAP = {"d": "K_d", "bG": "bG0", "tPU": ".undefined",
        "ppw": "true", "ppe": "R_e_e0", "ppc": "R_e_c0", "tyw": "true", "tye": "R_e_e1", "tyc": "R_e_c1",
        "fl1": f"(numberBinOp .bitAnd R_e_fl {L22})", "fe": "R_e_e2", "fc": "R_e_c2", "lw": "R_e_e6", "lc": "R_e_c6",
        "cw": "R_e_e7", "cc": "R_e_c7", "mpe'": "R_e_e8", "mpc'": "R_e_c8", "me": "R_e_e9", "mc": "R_e_c9",
        "uw_2": "R_e_e10", "uc_2": "R_e_c10", "dpw": "true", "dpe": "R_e_e11", "dpc": "R_e_c11",
        "vHT": "(.str (JSStr.ofString \"button\"))", "vMS": ".null", "wv": "(.obj C1)"}
KDROP = {"hC1pp", "hC1ty", "hC1f", "hC1l", "rhRFc", "hC1mp", "hC1m", "hC1u", "hC1d", "hGWIP", "hGWIPm", "hGWIPi",
         "hGDR", "hGDRm", "hGDRi", "hGHy", "hGHyv", "hGe", "hPUo", "hPUk", "hPUf", "hPUcode", "hPUcls", "hPUmode",
         "hPUenv"}
# --- the root: prefixed, its fibers and stack identified, its generic copied values the counter's
RMAP = {"fo": "fPU", "d": "dPU", "t": ".undefined", "X": "Rw", "H": "Rc", "e_C1": "C1", "e_C0": "C0", "bG": "bG0", "oG": "oG",
        "VS": "VS", "a_RI": "RI", "a_CF": "CF", "a_CS": "CS", "b_Cu": "Cu", "Cx": "Cx",
        "e_pp": "(.obj Pp)", "e_vT": "(.obj fK)", "e_vL": "ln", "e_vC": "ch0", "e_vMP": "mpv", "e_vMS": "ms1",
        "e_vUQ": "uq"}
# --- the button: prefixed, its fibers identified; what the counter's and root's posts give substituted
BMAP = {"fo": "fPU", "d": "dPU", "t": ".undefined", "g": "dPU.env", "X": "X", "H": "H", "C": "C1", "A": "C0", "R": "Rw",
        "RH": "Rc", "bG": "bG0", "VS": "VS", "RI": "RI", "CF": "CF", "CS": "CS", "Cu": "Cu", "Cx": "Cx",
        "mpv": "vMP", "mpe'": "e8", "mpc'": "c8", "tyw": "true", "tye": "r_e1", "tyc": "r_c1",
        "fl": f"(numberBinOp .bitAnd fl {L22})", "fe": "r_e2", "fc": "r_c2", "sf": Z, "se": "r_e3", "sc": "r_c3",
        "cl": "vCL", "le": "e5", "lc": "c5", "rwe": "rew", "rwc": "rec", "sbw": "true", "sbe": "e12", "sbc": "c12",
        "ppw": "true", "ppe": "e0", "ppc": "c0", "b_ppw": "true", "b_ppe": "e0", "b_ppc": "c0",
        "b_tyw": "true", "b_tye": "r_e1", "b_tyc": "r_c1", "b_msw": "true", "b_mse": "e9", "b_msc": "c9",
        "b_xrw": "true", "b_xre": "e14", "b_xrc": "c14", "b_l0": "vL", "b_lw": "e6", "b_lc": "c6",
        "b_ch0": "vC", "b_cw": "e7", "b_cc": "c7",
        "b_str": "(JSStr.ofString \"Count: \" ++ numberToJSStr xE ++ JSStr.ofString \"\")", "b_kw": "true",
        "b_ke": "true", "b_kc": "true",
        "a2": Z, "xlw2": "true", "xle2": "R_e_e6", "xlc2": "R_e_c6",
        "f2": f"(numberBinOp .bitOr (numberBinOp .bitAnd R_e_fl {L22}) {ONE})", "xfw2": "true", "xfe2": "R_e_e2",
        "xfc2": "R_e_c2", "cw2": "true", "ce2": "R_e_e7", "cc2": "R_e_c7",
        "e2": Z, "se2": "R_e_e3", "sc2": "R_e_c3", "cl2": "R_e_vCL", "le2": "R_e_e5", "lc2": "R_e_c5",
        "rwe2": "R_e_re", "rwc2": "R_e_rc", "sbw2": "true", "sbe2": "R_e_e12", "sbc2": "R_e_c12",
        "pp2": "Pp", "ppw2": "true", "ppe2": "R_e_e0", "ppc2": "R_e_c0",
        "cw3": "true", "ce3": "R_e_xce", "cc3": "R_e_xcc",
        "o0": "R_a_vr", "e0": "R_a_e0", "c0": "R_a_c0", "o1": "R_a_vf", "e1": "R_a_e1", "c1": "R_a_c1",
        "o2": "R_a_vc", "e2'": "R_a_e2", "c2": "R_a_c2", "o3": "R_b_cur", "e3'": "R_b_oe", "c3": "R_b_oc",
        "vu": "R_b_cv", "ue": "R_b_ce", "uc": "R_b_cc", "cxv": "R_cache", "xe": "R_b_xe", "xc": "R_b_xc",
        "vr": "(.obj R_C)", "re": "R_a_re", "rc": "R_a_rc", "Rb": "Rw", "fe'": "R_a_fe", "fc'": "R_a_fc",
        "vc": f"(.num {Z})", "vce": "R_a_ce", "vcc": "R_a_cc", "b_csw": "true", "b_cse": "R_a_ce", "b_csc": "R_a_cc",
        "wv": "(.obj X)"}
BDROP = {"hXpp", "b_hXpp", "b_hP1", "b_hP1k", "b_hP1c", "hP01", "b_hP01", "b_hdX", "hXmp", "hXty", "hXf", "hXs",
         "hXl", "hXr", "hXsb", "b_hXty", "b_hXms", "b_hXr", "b_hXl", "b_hXc", "hCla", "hCf", "hCc", "hCs", "hCl",
         "hCr", "hCsb", "hCpp", "hRc", "hV0", "hV1", "hV2", "hV3", "hCuc", "hCxv", "hRIc", "hCFc", "hCSc", "b_hCSc",
         "hGI", "hGIm", "hGIv", "hGWIP", "hGWIPm", "hGWIPi", "b_hGDR", "b_hGDRm", "b_hGDRi", "b_hGT", "b_hGTm",
         "b_hGTi", "b_hGS", "b_hGSm", "b_hGSi", "hGe", "b_hGe", "henv", "hlt", "hk", "hf", "hcode", "hcls", "hmode"}
def sub(ty, m):
    """Identifier substitution outside string literals."""
    parts = re.split(r'("(?:[^"\\]|\\.)*")', ty)
    return "".join(p if i % 2 else re.sub(r"(?<![\w.'])([A-Za-z_][\w']*)(?![\w'])",
                                           lambda x: m.get(x.group(1), x.group(1)), p) for i, p in enumerate(parts))
def full(m, pfx, names):
    """The callee's renaming: identified names, else prefixed."""
    out = {}
    for nm in names:
        if nm in SKIP: continue
        out[nm] = m.get(nm, pfx + nm)
    return out
rn = full(RMAP, "R_", [nm for _, nm, _ in RB])
kn = full(KMAP, "", [nm for _, nm, _ in KB])
# the button's substitutions name the counter's variables: apply the counter's substitutions to them
bn = full({k: sub(v, kn) for k, v in BMAP.items()}, "B_", [nm for _, nm, _ in BB])
# the units' levels: the root's applied at n + 5, the counter's at n, the button's at n + 4
rn["n"] = "(n + 5)"; bn["n"] = "(n + 4)"
ident = re.compile(r"^[A-Za-z_][\w']*$")
binds, prem, seen = [], [], set()
def add(B, m, drop, pfx):
    for imp, nm, ty in B:
        if nm in SKIP: continue
        t2 = sub(ty, m)
        if imp:
            n2 = m[nm]
            if not ident.match(n2) or n2 in seen or n2 in ("true", "false", "none"): continue
            seen.add(n2); binds.append(f"{{{n2} : {t2}}}")
        elif nm not in drop:
            prem.append(f"({pfx}{nm} : {t2})")
add(RB, rn, set(), "R_")
add(KB, kn, KDROP, "")
add(BB, bn, BDROP, "B_")
own_binds = ["{n : Nat}", "{h : σ}", "{s : State}", "{fWL : ObjId}", "{dWL : FuncData}", "{tWL : Value}",
             "{bdPU bdW0 : Binding}"]
own = ["(hWLo : fWL < s.heap.size) (hWLk : (s.objEntry fWL).kind = .func dWL) (hWLf : 2400 ≤ s.fuel)",
       "(hWLcode : dWL.code = WLSGen.workLoopSync_func) (hWLcls : dWL.isClassCtor = false) (hWLmode : dWL.thisMode = .strict)",
       "(hWLenv : dWL.env = dPU.env)",
       "(hGPU : bG0[JSStr.ofString \"performUnitOfWork\"]? = some bdPU) (hGPUv : bdPU.value = some (.obj fPU))",
       "(hGW0 : bG0[JSStr.ofString \"workInProgress\"]? = some bdW0) (hGW0v : bdW0.value = some (.obj Rw))",
       "(hKdEnv : K_d.env = dPU.env) (hP0 : B_P0 < s.heap.size) (hXs : X < s.heap.size)",
       "(hdXB : ∀ Y ∈ [B_b_fPH, B_b_fSS, B_b_fMR, B_b_fC, B_b_fGC, CS, B_b_fR, B_b_fI, B_b_fDel, B_b_fB], Y ≠ X)"]
# --- distinctness the frame transfers need: an object read at a property an earlier unit writes on another object
WIPK = ["pendingProps", "type", "flags", "subtreeFlags", "deletions", "childLanes", "lanes", "child", "memoizedProps",
        "memoizedState", "updateQueue", "dependencies", "sibling", "index", "ref", "refCleanup"]
ROOTW = ({("VS", k) for k in "0123"} | {(o, "current") for o in ["RI", "CF", "CS", "Cu"]} | {("Cx", "_currentValue")}
         | {("Rw", k) for k in ["dependencies", "child", "memoizedProps"]} | {("C1", k) for k in WIPK + ["return"]})
CNTW = ({("C1", k) for k in ["memoizedState", "updateQueue", "lanes", "flags", "child", "memoizedProps"]}
        | {("RSI", "H"), ("H0", "baseQueue"), ("Q", "pending"), ("Q", "lastRenderedReducer"), ("Q", "lastRenderedState")}
        | {("X", k) for k in WIPK + ["return"]})
need = set(); bad = []
def scan(B, m, drop, written):
    for imp, nm, ty in B:
        if imp or nm in drop or nm in SKIP: continue
        t2 = sub(ty, m)
        for o, kexp in re.findall(r'\(s\.objEntry (\w+)\)\.props\.get\? \(([^()]*)\)', t2):
            if not re.fullmatch(r'\.str "[^"]*"', kexp):
                for (w, kk) in written:
                    if w != o: need.add((o, w))
                continue
            k = kexp[len('.str "'):-1]
            if (o, k) in written: bad.append((nm, o, k)); continue
            for (w, kk) in written:
                if kk == k and w != o: need.add((o, w))
scan(KB, kn, KDROP, ROOTW)
scan(BB, bn, BDROP, ROOTW | CNTW)
assert not bad, bad
DIST = sorted(need)
ENVS = sorted(set(re.findall(r"Scope\.declLike\? \(s\.envEntry ([\w.]+)\)", " ".join(prem))) - {"dPU.env"})
own.append(" ".join(f"(de_{e.replace('.', '_')} : {e} ≠ dPU.env)" for e in ENVS))
own.append(" ".join(f"(dd_{o}_{w} : {o} ≠ {w})" for o, w in DIST))
stmt = ("theorem work_loop_spec " + " ".join(own_binds + binds) + "\n    " + "\n    ".join(own + prem))
open(os.path.join(ROOT, "tools", "react_wls", "stmt.txt"), "w").write(stmt)
print("binders", len(binds), "premises", len(prem), "distinct", len(DIST))

# --- the proof
FPR = "Logic.Footprint.union (ReactBeginRoot.fp dPU.env VS RI CF CS Cu Cx Rw C1) ⟨[(dPU.env, \"workInProgress\")], [(Rw, .str \"memoizedProps\")], false⟩"
FPK = "Logic.Footprint.union (fpB K_d.env C1 H0 Q RSI X) ⟨[(K_d.env, \"workInProgress\")], [(C1, .str \"memoizedProps\")], false⟩"
FPB = sub("Logic.Footprint.union (ReactBeginButton.fpBB g X) (Logic.Footprint.union ⟨[], [(X, .str \"memoizedProps\")], false⟩ (ReactCompleteUnit.fpU g VS Cu Cx CS CF RI R C X))", bn)
FP = f"Logic.Footprint.union ({FPR}) (Logic.Footprint.union ({FPK}) ({FPB}))"
FPDEFS = ("Logic.Footprint.union, ReactBeginRoot.fp, ReactEarlyBailout.fp, ReactHostContainer.fp, ReactBailout.fp, "
          "ReactCreateWIP.fp, fpB, ReactUpdateFunction.fpUF, ReactReconcileImpl.fpI, ReactBeginButton.fpBB, "
          "ReactCompleteUnit.fpU, ReactCompleteButton.fpCW, ReactCompleteButton.fpCC, ReactCompleteRoot.fpRC, "
          "List.cons_append, List.nil_append, List.mem_append, List.mem_cons")
DD = ", ".join([f"dd_{o}_{w}" for o, w in DIST] + [f"Ne.symm dd_{o}_{w}" for o, w in DIST])
stmt_full = stmt + f" :\n    WP eng answer (n + 10) h (callImpl eng (.obj fWL) tWL #[]) s fun v w h' =>\n      v = .undefined ∧ Frame ({FP}) s w ∧ s.fuel ≤ w.fuel + 2400 ∧ h' = h ∧\n      ∃ Cn F, @@FACTS@@ ∧ @@EXTRA@@ ∧\n      ReactNewProps.NewProps w Cn F OP (JSStr.ofString \"Count: \" ++ numberToJSStr xE ++ JSStr.ofString \"\") ∧\n      ∃ bm, Scope.declLike? (w.envEntry dPU.env) = some (bm, none) ∧\n      (∃ bd, bm[JSStr.ofString \"workInProgress\"]? = some bd ∧ bd.value = some .null) ∧\n      (∃ bd, bm[JSStr.ofString \"workInProgressRootExitStatus\"]? = some bd ∧ bd.value = some (.num (F64.fin false 5629499534213120 (-50))) ∧ bd.mutable = true) ∧\n      (∃ bd, bm[JSStr.ofString \"lastContextDependency\"]? = some bd ∧ bd.mutable = true) ∧\n      (∃ bd, bm[JSStr.ofString \"currentlyRenderingFiber$1\"]? = some bd ∧ bd.mutable = true)"
tmpl = open(os.path.join(ROOT, "tools", "react_wls", "tmpl.lean.in")).read()
out = tmpl.replace("@@FPK@@", FPK).replace("@@FPR@@", FPR).replace("@@FP@@", FP).replace("@@STMT@@", stmt_full).replace("@@FPDEFS@@", FPDEFS).replace("@@DD@@", DD)
bounds_file = J("ReactWorkLoop.lean")
open(bounds_file, "w").write(out)
bounds = A.caller_bounds(bounds_file, "work_loop_spec")
envb = A.caller_envbounds(bounds_file, "work_loop_spec")
# stage 1: the root's unit, objects as at the start
r1 = dict(rn); r1.update({nm: "R_" + nm for imp, nm, ty in RB if not imp})
DOMR = ("(fun w h1 hF => SRC w h1 (frame_mono (frame_trans (fp1 := {}) gF01 hF) "
        "(fun _ hq => by simpa [Logic.Footprint.union] using hq) (fun _ hq => by simpa [Logic.Footprint.union] using hq) "
        "(fun hj => by simp [Logic.Footprint.union, ReactHostContainer.fp, hj])))")
r1["n"] = "n + 5"; r1["oG"] = "none"
a1 = A.transfer(J("ReactUnitRoot.lean"), "root_spec", r1, {"hGe": "gG1"}, dict(rn), bounds, 1, "", envbounds=envb,
                objall=True, domread=DOMR, bside="trivial") + " (n := n + 5)"
out = open(bounds_file).read().replace("@@ARGS1@@", a1)
open(bounds_file, "w").write(out)

# stage 2: the counter's unit, after the root's
r2 = dict(kn); r2.update({nm: nm for imp, nm, ty in KB if not imp})
r2.update({"bdWIP": "bdW1", "bdDR": "bdD1", "bdHy": "bdH1", "wv": "(.obj C1)", "bG": "bm1", "oG": "none",
           "tPU": ".undefined", "d": "K_d", "n": "n"})
W = lambda r: f"(by rw [gW2]; exact {r})"
ex2 = {"hGe": "gG2", "hC1pp": W("r1"), "hC1ty": W("r2"), "hC1f": W("r3"), "hC1l": W("r7"), "rhRFc": W("r8"),
       "hC1mp": W("r9"), "hC1m": W("r10"), "hC1u": W("r11"), "hC1d": W("r12"),
       "hGWIP": "hbdW1", "hGWIPm": "hbdW1m", "hGWIPi": "hbdW1v", "hGDR": "hbdD1", "hGDRm": "hbdD1m",
       "hGDRi": "(by rw [hbdD1v]; rfl)", "hGHy": "hbdH1", "hGHyv": "hbdH1v",
       "hPUo": "(Nat.lt_of_lt_of_le R_hlt gZ2)", "hPUk": "(by rw [gK2 fPU R_hlt]; exact R_hk)", "hPUcode": "R_hcode",
       "hPUcls": "R_hcls", "hPUmode": "R_hmode", "hPUenv": "hKdEnv.symm", "hoG": "rfl"}
DS2 = FPDEFS + ", " + DD
a2 = A.transfer(J("ReactUnitCounter.lean"), "counter_unit_spec", r2, ex2, {}, bounds, 2, DS2, envbounds=envb,
                bside=f"(by simp [{FPDEFS}] <;> decide)", envne=" (by assumption)", protos=True)
out = open(bounds_file).read().replace("@@ARGS2@@", a2)
open(bounds_file, "w").write(out)

# stage 3: the button's unit, after the counter's
r3 = dict(bn); r3.update({nm: "B_" + nm for imp, nm, ty in BB if not imp})
r3.update({"P1": "Cn", "bdWIP": "bdW2", "b_bdDR": "bdD2", "b_bdT": "bdT2", "b_bdTS": "bdS2", "bdI": "bdI1",
           "bG": "bm2", "g": "dPU.env", "t": ".undefined"})
del r3["n"]
W3 = lambda r: f"(by rw [gW3]; exact {r})"
SIDE = f"(by simp [{FPDEFS}, {DD}])"
def T3(o, key, r, bnd):
    return (f"(by rw [gW3, props_frame hF2 (Nat.lt_of_lt_of_le {bnd} gZ2) {SIDE}, gW2']; exact {r})")
bC1 = bounds["C1"]; bRw = bounds["Rw"]; bVS = bounds["VS"]
ex3 = {"hXmp": W3("x8"), "hXty": W3("x1"), "hXf": W3("x2"), "hXs": W3("x3"), "hXl": W3("x5"), "hXr": W3("xret"),
       "hXsb": W3("x12"), "b_hXty": W3("x1"), "b_hXms": W3("x9"), "b_hXr": W3("x14"), "b_hXl": W3("x6"),
       "b_hXc": W3("x7"), "hXpp": W3("x0"), "b_hXpp": W3("x0"), "b_hP1k": W3("hCk2"), "b_hP1c": W3("hCch"),
       "hCla": W3("hC1l2"), "hCf": W3("hC1f2"), "hCc": W3("hch"),
       "b_hP1": "(by rw [gH3]; exact hCb2)",
       "hP01": "(Nat.ne_of_lt (Nat.lt_of_lt_of_le hP0 (Nat.le_trans gZ2 hCge2)))",
       "b_hP01": "(Nat.ne_of_lt (Nat.lt_of_lt_of_le hP0 (Nat.le_trans gZ2 hCge2)))",
       "b_hdX": "(fun Y hY => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hY; rcases hY with h | h | h | h | h | h | h | h | h | h | h <;> rw [h] <;> first | exact hCnX | exact hdXB _ (by simp))",
       "hCs": T3("C1", "subtreeFlags", "r4", bC1), "hCl": T3("C1", "childLanes", "r6", bC1),
       "hCr": T3("C1", "return", "r17", bC1), "hCsb": T3("C1", "sibling", "r13", bC1),
       "hCpp": T3("C1", "pendingProps", "r1", bC1), "hRc": T3("Rw", "child", "r18", bRw),
       "hV0": T3("VS", "0", "s0", bVS), "hV1": T3("VS", "1", "s1", bVS), "hV2": T3("VS", "2", "s2", bVS),
       "hV3": T3("VS", "3", "s3", bVS), "hRIc": T3("RI", "current", "sRI", bounds["RI"]),
       "hCFc": T3("CF", "current", "sCF", bounds["CF"]), "hCSc": T3("CS", "current", "sCS", bounds["CS"]),
       "b_hCSc": T3("CS", "current", "sCS", bounds["CS"]), "hCuc": T3("Cu", "current", "sCu", bounds["Cu"]),
       "hCxv": T3("Cx", "_currentValue", "sCx", bounds["Cx"]),
       "hGWIP": "hbdW2", "hGWIPm": "hbdW2m", "hGWIPi": "hbdW2v", "b_hGDR": "hbdD2", "b_hGDRm": "hbdD2m",
       "b_hGDRi": "hbdD2i", "b_hGT": "hbdT2", "b_hGTm": "hbdT2m", "b_hGTi": "hbdT2i", "b_hGS": "hbdS2",
       "b_hGSm": "hbdS2m", "b_hGSi": "hbdS2i",
       "hGI": f"(by rw [hbw2x _ (by simp [{FPDEFS}, hKdEnv] <;> decide)]; exact hbdI1)", "hGIm": "hbdI1m", "hGIv": "hbdI1v",
       "hGe": "gG3", "b_hGe": "gG3", "henv": "rfl", "hlt": "(Nat.lt_of_lt_of_le R_hlt gZ3)",
       "hk": "(by rw [gK3 fPU R_hlt]; exact R_hk)", "hcode": "R_hcode", "hcls": "R_hcls", "hmode": "R_hmode"}
DS3 = FPDEFS + ", " + DD
a3 = A.transfer(J("ReactUnitButton.lean"), "button_unit_spec", r3, ex3, {k: v for k, v in bn.items() if ident.match(v)},
                bounds, 3, DS3, envbounds=envb, bside=f"(by simp [{FPDEFS}] <;> decide) (by simp [{FPDEFS}] <;> decide)",
                envne=" (by assumption)", protos=True) + " (n := n + 4)"
sys.path.insert(0, os.path.join(ROOT, "tools", "react_commit"))
from export_facts import facts_group
from compose import _rename
FACTS = _rename(facts_group(J("ReactUnitButton.lean"), "button_unit_spec"), r3)
NF = FACTS.count("props.get?")
PROJ = " | ".join("exact hFacts3" + ".2" * i + (".1" if i < NF - 1 else "") for i in range(NF))
out = open(bounds_file).read().replace("@@ARGS3@@", a3).replace("@@FACTS@@", FACTS).replace("@@PROJ@@", PROJ)
open(bounds_file, "w").write(out)

# the fields the commit reads that the loop writes, beyond what the button's unit states: each the unit post's
# conjunct renamed through its call's arguments (variables the call leaves to unification matched against the
# stage-1 facts that supply them; the properties' attribute variables left existential), carried to the end
from export_facts import call_args
from unify import parse, match, text, subst as usubst
src = open(bounds_file).read()
from compose import binders as _binders, _theorem_header
loopnames = {n for n, k, t in _binders(bounds_file, "work_loop_spec")}
def conjs(path, thm):
    h = re.sub(r"\s+", " ", _theorem_header(path, thm)); post = h[h.rindex("fun v w h' =>"):]
    out = []
    for m in re.finditer(r"\(w\.objEntry \w+\)\.props\.get\? \(\.str \"\w+\"\) = some \(", post):
        j = m.end(); d = 1
        while d:
            d += {"(": 1, ")": -1}.get(post[j], 0); j += 1
        out.append(post[m.start():j])
    return out
RP, CP = J("ReactUnitRoot.lean"), J("ReactUnitCounter.lean")
A1, A2 = call_args(src, "ReactUnitRoot.root_spec"), call_args(src, "ReactUnitCounter.counter_unit_spec")
RC = [_rename(c, A1) for c in conjs(RP, "root_spec")]
CC = conjs(CP, "counter_unit_spec")
rfact = lambda N: RC[9 + N - 1]
cimpl = {n for n, k, t in _binders(CP, "counter_unit_spec") if k == "{"} - set(A2)
csub = {}
cb2 = dict((n, t) for n, k, t in _binders(CP, "counter_unit_spec"))
for pn, sup in ex2.items():
    m = re.fullmatch(r"\(by rw \[gW2\]; exact r(\d+)\)", sup)
    if not m or pn not in cb2: continue
    prem = re.sub(r"\s+", " ", _rename(cb2[pn].strip(), A2))
    src_f = rfact(int(m.group(1)))
    match(parse(prem.split(" = ", 1)[1]), parse(src_f.split(" = ", 1)[1]), cimpl, csub)
EX = [("r18", rfact(18), 1, "Rw"), ("r5", rfact(5), 1, "C1"), ("r13", rfact(13), 1, "C1"),
      ("hC1f2", usubst(_rename(CC[20], A2), csub), 2, "C1"), ("hch", usubst(_rename(CC[17], A2), csub), 2, "C1"),
      ("x12", usubst(_rename(CC[12], A2), csub), 2, "X")]
KEEP = {"w", "some", "true", "false", "F64", "numberBinOp", "JSStr"}
extra, haves, projs = [], [], []
for i, (hyp, c, stage, obj) in enumerate(EX):
    key = re.search(r'\.str "(\w+)"', c).group(1)
    rhs = parse(c.split(" = ", 1)[1])          # [some, [.data, V, W, E, C]]
    dat = rhs[1]
    V, W = text(dat[1]), text(dat[2])
    Vp = V if re.fullmatch(r"[\w.]+", V) else "(" + V + ")"
    stmt = lambda st: f"∃ a b, ({st}.objEntry {obj}).props.get? (.str \"{key}\") = some (.data {Vp} {W} a b)"
    extra.append(f"({stmt('w')})")
    bnd = bounds.get(obj, "hXs" if obj == "X" else None)
    chain = f"props_frame hF3 (Nat.lt_of_lt_of_le {bnd} gZ3) {SIDE}, gW3"
    if stage == 1: chain += f", props_frame hF2 (Nat.lt_of_lt_of_le {bnd} gZ2) {SIDE}, gW2'"
    haves.append(f"  have EX{i} : {stmt('wS3')} := ⟨_, _, by\n    rw [{chain}]; exact {hyp}⟩")
    projs.append(f"exact EX{i}")
OBJS3 = ["VS", "Cu", "Cx", "CS", "CF", "RI", "Rw", "C1"]
dn = ", ".join(f"Nat.ne_of_lt (Nat.lt_of_lt_of_le {bounds[o]} (Nat.le_trans gZ2 hCge2)), Ne.symm (Nat.ne_of_lt (Nat.lt_of_lt_of_le {bounds[o]} (Nat.le_trans gZ2 hCge2)))" for o in OBJS3)
haves.append(f"""  have NP3 : ReactNewProps.NewProps wS3 Cn F2 OP (JSStr.ofString "Count: " ++ numberToJSStr xE ++ JSStr.ofString "") :=
    ReactNewProps.NewProps.frame hF3 (by unfold ReactNewProps.NewProps at hNP2 ⊢; rw [gW3, gH3]; exact hNP2)
      (fun k hk => by simp [{FPDEFS}, hCnX, Ne.symm hCnX, {dn}] at hk)""")
out = open(bounds_file).read().replace("@@EXTRA@@", " ∧\n      ".join(extra)).replace("@@EXTRAHAVES@@", "\n".join(haves)).replace("@@EXTRAPROJ@@", " | ".join(projs))
open(bounds_file, "w").write(out)
print("extra", len(extra), "csub", csub)
