"""Generates the proof of ReactHostContainer.call_spec (pushHostContainer) from its statement: each call by its spec
(frames), each DOM read by wp_getMemberAcc and its DomRead hypothesis, explicit facts after each call."""
import sys
sys.path.insert(0, __import__("os").path.dirname(__import__("os").path.abspath(__file__)))
from react_sig import sig, hname
p = __import__("os").path.join(__import__("os").path.dirname(__import__("os").path.abspath(__file__)), "..", "JSProofs") + "/ReactHostContainer.lean"
s = open(p).read()
head = s[:s.index("  simp only [PHCGen.pushHostContainer]\n")]
head = head[:head.rindex("  have nts0")] if "  have nts0" in head else head
tail = s[s.index("\nend\n\nend ReactHostContainer"):]
M1 = "(F64.fin true 4503599627370496 (-52))"; Z = "(F64.fin false 0 (-1074))"
ONE = "(F64.fin false 4503599627370496 (-52))"; TWO = "(F64.fin false 4503599627370496 (-51))"
KEYS = '["nodeType", "tagName", "namespaceURI"]'
T = "(by first | assumption | (simp only [js_simp]; done) | (simp only [js_simp]; omega))"
D = ["d1", "d2", "d3", "d4", "d5", "d6", "dP1", "dP2", "dP3", "dP4", "dO1", "dO2", "dO3", "dO4", "dG1", "dG2", "dG3",
     "dG4", "dC1", "dC2", "dC3", "dC4"]
base = ("hnsE, hsub, hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGI, hGIm, hGIv, hGV, hGVv, hGCS, hGCSv, hGCF, hGCFv, hGRI, "
        "hGRIv, hGP, hGPv, hGO, hGOv, hGGO, hGGOv, hGGC, hGGCv, " + ", ".join(D + ["Ne.symm " + x for x in D]) +
        ", hPenv, hOenv, nts0, nts1, nts2, List.findIdx?_toArray, List.findIdx?_cons, List.findIdx?_nil, Option.isNone_some, Option.isNone_none, Option.map_some, Option.map_none, FDI.fdiCtx, Sem.inner")
def H(name, thm, file):
    return [hname(b) for b in sig(__import__("os").path.join(__import__("os").path.dirname(__import__("os").path.abspath(__file__)), "..", "JSProofs") + "/" + file, thm, "    WP eng answer")[1]]
pushH = H("push", "push_spec", "ReactStack.lean"); popH = H("pop", "pop_spec", "ReactStack.lean")
ownH = H("o", "own_html", "ReactHostContext.lean"); chH = H("c", "child_div", "ReactHostContext.lean")
def holes(names, given): return " ".join(given.get(nm, "?_") for nm in names)
BLOCKS = []
OBJS = ["VS", "RI", "CF", "CS", "fP", "fO", "fGO", "fGC"]
kindty = {"VS": ".kind = .array", "RI": ".kind.isPlain = true", "CF": ".kind.isPlain = true", "CS": ".kind.isPlain = true",
          "fP": ".kind = .func dP", "fO": ".kind = .func dO", "fGO": ".kind = .func dGO", "fGC": ".kind = .func dGC"}
heaps = {"VS": "hVS", "RI": "hRI", "CF": "hCF", "CS": "hCS", "fP": "hPo", "fO": "hOo", "fGO": "hGOo", "fGC": "hGCo"}
kinds = {"VS": "hVSk", "RI": "hRIk", "CF": "hCFk", "CS": "hCSk", "fP": "hPk", "fO": "hOk", "fGO": "hGOk", "fGC": "hGCk"}
# prop facts: (obj,key) -> (name, value, w, e, c)
props = {("VS","0"): ("hV0","o0","true","e0","c0"), ("VS","1"): ("hV1","o1","true","e1","c1"),
         ("VS","2"): ("hV2","o2","true","e2","c2"), ("VS","length"): ("hVL","(.num L)","lw","le","lc"),
         ("RI","current"): ("hRIc","vr","true","re","rc"), ("CF","current"): ("hCFc","vf","true","fe","fc"),
         ("CS","current"): ("hCSc","vc","true","ce","cc")}
extra = []
def allf():
    return ", ".join([base] + [v[0] for v in props.values()] + list(kinds.values()) + list(heaps.values()) + extra)
lines = []; ind = 2
def emit(t):
    for l in t.split("\n"): lines.append(" " * ind + l)
def after(k, wrote, fpdef):
    """facts at w{k} after a call with frame hF{k} whose footprint has props `fpdef`"""
    global extra
    emit(f"have hE{k} : s.envs.size < w{k}.envs.size := envs_frame hF{k} {T}")
    emit(f"have hEw{k} := envEntry_frame hF{k} (e := s.envs.size) {T} (by simp [Nat.ne_of_lt hG])")
    emit(f"have hGk{k} : d.env < w{k}.envs.size := envs_frame hF{k} {T}")
    emit(f"have hEa{k} : s.envs.size < w{k}.envs.size + 1 := Nat.lt_succ_of_lt hE{k}")
    emit(f"have hEb{k} : s.envs.size ≠ w{k}.envs.size := Nat.ne_of_lt hE{k}")
    emit(f"have hGa{k} : d.env < w{k}.envs.size + 1 := Nat.lt_succ_of_lt hGk{k}")
    emit(f"have hGb{k} : d.env ≠ w{k}.envs.size := Nat.ne_of_lt hGk{k}")
    for bi, b in enumerate(BLOCKS):
        emit(f"have hBl{k}_{bi} : {b} < w{k}.envs.size := envs_frame hF{k} {T}")
        emit(f"have hBw{k}_{bi} := envEntry_frame hF{k} (e := {b}) {T} (by simp <;> omega)")
        emit(f"have hBa{k}_{bi} : {b} < w{k}.envs.size + 1 := Nat.lt_succ_of_lt hBl{k}_{bi}")
        emit(f"have hBb{k}_{bi} : {b} ≠ w{k}.envs.size := Nat.ne_of_lt hBl{k}_{bi}")
    nh, nk, np = {}, {}, {}
    for o in OBJS:
        emit(f"have hh{k}_{o} : {o} < w{k}.heap.size := heap_frame hF{k} (by first | exact {heaps[o]} | (simp only [js_simp]; exact {heaps[o]}))")
        emit(f"have kk{k}_{o} : (w{k}.objEntry {o}){kindty[o]} := by rw [kind_frame hF{k} (by first | exact {heaps[o]} | (simp only [js_simp]; exact {heaps[o]}))]; first | exact {kinds[o]} | js_norm [{allf()}]")
        nh[o] = f"hh{k}_{o}"; nk[o] = f"kk{k}_{o}"
    for (o, key), (nm, v, w, e, c) in props.items():
        if (o, key) in wrote: continue
        emit(f"have pp{k}_{o}_{key} : (w{k}.objEntry {o}).props.get? (.str \"{key}\") = some (.data {v} {w} {e} {c}) := by rw [props_frame hF{k} (by first | exact {heaps[o]} | (simp only [js_simp]; exact {heaps[o]})) (by simp [nts0, nts1, nts2, {', '.join(D + ['Ne.symm ' + x for x in D])}])]; first | exact {nm} | js_norm [{allf()}]")
        np[(o, key)] = (f"pp{k}_{o}_{key}", v, w, e, c)
    np.update(wrote)
    heaps.clear(); heaps.update(nh); kinds.clear(); kinds.update(nk); props.clear(); props.update(np)
    extra = extra + [f"hE{k}", f"hEw{k}", f"hGk{k}", f"hEa{k}", f"hEb{k}", f"hGa{k}", f"hGb{k}", f"Ne.symm hEb{k}", f"Ne.symm hGb{k}"] + sum([[f"hBl{k}_{bi}", f"hBw{k}_{bi}", f"hBa{k}_{bi}", f"hBb{k}_{bi}", f"Ne.symm hBb{k}_{bi}"] for bi in range(len(BLOCKS))], [])
def push_call(k, cu, iv, nv, key, i, value):
    global ind
    (_, cur, _, ce, cc) = props[(cu, "current")]
    (_, old, _, oe, oc) = props[("VS", key)]
    given = {"hcode": "hPcode", "hcls": "hPcls", "hmode": "hPmode", "hGe": f"?hGe{k}", "hGI": f"?hGI{k}"}
    emit(f"-- (`push`, slot {key})")
    emit(f"refine ⟨by js_norm [CallableC, {allf()}], ?_⟩")
    emit(f"refine wp_mono (ReactStack.push_spec (d := dP) (bG := ?bG{k}) (oG := oG) (bdI := ?bI{k}) (bdV := bdV) (VS := VS) (Cu := {cu}) (iv := {iv}) (nv := {nv}) (L := L) (cur := {cur}) (old := {old}) (ce := {ce}) (cc := {cc}) (oe := {oe}) (oc := {oc}) (lw := lw) (le := le) (lc := lc) (i := {i}) {holes(pushH, given)}) ?p{k}")
    emit(f"case hGe{k} => rw [hPenv]; js_norm [{allf()}]; rfl")
    emit(f"case hGI{k} => js_norm [{allf()}]; rfl")
    emit(f"all_goals first | omega | decide | (simp only [js_simp]; omega) | (js_norm [{allf()}, hGIm]; done) | (simp only [js_simp]; done) | skip")
    emit(f"case p{k} =>"); ind += 2
    emit(f"intro v{k} w{k} h{k} ⟨hv{k}, hF{k}, hfu{k}, hh{k}, hR{k}, hS{k}, hC{k}⟩\nsubst hv{k} hh{k}\nrw [hPenv] at hF{k} hR{k}\ntry simp only [js_simp] at hfu{k}")
    after(k, {("VS", key): (f"hS{k}", cur, "true", oe, oc), (cu, "current"): (f"hC{k}", value, "true", ce, cc)},
          f"(VS, PropKey.str (numberToJSStr {nv})), ({cu}, PropKey.str \"current\")")
    extra.append(f"hR{k}")
    emit(f"js_until {KEYS} [{allf()}]")
emit('have nts0 : numberToJSStr (F64.fin false 0 (-1074)) = JSStr.ofString "0" := by decide')
emit('have nts1 : numberToJSStr (F64.fin false 4503599627370496 (-52)) = JSStr.ofString "1" := by decide')
emit('have nts2 : numberToJSStr (F64.fin false 4503599627370496 (-51)) = JSStr.ofString "2" := by decide')
emit('have hsub : Conv.subF (F64.fin false 4503599627370496 (-51)) F64.one = F64.fin false 4503599627370496 (-52) := by decide')
emit('have hnsE : (JSStr.ofString "http://www.w3.org/1999/xhtml").isEmpty = false := by decide')
emit("simp only [PHCGen.pushHostContainer]")
emit(f"js_until {KEYS} [{allf()}]")
push_call(1, "RI", M1, Z, "0", 0, "(.obj C)")
push_call(2, "CF", Z, ONE, "1", 1, "(.obj X)")
push_call(3, "CS", ONE, TWO, "2", 2, ".null")
def read_step(k, key, hyp):
    global ind
    emit(f"-- (`nextRootInstance.{key}`)")
    emit("refine wp_getMemberAcc ?_")
    emit(f"js_until [] [{allf()}]")
    emit(f"refine getsAcc_mono ({hyp} _ _ ?fr{k}) ?k{k}")
    emit(f"case fr{k} => frame_go' [*, fp, nts0, nts1, nts2, hne, Ne.symm hne, hG1]")
    emit(f"case k{k} =>"); ind += 2
    emit(f"intro v{k} w{k} h{k} ⟨hv{k}, hw{k}, hh{k}⟩\nsubst hv{k} hw{k} hh{k}")
    emit(f"js_until {KEYS} [{allf()}]")
def pure_call(k, thm, names, given):
    global ind
    emit(f"refine ⟨by js_norm [CallableC, {allf()}], ?_⟩")
    emit(f"refine wp_mono ({thm} {holes(names, given)}) ?p{k}")
    emit(f"all_goals first | omega | decide | (simp only [js_simp]; omega) | (js_norm [{allf()}]; done) | skip")
    emit(f"case p{k} =>"); ind += 2
    emit(f"intro v{k} w{k} h{k} ⟨hv{k}, hF{k}, hfu{k}, hh{k}⟩\nsubst hv{k} hh{k}\ntry simp only [js_simp] at hfu{k}")
    after(k, {}, "")
    emit(f"have hGw{k} := envEntry_frame hF{k} (e := d.env) {T} (by simp)")
    extra.append(f"hGw{k}")
    emit(f"js_until {KEYS} [{allf()}]")
def pop_call(k, cu, iv, key, i):
    global ind
    (_, cur, _, ce, cc) = props[(cu, "current")]
    (_, saved, _, oe, oc) = props[("VS", key)]
    given = {"hcode": "hOcode", "hcls": "hOcls", "hmode": "hOmode", "hGe": f"?hGe{k}", "hGI": f"?hGI{k}"}
    emit(f"-- (`pop`, slot {key})")
    emit(f"refine ⟨by js_norm [CallableC, {allf()}], ?_⟩")
    emit(f"refine wp_mono (ReactStack.pop_spec (d := dO) (bG := ?bG{k}) (oG := oG) (bdI := ?bI{k}) (bdV := bdV) (VS := VS) (Cu := {cu}) (iv := {iv}) (L := L) (cur := {cur}) (saved := {saved}) (ce := {ce}) (cc := {cc}) (oe := {oe}) (oc := {oc}) (lw := lw) (le := le) (lc := lc) (i := {i}) {holes(popH, given)}) ?p{k}")
    emit(f"case hGe{k} => rw [hOenv]; js_norm [{allf()}]; rfl")
    emit(f"case hGI{k} => js_norm [{allf()}]; rfl")
    emit(f"all_goals first | omega | decide | (simp only [js_simp]; omega) | (js_norm [{allf()}, hGIm]; done) | (simp only [js_simp]; done) | skip")
    emit(f"case p{k} =>"); ind += 2
    emit(f"intro v{k} w{k} h{k} ⟨hv{k}, hF{k}, hfu{k}, hh{k}, hR{k}, hS{k}, hC{k}⟩\nsubst hv{k} hh{k}\nrw [hOenv] at hF{k} hR{k}\ntry simp only [js_simp] at hfu{k}")
    after(k, {("VS", key): (f"hS{k}", ".null", "true", oe, oc), (cu, "current"): (f"hC{k}", saved, "true", ce, cc)},
          "")
    extra.append(f"hR{k}")
    emit(f"js_until {KEYS} [{allf()}]")
read_step(4, "nodeType", "hNT")
read_step(5, "tagName", "hTN")
read_step(6, "namespaceURI", "hNS")
BLOCKS.append("w4.envs.size")
pure_call(7, "ReactHostContext.own_html (d := dGO)", ownH, {"hcode": "hGOcode", "hcls": "hGOcls", "hmode": "hGOmode"})
pure_call(8, "ReactHostContext.child_div (d := dGC)", chH, {"hcode": "hGCcode", "hcls": "hGCcls", "hmode": "hGCmode"})
pop_call(9, "CS", TWO, "2", 2)
push_call(10, "CS", ONE, TWO, "2", 2, f"(.num {Z})")
emit("all_goals (repeat' apply And.intro)")
emit(f"all_goals first | rfl | omega | (simp only [js_simp] at *; omega) | (js_norm [{allf()}]; done) | skip")
emit("case' _ => skip")
emit("all_goals first | (frame_go' [*, fp, nts0, nts1, nts2, hne, Ne.symm hne, hG1]; done) | skip")
emit("all_goals refine ⟨_, rfl, ?_, ?_⟩")
emit("· simp [hGI, hGIm]")
emit("· intro x hx; simp [Std.HashMap.getElem?_modify, Ne.symm hx]")
open(p, "w").write(head + "\n".join(lines) + "\n" + tail)
