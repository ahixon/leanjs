"""Generates JSProofs/ReactWorkLoopTop.lean (zippy docs/react-proofs.md): `wls_top`, the click's work loop at a state
`w` framed from the microtask's start `s` by `fpA` (the microtask's, renderRootSync's and prepareFreshStack's writes).
Premises about what those write (React's module bindings in WB, the fields in WRITTEN, the fuel) are stated at `w`;
the rest at `s`, carried to `w` given that `fpA` leaves them alone: the bindings (hcb), properties (hcp), whole
objects (hco) and other modules' and closures' records (hce) they read."""
import re, sys
sys.path.insert(0, "tools/react_commit")
from compose import binders, _theorem_header

CF, THM = "JSProofs/ReactWorkLoop.lean", "work_loop_spec"
cb = binders(CF, THM)
MAINENV, MAP = "dPU.env", "bG0"
SRC = open("JSProofs/ReactPrepareFresh.lean").read()
i = SRC.index("def fp (g"); PB = re.findall(r'\(g, "([\w$]+)"\)', SRC[i:SRC.index("set_option", i)])
WB = set(PB) | {"executionContext", "workInProgressTransitions", "mightHavePendingSyncWork", "didScheduleMicrotask",
                "isFlushingWork"}
CWIP = {"pendingProps", "type", "flags", "subtreeFlags", "deletions", "childLanes", "lanes", "child", "memoizedProps",
        "memoizedState", "updateQueue", "dependencies", "sibling", "index", "ref", "refCleanup"}
# prepareFreshStack's objects under the loop's names: X = Rw (createWorkInProgress), H = Rc, F/Fa = C0/C1, Qo = Q, U;
# renderRootSync's dispatchers (RSI.H, RSI.A)
WRITTEN = {"Rw": CWIP, "Rc": {"childLanes"}, "C0": {"lanes"}, "C1": {"lanes"}, "Q": {"pending"}, "U": {"next"},
           "RSI": {"H", "A"}}
S = re.compile(r"(?<![A-Za-z0-9_'.])s(?![A-Za-z0-9_'])")
def norm0(x):
    x = re.sub(r"\s+", " ", x)
    while True:
        y = re.sub(r"\((\w+)\)", r"\1", x)
        if y == x: return x
        x = y
bdw = {}
for n, k, t in cb:
    m = re.match(MAP + r'\[JSStr\.ofString "([\w$]+)"\]\? = some (\w+)$', norm0(t.strip()))
    if m and m.group(1) in WB: bdw[m.group(2)] = m.group(1)
# the module record premises: (env expr, map var)
decl = {}
for n, k, t in cb:
    m = re.match(r"Scope\.declLike\? \(s\.envEntry (\w+)\.env\) = some \((\w+), (.+)\)$", norm0(t.strip()))
    if k == "(" and m: decl[n] = (m.group(1), m.group(2))
other_env_prems = [n for n, (e, mp) in decl.items() if mp != MAP]
sup, kept = [], []
kept_names, kept_props, whole = set(), set(), set()
SKIP = {"hWLo"}
for n, k, t in cb:
    if k != "(": continue
    tt = norm0(t.strip())
    if re.search(r"≤ s\.fuel$", tt) or tt.startswith("ReactHostContainer.DomRead"): sup.append(n); continue
    m = re.match(MAP + r'\[JSStr\.ofString "([\w$]+)"\]', tt)
    if m and m.group(1) in WB: sup.append(n); continue
    if any(tt.startswith(bd + ".") for bd in bdw): sup.append(n); continue
    m = re.match(r'\(s\.objEntry (\w+)\)\.props\.get\? \(\.str (?:\(JSStr\.ofString )?"([\w$]+)"', tt)
    if m and m.group(2) in WRITTEN.get(m.group(1), ()): sup.append(n); continue
    kept.append(n)
    for mm in re.finditer(MAP + r'\[JSStr\.ofString "([\w$]+)"\]', tt): kept_names.add(mm.group(1))
    for mm in re.finditer(r'\(s\.objEntry (\w+)\)\.props\.get\? \(\.str (\(JSStr\.ofString "[\w$]+"\)|"[\w$]+"|\w+)\)', tt):
        key = mm.group(2); key = f"(JSStr.ofString {key})" if key.startswith('"') else key
        kept_props.add((mm.group(1), ".str " + key))
    for mm in re.finditer(r'\(s\.objEntry (\w+)\)\.props\.get\? \(\.sym ([\w.]+)\)', tt):
        kept_props.add((mm.group(1), ".sym " + mm.group(2)))
    for mm in re.finditer(r'\(s\.objEntry (\w+)\)\.(proto|props\.keys|props\.get\? k\b|props\.toList|props =)', tt): whole.add(mm.group(1))
OENV = sorted({f"{e}.env" for n, (e, mp) in decl.items() if mp != MAP})
out_b = []
for n, k, t in cb:
    if n == "s":
        out_b.append("{s : State}"); out_b.append("{w : State} {fpA : Footprint} {bW : HashMap JSStr Binding}"); continue
    if n in sup: t = re.sub(r"(?<![A-Za-z0-9_'.])" + MAP + r"(?=\[)", "bW", S.sub("w", t))
    out_b.append(f"{k}{n} : {t}{'}' if k == '{' else ')'}")
KN = ", ".join(f'JSStr.ofString "{x}"' for x in sorted(kept_names))
KP = ", ".join(f"({o}, {key})" for o, key in sorted(kept_props))
WH = ", ".join(sorted(whole))
conds = ["(hFA : Frame fpA s w)",
         f"(hGw : Scope.declLike? (w.envEntry {MAINENV}) = some (bW, oG))",
         f"(hcb : ∀ x, x ∈ [{KN}] → ({MAINENV}, x) ∉ fpA.binds)",
         f"(hcp : ∀ o k, (o, k) ∈ ([{KP}] : List (ObjId × PropKey)) → (o, k) ∉ fpA.props)",
         f"(hco : ∀ o, o ∈ ([{WH}] : List ObjId) → ∀ k, (o, k) ∉ fpA.props)",
         f"(hce : ∀ e, e ∈ ([{', '.join(OENV)}] : List EnvId) → ∀ x, (e, x) ∉ fpA.binds)"]
binds = "\n    ".join(out_b + conds)
hdr = _theorem_header(CF, THM)
CALL = hdr[hdr.rindex("WP eng answer"):]
CALL = CALL.replace(") s fun v w h' =>", ") w fun v w' h' =>", 1)
post_i = CALL.index("fun v w' h' =>") + len("fun v w' h' =>")
post = re.sub(r"(?<![A-Za-z0-9_'.])w(?![A-Za-z0-9_'])", "w'", CALL[post_i:])
CALL = CALL[:post_i] + S.sub("w", post)
cimp = " ".join(f"({nm} := {nm})" for nm, k, t in cb if k == "{" and nm not in ("n", "h", "s", MAP, "eng", "σ", "answer"))
sg = " ".join(f"({nm} := {nm})" for nm in sup)
# the main module's record premises: hdw (along env equalities); other records: env_eq
eqs = {}
for n, k, t in cb:
    m = re.match(r"(\w+)\.env = (\w+)\.env$", norm0(t.strip()))
    if k == "(" and m: eqs[m.group(1)] = (n, m.group(2))
for n, (e, mp) in decl.items():
    if mp == MAP:
        chain, x = [], e
        while x in eqs and f"{x}.env" != MAINENV: chain.append(eqs[x][0]); x = eqs[x][1]
        rw = f"rw [{', '.join(chain)}]; " if chain else ""
        sg += f" ({n} := by {rw}exact hdw)"
    else:
        sg += (f" ({n} := by rw [hFA.env_eq _ (by with_reducible assumption) (hce _ (by simp))]; exact {n})")
RB = ("first | rebase_quick hFA | (rw [hFA.realms_eq] <;> with_reducible assumption) | (rw [hbw _ (hcb _ (by simp))] <;> with_reducible assumption) | "
      "(rw [props_frame hFA (by with_reducible assumption) (by simpa using hcp _ _ (by simp))] <;> with_reducible assumption) | "
      "(rw [kind_frame hFA (by with_reducible assumption)] <;> with_reducible assumption) | "
      "(rw [hFA.obj_eq _ (by with_reducible assumption) (fun k hk => hco _ (by simp) k hk)] <;> with_reducible assumption)")
MAINLT = next(n for n, k, t in cb if norm0(t.strip()) == f"{MAINENV} < s.envs.size")
MAINGE = next(n for n, (e, mp) in decl.items() if mp == MAP and f"{e}.env" == MAINENV)
stmt = f"""theorem wls_top {binds} :
    {CALL} := by
  obtain ⟨bw, hdw, hbw⟩ := declLike_frame hFA {MAINLT} {MAINGE}
  obtain rfl : bw = bW := by rw [hdw] at hGw; cases hGw; rfl
  refine' ReactWorkLoop.work_loop_spec (s := w) ({MAP} := bw) {cimp} {sg} ..
  all_goals {RB}
"""
OPENS = "\n".join(l for l in open(CF).read().split("\n") if l.startswith("open "))
out = f'''import JSProofs.ReactWorkLoop
import JSProofs.Rebase

/-!
# The click's work loop after `prepareFreshStack` (zippy docs/react-proofs.md)

`wls_top`: `work_loop_spec` at a state `w` framed from the microtask's start `s` by `fpA`. What the microtask,
`renderRootSync` and `prepareFreshStack` write is stated at `w`; the rest at `s`, given that `fpA` leaves it alone
(generated by `tools/react_commit/gen_wls_top.py`).
-/

{OPENS}

namespace ReactWorkLoopTop

section
variable {{eng : Engine}} {{σ : Type}} {{answer : HostAnswer σ}} {{HI : σ → Prop}}

set_option maxRecDepth 40000 in
set_option maxHeartbeats 8000000 in
{stmt}
end

end ReactWorkLoopTop
'''
open("JSProofs/ReactWorkLoopTop.lean", "w").write(out)
print(len(sup), "supplied;", len(kept), "kept;", len(kept_names), "names;", len(kept_props), "props;", len(whole),
      "whole;", len(OENV), "other records", OENV)
