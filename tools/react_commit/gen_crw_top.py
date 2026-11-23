"""Generates JSProofs/ReactCommitTop.lean (zippy docs/react-proofs.md): `crw_top`, completeRootWhenReady with the whole
commit at a state `w` framed from an earlier state `s` by a footprint `fpA` (the microtask's and the render's writes).
The premises about what the render writes (the work-in-progress fibers, a few FiberRoot fields and bindings) are stated
at `w`; every other premise at `s`, carried to `w` through the frame given that `fpA` leaves it alone (hcb/hcp/hco)."""
import re, sys
sys.path.insert(0, "tools/react_commit")
from compose import binders, _theorem_header

CF = "JSProofs/ReactCommitEntryFull.lean"
cb = binders(CF, "crw_full")
FIB = {"R", "CR_CM_ME_M_K", "CR_CM_LE_L_K", "CR_CM_ME_M_CT_B", "CR_CM_LE_L_B"}
FRESH = ["CR_CM_ME_M_CT_BT_NP"]
WB = {"concurrentlyUpdatedLanes", "executionContext", "isFlushingWork", "workInProgressRoot", "pendingEffectsLanes",
      "mightHavePendingSyncWork", "didScheduleMicrotask"}
S = re.compile(r"(?<![A-Za-z0-9_'.])s(?![A-Za-z0-9_'])")
bdw = {}
for n, k, t in cb:
    m = re.match(r'bG\[JSStr\.ofString "([\w$]+)"\]\? = some (\w+)$', t.strip())
    if m and m.group(1) in WB: bdw[m.group(2)] = m.group(1)
sup, kept, quant = [], [], []
kept_names, kept_props, whole = set(), set(), set()
def norm0(x):
    x = re.sub(r"\s+", " ", x)
    while True:
        y = re.sub(r"\((\w+)\)", r"\1", x)
        if y == x: return x
        x = y
for n, k, t in cb:
    if k != "(" or n in ("hG", "hGe", "hf", "hlt"): continue
    tt = norm0(t.strip())
    if tt.startswith("∀ s2"): quant.append(n); continue
    m = re.match(r'bG\[JSStr\.ofString "([\w$]+)"\]', tt)
    if m and m.group(1) in WB: sup.append(n); continue
    # objects the render creates: everything about them is at w
    if any(re.search(r"(?<![\w'])" + o + r"(?![\w'])", tt) for o in FRESH) and S.search(tt): sup.append(n); continue
    if any(tt.startswith(bd + ".") for bd in bdw): sup.append(n); continue
    m = re.match(r'\(s\.objEntry (\w+)\)\.props\.get\? \(\.str (?:\(JSStr\.ofString )?"([\w$]+)"', tt)
    if m and (m.group(1) in FIB or (m.group(1) == "FR" and m.group(2) in ("callbackNode", "callbackPriority"))
              or (m.group(1) == "CR_CM_MF_XA" and m.group(2) == "1")):
        sup.append(n); continue
    kept.append(n)
    nt = tt
    while True:
        nt2 = re.sub(r"\((\w+)\)", r"\1", nt)
        if nt2 == nt: break
        nt = nt2
    for mm in re.finditer(r'bG\[JSStr\.ofString "([\w$]+)"\]', nt): kept_names.add(mm.group(1))
    for mm in re.finditer(r'\(s\.objEntry (\w+)\)\.props\.get\? \(\.str (\(JSStr\.ofString "[\w$]+"\)|"[\w$]+"|\w+)\)', nt):
        key = mm.group(2); key = f"(JSStr.ofString {key})" if key.startswith('"') else key
        kept_props.add((mm.group(1), key))
    for mm in re.finditer(r'\(s\.objEntry (\w+)\)\.(proto|props\.keys|props\.get\? k\b|props\.toList|props =)', nt): whole.add(mm.group(1))
out_b = []
for n, k, t in cb:
    if n in ("hG", "hGe", "hf", "hlt"): continue
    if n == "s":
        out_b.append("{s : State}"); out_b.append("{w : State} {fpA : Footprint} {bW : HashMap JSStr Binding}"); continue
    if n in sup: t = re.sub(r"(?<![A-Za-z0-9_'.])bG(?=\[)", "bW", S.sub("w", t))
    if n in quant:
        t = f"∀ s3, Frame fpA s s3 → {S.sub('s3', t)}"
    if n == "CR_CM_SP_hfpE": pass
    out_b.append(f"{k}{n} : {t}{'}' if k == '{' else ')'}")
KN = ", ".join(f'JSStr.ofString "{x}"' for x in sorted(kept_names))
KP = ", ".join(f"({o}, .str {key})" for o, key in sorted(kept_props))
WH = ", ".join(sorted(whole))
conds = ["(hFA : Frame fpA s w)",
         "(hf : 59500 ≤ w.fuel) (hlt : fo < s.heap.size) (hG : d.env < s.envs.size)",
         "(hGe : Scope.declLike? (s.envEntry d.env) = some (bG, oG))",
         "(hGw : Scope.declLike? (w.envEntry d.env) = some (bW, oG))",
         f"(hcb : ∀ x, x ∈ [{KN}] → (d.env, x) ∉ fpA.binds)",
         f"(hcp : ∀ o k, (o, k) ∈ ([{KP}] : List (ObjId × PropKey)) → (o, k) ∉ fpA.props)",
         f"(hco : ∀ o, o ∈ ([{WH}] : List ObjId) → ∀ k, (o, k) ∉ fpA.props)"]
binds = "\n    ".join(out_b + conds)
hdr = _theorem_header(CF, "crw_full")
CALL = hdr[hdr.rindex("WP eng answer"):]
CALL = CALL.replace(") s fun v w h' =>", ") w fun v w' h' =>", 1)
CALL = re.sub(r"(?<![A-Za-z0-9_'.])w(?![A-Za-z0-9_'])(?=[.\s)])", "w'", CALL[CALL.index("fun v w' h' =>"):]) if False else CALL
post_i = CALL.index("fun v w' h' =>") + len("fun v w' h' =>")
post = CALL[post_i:]
post = re.sub(r"(?<![A-Za-z0-9_'.])w(?![A-Za-z0-9_'])", "w'", post)
post = S.sub("w", post)
CALL = CALL[:post_i] + post
cimp = " ".join(f"({nm} := {nm})" for nm, k, t in cb if k == "{" and nm not in ("n", "h", "s", "bG"))
qg = " ".join(f"({nm} := {nm} w hFA)" for nm in quant)
sg = " ".join(f"({nm} := {nm})" for nm in sup)
# declLike premises on another environment id: hdw along that id's chain of env equalities
eqs = {}
for n, k, t in cb:
    m = re.match(r"(\w+)\.env = (\w+)\.env$", t.strip())
    if k == "(" and m: eqs[m.group(1)] = (n, m.group(2))
def norm(x):
    while True:
        y = re.sub(r"\((\w+)\)", r"\1", x)
        if y == x: return x
        x = y
for n, k, t in cb:
    m = re.match(r"Scope\.declLike\? \(s\.envEntry (\w+)\.env\) = some \(bG, oG\)$", norm(t.strip()))
    if k == "(" and m and m.group(1) != "d" and n in kept:
        chain, x = [], m.group(1)
        while x in eqs: chain.append(eqs[x][0]); x = eqs[x][1]
        if x == "d" or x == "CR_d":
            sg += f" ({n} := by rw [{', '.join(chain)}]; exact hdw)"
RB = ("first | rebase_quick hFA | (rw [hbw _ (hcb _ (by simp))] <;> with_reducible assumption) | "
      "(rw [props_frame hFA (by with_reducible assumption) (by simpa using hcp _ _ (by simp))] <;> with_reducible assumption) | "
      "(rw [kind_frame hFA (by with_reducible assumption)] <;> with_reducible assumption) | "
      "(rw [hFA.obj_eq _ (by with_reducible assumption) (fun k hk => hco _ (by simp) k hk)] <;> with_reducible assumption)")
stmt = f"""theorem crw_top {binds} :
    {CALL} := by
  obtain ⟨bw, hdw, hbw⟩ := declLike_frame hFA hG hGe
  obtain rfl : bw = bW := by rw [hdw] at hGw; cases hGw; rfl
  refine' ReactCommitEntry.crw_full (s := w) (bG := bw) {cimp} (hf := hf) (hlt := lt_heap_of_frame hFA hlt)
    (hG := lt_envs_of_frame hFA hG) (hGe := hdw) {sg} {qg}
    (CR_CM_SP_E_hP := by rw [hFA.realms_eq]; exact CR_CM_SP_E_hP) ..
  all_goals {RB}
"""
out = f'''import JSProofs.ReactCommitEntryFull

/-!
# The click's commit at the end of its render (zippy docs/react-proofs.md)

`crw_top`: `crw_full` at a state `w` framed from an earlier state `s` by `fpA`. What the render writes is stated at
`w`; the rest at `s`, given that `fpA` leaves it alone (generated by `tools/react_commit/gen_crw_top.py`).
-/

open ES ES.M HostRuns Logic
open Std (HashMap)
open ReactFacts (BindIs PropIs SelInfo PropHas)
open ReactFlushMutation (FPRE)
open ReactSpawned (FPS FPA FP1)
open ReactCommitRootFn (FPC)
open ReactCommitEntry (FPE)

namespace ReactCommitTop

section
variable {{eng : Engine}} {{σ : Type}} {{answer : HostAnswer σ}}

set_option maxRecDepth 40000 in
set_option maxHeartbeats 8000000 in
{stmt}
end

end ReactCommitTop
'''
open("JSProofs/ReactCommitTop.lean", "w").write(out)
print(len(sup), "supplied;", len(kept), "kept;", len(quant), "quantified;", len(kept_names), "names;",
      len(kept_props), "props;", len(whole), "whole")
