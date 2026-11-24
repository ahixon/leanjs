"""Generates JSProofs/ReactMicrotaskAll.lean (zippy docs/react-proofs.md): `microtask_all`, the click's microtask with
prepareFreshStack (prep_hyp, inside microtask_render_prep), the work loop (loop_hyp) and the commit (complete_hyp)
proved. Its parameters are the three theorems', with the instantiations loop_hyp and complete_hyp made (composed)
applied throughout; left as premises: hEnsure (ensureRootIsScheduled after the commit), the host's clock, and the
host contracts and distinctness/equation premises the pieces state."""
import re, sys, io, contextlib, os
sys.path.insert(0, "tools/react_commit")
from compose import binders, _theorem_header
from unify import subst as usubst
def ws(x): return re.sub(r"\s+", " ", x).strip()
ID = re.compile(r"(?<![A-Za-z0-9_'.])([A-Za-z_][A-Za-z0-9_']*)(?![A-Za-z0-9_'])")
def load(path):
    g = {"__name__": "gen"}
    with contextlib.redirect_stdout(io.StringIO()): exec(open(path).read(), g)
    return g
GL = load("tools/react_commit/gen_react_loop.py")
GC = load("tools/react_commit/gen_react_complete.py")
LS, CS = dict(GL["sub"]), dict(GC["sub"])
def sigma(t): return usubst(usubst(t, LS), CS)
SIG = {k: sigma(v) for k, v in LS.items()}
SIG.update({k: v for k, v in CS.items() if k not in SIG})
T = binders("JSProofs/ReactMicrotaskPrep.lean", "microtask_render_prep")
L = binders("JSProofs/ReactMicrotaskLoop.lean", "loop_hyp")
C = binders("JSProofs/ReactMicrotaskComplete.lean", "complete_hyp")
RL = {"hHk": "L_hHk", "hfu": "L_hfu", "eq_0": "L_eq_0"}
RC = {"hfu": "C_hfu", "eq_0": "C_eq_0"}
def pv(v): return v if re.fullmatch(r"[\w.']+", v) else "(" + v + ")"
def rn(t, m): return ID.sub(lambda mm: m.get(mm.group(1), mm.group(1)), t)
# PRu, fpWL, kW from loop_hyp's conclusion; fpC, kC, PC from complete_hyp's
lh = ws(_theorem_header("JSProofs/ReactMicrotaskLoop.lean", "loop_hyp"))
HANDOFF = GC["HANDOFF"]
FPW = re.search(r"fun _ w' h' => Frame \((.*?)\) w w' ∧ w\.fuel ≤ w'\.fuel \+ 2400 ∧", lh).group(1)
FC, PC = GC["FC"], GC["PC"]
INST = {"PRu": HANDOFF, "fpWL": f"({FPW})", "kW": "2400", "fpC": FC, "kC": "59500", "PC": PC,
        "fpE": "(ReactEnsureRoot.fpS d.env)", "kE": "20"}
INST = {k: sigma(v) for k, v in INST.items()}
DROPT = {"r_Loop", "hComplete", "j"} | set(INST)
seen, binds, targs, largs, cargs = {}, [], [], [], []
def add(name, k, t):
    t2 = usubst(sigma(t), INST)
    if name in seen:
        if ws(seen[name]) != ws(t2): print("CLASH after sigma", name)
        return
    seen[name] = t2
    binds.append(f"{k}{name} : {t2}{'}' if k == '{' else ')'}")
ENSURE = """fun sP hP1 hP2 sW hW1 hW2 w3 w h1 hPC hHI1 hO hfw => by
      have hPC' := hPC
      obtain ⟨⟨ws, w0a, ⟨⟨s1, w0b, -, ⟨⟨w0c, ⟨-, hD⟩, hFc⟩, -⟩, hFb⟩, -⟩, hFa⟩, -⟩ := hPC
      have eg : c_CR_CM_d.env = d.env := by rw [c_CR_CM_hdenv, c_CR_hdenv, hcdenv]
      have ebG : c_bG = bG := by
        have hc := c_hGe; rw [hcdenv, hGe] at hc; simp only [Option.some.injEq, Prod.mk.injEq] at hc; exact hc.1.symm
      have eb : c_CR_CM_SP_bFSR = bdF := by
        have h0 := c_CR_CM_SP_gFSR; rw [ebG, hGF] at h0; exact (Option.some.inj h0).symm
      have eE : c_CR_CM_SP_bEn = v_bdE := by
        have h0 := c_CR_CM_SP_gEn; rw [ebG, y_hGE] at h0; exact (Option.some.inj h0).symm
      have ef : c_CR_CM_SP_fEn = v_fE := by
        have h0 := c_CR_CM_SP_gEnv; rw [eE, y_hGEv] at h0; simp only [Option.some.injEq, Value.obj.injEq] at h0; exact h0.symm
      rw [eg, eb, ef] at hD
      have hlt : d.env < sW.envs.size := Nat.lt_of_lt_of_le hG (Nat.le_trans hP1.envs_le hW1.envs_le)
      refine wp_mono (ReactEnsureAfter.ensure_call (sW := sW) (sP := sP) (Pu := Pu) hD
        (frame_trans (frame_trans (frame_trans hFc hFb) hFa) hO)
        (ReactEnsureAfter.binds_ne_of (e := sW.envs.size) (by simp [Logic.Footprint.union, ReactPerformWork.fpOwn])
          (Nat.ne_of_gt hlt))
        (by simp [Logic.Footprint.union, ReactPerformWork.fpOwn]) hfw (hPu sP hP1 hP2 sW hW1 hW2 w3 w h1 hPC' hHI1 hO)) ?_
      rintro v w' h' ⟨hS, hfu, hA, hPL, hPu', hh⟩
      exact ⟨hS, hfu, ⟨hA, hPL, hPu'⟩, by rw [hh]; exact hHI1⟩"""
for n, k, t in T:
    if n == "hEnsure":
        t2 = ws(usubst(sigma(t), INST))
        i = t2.index(" → 20 ≤ w.fuel → WP")
        add("hPu", "(", t2[:i] + " → ∀ w', Frame (ReactEnsureRoot.fpS d.env) w w' → Pu ((w'.restore sW).restore sP) h1")
        targs.append(f"(hEnsure := {ENSURE})"); continue
    if n in DROPT: continue
    if n in SIG: targs.append(f"({n} := {pv(SIG[n])})"); continue
    add(n, k, usubst(t, {"j": "(m + 10)"})); targs.append(f"({n} := {n})")
for n, k, t in L:
    if n == "n": continue
    nn = RL.get(n, n)
    if nn in SIG: largs.append(f"({n} := {pv(SIG[nn])})"); continue
    add(nn, k, usubst(rn(t, RL), {"n": "(m + 2)"})); largs.append(f"({n} := {nn})")
for n, k, t in C:
    if n == "n": continue
    nn = RC.get(n, n)
    if nn in SIG: cargs.append(f"({n} := {pv(SIG[nn])})"); continue
    add(nn, k, usubst(rn(t, RC), {"n": "m"})); cargs.append(f"({n} := {nn})")
th = ws(_theorem_header("JSProofs/ReactMicrotaskPrep.lean", "microtask_render_prep"))
CONCL = sigma(th[th.rindex("WP eng answer"):]).replace("((j + 2) + 6)", "(m + 18)")
iargs = " ".join(f"({k} := {v})" for k, v in INST.items())
binds = [b for b in binds if b.startswith("{")] + [b for b in binds if not b.startswith("{")]
stmt = (f"theorem microtask_all {{m : Nat}} " + "\n    ".join(binds) + " :\n    " + CONCL + " :=\n" +
        f"  ReactRenderClick.microtask_render_prep (j := m + 10) {iargs} {' '.join(targs)}\n" +
        f"    (r_Loop := ReactMicrotaskLoop.loop_hyp (n := m + 2) {' '.join(largs)})\n" +
        f"    (hComplete := ReactMicrotaskComplete.complete_hyp (n := m) {' '.join(cargs)})\n")
OPENS = open("JSProofs/ReactMicrotaskComplete.lean").read()
OPENS = "\n".join(l for l in OPENS.split("\n") if l.startswith("open "))
out = f'''import JSProofs.ReactMicrotaskComplete
import JSProofs.ReactEnsureAfter

/-!
# The click's microtask: render and commit proved (zippy docs/react-proofs.md)

Generated by `tools/react_commit/gen_react_all.py`.
-/

{OPENS}

namespace ReactMicrotaskAll

section
variable {{eng : Engine}} {{σ : Type}} {{answer : HostAnswer σ}} {{HI : σ → Prop}}

set_option maxRecDepth 40000 in
set_option maxHeartbeats 8000000 in
{stmt}
end

end ReactMicrotaskAll
'''
open("JSProofs/ReactMicrotaskAll.lean", "w").write(out)
print("binders", len(binds), "sigma", len(SIG))
