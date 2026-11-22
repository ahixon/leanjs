import sys; import os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from react_compose import compose
two = "(F64.fin false 4503599627370496 (-51))"
o = dict(path="" + os.path.join(os.path.dirname(os.path.abspath(__file__)), "..") + "/JSProofs/ReactPerformSync.lean", name="call_spec",
  marker="    WP eng answer (n + 2) h (callImpl eng (.obj fo) t #[root, lanes]) s fun",
  thm="ReactPerformSync.call_spec", newname="sync_render", level="(j + 3)",
  set={"n": "j + 1", "root": ".obj R", "lanes": ".num " + two},
  set_txt={"n": "j + 1", "root": ".obj R", "lanes": ".num " + two},
  fp="fpW", k="kW", hole="hWork",
  prove={"hfpWB": "simp [ReactRenderSync.fpRS, List.all_append, r_fpPB, r_fpWB, r_fpFB, hfpCE, hfpEB, hG]"},
  fresh=["hWenv", "hf2"],
  post="exact ⟨hFr, by omega, hQ⟩")
i = dict(path="" + os.path.join(os.path.dirname(os.path.abspath(__file__)), "..") + "/JSProofs/ReactRenderClick.lean", name="work_render",
  marker="    WP eng answer (j + 2) h (callImpl eng (.obj fo) t #[.obj R, .num",
  thm="ReactRenderClick.work_render",
  set={"fo": "fW", "d": "{ dW with env := d.env }", "t": ".undefined", "s": "w", "h": "h1", "bG": "bG", "oG": "oG",
       "Q": "(fun w h => Q (w.restore s) h)"},
  set_txt={"Q": "(fun w h => Q (w.restore s) h)", "fo": "fW", "t": ".undefined"},
  pre=[(r"(?<![\w.'])d\.(code|isClassCtor|thisMode)\b", r"dW.\1")],
  shared=["eng", "σ", "answer", "j"],
  self={"hlt": "heap_frame hF hWo", "hk": "by rw [objEntry_frame0 hF hWo, hWk]; cases dW; simp_all",
        "hf": "by omega", "hG": "envs_frame hF hG",
        "hGe": "by show Scope.declLike? (w.envEntry d.env) = _; rw [envEntry_frame0 hF hG]; exact hGe"},
  hop="{}", hopk="70", q="sW", pfx="w_", hpfx="x_",
  extra_hyps=["(hWenv : dW.env = d.env)", "(hf2 : kP + kW + kF + kC + kE + 900 ≤ s.fuel)"])
stmt, FP, K = compose(o, i)
hdr = '''import JSProofs.ReactRenderClick
import JSProofs.ReactPerformSync

/-!
# The render from `performSyncWorkOnRoot` (zippy docs/react-proofs.md)

L2: `performSyncWorkOnRoot(root, 2)` over `work_render`. The callees' hypotheses hold from every state the work can
start in (`∀ sW, Frame {} s sW → …`).
-/

open ES ES.M HostRuns Logic
open Std (HashMap)

namespace ReactRenderClick

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 20000 in
'''
open("" + os.path.join(os.path.dirname(os.path.abspath(__file__)), "..") + "/JSProofs/ReactSyncRender.lean", "w").write(
  hdr + stmt.replace("theorem sync_render ", "theorem sync_render {eng : Engine} {σ : Type} {answer : HostAnswer σ} {j : Nat} ", 1)
  + "\nend ReactRenderClick\n")
print(K)
