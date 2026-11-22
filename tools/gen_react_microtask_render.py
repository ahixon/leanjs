import sys; import os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from react_compose import compose
FPS = ["fpPF", "fpWL", "fpFQ", "fpC", "fpE"]
NAMES = ["getNextLanes", "isFlushingWork", "currentEventTransitionLane"]
extra_o = []
for nm in NAMES:
    for fp in FPS: extra_o.append(f'(n_{nm}_{fp} : (d.env, JSStr.ofString "{nm}") ∉ {fp}.binds)')
for fp in FPS: extra_o.append(f"(o_{fp} : {fp}.props.all (fun q => q.1 != fG) = true)")
extra_o.append("(o_I : I ≠ fG)")
def nprove(nm): return "simp [ReactRenderSync.fpRS, " + ", ".join(f"n_{nm}_{fp}" for fp in FPS) + "]"
TR = ("by first | exact {X} | exact heap_frame hF {X} | exact envs_frame hF {X} | "
      "(rw [kind_frame hF]; exact {X}; assumption) | "
      "(rw [props_frame hF]; exact {X}; all_goals first | assumption | simp [ReactMicrotaskClick.fpPerf, ReactSchedTaskRoot.fp])")
QV = ('(fun w h => ReactFlushSync.After w d.env oG R bdF ∧ (∃ a b c, (w.objEntry R).props.get? (.str "pendingLanes") = '
      'some (.data (.num (F64.fin false 0 (-1074))) a b c)) ∧ Pu w h)')
o = dict(path="" + os.path.join(os.path.dirname(os.path.abspath(__file__)), "..") + "/JSProofs/ReactMicrotaskClick.lean", name="microtask_click",
  marker="    WP eng answer (m + 4) h (callImpl eng (.obj c) .undefined #[]) s fun",
  thm="ReactMicrotaskClick.microtask_click", newname="microtask_render", level="(j + 6)",
  set={"m": "j + 2"}, set_txt={"m": "j + 2"},
  fp="fpP", k="kP", hole="hPerf",
  prove={"hfpB": "simp [ReactRenderSync.fpRS, List.all_append, r_fpPB, r_fpWB, r_fpFB, hfpCE, hfpEB, hG]",
         "hfpG": nprove("getNextLanes"), "hfpI": nprove("isFlushingWork"), "hfpC": nprove("currentEventTransitionLane"),
         "hfpO": "simp only [ReactRenderSync.fpRS, List.all_append, " + ", ".join(f"o_{fp}" for fp in FPS) + ", Bool.and_true]; simp [o_I]"},
  fresh=["hSenv", "hf3"],
  extra_hyps=extra_o,
  post="exact ⟨hFr, by omega, hQ.1, hQ.2.1, hQ.2.2⟩")
i = dict(path="" + os.path.join(os.path.dirname(os.path.abspath(__file__)), "..") + "/JSProofs/ReactSyncRender.lean", name="sync_render",
  marker="    WP eng answer (j + 3) h (callImpl eng (.obj fo) t #[.obj R, .num",
  thm="ReactRenderClick.sync_render",
  set={"fo": "fS", "d": "{ dS with env := d.env }", "t": ".undefined", "s": "w", "h": "h1", "bG": "bW", "Q": QV},
  set_txt={"Q": QV, "fo": "fS", "t": ".undefined"},
  pre=[(r"(?<![\w.'])d\.(code|isClassCtor|thisMode)\b", r"dS.\1")],
  shared=["eng", "σ", "answer", "j", "R", "oG"],
  self={"hlt": "heap_frame hF hSo", "hk": "by rw [kind_frame hF hSo, hSk]; cases dS; simp_all",
        "hf": "by omega", "hf2": "by omega", "hG": "envs_frame hF hG", "hGe": "hWd"},
  bG_tac="by rw [hWx _ (by simp [ReactMicrotaskClick.fpPerf])]; exact {X}",
  transfer=TR,
  pre_tac="    obtain ⟨bW, hWd, hWx⟩ := declLike_frame hF hG hGe",
  hop="(ReactMicrotaskClick.fpPerf d.env R A)", hopk="402", q="sP", pfx="v_", hpfx="y_",
  extra_hyps=["(hSenv : dS.env = d.env)"])
stmt, FP, K = compose(o, i)
hdr = '''import JSProofs.ReactSyncRender
import JSProofs.ReactMicrotaskClick

/-!
# A click's microtask down to the render's callees (zippy docs/react-proofs.md)

L3: `microtask_click` with its work (`performSyncWorkOnRoot(root, 2)`) by `sync_render`. Left as hypotheses:
`prepareFreshStack`, `workLoopSync`, `finishQueueingConcurrentUpdates` (`r_Prep`, `r_Loop`, `r_Finish`),
`completeRootWhenReady` (`hComplete`, the commit) and `ensureRootIsScheduled` (`hEnsure`), each from every state it can
start in, and the host's clock (`hClock`).
-/

open ES ES.M HostRuns Logic
open Std (HashMap)

namespace ReactRenderClick

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
'''
open("" + os.path.join(os.path.dirname(os.path.abspath(__file__)), "..") + "/JSProofs/ReactMicrotaskRender.lean", "w").write(
  hdr + stmt.replace("theorem microtask_render ", "theorem microtask_render {j : Nat} ", 1) + "\nend ReactRenderClick\n")
print(K)
