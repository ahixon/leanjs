import JSProofs.FactsComposeSync
import JSProofs.FactsDischarge

/-! The counter's click in a microtask, render and commit, from start facts and pure premises alone:
`microtask_render_comp`'s obligation discharged by `facts_top` (the render's obligations, the work loop's, the stack's
preparation's and the commit's, inside it). Its premises: the start facts (`hX`), the pure ones (`hP`, among them the
host's reads and calls as frame-closed facts over the way from the start, and the start objects assumed distinct). -/

open ES Logic

set_option maxHeartbeats 80000000 in
set_option maxRecDepth 20000 in
facts_top ReactRenderClick.microtask_render_comp ob_hPerf as microtask_top
