/-
  Round-trip composition theorems.

  Composes per-pass forward simulation theorems into end-to-end results:
  - JS round-trip: JS →(JSToIR)→ IR →(IRToJS)→ JS'
  - Lean round-trip: Lean →(LeanToIR)→ IR →(IRToLean)→ Lean'
  - Cross-language: JS →(JSToIR)→ IR →(IRToLean)→ Lean
-/
import LeanJS.Semantics.SimJSToIR
import LeanJS.Semantics.SimIRToJS
import LeanJS.Semantics.SimLeanToIR
import LeanJS.Semantics.SimIRToLean

set_option autoImplicit true

namespace LeanJS.Semantics

open LeanJS.JS
open LeanJS.Lean
open LeanJS.IR

/-! ## ResultCorr transitivity -/

/-- ResultCorr is transitive (up to store differences) -/
theorem ResultCorr.trans
    (h1 : ResultCorr r1 r2) (h2 : ResultCorr r2 r3) :
    ResultCorr r1 r3 := by
  cases h1 <;> cases h2 <;> constructor

/-! ## JS Round-trip -/

/-- JS round-trip: if JS program evaluates, and it translates to IR and back,
    then the round-tripped JS evaluates to a corresponding result. -/
theorem js_roundtrip
    (htrans1 : JSToIRExpr tenv1 js_e ir_e tenv1')
    (htrans2 : IRToJSExpr st2 ir_e js_e' st2')
    (heval : JSEvalExpr jsenv store fuel js_e result)
    (hcorr : EnvCorr jsenv irenv store)
    : ∃ result', JSEvalExpr jsenv store fuel js_e' result' ∧
        ResultCorr result result' := by
  -- Step 1: JS → IR simulation
  obtain ⟨result_ir, heval_ir, hcorr1⟩ := sim_js_to_ir_expr htrans1 heval hcorr
  -- Step 2: IR → JS simulation
  obtain ⟨result_js', heval_js', hcorr2⟩ := sim_ir_to_js_expr htrans2 heval_ir hcorr
  -- Step 3: Compose correspondences
  exact ⟨result_js', heval_js', ResultCorr.trans hcorr1 hcorr2⟩

/-- JS round-trip for statements -/
theorem js_roundtrip_stmt
    (htrans1 : JSToIRStmt tenv1 js_s ir_e tenv1')
    (htrans2 : IRToJSExpr st2 ir_e js_e' st2')
    (heval : JSEvalStmt jsenv store fuel js_s jsenv' result)
    (hcorr : EnvCorr jsenv irenv store)
    : ∃ result', JSEvalExpr jsenv store fuel js_e' result' ∧
        ResultCorr result result' := by
  obtain ⟨result_ir, heval_ir, hcorr1⟩ := sim_js_to_ir_stmt htrans1 heval hcorr
  obtain ⟨result_js', heval_js', hcorr2⟩ := sim_ir_to_js_expr htrans2 heval_ir hcorr
  exact ⟨result_js', heval_js', ResultCorr.trans hcorr1 hcorr2⟩

/-! ## Lean Round-trip -/

/-- Lean round-trip: if Lean expr evaluates, and it translates to IR and back,
    then the round-tripped Lean expr evaluates to a corresponding result. -/
theorem lean_roundtrip
    (htrans1 : LeanToIRExpr lenv1 lean_e ir_e lenv1')
    (htrans2 : IRToLeanExpr st2 ir_e lean_e' st2')
    (heval : LeanEvalExpr leanenv store fuel lean_e result)
    (hcorr : LeanEnvCorr leanenv irenv store)
    : ∃ result', LeanEvalExpr leanenv store fuel lean_e' result' ∧
        ResultCorr result result' := by
  obtain ⟨result_ir, heval_ir, hcorr1⟩ := sim_lean_to_ir_expr htrans1 heval hcorr
  obtain ⟨result_lean', heval_lean', hcorr2⟩ := sim_ir_to_lean_expr htrans2 heval_ir hcorr
  exact ⟨result_lean', heval_lean', ResultCorr.trans hcorr1 hcorr2⟩

/-! ## Cross-language -/

/-- JS → Lean via IR: semantic preservation through the hub.
    If JS evaluates to a result, and JS→IR→Lean translates it,
    then the Lean version evaluates to a corresponding result. -/
theorem js_to_lean_via_ir
    (htrans1 : JSToIRExpr tenv1 js_e ir_e tenv1')
    (htrans2 : IRToLeanExpr st2 ir_e lean_e st2')
    (heval : JSEvalExpr jsenv store fuel js_e result_js)
    (hcorr_js : EnvCorr jsenv irenv store)
    (hcorr_lean : LeanEnvCorr leanenv irenv store)
    : ∃ result_lean, LeanEvalExpr leanenv store fuel lean_e result_lean ∧
        ResultCorr result_js result_lean := by
  obtain ⟨result_ir, heval_ir, hcorr1⟩ := sim_js_to_ir_expr htrans1 heval hcorr_js
  obtain ⟨result_lean, heval_lean, hcorr2⟩ := sim_ir_to_lean_expr htrans2 heval_ir hcorr_lean
  exact ⟨result_lean, heval_lean, ResultCorr.trans hcorr1 hcorr2⟩

/-- Lean → JS via IR: semantic preservation through the hub. -/
theorem lean_to_js_via_ir
    (htrans1 : LeanToIRExpr lenv1 lean_e ir_e lenv1')
    (htrans2 : IRToJSExpr st2 ir_e js_e st2')
    (heval : LeanEvalExpr leanenv store fuel lean_e result_lean)
    (hcorr_lean : LeanEnvCorr leanenv irenv store)
    (hcorr_js : EnvCorr jsenv irenv store)
    : ∃ result_js, JSEvalExpr jsenv store fuel js_e result_js ∧
        ResultCorr result_lean result_js := by
  obtain ⟨result_ir, heval_ir, hcorr1⟩ := sim_lean_to_ir_expr htrans1 heval hcorr_lean
  obtain ⟨result_js, heval_js, hcorr2⟩ := sim_ir_to_js_expr htrans2 heval_ir hcorr_js
  exact ⟨result_js, heval_js, ResultCorr.trans hcorr1 hcorr2⟩

end LeanJS.Semantics
