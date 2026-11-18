/-
  Axiom audit: every correctness theorem must depend only on Lean's standard
  axioms (propext, Classical.choice, Quot.sound) — in particular not on
  `sorryAx`. `Test/run.sh` fails if `sorryAx` appears in this file's output.
-/
import LeanJS

#print axioms LeanJS.Semantics.sim_js_to_ir_expr
#print axioms LeanJS.Semantics.sim_js_to_ir_program
#print axioms LeanJS.Semantics.sim_ir_to_js_expr
#print axioms LeanJS.Semantics.sim_ir_to_js_stmts
#print axioms LeanJS.Semantics.sim_lean_to_ir_expr
#print axioms LeanJS.Semantics.sim_ir_to_lean_expr
#print axioms LeanJS.Semantics.js_roundtrip_expr
#print axioms LeanJS.Semantics.js_roundtrip_expr_prim
#print axioms LeanJS.Semantics.js_roundtrip_program
#print axioms LeanJS.Semantics.js_roundtrip_program_completes
#print axioms LeanJS.Semantics.lean_roundtrip_expr
#print axioms LeanJS.Semantics.lean_roundtrip_expr_prim
#print axioms LeanJS.Semantics.js_to_lean_expr
#print axioms LeanJS.Semantics.js_to_lean_program
#print axioms LeanJS.Semantics.lean_to_js_expr
#print axioms LeanJS.Semantics.lean_to_js_program
#print axioms LeanJS.Trans.Core.jsRoundtrip_correct
#print axioms LeanJS.Trans.Core.jsToLean_correct
#print axioms LeanJS.Trans.Core.leanToJS_correct
#print axioms LeanJS.Trans.Core.leanRoundtrip_correct
#print axioms LeanJS.Semantics.eval_deterministic
#print axioms LeanJS.Semantics.eval_fuel_mono
#print axioms LeanJS.Semantics.StoreExtends.alloc
#print axioms LeanJS.Semantics.Tests.jsIdApp_roundtrip
#print axioms LeanJS.Semantics.Tests.jsProg_roundtrip
#print axioms LeanJS.Semantics.Tests.leanIdApp_roundtrip
