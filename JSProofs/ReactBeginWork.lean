import JSProofs.BWGen
import JSProofs.BWSwitch
import JSProofs.FDI

/-!
# `beginWork`'s function data (shared by the counter's and the button's `beginWork` proofs)

In a module of its own so that `ReactBeginButton` need not import `ReactBeginCounter` (and rebuild with it).
-/

open ES

namespace ReactBeginCounter

theorem simpleB (d : FuncData) (hc : d.code = BWGen.beginWork_func) : FDI.Simple d := by
  constructor <;> rw [hc] <;> try rfl
  simp [BWGen.beginWork_func, Func.params, Func.info]

end ReactBeginCounter
