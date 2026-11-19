import Proofs.AddGen
import Proofs.Basic
open ES

/-! A proof about a program: `function add(a, b) { return a + b }` (examples/add.js, generated
into `Proofs/AddGen.lean` by `leanjs compile --defs`) returns the sum of two Numbers. -/

namespace AddProof

/-- With `a` and `b` bound to Numbers `x` and `y`, `add`'s body returns `x + y` (exact Number
addition) and changes nothing. -/
theorem add_spec (n f : Nat) (ctx : Ctx) (s : State) (x y : F64)
    (ha : identValue ctx.lex "a" ctx.strict s = .ok (.num x) s)
    (hb : identValue ctx.lex "b" ctx.strict s = .ok (.num y) s)
    (hg : ctx.isGen = false) (hf : s.fuel = f + 1) :
    AddGen.add n ctx s = .ok (.ret (.num (Conv.addF x y))) s := by
  simp [AddGen.add, Sem.stmts, M.repeatFrom, hf, M.loop, Sem.ret, Sem.binary, Sem.ident, Sem.inner,
    hg, ha, hb, Compl.updateEmpty]
  rfl

/-- The same for the interpreter itself, on add's syntax tree (via the generated theorem). -/
theorem add_interp_spec (n f : Nat) (ctx : Ctx) (s : State) (x y : F64)
    (ha : identValue ctx.lex "a" ctx.strict s = .ok (.num x) s)
    (hb : identValue ctx.lex "b" ctx.strict s = .ok (.num y) s)
    (hg : ctx.isGen = false) (hf : s.fuel = f + 1) :
    ES.evalStmts (n + 23) ctx AddGen.add_stmts s = .ok (.ret (.num (Conv.addF x y))) s := by
  rw [← congrFun (AddGen.add_eq n) ctx]
  exact add_spec n f ctx s x y ha hb hg hf

end AddProof
