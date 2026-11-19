import Proofs.State
import Proofs.AddGen
open ES

example (f : ObjId) (d : FuncData) (env : EnvId) (s : State) (x y : F64) (k : Nat)
    (hcode : d.code = AddGen.add_func) (hmode : d.thisMode = .global)
    (henv : env < s.envs.size)
    (hE : s.envs[env] = .func {} (some d.env) .initialized (.obj 0) f .undefined)
    (hf : s.fuel = k + 1) :
    ∃ ctx s', functionDeclarationInstantiation 999998 f d env #[.num x, .num y] s = .ok ctx s' := by
  simp only [functionDeclarationInstantiation, hcode]
  simp only [AddGen.add_func, Func.strict, Func.params, Func.info, Func.body, Func.kind, Func.isAsync]
  trace_state
  sorry
