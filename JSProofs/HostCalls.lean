import JSProofs.HostRuns
import JSProofs.Calls

/-!
# Calls of ECMAScript functions with host steps

`hr_callECMA_lexical`: the [[Call]] of an arrow function (lexical `this`), whose body runs (with host steps)
in a new function record: the caller's realm and script restored around it.
-/

namespace HostRuns

open ES

variable (eng : Engine) {σ : Type} (answer : HostAnswer σ)

/-- The record an arrow function's call runs its body in. -/
def arrowEnv (f : ObjId) (d : FuncData) : Env := .func {} (some d.env) .lexical .undefined f .undefined

/-- **The [[Call]] of an arrow function**: its body (`evalFunctionBody`) in a new function record (the next one),
in the function's realm and script; `this` and the arguments' count do not matter here. -/
theorem hr_callECMA_lexical {n : Nat} {h : σ} (f : ObjId) (d : FuncData) (thisArg : Value) (args : Array Value)
    (s : State) (hcls : d.isClassCtor = false) (hmode : d.thisMode = .lexical) (hasync : d.code.isAsync = false)
    (hgen : d.code.isGenerator = false) {v : Value} {w : State} {h' : σ} {k : Nat}
    (hb : HR eng answer n h (evalFunctionBody evalDepth f d s.envs.size args
      { s with realm := d.realm, script := d.script, envs := s.envs.push (arrowEnv f d) }) v w h' k) :
    HR eng answer n h (callECMA f d thisArg args s) v { w with realm := s.realm, script := s.script } h' k := by
  have hl : (d.thisMode == .lexical) = true := by rw [hmode]; rfl
  simp only [callECMA, hcls, Bool.false_eq_true, ↓reduceIte]
  apply hr_inCallee eng answer d.realm d.script _ s
  simp only [M.bind_eq, M.bind_apply, newFunctionEnv, hl, ↓reduceIte, allocEnv_apply, M.bindRes_ok,
    ordinaryCallBindThis, pure, M.pure, hasync, hgen]
  exact hb

end HostRuns
