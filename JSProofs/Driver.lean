import JSProofs.Object

/-!
# The driver: answering requests

`drive` passes a finished result through unchanged and answers a `call` request by running the
callee (`callImpl`) one call level deeper, then resumes the continuation with its outcome.
-/

namespace ES

variable {α : Type}

theorem drive_ok (eng : Engine) (n : Nat) (a : α) (s : State) (cs : Conts) :
    drive eng n (.ok a s) cs = (.ok a s, cs) := by
  cases n <;> simp [drive, driveWith]

/-- A call request whose callee returns normally (without requests of its own): the continuation
resumes with the returned value. -/
theorem drive_call_ok (eng : Engine) (n : Nat) (f t : Value) (args : Array Value) (s : State)
    (k : Outcome → State → Res α) (cs : Conts) (v : Value) (s' : State)
    (h : callImpl eng f t args s = .ok v s') :
    drive eng (n + 1) (.req (.call f t args) s k) cs = drive eng (n + 1) (k (.normal v) s') cs := by
  simp [drive, driveWith, h, drive_ok, outcomeOf]

theorem drive_err (eng : Engine) (n : Nat) (e : Value) (s : State) (cs : Conts) :
    drive eng n (.err e s : Res α) cs = (.err e s, cs) := by
  cases n <;> simp [drive, driveWith]

/-- A call request whose callee throws: the continuation resumes with the throw. -/
theorem drive_call_err (eng : Engine) (n : Nat) (f t : Value) (args : Array Value) (s : State)
    (k : Outcome → State → Res α) (cs : Conts) (e : Value) (s' : State)
    (h : callImpl eng f t args s = .err e s') :
    drive eng (n + 1) (.req (.call f t args) s k) cs = drive eng (n + 1) (k (.throw e) s') cs := by
  simp [drive, driveWith, h, drive_err, outcomeOf]

/-- [[Call]] of an ECMAScript function object: one step of fuel, then `callECMA`. -/
theorem callImpl_func (eng : Engine) (fo : ObjId) (d : FuncData) (t : Value) (args : Array Value) (s : State)
    (hfs : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : s.fuel ≠ 0) :
    callImpl eng (.obj fo) t args s = callECMA fo d t args { s with fuel := s.fuel - 1 } := by
  have hfs' : fo < ({ s with fuel := s.fuel - 1 } : State).heap.size := hfs
  have hk' : (({ s with fuel := s.fuel - 1 } : State).objEntry fo).kind = .func d := hk
  simp [callImpl, M.tick, hf, M.bind_eq, M.bind_apply, objKind, readObj_entry' _ _ _ hfs', hk']

end ES
