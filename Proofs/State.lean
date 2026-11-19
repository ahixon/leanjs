import Proofs.Basic
import ES.Driver

/-!
# The state primitives as rewriting rules

How the arena operations (environments, objects), state reads and updates, and exception handling
act on a state: the first layer of the call-proof library (docs/compile.md).
-/

namespace ES

variable {α β : Type}

/-! ## The monad -/

@[simp] theorem M.readS_apply (f : State → α) (s : State) : readS f s = .ok (f s) s := rfl
@[simp] theorem M.modify_apply (f : State → State) (s : State) :
    (modify f : M Unit) s = .ok () (f s) := rfl
@[simp] theorem M.throwV_apply (v : Value) (s : State) : (M.throwV v : M α) s = .err v s := rfl
@[simp] theorem M.tryCatch_apply (x : M α) (h : Value → M α) (s : State) :
    M.tryCatch x h s = M.tryCatchRes h (x s) := rfl
@[simp] theorem M.tryCatchRes_ok (h : Value → M α) (a : α) (s : State) :
    M.tryCatchRes h (.ok a s) = .ok a s := rfl
@[simp] theorem M.tryCatchRes_err (h : Value → M α) (e : Value) (s : State) :
    M.tryCatchRes h (.err e s) = h e s := rfl
@[simp] theorem M.bindRes_err (f : α → M β) (e : Value) (s : State) :
    M.bindRes f (.err e s) = .err e s := rfl
@[simp] theorem M.map_apply (f : α → β) (x : M α) (s : State) :
    (f <$> x) s = M.bindRes (fun a => M.pure (f a)) (x s) := rfl

/-- `attempt` of a computation that returns normally. -/
theorem M.attempt_ok (x : M α) (s s' : State) (a : α) (h : x s = .ok a s') :
    M.attempt x s = .ok (.ok a) s' := by
  simp [M.attempt, h]

/-! ## State updates -/

@[simp] theorem State.withEnvs_eq (s : State) (f : Array Env → Array Env) :
    s.withEnvs f = { s with envs := f s.envs } := rfl
@[simp] theorem State.withHeap_eq (s : State) (f : Array Obj → Array Obj) :
    s.withHeap f = { s with heap := f s.heap } := rfl

/-! ## Environments -/

@[simp] theorem allocEnv_apply (e : Env) (s : State) :
    allocEnv e s = .ok s.envs.size { s with envs := s.envs.push e } := rfl

@[simp] theorem modifyEnv_apply (id : EnvId) (f : Env → Env) (s : State) :
    modifyEnv id f s = .ok () { s with envs := s.envs.modify id f } := rfl

theorem readEnv_ok (id : EnvId) (f : Env → α) (s : State) (h : id < s.envs.size) :
    readEnv id f s = .ok (f s.envs[id]) s := by
  simp [readEnv, h]

/-! ## Objects -/

@[simp] theorem alloc_apply (o : Obj) (s : State) :
    alloc o s = .ok s.heap.size { s with heap := s.heap.push o } := rfl

theorem readObj_ok (id : ObjId) (f : Obj → α) (s : State) (h : id < s.heap.size) :
    readObj id f s = .ok (f s.heap[id]) s := by
  simp [readObj, h]

end ES
