import ES.Interp

/-!
# Lemmas for proofs about programs

The monad's laws as rewriting rules, and the runtime operations' behaviour on primitive values.
-/

namespace ES

variable {α β : Type}

@[simp] theorem M.bind_apply (x : M α) (f : α → M β) (s : State) :
    M.bind x f s = M.bindRes f (x s) := rfl
@[simp] theorem M.bind_eq (x : M α) (f : α → M β) : (x >>= f) = M.bind x f := rfl
@[simp] theorem M.bindRes_ok (f : α → M β) (a : α) (s : State) : M.bindRes f (.ok a s) = f a s := rfl
@[simp] theorem M.pure_apply (a : α) (s : State) : (pure a : M α) s = .ok a s := rfl
@[simp] theorem M.pure_def (a : α) : (pure a : M α) = M.pure a := rfl
@[simp] theorem M.pure_apply' (a : α) (s : State) : M.pure a s = .ok a s := rfl
@[simp] theorem M.loopRes_inr {σ} (next : σ → State → Res α) (a : α) (s : State) :
    M.loopRes next (.ok (.inr a) s) = .ok a s := rfl

/-- ToPrimitive of a primitive is itself. -/
@[simp] theorem toPrim_num (x : F64) (h : Option Bool) (s : State) :
    toPrim (.num x) h s = .ok (.num x) s := rfl

@[simp] theorem toNum_num (x : F64) (s : State) : toNum (.num x) s = .ok x s := rfl

@[simp] theorem toNumeric_num (x : F64) (s : State) : toNumeric (.num x) s = .ok (.num x) s := rfl

/-- `+` on two Numbers is (exact, correctly rounded) Number addition. -/
@[simp] theorem applyBinaryOp_add_num (x y : F64) (s : State) :
    applyBinaryOp .add (.num x) (.num y) s = .ok (.num (Conv.addF x y)) s := rfl

@[simp] theorem Sem.binaryOp_add (l r : Value) : Sem.binaryOp .add l r = applyBinaryOp .add l r := rfl

end ES
