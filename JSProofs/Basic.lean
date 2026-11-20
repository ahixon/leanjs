import ES.Interp

/-!
# Lemmas for proofs about programs

The monad's laws as rewriting rules, and the runtime operations' behaviour on primitive values.

Simp lemmas in this library are never proved by plain `rfl` (`Eq.trans rfl rfl` instead): `simp`
applies an `rfl` lemma as a definitional step without a proof term, which leaves the kernel to check
that whole goals are definitionally equal, and in large goals it can do that by evaluating terms
(e.g. building and comparing `JSStr` byte arrays): minutes and gigabytes instead of a second.
-/

namespace ES

variable {α β : Type}

@[simp] theorem M.bind_apply (x : M α) (f : α → M β) (s : State) :
    M.bind x f s = M.bindRes f (x s) := Eq.trans rfl rfl
@[simp] theorem M.bind_eq (x : M α) (f : α → M β) : (x >>= f) = M.bind x f := Eq.trans rfl rfl
@[simp] theorem M.bindRes_ok (f : α → M β) (a : α) (s : State) : M.bindRes f (.ok a s) = f a s := Eq.trans rfl rfl
@[simp] theorem M.pure_apply (a : α) (s : State) : (pure a : M α) s = .ok a s := Eq.trans rfl rfl
@[simp] theorem M.pure_def (a : α) : (pure a : M α) = M.pure a := Eq.trans rfl rfl
@[simp] theorem M.pure_apply' (a : α) (s : State) : M.pure a s = .ok a s := Eq.trans rfl rfl
@[simp] theorem M.loopRes_inr {σ} (next : σ → State → Res α) (a : α) (s : State) :
    M.loopRes next (.ok (.inr a) s) = .ok a s := Eq.trans rfl rfl

/-- ToPrimitive of a primitive is itself. -/
@[simp] theorem toPrim_num (x : F64) (h : Option Bool) (s : State) :
    toPrim (.num x) h s = .ok (.num x) s := Eq.trans rfl rfl

@[simp] theorem toNum_num (x : F64) (s : State) : toNum (.num x) s = .ok x s := Eq.trans rfl rfl

@[simp] theorem toNumeric_num (x : F64) (s : State) : toNumeric (.num x) s = .ok (.num x) s := Eq.trans rfl rfl

/-- `+` on two Numbers is (exact, correctly rounded) Number addition. -/
@[simp] theorem applyBinaryOp_add_num (x y : F64) (s : State) :
    applyBinaryOp .add (.num x) (.num y) s = .ok (.num (Conv.addF x y)) s := Eq.trans rfl rfl

@[simp] theorem Sem.binaryOp_add (l r : Value) : Sem.binaryOp .add l r = applyBinaryOp .add l r := Eq.trans rfl rfl

@[simp] theorem applyBinaryOp_sub_num (x y : F64) (s : State) :
    applyBinaryOp .sub (.num x) (.num y) s = .ok (.num (Conv.subF x y)) s := Eq.trans rfl rfl

@[simp] theorem Sem.binaryOp_sub (l r : Value) : Sem.binaryOp .sub l r = applyBinaryOp .sub l r := Eq.trans rfl rfl

end ES
