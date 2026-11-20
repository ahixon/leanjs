import Proofs.ArrayWrite
import Proofs.ArrayWriteGen

/-!
# Creating and writing an array: `f()` returns 9

```js
function f() { let a = [1, 2, 3]; a[1] = 5; return a[0] + a[1] + a[2]; }
```
(examples/array_write.js, generated into `Proofs/ArrayWriteGen.lean`.) The array literal creates an
array object with elements 1, 2, 3 (`array_literal`); `a[1] = 5` writes an element
(`putRefValue_element`); the reads see 1, 5, 3.
-/

open ES ES.Conv

namespace ArrayWriteEx

abbrev n0 : F64 := F64.fin false 0 (-1074)
abbrev n1 : F64 := F64.fin false 4503599627370496 (-52)
abbrev n2 : F64 := F64.fin false 4503599627370496 (-51)
abbrev n3 : F64 := F64.fin false 6755399441055744 (-51)
abbrev n5 : F64 := F64.fin false 5629499534213120 (-50)

theorem k0 : n0 = ofSmallInt (0 : Nat) := by decide
theorem k1 : n1 = ofSmallInt (1 : Nat) := by decide
theorem k2 : n2 = ofSmallInt (2 : Nat) := by decide
theorem sum9 : addF (addF n1 n5) n3 = ofSmallInt 9 := by decide

/-- The elements as `array_literal` takes them. -/
def ps : List (Sem.CExpr × Value) :=
  [(Sem.lit (Lit.num n1), .num n1), (Sem.lit (Lit.num n2), .num n2), (Sem.lit (Lit.num n3), .num n3)]

theorem ps_ev : ∀ p ∈ ps, ∀ (ctx : Ctx) (u : State), p.1 ctx u = .ok p.2 u := by
  intro p hp ctx u
  simp only [ps, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl <;> rfl

/-- **`f`'s body returns 9**, started (as a call starts it) with `a` declared, not yet initialized, in
the body's lexical environment `L`. -/
theorem f_spec (n : Nat) (ctx : Ctx) (L : EnvId) (o : Option EnvId) (b : Std.HashMap JSStr Binding) (bd : Binding)
    (hlex : ctx.lex = L) (hstr : ctx.strict = false) (hgen : ctx.isGen = false) (s0 : State) (hl : L < s0.envs.size)
    (hE : s0.envEntry L = .decl b o) (hb : b[JSStr.ofString "a"]? = some bd) (hbm : bd.mutable = true)
    (hf : 4 ≤ s0.fuel) :
    ∃ s', ArrayWriteGen.f n ctx s0 = .ok (.ret (.num (ofSmallInt 9))) s' := by
  -- `let a = [1, 2, 3]`
  have hr : resolveBinding L "a" false s0 = .ok (.env (some L) "a" false) s0 :=
    resolveBinding_here L _ false s0 hl (by rw [hE]; rfl)
      (by rw [hE]; simp [Env.bindingsMap, Std.HashMap.contains_eq_isSome_getElem?, hb]) (by omega)
  obtain ⟨t1, hlit, hA1, he1, hf1, -, -, -⟩ := array_literal { ctx with labels := #[], lex := L, strict := false, isGen := false } ps
    (fun p hp u => ps_ev p hp _ u)
    (by simp [ps]) s0
  simp only [ps, List.map_cons, List.map_nil, List.length_cons, List.length_nil] at hlit hA1
  obtain ⟨A, hAeq⟩ : ∃ A, s0.heap.size = A := ⟨_, rfl⟩
  rw [hAeq] at hlit hA1
  have hl1 : L < t1.envs.size := by rw [he1]; exact hl
  have hE1 : t1.envEntry L = .decl b o := by simp only [State.envEntry, he1]; exact hE
  have hin := initializeBinding_declLike L "a" (.obj A) t1 hl1 (by rw [hE1]; rfl)
  rw [hE1] at hin
  obtain ⟨t2, ht2⟩ : ∃ t2, t1.setEnv L ((Env.decl b o).withBindings
      (·.modify "a" fun bd => { bd with value := some (.obj A) })) = t2 := ⟨_, rfl⟩
  rw [ht2] at hin
  have hl2 : L < t2.envs.size := by rw [← ht2, State.setEnv_envs_size]; exact hl1
  have hE2 : t2.envEntry L = .decl (b.modify "a" fun bd => { bd with value := some (.obj A) }) o := by
    rw [← ht2, State.setEnv_envEntry_self _ _ _ hl1]; rfl
  let xs0 : Nat → Value := fun j => ([Value.num n1, .num n2, .num n3][j]?).getD .undefined
  have hA1' : ArrayObj A 3 xs0 t1 := hA1
  have hA2 : ArrayObj A 3 xs0 t2 := by
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hA1'
    exact ⟨by rw [← ht2, State.setEnv_heap_size]; exact a1, by rw [← ht2, State.setEnv_objEntry]; exact a2,
      by rw [← ht2, State.setEnv_objEntry]; exact a3, by rw [← ht2, State.setEnv_objEntry]; exact a4,
      fun j hj => by rw [← ht2, State.setEnv_objEntry]; exact a5 j hj,
      fun j hj hjb => by rw [← ht2, State.setEnv_objEntry]; exact a6 j hj hjb⟩
  have hf2 : t2.fuel = s0.fuel := by rw [← ht2, State.setEnv_fuel, hf1]
  have ra2 : identValue L "a" false t2 = .ok (.obj A) t2 :=
    identValue_skip0 L _ false t2 { bd with value := some (.obj A) } _ hl2 (by rw [hE2]; rfl)
      (by rw [hE2]; simp [Env.bindingsMap, Std.HashMap.getElem?_modify, hb]) rfl (by omega)
  -- `a[1] = 5`
  have hw := putRefValue_element A 3 xs0 1 (.num n5) false t2 hA2 (by omega) (by omega)
  obtain ⟨t3, ht3⟩ : ∃ t3, t2.setProp A (PropKey.ofNat 1) (.data (.num n5) true true true) = t3 := ⟨_, rfl⟩
  rw [ht3] at hw
  have hA3 := arrayObj_set A 3 xs0 1 (.num n5) t2 hA2 (by omega) (by omega)
  rw [ht3] at hA3
  have ra3 : identValue L "a" false t3 = .ok (.obj A) t3 := by
    have hl3 : L < t3.envs.size := by rw [← ht3, State.setProp_envs]; exact hl2
    have hE3 : t3.envEntry L = t2.envEntry L := by simp only [State.envEntry, ← ht3, State.setProp_envs]
    exact identValue_skip0 L _ false t3 { bd with value := some (.obj A) } _ hl3 (by rw [hE3, hE2]; rfl)
      (by rw [hE3, hE2]; simp [Env.bindingsMap, Std.HashMap.getElem?_modify, hb]) rfl
      (by rw [← ht3, State.setProp_fuel, hf2]; omega)
  have r0 := getRefValue_element A 3 _ 0 false t3 hA3 (by omega) (by omega)
  have r1 := getRefValue_element A 3 _ 1 false t3 hA3 (by omega) (by omega)
  have r2 := getRefValue_element A 3 _ 2 false t3 hA3 (by omega) (by omega)
  have r0' : getRefValue (.prop (.obj A) (.num n0) false none) t3 = .ok (.num n1) t3 := by rw [k0]; exact r0
  have r1' : getRefValue (.prop (.obj A) (.num n1) false none) t3 = .ok (.num n5) t3 := by rw [k1]; simpa using r1
  have r2' : getRefValue (.prop (.obj A) (.num n2) false none) t3 = .ok (.num n3) t3 := by rw [k2]; exact r2
  have hw' : putRefValue (.prop (.obj A) (.num n1) false none) (.num n5) t2 = .ok () t3 := by rw [k1]; exact hw
  have hf3 : t3.fuel = s0.fuel := by rw [← ht3, State.setProp_fuel, hf2]
  obtain ⟨j, hj⟩ : ∃ j, s0.fuel = j + 4 := ⟨s0.fuel - 4, by omega⟩
  have hlu : (VarKind.let == VarKind.using) = false := by decide
  have hla : (VarKind.let == VarKind.awaitUsing) = false := by decide
  simp only [ArrayWriteGen.f, Sem.stmts, M.repeatFrom, hj, M.loop]
  simp [M.bind_eq, M.bind_apply, Sem.varDecl, Sem.inner, Sem.declLex, hlex, hstr, hr, hlit, initializeRefBinding,
    hin, hlu, hla, M.forArr, pure, M.pure, Sem.exprStmt, Sem.assign, Sem.memberRef, Sem.ident, ra2, Sem.lit, litValue,
    Value.isNullish, hw', Sem.ret, Sem.binary, Sem.getValue, ra3, r0', r1', r2', Sem.binaryOp, applyBinaryOp_add_num,
    sum9, hgen, Compl.updateEmpty]

/-- The same for the interpreter itself, on `f`'s syntax tree. -/
theorem f_interp_spec (n : Nat) (ctx : Ctx) (L : EnvId) (o : Option EnvId) (b : Std.HashMap JSStr Binding)
    (bd : Binding) (hlex : ctx.lex = L) (hstr : ctx.strict = false) (hgen : ctx.isGen = false) (s0 : State)
    (hl : L < s0.envs.size) (hE : s0.envEntry L = .decl b o) (hb : b[JSStr.ofString "a"]? = some bd)
    (hbm : bd.mutable = true) (hf : 4 ≤ s0.fuel) :
    ∃ s', evalStmts (n + 38) ctx ArrayWriteGen.f_stmts s0 = .ok (.ret (.num (ofSmallInt 9))) s' := by
  rw [← congrFun (ArrayWriteGen.f_eq n) ctx]
  exact f_spec n ctx L o b bd hlex hstr hgen s0 hl hE hb hbm hf

end ArrayWriteEx
