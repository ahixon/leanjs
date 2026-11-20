import Proofs.Total
import Proofs.ArrayWrite
import Proofs.DoubleGen

/-!
# A loop that writes: `double(a)` doubles every element of `a` in place

```js
function double(a) { for (let i = 0; i < a.length; i = i + 1) { a[i] = a[i] + a[i]; } }
```
(examples/double.js, generated into `Proofs/DoubleGen.lean`.) The invariant is about the heap: after
`k` iterations the array holds `2 · xs j` for `j < k` and `xs j` beyond.
-/

open ES ES.Conv SumProof SumForProof TotalProof

namespace DoubleProof

def initD : Sem.ForInitD := (Sem.ForInitD.lex VarKind.let #[(VarDeclarator.mk (Pattern.ident "i") (some (Expr.lit (Lit.num (F64.fin false 0 (-1074))))))] (Sem.varDecl #[(Sem.declLex VarKind.let "i" (some (Sem.lit (Lit.num (F64.fin false 0 (-1074))))))]))
def testD : Option Sem.CExpr := (some (Sem.binary BinOp.lt (Sem.ident "i") (Sem.getValue (Sem.memberRef (Sem.ident "a") (Sem.Key.name "length") false))))
def updD : Option Sem.CExpr := (some (Sem.assign (Sem.identRef "i") (Sem.binary BinOp.add (Sem.ident "i") (Sem.lit (Lit.num (F64.fin false 4503599627370496 (-52)))))))
def bodyD : Sem.CStmt := (Sem.block (lexicallyScoped #[(Stmt.expr (Expr.assign AssignOp.assign (Pattern.expr (Expr.member (Expr.ident "a") (MemberKey.computed (Expr.ident "i")) false)) (Expr.binary BinOp.add (Expr.member (Expr.ident "a") (MemberKey.computed (Expr.ident "i")) false) (Expr.member (Expr.ident "a") (MemberKey.computed (Expr.ident "i")) false))))]) #[(Sem.exprStmt (Sem.assign (Sem.memberRef (Sem.ident "a") (Sem.Key.computed (Sem.ident "i")) false) (Sem.binary BinOp.add (Sem.getValue (Sem.memberRef (Sem.ident "a") (Sem.Key.computed (Sem.ident "i")) false)) (Sem.getValue (Sem.memberRef (Sem.ident "a") (Sem.Key.computed (Sem.ident "i")) false)))))])

theorem lexBodyD : (lexicallyScoped #[(Stmt.expr (Expr.assign AssignOp.assign (Pattern.expr (Expr.member (Expr.ident "a") (MemberKey.computed (Expr.ident "i")) false)) (Expr.binary BinOp.add (Expr.member (Expr.ident "a") (MemberKey.computed (Expr.ident "i")) false) (Expr.member (Expr.ident "a") (MemberKey.computed (Expr.ident "i")) false))))]) = #[] := by rfl

/-- The array after `k` iterations: elements below `k` doubled. -/
def dbl (xs : Nat → Nat) (k : Nat) : Nat → Value := fun j => num ((if j < k then 2 * xs j else xs j : Nat) : Int)

/-- The environments in iteration with `i = iv`; `a` (in `F`, outside the body's `L`) is `A`. -/
def ShapeD (E L F A : Nat) (iv : Option Value) (t : State) : Prop :=
  E < t.envs.size ∧ L < t.envs.size ∧ F < t.envs.size ∧ E ≠ L ∧ E ≠ F ∧ L ≠ F ∧
  (∃ bE bdi, t.envEntry E = .decl bE (some L) ∧ bE[JSStr.ofString "i"]? = some bdi ∧ bdi.value = iv ∧
    bdi.mutable = true ∧ bE[JSStr.ofString "a"]? = none) ∧
  (∃ bL, t.envEntry L = .decl bL (some F) ∧ bL[JSStr.ofString "a"]? = none) ∧
  (∃ bF o ts tv fo nt bn, t.envEntry F = .func bF o ts tv fo nt ∧ bF[JSStr.ofString "a"]? = some bn ∧
    bn.value = some (.obj A))

theorem dbl_succ (xs : Nat → Nat) (k : Nat) :
    (fun j => if j = k then num ((2 * xs k : Nat) : Int) else dbl xs k j) = dbl xs (k + 1) := by
  funext j; simp only [dbl]
  by_cases h : j = k
  · subst h; simp
  · by_cases h2 : j < k
    · simp [h, h2, show j < k + 1 by omega]
    · simp [h, h2, show ¬ j < k + 1 by omega]

/-- One iteration that continues: element `k` is doubled; `i = k + 1` in the fresh copy `E'`. -/
theorem iterD_cont (ctx : Ctx) (labels : Array JSStr) (E L F A : EnvId) (len k : Nat) (xs : Nat → Nat)
    (hstr : ctx.strict = false) (hk : k < len) (hlen : len < 2 ^ 26) (hx : ∀ j < len, xs j < 2 ^ 26) (t : State)
    (v : Value) (hS : ShapeD E L F A (some (num k)) t) (hA : ArrayObj A len (dbl xs k) t) (hf : 5 ≤ t.fuel) :
    ∃ E' v' t', forIter testD updD bodyD labels ctx #["i"] (E, v) t = .ok (.inl (E', v')) t' ∧
      ShapeD E' L F A (some (num ((k : Int) + 1))) t' ∧ ArrayObj A len (dbl xs (k + 1)) t' ∧
      t'.fuel = t.fuel - 1 := by
  obtain ⟨hE, hL, hF, hEL, hEF, hLF, ⟨bE, bdi, hEE, hbi, hiv, him, hbn⟩, ⟨bL, hLE, hln⟩,
    ⟨bF, o, ts, tv, fo, nt, bn, hFE, hbF, hbnv⟩⟩ := hS
  have hA' := hA
  obtain ⟨hAs, hAk, -, hAl, -, -⟩ := hA
  have hkb : (k : Int).natAbs < intBound := by simp only [intBound]; omega
  have hNb : (len : Int).natAbs < intBound := by simp only [intBound]; omega
  have hxb : (xs k : Int).natAbs < intBound := by have := hx k hk; simp only [intBound]; omega
  have hx2b : ((2 * xs k : Nat) : Int).natAbs < intBound := by have := hx k hk; simp only [intBound]; omega
  have hk1b : ((k : Int) + 1).natAbs < intBound := by simp only [intBound]; omega
  -- the tick
  obtain ⟨t1, ht1⟩ : ∃ t1, ({ t with fuel := t.fuel - 1 } : State) = t1 := ⟨_, rfl⟩
  have e1 : ∀ x, t1.envEntry x = t.envEntry x := by intro x; rw [← ht1]; rfl
  have z1 : t1.envs.size = t.envs.size := by rw [← ht1]
  have f1 : t1.fuel = t.fuel - 1 := by rw [← ht1]
  have htick : M.tick t = .ok () t1 := by rw [← ht1]; simp [M.tick, show t.fuel ≠ 0 by omega]
  have h1E : E < t1.envs.size := by rw [z1]; exact hE
  have h1L : L < t1.envs.size := by rw [z1]; exact hL
  have h1F : F < t1.envs.size := by rw [z1]; exact hF
  have hA1 : ArrayObj A len (dbl xs k) t1 := by rw [← ht1]; exact hA'
  -- the test: `i < a.length`
  have ri : identValue E "i" false t1 = .ok (num k) t1 :=
    identValue_skip0 E _ false t1 bdi _ h1E (by rw [e1, hEE]; rfl) (by rw [e1, hEE]; exact hbi) hiv (by omega)
  have ra : identValue E "a" false t1 = .ok (.obj A) t1 :=
    identValue_skip2 E L F _ false t1 bE bL bn _ h1E (by rw [e1]; exact hEE) hbn h1L
      (by rw [e1]; exact hLE) hln h1F (by rw [e1, hFE]; rfl) (by rw [e1, hFE]; exact hbF) hbnv (by omega)
  have rlen : getRefValue (.prop (.obj A) (.str (JSStr.ofString "length")) false none) t1 = .ok (num len) t1 :=
    getRefValue_name A _ false t1 _ true false false (by rw [← ht1]; exact hAs) (by rw [← ht1]; exact hAk)
      (by rw [← ht1, ← kLength_eq]; exact hAl)
  have hlt : ltF (ofSmallInt k) (ofSmallInt len) = true := by rw [ltF_int _ _ hkb hNb]; simp [hk]
  -- the body: `a[i] = a[i] + a[i]`
  have rx : getRefValue (.prop (.obj A) (.num (ofSmallInt k)) false none) t1 = .ok (num (xs k)) t1 := by
    have := getRefValue_element A len (dbl xs k) k false t1 hA1 hk hlen
    simpa [dbl] using this
  have hadd : addF (ofSmallInt (xs k)) (ofSmallInt (xs k)) = ofSmallInt (2 * (xs k : Int)) := by
    rw [addF_int _ _ hxb hxb (by have := hx k hk; simp only [intBound]; omega)]; congr 1; omega
  have hcast : ((2 * xs k : Nat) : Int) = 2 * (xs k : Int) := by omega
  have hw := putRefValue_element A len (dbl xs k) k (num (2 * (xs k : Int))) false t1 hA1 hk hlen
  obtain ⟨t2, ht2⟩ : ∃ t2, t1.setProp A (PropKey.ofNat k) (.data (num (2 * (xs k : Int))) true true true) = t2 :=
    ⟨_, rfl⟩
  rw [ht2] at hw
  have hA2 : ArrayObj A len (dbl xs (k + 1)) t2 := by
    have := arrayObj_set A len (dbl xs k) k (num (2 * (xs k : Int))) t1 hA1 hk hlen
    rw [ht2, ← hcast, dbl_succ] at this; exact this
  have z2 : t2.envs.size = t.envs.size := by rw [← ht2, State.setProp_envs, z1]
  have f2 : t2.fuel = t.fuel - 1 := by rw [← ht2, State.setProp_fuel, f1]
  have e2 : ∀ x, t2.envEntry x = t.envEntry x := by
    intro x; simp only [State.envEntry, ← ht2, State.setProp_envs]; exact e1 x
  -- the copy of the loop environment
  have hpi := perIterationEnv_one "i" E L t2 bE bdi (num k) (by rw [z2]; exact hE) (by rw [e2]; exact hEE) hbi hiv
  obtain ⟨E', hE'⟩ : ∃ E', t2.envs.size = E' := ⟨_, rfl⟩
  obtain ⟨bE', hbE'⟩ : ∃ b, ((∅ : Std.HashMap JSStr Binding).insert "i" { deletable := false }).modify "i"
    (fun bd => { bd with value := some (num k) }) = b := ⟨_, rfl⟩
  rw [hE', hbE'] at hpi
  obtain ⟨t3, ht3⟩ : ∃ t3, (t2.pushEnv (.decl {} (some L))).setEnv E' (.decl bE' (some L)) = t3 := ⟨_, rfl⟩
  rw [ht3] at hpi
  have z3 : t3.envs.size = t.envs.size + 1 := by rw [← ht3, State.setEnv_envs_size, State.pushEnv_size, z2]
  have f3 : t3.fuel = t.fuel - 1 := by rw [← ht3, State.setEnv_fuel, State.pushEnv_fuel, f2]
  have hE'lt : E' < t3.envs.size := by rw [z3, ← hE', z2]; exact Nat.lt_succ_self _
  have e3E' : t3.envEntry E' = .decl bE' (some L) := by
    rw [← ht3]; exact State.setEnv_envEntry_self _ _ _ (by rw [State.pushEnv_size, ← hE']; exact Nat.lt_succ_self _)
  have hbi' : bE'[JSStr.ofString "i"]? = some { value := some (num k), deletable := false } := by
    rw [← hbE']; simp [Std.HashMap.getElem?_modify]
  -- the update: `i = i + 1` in the copy
  have ri3 : identValue E' "i" false t3 = .ok (num k) t3 :=
    identValue_skip0 E' _ false t3 _ _ hE'lt (by rw [e3E']; rfl) (by rw [e3E']; exact hbi') rfl (by omega)
  have rri3 : resolveBinding E' "i" false t3 = .ok (.env (some E') "i" false) t3 := by
    obtain ⟨j, hj⟩ : ∃ j, t3.fuel = j + 1 := ⟨t3.fuel - 1, by omega⟩
    rw [resolveBinding_loop, hj, resolveBody_found j E' _ false t3 hE'lt (by rw [e3E']; rfl)
      (by rw [e3E']; simp [Env.bindingsMap, Std.HashMap.contains_eq_isSome_getElem?, hbi'])]
  have hadd_i : addF (ofSmallInt k) (ofSmallInt 1) = ofSmallInt ((k : Int) + 1) := by
    rw [addF_int _ _ hkb (by simp [intBound]) (by simpa using hk1b)]
  have hset_i := setMutableBinding_decl E' "i" (num ((k : Int) + 1)) false t3 bE' (some L) _ hE'lt e3E' hbi'
    (by simp) (by simp)
  obtain ⟨t4, ht4⟩ : ∃ t4, t3.setEnv E' (.decl (bE'.modify "i" fun bd => { bd with value := some (num ((k : Int) + 1)) })
      (some L)) = t4 := ⟨_, rfl⟩
  rw [ht4] at hset_i
  have z4 : t4.envs.size = t.envs.size + 1 := by rw [← ht4, State.setEnv_envs_size, z3]
  have f4 : t4.fuel = t.fuel - 1 := by rw [← ht4, State.setEnv_fuel, f3]
  have hLE' : L ≠ E' := by rw [← hE']; exact Nat.ne_of_lt (show L < t2.envs.size by rw [z2]; exact hL)
  have hFE' : F ≠ E' := by rw [← hE']; exact Nat.ne_of_lt (show F < t2.envs.size by rw [z2]; exact hF)
  have e4 : ∀ x, x ≠ E' → x < t2.envs.size → t4.envEntry x = t2.envEntry x := by
    intro x hx hlt
    rw [← ht4, State.setEnv_envEntry_ne _ _ _ _ (Ne.symm hx), ← ht3, State.setEnv_envEntry_ne _ _ _ _ (Ne.symm hx),
      State.pushEnv_entry_lt _ _ _ hlt]
  have hS4 : ShapeD E' L F A (some (num ((k : Int) + 1))) t4 := by
    refine ⟨by rw [z4, ← hE', z2]; exact Nat.lt_succ_self _, by rw [z4]; exact Nat.lt_succ_of_lt hL,
      by rw [z4]; exact Nat.lt_succ_of_lt hF, Ne.symm hLE', Ne.symm hFE', hLF, ?_, ?_, ?_⟩
    · refine ⟨bE'.modify "i" fun bd => { bd with value := some (num ((k : Int) + 1)) },
        { value := some (num ((k : Int) + 1)), deletable := false }, ?_, ?_, rfl, rfl, ?_⟩
      · rw [← ht4]; exact State.setEnv_envEntry_self _ _ _ hE'lt
      · rw [← hbE']; simp [Std.HashMap.getElem?_modify]
      · rw [← hbE']; simp [Std.HashMap.getElem?_modify, Std.HashMap.getElem?_insert, ne_ia]
    · exact ⟨bL, by rw [e4 L hLE' (by rw [z2]; exact hL), e2, hLE], hln⟩
    · exact ⟨bF, o, ts, tv, fo, nt, bn, by rw [e4 F hFE' (by rw [z2]; exact hF), e2, hFE], hbF, hbnv⟩
  have hA4 : ArrayObj A len (dbl xs (k + 1)) t4 := by
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hA2
    have o4 : ∀ x, t4.objEntry x = t2.objEntry x := by
      intro x; rw [← ht4, State.setEnv_objEntry, ← ht3, State.setEnv_objEntry, State.pushEnv_objEntry]
    have h4 : t4.heap.size = t2.heap.size := by
      rw [← ht4, State.setEnv_heap_size, ← ht3, State.setEnv_heap_size, State.pushEnv_heap_size]
    exact ⟨by rw [h4]; exact a1, by rw [o4]; exact a2, by rw [o4]; exact a3, by rw [o4]; exact a4,
      fun j hj => by rw [o4]; exact a5 j hj, fun j hj hjb => by rw [o4]; exact a6 j hj hjb⟩
  have hpe : putRefValue (.env (some E') "i" false) (num ((k : Int) + 1)) t3 = .ok () t4 := by
    simp [putRefValue, hset_i]
  refine ⟨E', num (2 * (xs k : Int)), t4, ?_, hS4, hA4, f4⟩
  obtain ⟨j, hj⟩ : ∃ j, t1.fuel = j + 2 := ⟨t1.fuel - 2, by omega⟩
  simp only [forIter, M.bind_eq, M.bind_apply, htick, M.bindRes_ok, testD, Sem.binary, Sem.ident, hstr, ri, ra,
    Sem.getValue, Sem.memberRef, Value.isNullish, Bool.and_false, Bool.false_eq_true, ↓reduceIte, rlen]
  simp [Sem.binaryOp, isLessThan, M.bind_eq, M.bind_apply, hlt, ofSmallInt_eq_nan, toBoolean, pure, M.pure, bodyD,
    lexBodyD, Sem.block, Sem.stmts, M.repeatFrom, hj, M.loop, Sem.exprStmt, Sem.assign, Sem.inner, hstr,
    Sem.binary, Sem.ident, ri, ra, Sem.getValue, Sem.memberRef, Value.isNullish, rx, rlen, applyBinaryOp_add_num,
    hadd, hw, loopContinues, Compl.value?, hpi, updD, rri3, ri3, Sem.lit, litValue, one_eq, hadd_i, hset_i,
    Sem.identRef, hpe]

/-- The last iteration: `i < a.length` fails. -/
theorem iterD_exit (ctx : Ctx) (labels : Array JSStr) (E L F A : EnvId) (len : Nat) (xs : Nat → Nat)
    (hstr : ctx.strict = false) (hlen : len < 2 ^ 26) (t : State) (v : Value)
    (hS : ShapeD E L F A (some (num len)) t) (hA : ArrayObj A len (dbl xs len) t) (hf : 4 ≤ t.fuel) :
    ∃ t', forIter testD updD bodyD labels ctx #["i"] (E, v) t = .ok (.inr (.normal (some v))) t' ∧
      ShapeD E L F A (some (num len)) t' ∧ t'.fuel = t.fuel - 1 ∧
      (∀ o, t'.objEntry o = t.objEntry o) ∧ t'.heap.size = t.heap.size := by
  obtain ⟨hAs, hAk, -, hAl, -, -⟩ := hA
  have hS' := hS
  obtain ⟨hE, hL, hF, -, -, -, ⟨bE, bdi, hEE, hbi, hiv, -, hbn⟩, ⟨bL, hLE, hln⟩,
    ⟨bF, o, ts, tv, fo, nt, bn, hFE, hbF, hbnv⟩⟩ := hS
  have hNb : (len : Int).natAbs < intBound := by simp only [intBound]; omega
  obtain ⟨t1, ht1⟩ : ∃ t1, ({ t with fuel := t.fuel - 1 } : State) = t1 := ⟨_, rfl⟩
  have e1 : ∀ x, t1.envEntry x = t.envEntry x := by intro x; rw [← ht1]; rfl
  have z1 : t1.envs.size = t.envs.size := by rw [← ht1]
  have f1 : t1.fuel = t.fuel - 1 := by rw [← ht1]
  have htick : M.tick t = .ok () t1 := by rw [← ht1]; simp [M.tick, show t.fuel ≠ 0 by omega]
  have h1E : E < t1.envs.size := by rw [z1]; exact hE
  have h1L : L < t1.envs.size := by rw [z1]; exact hL
  have h1F : F < t1.envs.size := by rw [z1]; exact hF
  have ri : identValue E "i" false t1 = .ok (num len) t1 :=
    identValue_skip0 E _ false t1 bdi _ h1E (by rw [e1, hEE]; rfl) (by rw [e1, hEE]; exact hbi) hiv (by omega)
  have ra : identValue E "a" false t1 = .ok (.obj A) t1 :=
    identValue_skip2 E L F _ false t1 bE bL bn _ h1E (by rw [e1]; exact hEE) hbn h1L
      (by rw [e1]; exact hLE) hln h1F (by rw [e1, hFE]; rfl) (by rw [e1, hFE]; exact hbF) hbnv (by omega)
  have oA : ∀ x, t1.objEntry x = t.objEntry x := by intro x; rw [← ht1]; rfl
  have hA1 : A < t1.heap.size := by rw [← ht1]; exact hAs
  have rlen : getRefValue (.prop (.obj A) (.str (JSStr.ofString "length")) false none) t1 = .ok (num len) t1 :=
    getRefValue_name A _ false t1 _ true false false hA1 (by rw [oA]; exact hAk) (by rw [oA, ← kLength_eq]; exact hAl)
  have hlt : ltF (ofSmallInt len) (ofSmallInt len) = false := by rw [ltF_int _ _ hNb hNb]; simp
  refine ⟨t1, ?_, by rw [← ht1]; exact hS', f1, oA, by rw [← ht1]⟩
  simp only [forIter, M.bind_eq, M.bind_apply, htick, M.bindRes_ok, testD, Sem.binary, Sem.ident, hstr, ri, ra,
    Sem.getValue, Sem.memberRef, Value.isNullish, Bool.and_false, Bool.false_eq_true, ↓reduceIte, rlen]
  simp [Sem.binaryOp, isLessThan, M.bind_eq, M.bind_apply, hlt, ofSmallInt_eq_nan, toBoolean, pure, M.pure, rlen]

/-- The loop, from the first iteration's environment with `i = 0` and `s = tri 0`. -/
theorem loopD_spec (ctx : Ctx) (labels : Array JSStr) (L F A : EnvId) (len : Nat) (xs : Nat → Nat)
    (hstr : ctx.strict = false) (hlen : len < 2 ^ 26) (hx : ∀ j < len, xs j < 2 ^ 26) (E0 : EnvId) (t : State)
    (hS : ShapeD E0 L F A (some (num (0 : Nat))) t) (hA : ArrayObj A len (dbl xs 0) t)
    (hf : len + 5 ≤ t.fuel) :
    ∃ c t', M.loop (forIter testD updD bodyD labels ctx #["i"]) t.fuel (E0, .undefined) t = .ok c t' ∧
      (∃ w, c = Compl.normal (some w)) ∧ (∃ E, ShapeD E L F A (some (num len)) t') ∧
      ArrayObj A len (dbl xs len) t' ∧ t'.fuel + len + 1 = t.fuel := by
  let N := len
  let I : EnvId × Value → State → Prop := fun st u =>
    ∃ k, k ≤ N ∧ ShapeD st.1 L F A (some (num k)) u ∧ ArrayObj A len (dbl xs k) u ∧ u.fuel + k = t.fuel
  let Q : Compl → State → Prop := fun c u =>
    (∃ w, c = Compl.normal (some w)) ∧ (∃ E, ShapeD E L F A (some (num N)) u) ∧ ArrayObj A len (dbl xs N) u ∧
      u.fuel + N + 1 = t.fuel
  let V : EnvId × Value → State → Nat := fun _ u => u.fuel + N - t.fuel
  have hstep : ∀ st u, I st u →
      (∃ st' u', forIter testD updD bodyD labels ctx #["i"] st u = .ok (.inl st') u' ∧ I st' u' ∧ V st' u' < V st u) ∨
      (∃ c u', forIter testD updD bodyD labels ctx #["i"] st u = .ok (.inr c) u' ∧ Q c u') := by
    intro ⟨E, v⟩ u ⟨k, hk, hSu, hAu, hfu⟩
    by_cases hkN : k < N
    · obtain ⟨E', v', u', h, hS', hA', hf'⟩ := iterD_cont ctx labels E L F A len k xs hstr hkN hlen hx u v hSu hAu
        (by omega)
      have hc : ((k + 1 : Nat) : Int) = (k : Int) + 1 := by omega
      exact Or.inl ⟨(E', v'), u', h, ⟨k + 1, hkN, by rw [hc]; exact hS', hA', by omega⟩, by simp only [V]; omega⟩
    · have hkN' : k = N := by omega
      subst hkN'
      obtain ⟨u', h, hS', hf', ho', hz'⟩ := iterD_exit ctx labels E L F A k xs hstr hlen u v hSu hAu (by omega)
      have hA' : ArrayObj A k (dbl xs k) u' := by
        obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hAu
        exact ⟨by rw [hz']; exact a1, by rw [ho']; exact a2, by rw [ho']; exact a3, by rw [ho']; exact a4,
          fun j hj => by rw [ho']; exact a5 j hj, fun j hj hjb => by rw [ho']; exact a6 j hj hjb⟩
      exact Or.inr ⟨_, u', h, ⟨v, rfl⟩, ⟨E, hS'⟩, hA', by omega⟩
  exact M.loop_inv _ I Q V hstep t.fuel (E0, .undefined) t ⟨0, Nat.zero_le _, hS, hA, by simp⟩ (by simp only [V]; omega)

/-- The environments before the loop: `L` binds `s` (value `sv`), not `i` or `a`; `F` binds `a` to `A`. -/
def ShapeBD (L F A : Nat) (t : State) : Prop :=
  L < t.envs.size ∧ F < t.envs.size ∧ L ≠ F ∧
  (∃ bL, t.envEntry L = .decl bL (some F) ∧ bL[JSStr.ofString "a"]? = none) ∧
  (∃ bF o ts tv fo nt bn, t.envEntry F = .func bF o ts tv fo nt ∧ bF[JSStr.ofString "a"]? = some bn ∧
    bn.value = some (.obj A))

/-- The `for` statement: from `s = 0`, it completes normally with `s = psum xs len`. -/
theorem forD_spec (ctx : Ctx) (L F A : EnvId) (len : Nat) (xs : Nat → Nat) (hlex : ctx.lex = L)
    (hstr : ctx.strict = false) (hlen : len < 2 ^ 26) (hx : ∀ j < len, xs j < 2 ^ 26) (t : State)
    (hS : ShapeBD L F A t) (hA : ArrayObj A len (dbl xs 0) t) (hf : len + 8 ≤ t.fuel) :
    ∃ c t', Sem.forS initD testD updD bodyD ctx t = .ok (Sem.breakToNormal c) t' ∧
      (∃ w, c = Compl.normal (some w)) ∧ ArrayObj A len (dbl xs len) t' := by
  obtain ⟨hL, hF, hLF, ⟨bL, hLE, hln⟩, hFn⟩ := hS
  have h1 : (VarKind.let == VarKind.using) = false := by decide
  have h2 : (VarKind.let == VarKind.awaitUsing) = false := by decide
  have h3 : (VarKind.let == VarKind.const) = false := by decide
  simp only [Sem.forS, initD, h1, h2, h3, withDisposeScope, Bool.or_false, Bool.false_eq_true, ↓reduceIte,
    Bool.not_false, M.bind_eq, M.bind_apply, hlex, newDeclEnv_eq, M.bindRes_ok, ← perIterationEnv_def]
  -- the loop environment E0 with `i`
  obtain ⟨E0, hE0⟩ : ∃ E0, t.envs.size = E0 := ⟨_, rfl⟩
  have hLE0 : L ≠ E0 := by rw [← hE0]; exact Nat.ne_of_lt hL
  have hFE0 : F ≠ E0 := by rw [← hE0]; exact Nat.ne_of_lt hF
  obtain ⟨t1, ht1⟩ : ∃ t1, t.pushEnv (.decl {} (some L)) = t1 := ⟨_, rfl⟩
  have hE01 : E0 < t1.envs.size := by rw [← ht1, State.pushEnv_size, ← hE0]; exact Nat.lt_succ_self _
  have e1E0 : t1.envEntry E0 = .decl {} (some L) := by rw [← ht1, ← hE0]; exact State.pushEnv_entry_new _ _
  have e1 : ∀ x, x < t.envs.size → t1.envEntry x = t.envEntry x := by
    intro x hx; rw [← ht1]; exact State.pushEnv_entry_lt _ _ _ hx
  have hcm := createMutableBinding_declLike E0 "i" false t1 hE01 (by rw [e1E0]; rfl)
  rw [e1E0] at hcm
  obtain ⟨t2, ht2⟩ : ∃ t2, t1.setEnv E0 ((Env.decl {} (some L)).withBindings
      (·.insert "i" { deletable := false })) = t2 := ⟨_, rfl⟩
  rw [ht2] at hcm
  have e2E0 : t2.envEntry E0 = .decl ((∅ : Std.HashMap JSStr Binding).insert "i" { deletable := false }) (some L) := by
    rw [← ht2, State.setEnv_envEntry_self _ _ _ hE01]; rfl
  have hE02 : E0 < t2.envs.size := by rw [← ht2, State.setEnv_envs_size]; exact hE01
  have f2 : t2.fuel = t.fuel := by rw [← ht2, State.setEnv_fuel, ← ht1, State.pushEnv_fuel]
  have hr0 : resolveBinding E0 "i" false t2 = .ok (.env (some E0) "i" false) t2 :=
    resolveBinding_here E0 _ false t2 hE02 (by rw [e2E0]; rfl)
      (by rw [e2E0]; simp [Env.bindingsMap]) (by omega)
  have hin := initializeBinding_declLike E0 "i" (num 0) t2 hE02 (by rw [e2E0]; rfl)
  rw [e2E0] at hin
  obtain ⟨t3, ht3⟩ : ∃ t3, t2.setEnv E0 ((Env.decl ((∅ : Std.HashMap JSStr Binding).insert "i" { deletable := false })
      (some L)).withBindings (·.modify "i" fun bd => { bd with value := some (num 0) })) = t3 := ⟨_, rfl⟩
  rw [ht3] at hin
  have e3E0 : t3.envEntry E0 = .decl (((∅ : Std.HashMap JSStr Binding).insert "i" { deletable := false }).modify "i"
      fun bd => { bd with value := some (num 0) }) (some L) := by
    rw [← ht3, State.setEnv_envEntry_self _ _ _ hE02]; rfl
  have hE03 : E0 < t3.envs.size := by rw [← ht3, State.setEnv_envs_size]; exact hE02
  have z3 : t3.envs.size = t.envs.size + 1 := by
    rw [← ht3, State.setEnv_envs_size, ← ht2, State.setEnv_envs_size, ← ht1, State.pushEnv_size]
  have f3 : t3.fuel = t.fuel := by rw [← ht3, State.setEnv_fuel, f2]
  have e3 : ∀ x, x < t.envs.size → t3.envEntry x = t.envEntry x := by
    intro x hx
    have hx0 : E0 ≠ x := by rw [← hE0]; exact Ne.symm (Nat.ne_of_lt hx)
    rw [← ht3, State.setEnv_envEntry_ne _ _ _ _ hx0, ← ht2, State.setEnv_envEntry_ne _ _ _ _ hx0, e1 x hx]
  -- the first iteration's copy
  have hpi := perIterationEnv_one "i" E0 L t3 _ { value := some (num 0), deletable := false } (num 0) hE03 e3E0
    (by simp [Std.HashMap.getElem?_modify]) rfl
  obtain ⟨E1, hE1⟩ : ∃ E1, t3.envs.size = E1 := ⟨_, rfl⟩
  rw [hE1] at hpi
  obtain ⟨t4, ht4⟩ : ∃ t4, (t3.pushEnv (.decl {} (some L))).setEnv E1 (.decl (((∅ : Std.HashMap JSStr Binding).insert
      "i" { deletable := false }).modify "i" fun bd => { bd with value := some (num 0) }) (some L)) = t4 := ⟨_, rfl⟩
  rw [ht4] at hpi
  have f4 : t4.fuel = t.fuel := by rw [← ht4, State.setEnv_fuel, State.pushEnv_fuel, f3]
  have hS4 : ShapeD E1 L F A (some (num (0 : Nat))) t4 := by
    have hE14 : E1 < t4.envs.size := by
      rw [← ht4, State.setEnv_envs_size, State.pushEnv_size, ← hE1]; exact Nat.lt_succ_self _
    have hL3 : L < t3.envs.size := by rw [z3]; exact Nat.lt_succ_of_lt hL
    have hF3 : F < t3.envs.size := by rw [z3]; exact Nat.lt_succ_of_lt hF
    have hLE1 : L ≠ E1 := by rw [← hE1]; exact Nat.ne_of_lt hL3
    have hFE1 : F ≠ E1 := by rw [← hE1]; exact Nat.ne_of_lt hF3
    have e4 : ∀ x, x ≠ E1 → x < t3.envs.size → t4.envEntry x = t3.envEntry x := by
      intro x hx hlt
      rw [← ht4, State.setEnv_envEntry_ne _ _ _ _ (Ne.symm hx), State.pushEnv_entry_lt _ _ _ hlt]
    refine ⟨hE14, by rw [← ht4, State.setEnv_envs_size, State.pushEnv_size]; exact Nat.lt_succ_of_lt hL3,
      by rw [← ht4, State.setEnv_envs_size, State.pushEnv_size]; exact Nat.lt_succ_of_lt hF3,
      Ne.symm hLE1, Ne.symm hFE1, hLF, ?_, ?_, ?_⟩
    · refine ⟨_, { value := some (num 0), deletable := false },
        by rw [← ht4]; exact State.setEnv_envEntry_self _ _ _ (by rw [State.pushEnv_size, ← hE1]; exact Nat.lt_succ_self _),
        by simp [Std.HashMap.getElem?_modify], by simp,
        rfl, by simp [Std.HashMap.getElem?_modify, Std.HashMap.getElem?_insert, ne_ia]⟩
    · exact ⟨bL, by rw [e4 L hLE1 hL3, e3 L hL, hLE], hln⟩
    · obtain ⟨bF, o, ts, tv, fo, nt, bn, hFE, hbF, hbnv⟩ := hFn
      exact ⟨bF, o, ts, tv, fo, nt, bn, by rw [e4 F hFE1 hF3, e3 F hF, hFE], hbF, hbnv⟩
  -- the loop
  have hA4 : ArrayObj A len (dbl xs 0) t4 := by
    have o4 : ∀ x, t4.objEntry x = t.objEntry x := by
      intro x; rw [← ht4, State.setEnv_objEntry, State.pushEnv_objEntry, ← ht3, State.setEnv_objEntry, ← ht2,
        State.setEnv_objEntry, ← ht1, State.pushEnv_objEntry]
    have z4 : t4.heap.size = t.heap.size := by
      rw [← ht4, State.setEnv_heap_size, State.pushEnv_heap_size, ← ht3, State.setEnv_heap_size, ← ht2,
        State.setEnv_heap_size, ← ht1, State.pushEnv_heap_size]
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hA
    exact ⟨by rw [z4]; exact a1, by rw [o4]; exact a2, by rw [o4]; exact a3, by rw [o4]; exact a4,
      fun j hj => by rw [o4]; exact a5 j hj, fun j hj hjb => by rw [o4]; exact a6 j hj hjb⟩
  obtain ⟨c, t5, hloop, hc, -, hA5, hf5⟩ := loopD_spec { Sem.inner ctx with strict := false } ctx.labels L F A len xs
    rfl hlen hx E1 t4 hS4 hA4 (by omega)
  rw [f4] at hloop
  refine ⟨c, t5, ?_, hc, hA5⟩
  have hil : (Sem.inner ctx).lex = L := hlex
  simp only [hil, hE0, ht1]
  simp only [boundNames_ident, List.foldl_toArray', List.foldl_cons, List.foldl_nil, Array.foldl_toList,
    List.foldl, Array.empty_append, M.forArr_def, M.foldArr_toArray, M.foldList_cons, M.foldList_nil, hcm, M.bindRes_ok]
  have his : (Sem.inner ctx).strict = false := hstr
  simp only [Sem.varDecl, Sem.inner, M.bind_eq, M.bind_apply, M.forArr_def, M.foldArr_toArray, M.foldList_cons,
    M.foldList_nil, Sem.declLex, hstr, hr0, M.bindRes_ok, Sem.lit, litValue, zero_eq, pure, M.pure, initializeRefBinding,
    hin, h1, h2, Bool.false_eq_true, Bool.or_false, ↓reduceIte, hpi, M.repeatFrom, f4]
  erw [hloop]
  rfl

/-- **`double`'s body doubles every element**: started with `a` bound to the array `A` (elements
`xs j`, naturals below 2^26, `len < 2^26`) in the function environment `F`, it completes normally,
and afterwards `A` holds `2 · xs j` at every index `j < len`. -/
theorem double_spec (n : Nat) (ctx : Ctx) (L F A : EnvId) (len : Nat) (xs : Nat → Nat) (hlex : ctx.lex = L)
    (hstr : ctx.strict = false) (hlen : len < 2 ^ 26) (hx : ∀ j < len, xs j < 2 ^ 26) (s0 : State)
    (hS : ShapeBD L F A s0) (hA : ArrayObj A len (fun j => num (xs j)) s0) (hf : len + 10 ≤ s0.fuel) :
    ∃ w s', DoubleGen.double n ctx s0 = .ok (.normal (some w)) s' ∧
      ArrayObj A len (fun j => num ((2 * xs j : Nat) : Int)) s' := by
  have hA0 : ArrayObj A len (dbl xs 0) s0 := by
    have : dbl xs 0 = fun j => num (xs j) := by funext j; simp [dbl]
    rw [this]; exact hA
  obtain ⟨c, s1, hfor, ⟨w, hc⟩, hA1⟩ := forD_spec ctx L F A len xs hlex hstr hlen hx s0 hS hA0 (by omega)
  subst hc
  simp only [initD, testD, updD, bodyD] at hfor
  obtain ⟨j, hj⟩ : ∃ j, s0.fuel = j + 3 := ⟨s0.fuel - 3, by omega⟩
  refine ⟨w, s1, ?_, arrayObj_congr A len _ _ s1 (fun j hj => by simp [dbl, hj]) hA1⟩
  simp only [DoubleGen.double, Sem.stmts, M.repeatFrom, hj, M.loop]
  simp [M.bind_eq, M.bind_apply, hfor, Sem.breakToNormal, pure, M.pure]

/-- The same for the interpreter itself, on `double`'s syntax tree. -/
theorem double_interp_spec (n : Nat) (ctx : Ctx) (L F A : EnvId) (len : Nat) (xs : Nat → Nat) (hlex : ctx.lex = L)
    (hstr : ctx.strict = false) (hlen : len < 2 ^ 26) (hx : ∀ j < len, xs j < 2 ^ 26) (s0 : State)
    (hS : ShapeBD L F A s0) (hA : ArrayObj A len (fun j => num (xs j)) s0) (hf : len + 10 ≤ s0.fuel) :
    ∃ w s', evalStmts (n + 35) ctx DoubleGen.double_stmts s0 = .ok (.normal (some w)) s' ∧
      ArrayObj A len (fun j => num ((2 * xs j : Nat) : Int)) s' := by
  rw [← congrFun (DoubleGen.double_eq n) ctx]
  exact double_spec n ctx L F A len xs hlex hstr hlen hx s0 hS hA hf

end DoubleProof
