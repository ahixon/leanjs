import Proofs.SumFor
import Proofs.Total
import Proofs.ArrayAppend
import Proofs.IotaGen
import Proofs.Double

/-!
# A loop that builds an array: `iota(n)` returns `[0, 1, …, n − 1]`

```js
function iota(n) { let a = []; for (let i = 0; i < n; i = i + 1) { a[i] = i; } return a; }
```
(examples/iota.js, generated into `Proofs/IotaGen.lean`.) Every write `a[i] = i` is past the end
(`putRefValue_append`): it goes through the prototype chain, so the theorem assumes that
`Array.prototype`'s chain has no index property below `n` (a page could define one, with a setter).
-/

open ES ES.Conv SumProof
open DoubleProof (Frame Frame.refl Frame.trans)

namespace IotaProof

def bodyD : Sem.CStmt := (Sem.block (lexicallyScoped #[(Stmt.expr (Expr.assign AssignOp.assign (Pattern.expr (Expr.member (Expr.ident "a") (MemberKey.computed (Expr.ident "i")) false)) (Expr.ident "i")))]) #[(Sem.exprStmt (Sem.assign (Sem.memberRef (Sem.ident "a") (Sem.Key.computed (Sem.ident "i")) false) (Sem.ident "i")))])

theorem lexBodyI : lexicallyScoped #[(Stmt.expr (Expr.assign AssignOp.assign (Pattern.expr (Expr.member (Expr.ident "a") (MemberKey.computed (Expr.ident "i")) false)) (Expr.ident "i")))] = #[] := by rfl

theorem ne_an : (JSStr.ofString "a" = JSStr.ofString "n") = False := by simp; decide
theorem ne_ai : (JSStr.ofString "a" = JSStr.ofString "i") = False := by simp; decide

/-- The environments in iteration with `i = iv`: `a` (in `L`) is the array `A`, `n = N` in `F`. -/
def ShapeI (E L F : EnvId) (N : Nat) (A : ObjId) (iv : Option Value) (t : State) : Prop :=
  E < t.envs.size ∧ L < t.envs.size ∧ F < t.envs.size ∧ E ≠ L ∧ E ≠ F ∧ L ≠ F ∧
  (∃ bE bdi, t.envEntry E = .decl bE (some L) ∧ bE[JSStr.ofString "i"]? = some bdi ∧ bdi.value = iv ∧
    bdi.mutable = true ∧ bE[JSStr.ofString "a"]? = none ∧ bE[JSStr.ofString "n"]? = none) ∧
  (∃ bL bda, t.envEntry L = .decl bL (some F) ∧ bL[JSStr.ofString "a"]? = some bda ∧ bda.value = some (.obj A) ∧
    bL[JSStr.ofString "n"]? = none) ∧
  (∃ bF o ts tv fo nt bn, t.envEntry F = .func bF o ts tv fo nt ∧ bF[JSStr.ofString "n"]? = some bn ∧
    bn.value = some (num N))

/-- The heap after `k` iterations: `A` holds `0, …, k − 1` and has prototype `P`; the objects that
existed in `R` (before the call) are unchanged. -/
def HeapI (R : State) (A P : ObjId) (k : Nat) (u : State) : Prop :=
  ArrayObj A k (fun j => num j) u ∧ (u.objEntry A).proto = .obj P ∧
  (∀ x, x < R.heap.size → u.objEntry x = R.objEntry x) ∧ R.heap.size ≤ u.heap.size

theorem heapI_of (R : State) (A P : ObjId) (k : Nat) (u u' : State) (h1 : ∀ x, u'.objEntry x = u.objEntry x)
    (h2 : u'.heap.size = u.heap.size) (hH : HeapI R A P k u) : HeapI R A P k u' := by
  obtain ⟨⟨a1, a2, a3, a4, a5, a6⟩, hpr, hobj, hsz⟩ := hH
  exact ⟨⟨by rw [h2]; exact a1, by rw [h1]; exact a2, by rw [h1]; exact a3, by rw [h1]; exact a4,
    fun j hj => by rw [h1]; exact a5 j hj, fun j hj hjb => by rw [h1]; exact a6 j hj hjb⟩,
    by rw [h1]; exact hpr, fun x hx => by rw [h1]; exact hobj x hx, by rw [h2]; exact hsz⟩

theorem chain_at (R u : State) (A P : ObjId) (k N : Nat) (hP : ∀ j < N, AbsentChain R 2 P (PropKey.ofNat j))
    (hk : k < N) (hN : N < 2 ^ 26) (hH : HeapI R A P k u) : AbsentChain u 3 A (PropKey.ofNat k) := by
  obtain ⟨⟨a1, a2, -, -, -, a6⟩, hpr, hobj, hsz⟩ := hH
  refine ⟨a1, by rw [a2]; rfl, a6 k (Nat.le_refl _) (by omega), ?_⟩
  rw [hpr]; exact absentChain_mono R u _ hobj hsz 2 P (hP k hk)

theorem heapI_append (R u : State) (A P : ObjId) (k : Nat) (hRA : R.heap.size ≤ A) (hlen : k < 2 ^ 26)
    (hH : HeapI R A P k u) : HeapI R A P (k + 1) (appendState A k (num k) u) := by
  obtain ⟨hA, hpr, hobj, hsz⟩ := hH
  refine ⟨arrayObj_congr A (k + 1) _ _ _ (fun j hj => by by_cases h : j = k <;> simp [h])
      (arrayObj_appendState A k _ (num k) u hA hlen),
    by simp only [appendState]; rw [setProp_proto, setProp_proto, hpr], fun x hx => ?_,
    by simp [appendState, State.setProp]; exact hsz⟩
  have hne : A ≠ x := Nat.ne_of_gt (Nat.lt_of_lt_of_le hx hRA)
  simp only [appendState]
  rw [State.setProp_entry_ne _ _ _ _ _ hne, State.setProp_entry_ne _ _ _ _ _ hne, hobj x hx]

/-- One iteration that continues: `a[k] = k` appends; in the fresh copy `E'`, `i = k + 1`. -/
theorem iterI_cont (ctx : Ctx) (labels : Array JSStr) (E L F : EnvId) (N : Nat) (A P : ObjId) (k : Nat) (R : State)
    (hstr : ctx.strict = false) (hk : k < N) (hN : N < 2 ^ 26) (hP : ∀ j < N, AbsentChain R 2 P (PropKey.ofNat j))
    (hRA : R.heap.size ≤ A) (t : State) (v : Value)
    (hS : ShapeI E L F N A (some (num k)) t) (hH : HeapI R A P k t) (hf : 5 ≤ t.fuel) :
    ∃ E' v' t', forIter SumForProof.testD SumForProof.updD bodyD labels ctx #["i"] (E, v) t = .ok (.inl (E', v')) t' ∧
      ShapeI E' L F N A (some (num ((k : Int) + 1))) t' ∧ HeapI R A P (k + 1) t' ∧ t'.fuel = t.fuel - 1 ∧
      Frame A t t' := by
  obtain ⟨hE, hL, hF, hEL, hEF, hLF, ⟨bE, bdi, hEE, hbi, hiv, him, hba, hbn⟩, ⟨bL, bda, hLE, hla, hav, hln⟩,
    ⟨bF, o, ts, tv, fo, nt, bn, hFE, hbF, hbnv⟩⟩ := hS
  have hkb : (k : Int).natAbs < intBound := by simp only [intBound]; omega
  have hNb : (N : Int).natAbs < intBound := by simp only [intBound]; omega
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
  have hH1 : HeapI R A P k t1 := heapI_of R A P k t t1 (fun x => by rw [← ht1]; rfl) (by rw [← ht1]) hH
  -- the test: `i < n`
  have ri : identValue E "i" false t1 = .ok (num k) t1 :=
    identValue_skip0 E _ false t1 bdi _ h1E (by rw [e1, hEE]; rfl) (by rw [e1, hEE]; exact hbi) hiv (by omega)
  have rn : identValue E "n" false t1 = .ok (num N) t1 :=
    identValue_skip2 E L F _ false t1 bE bL bn _ h1E (by rw [e1]; exact hEE) hbn h1L
      (by rw [e1]; exact hLE) hln h1F (by rw [e1, hFE]; rfl) (by rw [e1, hFE]; exact hbF) hbnv (by omega)
  have hlt : ltF (ofSmallInt k) (ofSmallInt N) = true := by rw [ltF_int _ _ hkb hNb]; simp [hk]
  -- the body: `a[i] = i`, past the end
  have ra : identValue E "a" false t1 = .ok (.obj A) t1 :=
    identValue_skip1 E L _ false t1 bE bda _ h1E (by rw [e1]; exact hEE) hba h1L
      (by rw [e1, hLE]; rfl) (by rw [e1, hLE]; exact hla) hav (by omega)
  have hw := putRefValue_append A k (fun j => num j) (num k) false t1 3 hH1.1 (by omega)
    (chain_at R t1 A P k N hP hk hN hH1) (by omega)
  obtain ⟨t2, ht2⟩ : ∃ t2, appendState A k (num k) t1 = t2 := ⟨_, rfl⟩
  rw [ht2] at hw
  have hH2 : HeapI R A P (k + 1) t2 := by rw [← ht2]; exact heapI_append R t1 A P k hRA (by omega) hH1
  have z2 : t2.envs.size = t.envs.size := by rw [← ht2]; simp only [appendState, State.setProp_envs]; exact z1
  have f2 : t2.fuel = t.fuel - 1 := by rw [← ht2]; simp only [appendState, State.setProp_fuel]; exact f1
  have e2 : ∀ x, t2.envEntry x = t.envEntry x := by
    intro x; simp only [State.envEntry, ← ht2, appendState, State.setProp_envs]; exact e1 x
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
  have hS4 : ShapeI E' L F N A (some (num ((k : Int) + 1))) t4 := by
    refine ⟨by rw [z4, ← hE', z2]; exact Nat.lt_succ_self _, by rw [z4]; exact Nat.lt_succ_of_lt hL,
      by rw [z4]; exact Nat.lt_succ_of_lt hF, Ne.symm hLE', Ne.symm hFE', hLF, ?_, ?_, ?_⟩
    · refine ⟨bE'.modify "i" fun bd => { bd with value := some (num ((k : Int) + 1)) },
        { value := some (num ((k : Int) + 1)), deletable := false }, ?_, ?_, rfl, rfl, ?_, ?_⟩
      · rw [← ht4]; exact State.setEnv_envEntry_self _ _ _ hE'lt
      · rw [← hbE']; simp [Std.HashMap.getElem?_modify]
      · rw [← hbE']; simp [Std.HashMap.getElem?_modify, Std.HashMap.getElem?_insert, TotalProof.ne_ia]
      · rw [← hbE']; simp [Std.HashMap.getElem?_modify, Std.HashMap.getElem?_insert, ne_in]
    · exact ⟨bL, bda, by rw [e4 L hLE' (by rw [z2]; exact hL), e2, hLE], hla, hav, hln⟩
    · exact ⟨bF, o, ts, tv, fo, nt, bn, by rw [e4 F hFE' (by rw [z2]; exact hF), e2, hFE], hbF, hbnv⟩
  have hH4 : HeapI R A P (k + 1) t4 := by
    refine heapI_of R A P (k + 1) t2 t4 (fun x => ?_) ?_ hH2
    · rw [← ht4, State.setEnv_objEntry, ← ht3, State.setEnv_objEntry, State.pushEnv_objEntry]
    · rw [← ht4, State.setEnv_heap_size, ← ht3, State.setEnv_heap_size, State.pushEnv_heap_size]
  have hpe : putRefValue (.env (some E') "i" false) (num ((k : Int) + 1)) t3 = .ok () t4 := by
    simp [putRefValue, hset_i]
  have hfr : Frame A t t4 := by
    refine ⟨by rw [z4]; exact Nat.le_succ _, fun e he => ?_, ?_, fun o ho => ?_, ?_⟩
    · rw [e4 e (by rw [← hE', z2]; exact Nat.ne_of_lt he) (by rw [z2]; exact he), e2]
    · rw [← ht4, State.setEnv_heap_size, ← ht3, State.setEnv_heap_size, State.pushEnv_heap_size, ← ht2, ← ht1]
      simp [appendState, State.setProp]
    · rw [← ht4, State.setEnv_objEntry, ← ht3, State.setEnv_objEntry, State.pushEnv_objEntry, ← ht2]
      simp only [appendState]
      rw [State.setProp_entry_ne _ _ _ _ _ (Ne.symm ho), State.setProp_entry_ne _ _ _ _ _ (Ne.symm ho), ← ht1]; rfl
    · rw [← ht4, State.setEnv_realms, ← ht3, State.setEnv_realms, State.pushEnv_realms, ← ht2]
      simp only [appendState, State.setProp_realms]; rw [← ht1]
  refine ⟨E', num k, t4, ?_, hS4, hH4, f4, hfr⟩
  obtain ⟨j, hj⟩ : ∃ j, t1.fuel = j + 2 := ⟨t1.fuel - 2, by omega⟩
  simp only [forIter, M.bind_eq, M.bind_apply, htick, M.bindRes_ok, SumForProof.testD, Sem.binary, Sem.ident, hstr, ri, rn]
  simp [Sem.binaryOp, isLessThan, M.bind_eq, M.bind_apply, hlt, ofSmallInt_eq_nan, toBoolean, pure, M.pure, bodyD,
    lexBodyI, Sem.block, Sem.stmts, M.repeatFrom, hj, M.loop, Sem.exprStmt, Sem.assign, Sem.inner, hstr,
    Sem.ident, ri, ra, Sem.memberRef, Value.isNullish, hw, loopContinues, Compl.value?, hpi, SumForProof.updD, rri3, ri3, Sem.lit,
    litValue, one_eq, hadd_i, hset_i, Sem.identRef, hpe, Sem.binary]

/-- The last iteration: `i < n` fails. -/
theorem iterI_exit (ctx : Ctx) (labels : Array JSStr) (E L F : EnvId) (N : Nat) (A : ObjId) (hstr : ctx.strict = false)
    (hN : N < 2 ^ 26) (t : State) (v : Value) (hS : ShapeI E L F N A (some (num N)) t) (hf : 4 ≤ t.fuel) :
    ∃ t', forIter SumForProof.testD SumForProof.updD bodyD labels ctx #["i"] (E, v) t = .ok (.inr (.normal (some v))) t' ∧
      ShapeI E L F N A (some (num N)) t' ∧ t'.fuel = t.fuel - 1 ∧ (∀ x, t'.objEntry x = t.objEntry x) ∧
      t'.heap.size = t.heap.size ∧ Frame A t t' := by
  have hS' := hS
  obtain ⟨hE, hL, hF, -, -, -, ⟨bE, bdi, hEE, hbi, hiv, -, -, hbn⟩, ⟨bL, -, hLE, -, -, hln⟩,
    ⟨bF, o, ts, tv, fo, nt, bn, hFE, hbF, hbnv⟩⟩ := hS
  have hNb : (N : Int).natAbs < intBound := by simp only [intBound]; omega
  obtain ⟨t1, ht1⟩ : ∃ t1, ({ t with fuel := t.fuel - 1 } : State) = t1 := ⟨_, rfl⟩
  have e1 : ∀ x, t1.envEntry x = t.envEntry x := by intro x; rw [← ht1]; rfl
  have z1 : t1.envs.size = t.envs.size := by rw [← ht1]
  have f1 : t1.fuel = t.fuel - 1 := by rw [← ht1]
  have htick : M.tick t = .ok () t1 := by rw [← ht1]; simp [M.tick, show t.fuel ≠ 0 by omega]
  have h1E : E < t1.envs.size := by rw [z1]; exact hE
  have h1L : L < t1.envs.size := by rw [z1]; exact hL
  have h1F : F < t1.envs.size := by rw [z1]; exact hF
  have ri : identValue E "i" false t1 = .ok (num N) t1 :=
    identValue_skip0 E _ false t1 bdi _ h1E (by rw [e1, hEE]; rfl) (by rw [e1, hEE]; exact hbi) hiv (by omega)
  have rn : identValue E "n" false t1 = .ok (num N) t1 :=
    identValue_skip2 E L F _ false t1 bE bL bn _ h1E (by rw [e1]; exact hEE) hbn h1L
      (by rw [e1]; exact hLE) hln h1F (by rw [e1, hFE]; rfl) (by rw [e1, hFE]; exact hbF) hbnv (by omega)
  have hlt : ltF (ofSmallInt N) (ofSmallInt N) = false := by rw [ltF_int _ _ hNb hNb]; simp
  refine ⟨t1, ?_, by rw [← ht1]; exact hS', f1, fun x => by rw [← ht1]; rfl, by rw [← ht1],
    ⟨Nat.le_of_eq z1.symm, fun e _ => e1 e, by rw [← ht1], fun o _ => by rw [← ht1]; rfl, by rw [← ht1]⟩⟩
  simp only [forIter, M.bind_eq, M.bind_apply, htick, M.bindRes_ok, SumForProof.testD, Sem.binary, Sem.ident, hstr,
    ri, rn]
  simp [Sem.binaryOp, isLessThan, M.bind_eq, M.bind_apply, hlt, ofSmallInt_eq_nan, toBoolean, pure, M.pure]

/-- The loop, from the first iteration's environment with `i = 0` and `a` empty. -/
theorem loopI_spec (ctx : Ctx) (labels : Array JSStr) (L F : EnvId) (N : Nat) (A P : ObjId) (R : State)
    (hstr : ctx.strict = false) (hN : N < 2 ^ 26) (hP : ∀ j < N, AbsentChain R 2 P (PropKey.ofNat j))
    (hRA : R.heap.size ≤ A) (E0 : EnvId) (t : State)
    (hS : ShapeI E0 L F N A (some (num (0 : Nat))) t) (hH : HeapI R A P 0 t) (hf : N + 5 ≤ t.fuel) :
    ∃ c t', M.loop (forIter SumForProof.testD SumForProof.updD bodyD labels ctx #["i"]) t.fuel (E0, .undefined) t =
        .ok c t' ∧
      (∃ w, c = Compl.normal (some w)) ∧ (∃ E, ShapeI E L F N A (some (num N)) t') ∧ HeapI R A P N t' ∧
      t'.fuel + N + 1 = t.fuel ∧ Frame A t t' := by
  let I : EnvId × Value → State → Prop := fun st u =>
    ∃ k, k ≤ N ∧ ShapeI st.1 L F N A (some (num k)) u ∧ HeapI R A P k u ∧ u.fuel + k = t.fuel ∧ Frame A t u
  let Q : Compl → State → Prop := fun c u =>
    (∃ w, c = Compl.normal (some w)) ∧ (∃ E, ShapeI E L F N A (some (num N)) u) ∧ HeapI R A P N u ∧
      u.fuel + N + 1 = t.fuel ∧ Frame A t u
  let V : EnvId × Value → State → Nat := fun _ u => u.fuel + N - t.fuel
  have hstep : ∀ st u, I st u →
      (∃ st' u', forIter SumForProof.testD SumForProof.updD bodyD labels ctx #["i"] st u = .ok (.inl st') u' ∧
        I st' u' ∧ V st' u' < V st u) ∨
      (∃ c u', forIter SumForProof.testD SumForProof.updD bodyD labels ctx #["i"] st u = .ok (.inr c) u' ∧ Q c u') := by
    intro ⟨E, v⟩ u ⟨k, hk, hSu, hHu, hfu, hfru⟩
    by_cases hkN : k < N
    · obtain ⟨E', v', u', h, hS', hH', hf', hfr'⟩ := iterI_cont ctx labels E L F N A P k R hstr hkN hN hP hRA u v hSu hHu
        (by omega)
      have hc : ((k + 1 : Nat) : Int) = (k : Int) + 1 := by omega
      exact Or.inl ⟨(E', v'), u', h, ⟨k + 1, hkN, by rw [hc]; exact hS', hH', by omega, hfru.trans hfr'⟩, by simp only [V]; omega⟩
    · have hkN' : k = N := by omega
      subst hkN'
      obtain ⟨u', h, hS', hf', ho', hz', hfr'⟩ := iterI_exit ctx labels E L F k A hstr hN u v hSu (by omega)
      exact Or.inr ⟨_, u', h, ⟨v, rfl⟩, ⟨E, hS'⟩, heapI_of R A P k u u' ho' hz' hHu, by omega,
        hfru.trans hfr'⟩
  exact M.loop_inv _ I Q V hstep t.fuel (E0, .undefined) t ⟨0, Nat.zero_le _, hS, hH, by simp, Frame.refl A t⟩
    (by simp only [V]; omega)

/-- The environments before the loop: `L` binds `a` to `A`, not `i` or `n`; `F` binds `n = N`. -/
def ShapeBI (L F : EnvId) (N : Nat) (A : ObjId) (t : State) : Prop :=
  L < t.envs.size ∧ F < t.envs.size ∧ L ≠ F ∧
  (∃ bL bda, t.envEntry L = .decl bL (some F) ∧ bL[JSStr.ofString "a"]? = some bda ∧ bda.value = some (.obj A) ∧
    bL[JSStr.ofString "n"]? = none ∧ bL[JSStr.ofString "i"]? = none) ∧
  (∃ bF o ts tv fo nt bn, t.envEntry F = .func bF o ts tv fo nt ∧ bF[JSStr.ofString "n"]? = some bn ∧
    bn.value = some (num N))

/-- The `for` statement: from `a` empty, it completes normally with `a = [0, …, N − 1]`. -/
theorem forI_spec (ctx : Ctx) (L F : EnvId) (N : Nat) (A P : ObjId) (R : State) (hlex : ctx.lex = L)
    (hstr : ctx.strict = false) (hN : N < 2 ^ 26) (hP : ∀ j < N, AbsentChain R 2 P (PropKey.ofNat j))
    (hRA : R.heap.size ≤ A) (t : State) (hS : ShapeBI L F N A t) (hH : HeapI R A P 0 t) (hf : N + 8 ≤ t.fuel) :
    ∃ c t', Sem.forS SumForProof.initD SumForProof.testD SumForProof.updD bodyD ctx t = .ok (Sem.breakToNormal c) t' ∧
      (∃ w, c = Compl.normal (some w)) ∧ (∃ E, ShapeI E L F N A (some (num N)) t') ∧ HeapI R A P N t' ∧
      t'.fuel + N + 1 = t.fuel ∧ Frame A t t' := by
  obtain ⟨hL, hF, hLF, ⟨bL, bda, hLE, hla, hav, hln, hli⟩, hFn⟩ := hS
  have h1 : (VarKind.let == VarKind.using) = false := by decide
  have h2 : (VarKind.let == VarKind.awaitUsing) = false := by decide
  have h3 : (VarKind.let == VarKind.const) = false := by decide
  simp only [Sem.forS, SumForProof.initD, h1, h2, h3, withDisposeScope, Bool.or_false, Bool.false_eq_true, ↓reduceIte,
    Bool.not_false, M.bind_eq, M.bind_apply, hlex, newDeclEnv_eq, M.bindRes_ok, ← perIterationEnv_def]
  obtain ⟨E0, hE0⟩ : ∃ E0, t.envs.size = E0 := ⟨_, rfl⟩
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
  have hpi := perIterationEnv_one "i" E0 L t3 _ { value := some (num 0), deletable := false } (num 0) hE03 e3E0
    (by simp [Std.HashMap.getElem?_modify]) rfl
  obtain ⟨E1, hE1⟩ : ∃ E1, t3.envs.size = E1 := ⟨_, rfl⟩
  rw [hE1] at hpi
  obtain ⟨t4, ht4⟩ : ∃ t4, (t3.pushEnv (.decl {} (some L))).setEnv E1 (.decl (((∅ : Std.HashMap JSStr Binding).insert
      "i" { deletable := false }).modify "i" fun bd => { bd with value := some (num 0) }) (some L)) = t4 := ⟨_, rfl⟩
  rw [ht4] at hpi
  have f4 : t4.fuel = t.fuel := by rw [← ht4, State.setEnv_fuel, State.pushEnv_fuel, f3]
  have hS4 : ShapeI E1 L F N A (some (num (0 : Nat))) t4 := by
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
        rfl, by simp [Std.HashMap.getElem?_modify, Std.HashMap.getElem?_insert, TotalProof.ne_ia],
        by simp [Std.HashMap.getElem?_modify, Std.HashMap.getElem?_insert, ne_in]⟩
    · exact ⟨bL, bda, by rw [e4 L hLE1 hL3, e3 L hL, hLE], hla, hav, hln⟩
    · obtain ⟨bF, o, ts, tv, fo, nt, bn, hFE, hbF, hbnv⟩ := hFn
      exact ⟨bF, o, ts, tv, fo, nt, bn, by rw [e4 F hFE1 hF3, e3 F hF, hFE], hbF, hbnv⟩
  have hH4 : HeapI R A P 0 t4 := by
    refine heapI_of R A P 0 t t4 (fun x => ?_) ?_ hH
    · rw [← ht4, State.setEnv_objEntry, State.pushEnv_objEntry, ← ht3, State.setEnv_objEntry, ← ht2,
        State.setEnv_objEntry, ← ht1, State.pushEnv_objEntry]
    · rw [← ht4, State.setEnv_heap_size, State.pushEnv_heap_size, ← ht3, State.setEnv_heap_size, ← ht2,
        State.setEnv_heap_size, ← ht1, State.pushEnv_heap_size]
  have hfr4 : Frame A t t4 := by
    refine ⟨by rw [← ht4, State.setEnv_envs_size, State.pushEnv_size, z3]; omega, fun e he => ?_,
      by rw [← ht4, State.setEnv_heap_size, State.pushEnv_heap_size, ← ht3, State.setEnv_heap_size, ← ht2,
        State.setEnv_heap_size, ← ht1, State.pushEnv_heap_size], fun o _ => ?_, ?_⟩
    · have he3 : e < t3.envs.size := by rw [z3]; exact Nat.lt_succ_of_lt he
      have hne : E1 ≠ e := by rw [← hE1, z3]; exact Ne.symm (Nat.ne_of_lt (Nat.lt_succ_of_lt he))
      rw [← ht4, State.setEnv_envEntry_ne _ _ _ _ hne, State.pushEnv_entry_lt _ _ _ he3, e3 e he]
    · rw [← ht4, State.setEnv_objEntry, State.pushEnv_objEntry, ← ht3, State.setEnv_objEntry, ← ht2,
        State.setEnv_objEntry, ← ht1, State.pushEnv_objEntry]
    · rw [← ht4, State.setEnv_realms, State.pushEnv_realms, ← ht3, State.setEnv_realms, ← ht2, State.setEnv_realms,
        ← ht1, State.pushEnv_realms]
  obtain ⟨c, t5, hloop, hc, hS5, hH5, hf5, hfr5⟩ := loopI_spec { Sem.inner ctx with strict := false } ctx.labels L F N A P R
    rfl hN hP hRA E1 t4 hS4 hH4 (by omega)
  rw [f4] at hloop
  refine ⟨c, t5, ?_, hc, hS5, hH5, by rw [← f4]; exact hf5, hfr4.trans hfr5⟩
  have hil : (Sem.inner ctx).lex = L := hlex
  simp only [hil, hE0, ht1]
  simp only [SumForProof.boundNames_ident, List.foldl_toArray', List.foldl_cons, List.foldl_nil, Array.foldl_toList,
    List.foldl, Array.empty_append, M.forArr_def, M.foldArr_toArray, M.foldList_cons, M.foldList_nil, hcm, M.bindRes_ok]
  simp only [Sem.varDecl, Sem.inner, M.bind_eq, M.bind_apply, M.forArr_def, M.foldArr_toArray, M.foldList_cons,
    M.foldList_nil, Sem.declLex, hstr, hr0, M.bindRes_ok, Sem.lit, litValue, zero_eq, pure, M.pure, initializeRefBinding,
    hin, h1, h2, Bool.false_eq_true, Bool.or_false, ↓reduceIte, hpi, M.repeatFrom, f4]
  erw [hloop]
  rfl

/-- **`iota`'s body returns a new array holding `0, 1, …, N − 1`** for every natural `N < 2^26`: started
with `a` declared (not yet initialized) in the body's lexical environment `L` and `n = N` in the function
environment `F`, provided no object on `Array.prototype`'s chain has an index property below `N`. The
array is the next object allocated. -/
theorem iota_spec (n : Nat) (ctx : Ctx) (L F : EnvId) (N : Nat) (hlex : ctx.lex = L) (hstr : ctx.strict = false)
    (hgen : ctx.isGen = false) (hN : N < 2 ^ 26) (s0 : State) (hL : L < s0.envs.size) (hF : F < s0.envs.size)
    (hLF : L ≠ F) (bL : Std.HashMap JSStr Binding) (bda : Binding) (hLE : s0.envEntry L = .decl bL (some F))
    (hla : bL[JSStr.ofString "a"]? = some bda) (hln : bL[JSStr.ofString "n"]? = none)
    (hli : bL[JSStr.ofString "i"]? = none)
    (hFn : ∃ bF o ts tv fo nt bn, s0.envEntry F = .func bF o ts tv fo nt ∧ bF[JSStr.ofString "n"]? = some bn ∧
      bn.value = some (num N))
    (hP : ∀ j < N, AbsentChain s0 2 s0.curRealm.arrayProto (PropKey.ofNat j)) (hf : N + 12 ≤ s0.fuel) :
    ∃ s', IotaGen.iota n ctx s0 = .ok (.ret (.obj s0.heap.size)) s' ∧ ArrayObj s0.heap.size N (fun j => num j) s' ∧
      s0.envs.size ≤ s'.envs.size ∧ (∀ e, e < s0.envs.size → e ≠ L → s'.envEntry e = s0.envEntry e) ∧
      s'.heap.size = s0.heap.size + 1 ∧ (∀ x, x < s0.heap.size → s'.objEntry x = s0.objEntry x) ∧
      s'.realms = s0.realms ∧ s'.fuel + N + 1 = s0.fuel := by
  -- `let a = []`
  have hr : resolveBinding L "a" false s0 = .ok (.env (some L) "a" false) s0 :=
    resolveBinding_here L _ false s0 hL (by rw [hLE]; rfl)
      (by rw [hLE]; simp [Env.bindingsMap, Std.HashMap.contains_eq_isSome_getElem?, hla]) (by omega)
  obtain ⟨t1, hlit, hA1, he1, hf1, hz1, ho1, hr1, hp1⟩ := array_literal { ctx with labels := #[], lex := L, strict := false, isGen := false } [] (by simp) (by simp) s0
  simp only [List.map_nil, List.length_nil] at hlit hA1
  obtain ⟨A, hAeq⟩ : ∃ A, s0.heap.size = A := ⟨_, rfl⟩
  rw [hAeq] at hlit hA1 hp1
  have hl1 : L < t1.envs.size := by rw [he1]; exact hL
  have hE1 : t1.envEntry L = .decl bL (some F) := by simp only [State.envEntry, he1]; exact hLE
  have hin := initializeBinding_declLike L "a" (.obj A) t1 hl1 (by rw [hE1]; rfl)
  rw [hE1] at hin
  obtain ⟨t2, ht2⟩ : ∃ t2, t1.setEnv L ((Env.decl bL (some F)).withBindings
      (·.modify "a" fun bd => { bd with value := some (.obj A) })) = t2 := ⟨_, rfl⟩
  rw [ht2] at hin
  have hS2 : ShapeBI L F N A t2 := by
    refine ⟨by rw [← ht2, State.setEnv_envs_size]; exact hl1, by rw [← ht2, State.setEnv_envs_size, he1]; exact hF, hLF,
      ⟨_, { bda with value := some (.obj A) }, by rw [← ht2, State.setEnv_envEntry_self _ _ _ hl1]; rfl,
        by simp [Std.HashMap.getElem?_modify, hla], rfl, by simp [Std.HashMap.getElem?_modify, ne_an, hln],
        by simp [Std.HashMap.getElem?_modify, ne_ai, hli]⟩, ?_⟩
    obtain ⟨bF, o, ts, tv, fo, nt, bn, hFE, hbF, hbnv⟩ := hFn
    refine ⟨bF, o, ts, tv, fo, nt, bn, ?_, hbF, hbnv⟩
    rw [← ht2, State.setEnv_envEntry_ne _ _ _ _ hLF]; simp only [State.envEntry, he1]; exact hFE
  have hH2 : HeapI s0 A s0.curRealm.arrayProto 0 t2 := by
    obtain ⟨a1, a2, a3, a4, -, a6⟩ := hA1
    refine ⟨⟨by rw [← ht2, State.setEnv_heap_size]; exact a1, by rw [← ht2, State.setEnv_objEntry]; exact a2,
      by rw [← ht2, State.setEnv_objEntry]; exact a3, by rw [← ht2, State.setEnv_objEntry]; exact a4,
      fun j hj => absurd hj (Nat.not_lt_zero _), fun j hj hjb => by rw [← ht2, State.setEnv_objEntry]; exact a6 j hj hjb⟩,
      by rw [← ht2, State.setEnv_objEntry]; exact hp1, fun x hx => by rw [← ht2, State.setEnv_objEntry, ho1 x hx],
      by rw [← ht2, State.setEnv_heap_size, hz1]; omega⟩
  have hf2 : t2.fuel = s0.fuel := by rw [← ht2, State.setEnv_fuel, hf1]
  -- the loop
  obtain ⟨c, t3, hfor, ⟨w, hc⟩, ⟨E, hS3⟩, hH3, hf3, hfr3⟩ := forI_spec ctx L F N A s0.curRealm.arrayProto s0 hlex hstr hN hP
    (by rw [hAeq]; exact Nat.le_refl _) t2 hS2 hH2 (by omega)
  subst hc
  obtain ⟨-, h3L, -, -, -, -, -, ⟨bL3, bda3, h3LE, hla3, hav3, -⟩, -⟩ := hS3
  -- `return a`
  have hret : identValue L "a" false t3 = .ok (.obj A) t3 :=
    identValue_skip0 L _ false t3 bda3 _ h3L (by rw [h3LE]; rfl) (by rw [h3LE]; exact hla3) hav3 (by omega)
  have hz2e : t2.envs.size = s0.envs.size := by rw [← ht2, State.setEnv_envs_size, he1]
  rw [hAeq]
  refine ⟨t3, ?_, hH3.1, by rw [← hz2e]; exact hfr3.1,
    fun e he heL => by
      rw [hfr3.2.1 e (by rw [hz2e]; exact he), ← ht2, State.setEnv_envEntry_ne _ _ _ _ (Ne.symm heL)]
      simp only [State.envEntry, he1],
    by rw [hfr3.2.2.1, ← ht2, State.setEnv_heap_size, hz1, hAeq], fun x hx => hH3.2.2.1 x (by rw [hAeq]; exact hx),
    by rw [hfr3.2.2.2.2, ← ht2, State.setEnv_realms, hr1], by rw [hf3, hf2]⟩
  simp only [SumForProof.initD, SumForProof.testD, SumForProof.updD, bodyD, zero_eq] at hfor
  obtain ⟨j, hj⟩ : ∃ j, s0.fuel = j + 4 := ⟨s0.fuel - 4, by omega⟩
  have hlu : (VarKind.let == VarKind.using) = false := by decide
  have hla' : (VarKind.let == VarKind.awaitUsing) = false := by decide
  simp only [IotaGen.iota, Sem.stmts, M.repeatFrom, hj, M.loop]
  simp [M.bind_eq, M.bind_apply, Sem.varDecl, Sem.inner, Sem.declLex, hlex, hstr, hr, hlit, initializeRefBinding,
    hin, hlu, hla', M.forArr, pure, M.pure, hfor, Sem.breakToNormal, Sem.ret, Sem.ident, hret, hgen, Compl.updateEmpty,
    zero_eq]

/-- The same for the interpreter itself, on `iota`'s syntax tree. -/
theorem iota_interp_spec (n : Nat) (ctx : Ctx) (L F : EnvId) (N : Nat) (hlex : ctx.lex = L)
    (hstr : ctx.strict = false) (hgen : ctx.isGen = false) (hN : N < 2 ^ 26) (s0 : State) (hL : L < s0.envs.size)
    (hF : F < s0.envs.size) (hLF : L ≠ F) (bL : Std.HashMap JSStr Binding) (bda : Binding)
    (hLE : s0.envEntry L = .decl bL (some F)) (hla : bL[JSStr.ofString "a"]? = some bda)
    (hln : bL[JSStr.ofString "n"]? = none) (hli : bL[JSStr.ofString "i"]? = none)
    (hFn : ∃ bF o ts tv fo nt bn, s0.envEntry F = .func bF o ts tv fo nt ∧ bF[JSStr.ofString "n"]? = some bn ∧
      bn.value = some (num N))
    (hP : ∀ j < N, AbsentChain s0 2 s0.curRealm.arrayProto (PropKey.ofNat j)) (hf : N + 12 ≤ s0.fuel) :
    ∃ s', evalStmts (n + 35) ctx IotaGen.iota_stmts s0 = .ok (.ret (.obj s0.heap.size)) s' ∧
      ArrayObj s0.heap.size N (fun j => num j) s' ∧
      s0.envs.size ≤ s'.envs.size ∧ (∀ e, e < s0.envs.size → e ≠ L → s'.envEntry e = s0.envEntry e) ∧
      s'.heap.size = s0.heap.size + 1 ∧ (∀ x, x < s0.heap.size → s'.objEntry x = s0.objEntry x) ∧
      s'.realms = s0.realms ∧ s'.fuel + N + 1 = s0.fuel := by
  rw [← congrFun (IotaGen.iota_eq n) ctx]
  exact iota_spec n ctx L F N hlex hstr hgen hN s0 hL hF hLF bL bda hLE hla hln hli hFn hP hf

end IotaProof
