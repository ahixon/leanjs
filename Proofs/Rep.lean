import Proofs.SumFor
import Proofs.Strings
import Proofs.RPGen
import Proofs.MoreCalls
import Proofs.Script
import Proofs.Stmts
import Proofs.Runs

/-!
# Strings: `rep(n)` builds "ab" repeated `n` times (examples/rep.js)

```js
function rep(n) { let s = ""; for (let i = 0; i < n; i = i + 1) { s = s + "ab"; } return s; }
let r = rep(5);
r.length;
```
The loop as for `sumFor` (Proofs/SumFor.lean, whose environment shapes are reused), with `s` a string:
each iteration concatenates (`applyBinaryOp_add_str`). `rep(N)` returns `reps N` for every `N < 2^26`; the
script reads its `length`: 10.
-/

open ES ES.Conv SumProof SumForProof

namespace Rep

/-- "ab" repeated `k` times. -/
def reps : Nat → JSStr
  | 0 => ""
  | k + 1 => reps k ++ JSStr.ofString "ab"

def bodyR : Sem.CStmt := (Sem.block (lexicallyScoped #[(Stmt.expr (Expr.assign AssignOp.assign (Pattern.ident "s") (Expr.binary BinOp.add (Expr.ident "s") (Expr.lit (Lit.str "ab")))))]) #[(Sem.exprStmt (Sem.assign (Sem.identRef "s") (Sem.binary BinOp.add (Sem.ident "s") (Sem.lit (Lit.str "ab")))))])

theorem lexBodyR : lexicallyScoped #[(Stmt.expr (Expr.assign AssignOp.assign (Pattern.ident "s") (Expr.binary BinOp.add (Expr.ident "s") (Expr.lit (Lit.str "ab")))))] = #[] := by rfl

/-- One iteration that continues: in the fresh copy `E'`, `i = k + 1`; `s = tri (k + 1)` in `L`. -/
theorem iterR_cont (ctx : Ctx) (labels : Array JSStr) (E L F : EnvId) (N k : Nat) (hstr : ctx.strict = false)
    (hk : k < N) (hN : N < 2 ^ 26) (t : State) (v : Value)
    (hS : ShapeF E L F N (some (.str (reps k))) (some (num k)) t) (hf : 5 ≤ t.fuel) :
    ∃ E' v' t', forIter SumForProof.testD SumForProof.updD bodyR labels ctx #["i"] (E, v) t = .ok (.inl (E', v')) t' ∧
      ShapeF E' L F N (some (.str (reps (k + 1)))) (some (num ((k : Int) + 1))) t' ∧ t'.fuel = t.fuel - 1 := by
  obtain ⟨hE, hL, hF, hEL, hEF, hLF, ⟨bE, bdi, hEE, hbi, hiv, him, hbs, hbn⟩, ⟨bL, bds, hLE, hls, hsv, hsm, hln⟩,
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
  -- the test: `i < n`
  have ri : identValue E "i" false t1 = .ok (num k) t1 :=
    identValue_skip0 E _ false t1 bdi _ h1E (by rw [e1, hEE]; rfl) (by rw [e1, hEE]; exact hbi) hiv (by omega)
  have rn : identValue E "n" false t1 = .ok (num N) t1 :=
    identValue_skip2 E L F _ false t1 bE bL bn _ h1E (by rw [e1]; exact hEE) hbn h1L
      (by rw [e1]; exact hLE) hln h1F (by rw [e1, hFE]; rfl) (by rw [e1, hFE]; exact hbF) hbnv (by omega)
  have hlt : ltF (ofSmallInt k) (ofSmallInt N) = true := by rw [ltF_int _ _ hkb hNb]; simp [hk]
  -- the body: `s = s + i`
  have rs : identValue E "s" false t1 = .ok (.str (reps k)) t1 :=
    identValue_skip1 E L _ false t1 bE bds _ h1E (by rw [e1]; exact hEE) hbs h1L
      (by rw [e1, hLE]; rfl) (by rw [e1, hLE]; exact hls) hsv (by omega)
  have rrs : resolveBinding E "s" false t1 = .ok (.env (some L) "s" false) t1 :=
    resolveBinding_skip1 E L _ false t1 bE h1E (by rw [e1]; exact hEE) hbs h1L (by rw [e1, hLE]; rfl)
      (by rw [e1, hLE]; simp [Env.bindingsMap, Std.HashMap.contains_eq_isSome_getElem?, hls]) (by omega)
  have hcat : (reps k ++ JSStr.ofString "ab") = reps (k + 1) := rfl
  have hset_s := setMutableBinding_decl L "s" (.str (reps (k + 1))) false t1 bL (some F) bds h1L
    (by rw [e1]; exact hLE) hls (by simp [hsv]) hsm
  obtain ⟨t2, ht2⟩ : ∃ t2, t1.setEnv L (.decl (bL.modify "s" fun bd => { bd with value := some (.str (reps (k + 1))) })
      (some F)) = t2 := ⟨_, rfl⟩
  rw [ht2] at hset_s
  have z2 : t2.envs.size = t.envs.size := by rw [← ht2, State.setEnv_envs_size, z1]
  have f2 : t2.fuel = t.fuel - 1 := by rw [← ht2, State.setEnv_fuel, f1]
  have e2E : t2.envEntry E = .decl bE (some L) := by rw [← ht2, State.setEnv_envEntry_ne _ _ _ _ (Ne.symm hEL), e1, hEE]
  have e2L : t2.envEntry L = .decl (bL.modify "s" fun bd => { bd with value := some (.str (reps (k + 1))) }) (some F) := by
    rw [← ht2]; exact State.setEnv_envEntry_self _ _ _ h1L
  have e2F : t2.envEntry F = .func bF o ts tv fo nt := by rw [← ht2, State.setEnv_envEntry_ne _ _ _ _ hLF, e1, hFE]
  -- the copy of the loop environment
  have hpi := perIterationEnv_one "i" E L t2 bE bdi (num k) (by rw [z2]; exact hE) e2E hbi hiv
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
  have hS4 : ShapeF E' L F N (some (.str (reps (k + 1)))) (some (num ((k : Int) + 1))) t4 := by
    refine ⟨by rw [z4, ← hE', z2]; exact Nat.lt_succ_self _, by rw [z4]; exact Nat.lt_succ_of_lt hL,
      by rw [z4]; exact Nat.lt_succ_of_lt hF, Ne.symm hLE', Ne.symm hFE', hLF, ?_, ?_, ?_⟩
    · refine ⟨bE'.modify "i" fun bd => { bd with value := some (num ((k : Int) + 1)) },
        { value := some (num ((k : Int) + 1)), deletable := false }, ?_, ?_, rfl, rfl, ?_, ?_⟩
      · rw [← ht4]; exact State.setEnv_envEntry_self _ _ _ hE'lt
      · rw [← hbE']; simp [Std.HashMap.getElem?_modify]
      · rw [← hbE']; simp [Std.HashMap.getElem?_modify, Std.HashMap.getElem?_insert, ne_is]
      · rw [← hbE']; simp [Std.HashMap.getElem?_modify, Std.HashMap.getElem?_insert, ne_in]
    · refine ⟨bL.modify "s" fun bd => { bd with value := some (.str (reps (k + 1))) },
        { bds with value := some (.str (reps (k + 1))) }, ?_, ?_, rfl, hsm, ?_⟩
      · rw [e4 L hLE' (by rw [z2]; exact hL), e2L]
      · simp [Std.HashMap.getElem?_modify, hls]
      · simp [Std.HashMap.getElem?_modify, ne_sn, hln]
    · exact ⟨bF, o, ts, tv, fo, nt, bn, by rw [e4 F hFE' (by rw [z2]; exact hF), e2F], hbF, hbnv⟩
  refine ⟨E', .str (reps (k + 1)), t4, ?_, hS4, f4⟩
  obtain ⟨j, hj⟩ : ∃ j, t1.fuel = j + 2 := ⟨t1.fuel - 2, by omega⟩
  simp only [forIter, M.bind_eq, M.bind_apply, htick, M.bindRes_ok, SumForProof.testD, Sem.binary, Sem.ident, hstr, ri, rn]
  simp [Sem.binaryOp, isLessThan, M.bind_eq, M.bind_apply, hlt, ofSmallInt_eq_nan, toBoolean, pure, M.pure, bodyR,
    lexBodyR, Sem.block, Sem.stmts, M.repeatFrom, hj, M.loop, Sem.exprStmt, Sem.assign, Sem.identRef, Sem.inner, hstr,
    rrs, Sem.binary, Sem.ident, rs, ri, applyBinaryOp_add_str, hcat, putRefValue, hset_s, loopContinues,
    Compl.value?, hpi, SumForProof.updD, rri3, ri3, Sem.lit, litValue, one_eq, hadd_i, hset_i]

/-- The last iteration: `i < n` fails. -/
theorem iterR_exit (ctx : Ctx) (labels : Array JSStr) (E L F : EnvId) (N : Nat) (hstr : ctx.strict = false)
    (hN : N < 2 ^ 26) (t : State) (v : Value)
    (hS : ShapeF E L F N (some (.str (reps N))) (some (num N)) t) (hf : 4 ≤ t.fuel) :
    ∃ t', forIter SumForProof.testD SumForProof.updD bodyR labels ctx #["i"] (E, v) t = .ok (.inr (.normal (some v))) t' ∧
      ShapeF E L F N (some (.str (reps N))) (some (num N)) t' ∧ t'.fuel = t.fuel - 1 := by
  have hS' := hS
  obtain ⟨hE, hL, hF, -, -, -, ⟨bE, bdi, hEE, hbi, hiv, -, -, hbn⟩, ⟨bL, -, hLE, -, -, -, hln⟩,
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
  refine ⟨t1, ?_, by rw [← ht1]; exact hS', f1⟩
  simp only [forIter, M.bind_eq, M.bind_apply, htick, M.bindRes_ok, SumForProof.testD, Sem.binary, Sem.ident, hstr, ri, rn]
  simp [Sem.binaryOp, isLessThan, M.bind_eq, M.bind_apply, hlt, ofSmallInt_eq_nan, toBoolean, pure, M.pure]

/-- The loop, from the first iteration's environment with `i = 0` and `s = tri 0`. -/
theorem loopR_spec (ctx : Ctx) (labels : Array JSStr) (L F : EnvId) (N : Nat) (hstr : ctx.strict = false)
    (hN : N < 2 ^ 26) (E0 : EnvId) (t : State)
    (hS : ShapeF E0 L F N (some (.str (reps 0))) (some (num (0 : Nat))) t) (hf : N + 5 ≤ t.fuel) :
    ∃ c t', M.loop (forIter SumForProof.testD SumForProof.updD bodyR labels ctx #["i"]) t.fuel (E0, .undefined) t = .ok c t' ∧
      (∃ w, c = Compl.normal (some w)) ∧ (∃ E, ShapeF E L F N (some (.str (reps N))) (some (num N)) t') ∧
      t'.fuel + N + 1 = t.fuel := by
  let I : EnvId × Value → State → Prop := fun st u =>
    ∃ k, k ≤ N ∧ ShapeF st.1 L F N (some (.str (reps k))) (some (num k)) u ∧ u.fuel + k = t.fuel
  let Q : Compl → State → Prop := fun c u =>
    (∃ w, c = Compl.normal (some w)) ∧ (∃ E, ShapeF E L F N (some (.str (reps N))) (some (num N)) u) ∧
      u.fuel + N + 1 = t.fuel
  let V : EnvId × Value → State → Nat := fun _ u => u.fuel + N - t.fuel
  have hstep : ∀ st u, I st u →
      (∃ st' u', forIter SumForProof.testD SumForProof.updD bodyR labels ctx #["i"] st u = .ok (.inl st') u' ∧ I st' u' ∧ V st' u' < V st u) ∨
      (∃ c u', forIter SumForProof.testD SumForProof.updD bodyR labels ctx #["i"] st u = .ok (.inr c) u' ∧ Q c u') := by
    intro ⟨E, v⟩ u ⟨k, hk, hSu, hfu⟩
    by_cases hkN : k < N
    · obtain ⟨E', v', u', h, hS', hf'⟩ := iterR_cont ctx labels E L F N k hstr hkN hN u v hSu (by omega)
      have hc : ((k + 1 : Nat) : Int) = (k : Int) + 1 := by omega
      exact Or.inl ⟨(E', v'), u', h, ⟨k + 1, hkN, by rw [hc]; exact hS', by omega⟩, by simp only [V]; omega⟩
    · have hkN' : k = N := by omega
      subst hkN'
      obtain ⟨u', h, hS', hf'⟩ := iterR_exit ctx labels E L F k hstr hN u v hSu (by omega)
      exact Or.inr ⟨_, u', h, ⟨v, rfl⟩, ⟨E, hS'⟩, by omega⟩
  exact M.loop_inv _ I Q V hstep t.fuel (E0, .undefined) t ⟨0, Nat.zero_le _, hS, by simp⟩ (by simp only [V]; omega)

/-- The `for` statement: from `s = 0`, it completes normally with `s = tri N`. -/
theorem forSR_spec (ctx : Ctx) (L F : EnvId) (N : Nat) (hlex : ctx.lex = L) (hstr : ctx.strict = false)
    (hN : N < 2 ^ 26) (t : State) (hS : ShapeB L F N (some (.str "")) t) (hf : N + 8 ≤ t.fuel) :
    ∃ c t', Sem.forS SumForProof.initD SumForProof.testD SumForProof.updD bodyR ctx t = .ok (Sem.breakToNormal c) t' ∧
      (∃ w, c = Compl.normal (some w)) ∧ (∃ E, ShapeF E L F N (some (.str (reps N))) (some (num N)) t') ∧
      t'.fuel + N + 1 = t.fuel := by
  obtain ⟨hL, hF, hLF, ⟨bL, bds, hLE, hls, hsv, hsm, hln, hli⟩, hFn⟩ := hS
  have h1 : (VarKind.let == VarKind.using) = false := by decide
  have h2 : (VarKind.let == VarKind.awaitUsing) = false := by decide
  have h3 : (VarKind.let == VarKind.const) = false := by decide
  simp only [Sem.forS, SumForProof.initD, h1, h2, h3, withDisposeScope, Bool.or_false, Bool.false_eq_true, ↓reduceIte,
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
  have hS4 : ShapeF E1 L F N (some (.str (reps 0))) (some (num (0 : Nat))) t4 := by
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
        by simp [Std.HashMap.getElem?_modify], by simp [tri],
        rfl, by simp [Std.HashMap.getElem?_modify, Std.HashMap.getElem?_insert, ne_is],
        by simp [Std.HashMap.getElem?_modify, Std.HashMap.getElem?_insert, ne_in]⟩
    · exact ⟨bL, bds, by rw [e4 L hLE1 hL3, e3 L hL, hLE], hls, hsv, hsm, hln⟩
    · obtain ⟨bF, o, ts, tv, fo, nt, bn, hFE, hbF, hbnv⟩ := hFn
      exact ⟨bF, o, ts, tv, fo, nt, bn, by rw [e4 F hFE1 hF3, e3 F hF, hFE], hbF, hbnv⟩
  -- the loop
  obtain ⟨c, t5, hloop, hc, hS5, hf5⟩ := loopR_spec { Sem.inner ctx with strict := false } ctx.labels L F N rfl hN E1 t4
    hS4 (by omega)
  rw [f4] at hloop
  refine ⟨c, t5, ?_, hc, hS5, by rw [← f4]; exact hf5⟩
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

/-- **`sumFor`'s body returns 0 + 1 + … + (N − 1)** for every natural `N < 2^26`: started with `s` declared
(not yet initialized) in the body's lexical environment `L` and `n = N` in the function environment `F`. -/
theorem rep_spec (n : Nat) (ctx : Ctx) (L F : EnvId) (N : Nat) (hlex : ctx.lex = L) (hstr : ctx.strict = false)
    (hgen : ctx.isGen = false) (hN : N < 2 ^ 26) (s0 : State) (hS : ShapeB L F N none s0)
    (hf : N + 12 ≤ s0.fuel) :
    ∃ s', RPGen.rep n ctx s0 = .ok (.ret (.str (reps N))) s' := by
  obtain ⟨hL, hF, hLF, ⟨bL, bds, hLE, hls, hsv, hsm, hln, hli⟩, hFn⟩ := hS
  -- `let s = 0`
  have hr : resolveBinding L "s" false s0 = .ok (.env (some L) "s" false) s0 :=
    resolveBinding_here L _ false s0 hL (by rw [hLE]; rfl)
      (by rw [hLE]; simp [Env.bindingsMap, Std.HashMap.contains_eq_isSome_getElem?, hls]) (by omega)
  have hin := initializeBinding_declLike L "s" (.str "") s0 hL (by rw [hLE]; rfl)
  rw [hLE] at hin
  obtain ⟨s1, hs1⟩ : ∃ s1, s0.setEnv L ((Env.decl bL (some F)).withBindings
      (·.modify "s" fun bd => { bd with value := some (.str "") })) = s1 := ⟨_, rfl⟩
  rw [hs1] at hin
  have e1L : s1.envEntry L = .decl (bL.modify "s" fun bd => { bd with value := some (.str "") }) (some F) := by
    rw [← hs1, State.setEnv_envEntry_self _ _ _ hL]; rfl
  have hS1 : ShapeB L F N (some (.str "")) s1 := by
    refine ⟨by rw [← hs1, State.setEnv_envs_size]; exact hL, by rw [← hs1, State.setEnv_envs_size]; exact hF, hLF,
      ⟨_, { bds with value := some (.str "") }, e1L, by simp [Std.HashMap.getElem?_modify, hls], rfl, hsm,
        by simp [Std.HashMap.getElem?_modify, ne_sn, hln], by simp [Std.HashMap.getElem?_modify, ne_si, hli]⟩, ?_⟩
    obtain ⟨bF, o, ts, tv, fo, nt, bn, hFE, hbF, hbnv⟩ := hFn
    exact ⟨bF, o, ts, tv, fo, nt, bn, by rw [← hs1, State.setEnv_envEntry_ne _ _ _ _ hLF, hFE], hbF, hbnv⟩
  have f1 : s1.fuel = s0.fuel := by rw [← hs1, State.setEnv_fuel]
  -- the loop
  obtain ⟨c, s2, hfor, ⟨w, hc⟩, ⟨E, hS2⟩, hf2⟩ := forSR_spec ctx L F N hlex hstr hN s1 hS1 (by omega)
  subst hc
  obtain ⟨-, h2L, -, -, -, -, -, ⟨bL2, bds2, h2LE, hls2, hsv2, -, -⟩, -⟩ := hS2
  have hret : identValue L "s" false s2 = .ok (.str (reps N)) s2 :=
    identValue_skip0 L _ false s2 bds2 _ h2L (by rw [h2LE]; rfl) (by rw [h2LE]; exact hls2) hsv2 (by omega)
  simp only [SumForProof.initD, SumForProof.testD, SumForProof.updD, bodyR, zero_eq] at hfor
  obtain ⟨j, hj⟩ : ∃ j, s0.fuel = j + 4 := ⟨s0.fuel - 4, by omega⟩
  have hlu : (VarKind.let == VarKind.using) = false := by decide
  have hla : (VarKind.let == VarKind.awaitUsing) = false := by decide
  simp only [RPGen.rep, Sem.stmts, M.repeatFrom, hj, M.loop]
  simp [M.bind_eq, M.bind_apply, Sem.varDecl, Sem.inner, Sem.declLex, hlex, hstr, hr, Sem.lit, litValue,
    zero_eq, initializeRefBinding, hin, hlu, hla, M.forArr, pure, M.pure, hfor, Sem.breakToNormal, Sem.ret,
    Sem.ident, hret, hgen, Compl.updateEmpty]

/-! ## The call of `rep` -/

theorem lexRep : topLevelLexicallyScoped RPGen.rep_stmts = #[.binding .let (.ident "s")] := by
  have hv : (VarKind.let == VarKind.var) = false := by decide
  simp [topLevelLexicallyScoped, stmtLexScoped, RPGen.rep_stmts, hv]

open MoreCalls in
theorem rep_fdi (f : ObjId) (d : FuncData) (env : EnvId) (s : State) (N : Nat) (tv : Value)
    (hcode : d.code = RPGen.rep_func) (henv : env < s.envs.size)
    (hE : s.envEntry env = .func ∅ (some d.env) .initialized tv f .undefined)
    (hf : s.fuel ≠ 0) :
    ∃ ctx s', functionDeclarationInstantiation 999999 f d env #[num N] s = .ok ctx s' ∧
      ctx.lex = s.envs.size ∧ ctx.strict = false ∧ ctx.isGen = false ∧
      ShapeB s.envs.size env N none s' ∧ s'.fuel = s.fuel ∧ s'.heap = s.heap ∧
      (∀ e, e < s.envs.size → e ≠ env → s'.envEntry e = s.envEntry e) := by
  have hr : Array.range 1 = [0].toArray := by decide
  have hbe : ∀ ctx x v b, b.contains x = true →
      bindElement 999998 ctx (.ident x) none (.init (some env)) (M.pure v)
          (s.setEnv env (.func b (some d.env) .initialized tv f .undefined)) =
        .ok () (s.setEnv env (.func (b.modify x fun bd => { bd with value := some v })
          (some d.env) .initialized tv f .undefined)) := by
    intro ctx x v b hb
    have := bindElement_ident 999998 ctx x env v (s.setEnv env (.func b (some d.env) .initialized tv f .undefined))
      (by omega) (by simpa using henv) (by simp [henv]) (by simpa [henv] using hb) (by simpa using hf)
    simpa [henv] using this
  have hbody : RPGen.rep_func.body = .stmts RPGen.rep_stmts := rfl
  have hparams : RPGen.rep_func.params = #[.mk (.ident "n") none false] := rfl
  have hstr : RPGen.rep_func.strict = false := rfl
  have hasync : RPGen.rep_func.isAsync = false := rfl
  have hgen : RPGen.rep_func.isGenerator = false := rfl
  have hkind : RPGen.rep_func.kind = .normal := rfl
  have hfdi : RPGen.rep_func.info.fdi = { paramNames := #["n"], hasDuplicates := false, varNames := #[], hasFunctions := false, functionNames := #[], hasLexical := true, lexNames := #["s"], argumentsNeeded := false, hasAnnexB := false, usesDispose := false } := rfl
  have hk1 : (VarKind.let == VarKind.const) = false := by decide
  have hk2 : (VarKind.let == VarKind.using) = false := by decide
  have hk3 : (VarKind.let == VarKind.awaitUsing) = false := by decide
  have hphe : RPGen.rep_func.info.paramsHaveExpressions = false := rfl
  refine ⟨?c, ?t, ?h, ?_⟩
  case h =>
    conv =>
      lhs
      simp only [functionDeclarationInstantiation, hcode, hbody, hparams, hstr, hfdi, hasync, hgen, hkind, hphe]
      simp [hr, hasBinding_declLike, createMutableBinding_declLike, hbe, newDeclEnv, pure,
        M.pure, hE, henv, hf, lexRep, TotalCall.names_s, -allocEnv_apply, allocEnv_eq, LexScoped.isConstant,
        State.pushEnv_entry_at, State.setEnv_envEntry_self, hk1, hk2, hk3]
  have hne : s.envs.size ≠ env := Nat.ne_of_gt henv
  have hne' : env ≠ s.envs.size := Nat.ne_of_lt henv
  refine ⟨rfl, rfl, rfl, ?_, by simp, by simp [State.setEnv, State.pushEnv], ?_⟩
  · refine ⟨by simp, by simp; exact Nat.lt_succ_of_lt henv, hne, ?_, ?_⟩
    · simp [State.setEnv_envEntry_self, Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert, ne_sn', ne_is, ne_in, ne_si]
    · simp [State.setEnv_envEntry_ne _ _ _ _ hne, State.pushEnv_entry_lt, State.setEnv_envEntry_self,
        henv, Std.HashMap.getElem?_modify]
  · intro e he hee
    simp [State.setEnv_envEntry_ne _ _ _ _ (show s.envs.size ≠ e by omega), State.pushEnv_entry_lt, he,
      State.setEnv_envEntry_ne _ _ _ _ (Ne.symm hee)]

theorem rep_body (f : ObjId) (d : FuncData) (env : EnvId) (s : State) (N : Nat) (tv : Value)
    (hcode : d.code = RPGen.rep_func) (henv : env < s.envs.size)
    (hE : s.envEntry env = .func ∅ (some d.env) .initialized tv f .undefined)
    (hN : N < 2 ^ 26) (hf : N + 12 ≤ s.fuel) :
    ∃ s', evalFunctionBody evalDepth f d env #[num N] s = .ok (.str (reps N)) s' := by
  obtain ⟨ctx, s', hfdi, hlex, hstr, hgen, hS, hfuel, -, -⟩ := rep_fdi f d env s N tv hcode henv hE (by omega)
  obtain ⟨s'', hbody⟩ := rep_spec 999964 ctx s.envs.size env N hlex hstr hgen hN s' hS (by omega)
  refine ⟨s'', ?_⟩
  have hbd : d.code.body = .stmts RPGen.rep_stmts := by rw [hcode]; rfl
  have hdisp : d.code.info.fdi.usesDispose = false := by rw [hcode]; rfl
  have hbody' : evalStmts (999964 + 35) ctx RPGen.rep_stmts s' = .ok (.ret (.str (reps N))) s'' := by
    rw [← congrFun (RPGen.rep_eq 999964) ctx]; exact hbody
  simp only [evalDepth, evalFunctionBody, M.bind_eq, M.bind_apply, hfdi, M.bindRes_ok, hbd, hdisp, withDisposeScope]
  rw [show (999999 : Nat) = 999964 + 35 from rfl]
  simp [hbody', pure, M.pure]

/-- **The [[Call]] of `rep` with `N`** (`this` undefined): returns "ab" repeated `N` times, for every `N < 2^26`. -/
theorem rep_call (f : ObjId) (d : FuncData) (s : State) (N : Nat) (go : ObjId)
    (gb : Std.HashMap JSStr Binding) (gtv : Value)
    (hcode : d.code = RPGen.rep_func) (hcls : d.isClassCtor = false) (hmode : d.thisMode = .global)
    (hge : (s.realms[d.realm]!).globalEnv < s.envs.size)
    (hgE : s.envEntry (s.realms[d.realm]!).globalEnv = .global go gb gtv)
    (hN : N < 2 ^ 26) (hf : N + 12 ≤ s.fuel) :
    ∃ s', callECMA f d .undefined #[num N] s = .ok (.str (reps N)) s' :=
  let ⟨s', h1, _⟩ := Calls.callECMA_undef (Q := fun _ => True) f d s _ _ go gb gtv hcls hmode
    (by rw [hcode]; rfl) (by rw [hcode]; rfl) hge hgE
    (fun t hlt hEt _ _ hfu _ _ =>
      let ⟨t', ht'⟩ := rep_body f d s.envs.size t N gtv hcode hlt hEt hN (by omega)
      ⟨t', ht', trivial⟩)
  ⟨s', h1⟩

/-! ## Its length -/

theorem size_ab : (JSStr.ofString "ab").b.size = 4 := by decide

theorem reps_size (n : Nat) : (reps n).b.size = 4 * n := by
  induction n with
  | zero => decide
  | succ k ih => simp only [reps, JSStr.size_append, ih, size_ab]; omega

/-- `rep(N)` has `2N` code units. -/
theorem reps_length (n : Nat) : (reps n).length = 2 * n := by
  simp only [JSStr.length, reps_size]; omega

/-- The string itself, for `N = 5`. -/
theorem reps_five : reps 5 = JSStr.ofString "ababababab" := by
  apply congrArg JSStr.mk; apply ByteArray.ext; decide

/-! ## The whole script -/

open Script

abbrev l5 : F64 := F64.fin false 5629499534213120 (-50)
theorem l5_eq : l5 = ofSmallInt ((5 : Nat) : Int) := by decide
abbrev callRep : Sem.CExpr := Sem.call (Sem.identRef "rep") (Sem.args #[Sem.ArgD.expr (Sem.lit (Lit.num l5))]) false
  (CalleeDesc.ident "rep")
abbrev lenStmt : Sem.CStmt := Sem.exprStmt (Sem.getValue (Sem.memberRef callRep (Sem.Key.name "length") false))

theorem script_def (n : Nat) : RPGen.script n = Sem.stmts #[Sem.funDecl RPGen.rep_func, lenStmt] := rfl
theorem lexScoped : topLevelLexicallyScoped RPGen.script_stmts = #[] := by
  simp [topLevelLexicallyScoped, stmtLexScoped, RPGen.script_stmts]

def fs : List (Func × JSStr) := [(RPGen.rep_func, "rep")]

theorem varS : topLevelVarScoped RPGen.program.body = (fs.map fun p => VarScoped.func p.1).toArray := rfl
theorem lexS : topLevelLexicallyScoped RPGen.program.body =
    (([] : List JSStr).map fun x => LexScoped.binding .let (.ident x)).toArray := by
  rw [show RPGen.program.body = RPGen.script_stmts from rfl, lexScoped]; rfl
theorem annS : annexBFunctions RPGen.program.body ([] : List JSStr).toArray = #[] := rfl
theorem simpleS : ∀ p ∈ fs, Inst.SimpleFn p.1 p.2 := by
  intro p hp; simp only [fs, List.mem_cons, List.mem_nil_iff, or_false] at hp; rcases hp with rfl
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem nodupS : (fs.map Prod.snd).Nodup := by decide
theorem body_eq : RPGen.program.body = RPGen.script_stmts := rfl
theorem depth_eq : evalDepth = 999956 + 44 := rfl
theorem script_body (u : State) (c : Ctx) : evalStmts evalDepth c RPGen.program.body u = RPGen.script 999956 c u := by
  rw [RPGen.script_eq, body_eq, depth_eq]
theorem ten : Conv.ofNat 10 = ofSmallInt ((10 : Nat) : Int) := by decide

/-- **`rep(5).length`**: asks the driver to call `rep`; when it returns a string, the statement's value is its
length. -/
theorem len_req (c : Ctx) (u : State) (r : Req) (K0 : Outcome → State → Res Value)
    (h0 : callRep (Sem.inner c) u = .req r u K0) (hK0 : ∀ v t, K0 (.normal v) t = .ok v t) :
    ∃ K, lenStmt c u = .req r u K ∧
      ∀ x t, K (.normal (.str x)) t = .ok (.normal (some (.num (Conv.ofNat x.length)))) t := by
  refine ⟨?K, ?h, ?_⟩
  case h =>
    conv =>
      lhs
      simp only [lenStmt, Sem.exprStmt, Sem.getValue, Sem.memberRef, M.bind_eq, M.bind_apply, h0, M.bindRes_req]
  intro x t
  simp [hK0, Value.isNullish, getRefValue_str_length, M.bind_eq, M.bind_apply, pure, M.pure, Sem.inner]

/-- **The whole program** (examples/rep.js): `rep(5)` builds "ababababab"; the script evaluates to its length,
10. Started from a realm whose global object is an ordinary extensible object without `rep`. -/
theorem rp_script (eng : Engine) (s : State) (cs : Conts) (gb : Std.HashMap JSStr Binding) (gtv : Value)
    (fp : ObjId) (hge : s.curRealm.globalEnv < s.envs.size)
    (hE : s.envEntry s.curRealm.globalEnv = .global s.curRealm.globalObj gb gtv)
    (hgbs : gb.contains "rep" = false)
    (hgs : s.curRealm.globalObj < s.heap.size) (hk : (s.objEntry s.curRealm.globalObj).kind = .ordinary)
    (hx : (s.objEntry s.curRealm.globalObj).extensible = true)
    (hps : (s.objEntry s.curRealm.globalObj).props.get? (.str "rep") = none)
    (hfp : s.curRealm.intrinsics["%Function.prototype%"]? = some fp) (hf : 30 ≤ s.fuel) :
    ∃ s', (runM eng (scriptEvaluation RPGen.program) s cs).1 = .ok (num 10) s' := by
  let ge := s.curRealm.globalEnv
  let g := s.curRealm.globalObj
  let c := scriptCtx s false
  obtain ⟨t0, ht0⟩ : ∃ y, (scriptStart s RPGen.program).setEnv ge (.global g (insertLets gb []) gtv) = y := ⟨_, rfl⟩
  have ho0 : ∀ y, t0.objEntry y = s.objEntry y := by intro y; rw [← ht0, State.setEnv_objEntry]; rfl
  have hz0 : t0.heap.size = s.heap.size := by rw [← ht0, State.setEnv_heap_size]; rfl
  have hge0 : ge < t0.envs.size := by rw [← ht0, State.setEnv_envs_size]; exact hge
  have hgood : GoodG g fp t0 := ⟨by rw [hz0]; exact hgs, by rw [ho0]; exact hk, by rw [ho0]; exact hx,
    by rw [← ht0, State.setEnv_curRealm]; exact hfp⟩
  obtain ⟨⟨-, hku, -, -⟩, heu, hfuu, hru, -, hszu, -, -, -, hnames, hfuns⟩ :=
    instAll_facts ge g s.scripts.size fp fs t0 hgood (by decide)
  obtain ⟨u, hu⟩ : ∃ y, instAll ge g s.scripts.size fp fs t0 = y := ⟨_, rfl⟩
  rw [hu] at hku heu hfuu hru hszu hnames hfuns
  have hfu0 : t0.fuel = s.fuel := by rw [← ht0, State.setEnv_fuel]; rfl
  have hrl0 : t0.realm = s.realm := by rw [← ht0, State.setEnv_realm]; rfl
  have hr0 : t0.realms = s.realms := by rw [← ht0, State.setEnv_realms]; rfl
  let fR := s.heap.size
  obtain ⟨dR, hfRk, hcR, hrR, hmR, hclsR, -, -⟩ := hfuns 0 (by decide)
  rw [hz0] at hfRk hszu hnames
  simp only [fs, List.length_cons, List.length_nil] at hszu
  simp only [Nat.mul_zero, Nat.add_zero] at hfRk
  have hpR : (u.objEntry g).props.get? (.str "rep") = some (.data (.obj fR) true true false) := hnames 0 (by decide)
  have hE1 : u.envEntry ge = .global g gb gtv := by
    have h1 : u.envEntry ge = t0.envEntry ge := by simp only [State.envEntry, heu]
    rw [h1, ← ht0, State.setEnv_envEntry_self _ _ _ (show ge < (scriptStart s RPGen.program).envs.size from hge)]
    simp [insertLets]
  have hgeu : ge < u.envs.size := by rw [heu]; exact hge0
  have hgu : g < u.heap.size := by rw [hszu]; exact Nat.lt_of_lt_of_le hgs (Nat.le_add_right _ _)
  have hfRu : fR < u.heap.size := by show s.heap.size < u.heap.size; rw [hszu]; omega
  have hgbs' : gb[JSStr.ofString "rep"]? = none := Std.HashMap.getElem?_eq_none (fun hm => by
    rw [Std.HashMap.mem_iff_contains, hgbs] at hm; exact Bool.false_ne_true hm)
  have hgbsm : (JSStr.ofString "rep" ∈ gb) = False := by simp [Std.HashMap.mem_iff_contains, hgbs]
  -- `rep(5)` asks for its call
  obtain ⟨K0, h0, hK0⟩ := Stmts.call_expr_req (Sem.inner c) u ge g fR "rep" gb gtv dR
    [(Sem.lit (Lit.num l5), .num l5)]
    (by intro p hp; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp; rcases hp with rfl; rfl)
    rfl rfl hgeu hE1 hgbs hgbs' hgbsm hgu hku hpR hfRu hfRk (by rw [hfuu, hfu0]; omega)
  obtain ⟨K4, h4, hK4⟩ := len_req c u _ K0 h0 hK0
  -- the call (`rep_call`)
  obtain ⟨u', hu'⟩ : ∃ y, ({ u with fuel := u.fuel - 1 } : State) = y := ⟨_, rfl⟩
  have hr' : u'.realms = s.realms := by rw [← hu']; exact hru.trans hr0
  have hz' : u'.envs = u.envs := by rw [← hu']
  obtain ⟨s4, hc4⟩ := rep_call fR dR u' 5 g gb gtv hcR hclsR hmR (by rw [hr', hrR, hrl0, hz']; exact hgeu)
    (by rw [hr', hrR, hrl0]; simp only [State.envEntry, hz']; exact hE1) (by decide)
    (by rw [← hu']; simp only; rw [hfuu, hfu0]; omega)
  have himpl : callImpl eng (.obj fR) .undefined #[.num l5] u = .ok (.str (reps 5)) s4 := by
    rw [l5_eq, callImpl_func eng fR dR _ _ u hfRu hfRk (by rw [hfuu, hfu0]; omega), hu']
    exact hc4
  have hlen : Conv.ofNat (reps 5).length = ofSmallInt ((10 : Nat) : Int) := by rw [reps_length]; exact ten
  -- the script
  refine ⟨s4, script_value eng s cs RPGen.program fs [] gb gtv fp _ s4 rfl varS lexS annS simpleS nodupS hge hE
    (by intro p hp; simp only [fs, List.mem_cons, List.mem_nil_iff, or_false] at hp; rcases hp with rfl; exact hgbs)
    (by simp) hgs hk hx
    (by intro p hp; simp only [fs, List.mem_cons, List.mem_nil_iff, or_false] at hp; rcases hp with rfl; exact hps)
    (by simp) hfp ?_⟩
  have hu0 : scriptState s RPGen.program fs [] gb gtv fp = u := by rw [← hu, ← ht0]; rfl
  rw [hu0, script_body, script_def]
  refine _root_.Runs.script_runs eng _ _ _ (_root_.Runs.stmts_run eng c _ u _ s4 ?_ (by simp; rw [hfuu, hfu0]; omega))
  show _root_.Runs.StmtsRun eng c [Sem.funDecl RPGen.rep_func, lenStmt] u none (some (num 10)) s4
  refine .cons _ _ u u s4 none none _ (_root_.Runs.runs_funDecl eng _ c u rfl) ?_
  refine .cons _ _ u s4 s4 (some (num 10)) none _ ?_ (.nil _ _)
  rw [h4]
  exact _root_.Runs.runsTo_req1 eng _ _ _ u K4 _ s4 _ s4 himpl (by rw [hK4, hlen]; rfl)

end Rep
