import JSProofs.While
import JSProofs.Env
import JSProofs.NumInt
import JSProofs.SumGen

/-!
# A loop: `sum(n)` returns 0 + 1 + … + (n − 1)

```js
function sum(n) { let s = 0; let i = 0; while (i < n) { s = s + i; i = i + 1; } return s; }
```
(examples/sum.js, generated into `Proofs/SumGen.lean`.) The body, started as a call starts it (`s`, `i`
declared in the body's lexical environment `L`, the parameter `n` in the function environment `F`),
returns `tri N` for any natural `N < 2^26`. The loop invariant: after `k` iterations `i = k` and
`s = tri k`.
-/

open ES ES.Conv

namespace SumProof

/-- 0 + 1 + … + (k − 1). -/
def tri : Nat → Nat
  | 0 => 0
  | k + 1 => tri k + k

theorem two_tri (k : Nat) : 2 * tri k = k * (k - 1) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [tri, Nat.mul_add, ih, Nat.add_sub_cancel]
    cases k with
    | zero => rfl
    | succ j => simp only [Nat.add_sub_cancel, Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul]; omega

/-- The closed form. -/
theorem tri_eq (k : Nat) : tri k = k * (k - 1) / 2 := by
  have := two_tri k; omega

theorem tri_le (k : Nat) : tri k ≤ k * k := by
  induction k with
  | zero => exact Nat.le_refl _
  | succ k ih =>
    simp only [tri, Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]; omega

/-- A Number from an integer. -/
abbrev num (i : Int) : Value := .num (ofSmallInt i)

/-- The loop's test and body, as in `SumGen.sum`. -/
def testD : Sem.CExpr := (Sem.binary BinOp.lt (Sem.ident "i") (Sem.ident "n"))
def bodyD : Sem.CStmt := (Sem.block (lexicallyScoped #[(Stmt.expr (Expr.assign AssignOp.assign (Pattern.ident "s") (Expr.binary BinOp.add (Expr.ident "s") (Expr.ident "i")))), (Stmt.expr (Expr.assign AssignOp.assign (Pattern.ident "i") (Expr.binary BinOp.add (Expr.ident "i") (Expr.lit (Lit.num (F64.fin false 4503599627370496 (-52)))))))]) #[(Sem.exprStmt (Sem.assign (Sem.identRef "s") (Sem.binary BinOp.add (Sem.ident "s") (Sem.ident "i")))), (Sem.exprStmt (Sem.assign (Sem.identRef "i") (Sem.binary BinOp.add (Sem.ident "i") (Sem.lit (Lit.num (F64.fin false 4503599627370496 (-52)))))))])

theorem ne_si : (JSStr.ofString "s" = JSStr.ofString "i") = False := by simp; decide
theorem ne_is : (JSStr.ofString "i" = JSStr.ofString "s") = False := by simp; decide
theorem ne_sn : (JSStr.ofString "s" = JSStr.ofString "n") = False := by simp; decide
theorem ne_in : (JSStr.ofString "i" = JSStr.ofString "n") = False := by simp; decide

/-- The environments during the body: `L` binds `s` and `i` (mutable, with values `sv`, `iv`) and not
`n`; its outer environment `F` binds `n` to `N`. -/
def Shape (L F : EnvId) (N : Nat) (sv iv : Option Value) (t : State) : Prop :=
  L < t.envs.size ∧ F < t.envs.size ∧ L ≠ F ∧
  (∃ b, t.envEntry L = .decl b (some F) ∧
    (∃ bd, b[JSStr.ofString "s"]? = some bd ∧ bd.value = sv ∧ bd.mutable = true) ∧
    (∃ bd, b[JSStr.ofString "i"]? = some bd ∧ bd.value = iv ∧ bd.mutable = true) ∧ b[JSStr.ofString "n"]? = none) ∧
  (∃ bF o ts tv fo nt bn, t.envEntry F = .func bF o ts tv fo nt ∧ bF[JSStr.ofString "n"]? = some bn ∧
    bn.value = some (num N))

theorem shape_fuel (L F : EnvId) (N : Nat) (sv iv : Option Value) (t : State) (f : Nat) :
    Shape L F N sv iv { t with fuel := f } ↔ Shape L F N sv iv t := Iff.rfl

/-- Assigning `x ∈ {s, i}` in `L` keeps the shape, with the new value. -/
theorem shape_set (L F : EnvId) (N : Nat) (t : State) (b : Std.HashMap JSStr Binding)
    (hl : L < t.envs.size) (hf : F < t.envs.size) (hLF : L ≠ F) (hL : t.envEntry L = .decl b (some F))
    (hF : ∃ bF o ts tv fo nt bn, t.envEntry F = .func bF o ts tv fo nt ∧ bF[JSStr.ofString "n"]? = some bn ∧
      bn.value = some (num N))
    (bs bi : Binding) (hbs : b[JSStr.ofString "s"]? = some bs) (hsm : bs.mutable = true)
    (hbi : b[JSStr.ofString "i"]? = some bi) (him : bi.mutable = true) (hbn : b[JSStr.ofString "n"]? = none) (x : JSStr) (vx : Value)
    (sv iv : Option Value) (hsv : (if x = JSStr.ofString "s" then some vx else bs.value) = sv)
    (hiv : (if x = JSStr.ofString "i" then some vx else bi.value) = iv) (hx : x = JSStr.ofString "s" ∨ x = JSStr.ofString "i") :
    Shape L F N sv iv (t.setEnv L (.decl (b.modify x fun bd => { bd with value := some vx }) (some F))) := by
  have hFe : (t.setEnv L (.decl (b.modify x fun bd => { bd with value := some vx }) (some F))).envEntry F =
      t.envEntry F := by
    simp [State.envEntry, State.setEnv, Array.getElem?_modify, hLF]
  have hL' : (t.setEnv L (.decl (b.modify x fun bd => { bd with value := some vx }) (some F))).envEntry L =
      .decl (b.modify x fun bd => { bd with value := some vx }) (some F) := State.setEnv_envEntry_self _ _ _ hl
  refine ⟨by simp [hl], by simp [hf], hLF, ⟨_, hL', ?_, ?_, ?_⟩, by rw [hFe]; exact hF⟩
  · rcases hx with rfl | rfl
    · exact ⟨{ bs with value := some vx }, by simp [Std.HashMap.getElem?_modify, hbs], by simp_all, hsm⟩
    · exact ⟨bs, by simp [Std.HashMap.getElem?_modify, hbs, ne_is], by simp_all [ne_is], hsm⟩
  · rcases hx with rfl | rfl
    · exact ⟨bi, by simp [Std.HashMap.getElem?_modify, hbi, ne_si], by simp_all [ne_si], him⟩
    · exact ⟨{ bi with value := some vx }, by simp [Std.HashMap.getElem?_modify, hbi], by simp_all, him⟩
  · rcases hx with rfl | rfl <;> simp [Std.HashMap.getElem?_modify, ne_sn, ne_in, hbn]

theorem one_eq : F64.fin false 4503599627370496 (-52) = ofSmallInt 1 := by decide
theorem zero_eq : F64.fin false 0 (-1074) = ofSmallInt 0 := by decide

theorem ofSmallInt_ne_nan (i : Int) : (ofSmallInt i == F64.nan) = false := by
  unfold ofSmallInt; split
  · rfl
  · dsimp only; split <;> rfl

theorem ofSmallInt_eq_nan (i : Int) : (ofSmallInt i = F64.nan) = False := by
  have := ofSmallInt_ne_nan i
  simp only [beq_eq_false_iff_ne] at this
  simp [this]

theorem lexBody : lexicallyScoped #[(Stmt.expr (Expr.assign AssignOp.assign (Pattern.ident "s") (Expr.binary BinOp.add (Expr.ident "s") (Expr.ident "i")))), (Stmt.expr (Expr.assign AssignOp.assign (Pattern.ident "i") (Expr.binary BinOp.add (Expr.ident "i") (Expr.lit (Lit.num (F64.fin false 4503599627370496 (-52)))))))] = #[] := by rfl

theorem tri_bound (k N : Nat) (hk : k ≤ N) (hN : N < 2 ^ 26) : tri k < intBound := by
  have h1 := tri_le k
  have h2 : k * k ≤ N * N := Nat.mul_le_mul hk hk
  have h3 : N * N < 2 ^ 26 * 2 ^ 26 := Nat.mul_lt_mul_of_lt_of_le hN (Nat.le_of_lt hN) (by omega)
  simp only [intBound]; omega

/-- One iteration that continues: `i < n` holds, `s` becomes `tri (k + 1)` and `i` becomes `k + 1`. -/
theorem iter_cont (ctx : Ctx) (labels : Array JSStr) (L F : EnvId) (N k : Nat) (hlex : ctx.lex = L)
    (hstr : ctx.strict = false) (hk : k < N) (hN : N < 2 ^ 26) (t : State) (v : Value)
    (hS : Shape L F N (some (num (tri k))) (some (num k)) t) (hf : 5 ≤ t.fuel) :
    ∃ t', whileIter testD bodyD labels ctx v t = .ok (.inl (num ((k : Int) + 1))) t' ∧
      Shape L F N (some (num (tri (k + 1)))) (some (num ((k : Int) + 1))) t' ∧ t'.fuel = t.fuel - 1 := by
  obtain ⟨hl, hfF, hLF, ⟨b, hL, ⟨bs, hbs, hsv, hsm⟩, ⟨bi, hbi, hiv, him⟩, hbn⟩,
    ⟨bF, o, ts, tv, fo, nt, bn, hFE, hbF, hbnv⟩⟩ := hS
  -- after the tick
  obtain ⟨t1, ht1⟩ : ∃ t1, ({ t with fuel := t.fuel - 1 } : State) = t1 := ⟨_, rfl⟩
  have h1l : L < t1.envs.size := by rw [← ht1]; exact hl
  have h1f : F < t1.envs.size := by rw [← ht1]; exact hfF
  have h1L : t1.envEntry L = .decl b (some F) := by rw [← ht1]; exact hL
  have h1F : t1.envEntry F = .func bF o ts tv fo nt := by rw [← ht1]; exact hFE
  have h1fuel : t1.fuel = t.fuel - 1 := by rw [← ht1]
  have hkb : (k : Int).natAbs < intBound := by simp only [intBound]; omega
  have hNb : (N : Int).natAbs < intBound := by simp only [intBound]; omega
  have hk1b : ((k : Int) + 1).natAbs < intBound := by simp only [intBound]; omega
  have htb : ((tri k : Nat) : Int).natAbs < intBound := by
    have := tri_bound k N (Nat.le_of_lt hk) hN; simpa using this
  have htb1 : ((tri (k + 1) : Nat) : Int).natAbs < intBound := by
    have := tri_bound (k + 1) N hk hN; simpa using this
  -- the test
  have hi1 : identValue L "i" false t1 = .ok (num k) t1 :=
    identValue_decl_here L _ false t1 _ b _ bi h1l h1L hbi hiv (by omega)
  have hn1 : identValue L "n" false t1 = .ok (num N) t1 :=
    identValue_decl_outer L F _ false t1 _ b bF bn o ts tv fo nt h1l h1L hbn h1f h1F hbF hbnv (by omega)
  have hlt : ltF (ofSmallInt k) (ofSmallInt N) = true := by rw [ltF_int _ _ hkb hNb]; simp [hk]
  -- `s = s + i`
  have hs1 : identValue L "s" false t1 = .ok (num (tri k)) t1 :=
    identValue_decl_here L _ false t1 _ b _ bs h1l h1L hbs hsv (by omega)
  have hadd_s : addF (ofSmallInt (tri k)) (ofSmallInt k) = ofSmallInt (tri (k + 1)) := by
    rw [addF_int _ _ htb hkb (by simpa [tri] using htb1)]; simp [tri]
  have hrs : resolveBinding L "s" false t1 = .ok (.env (some L) "s" false) t1 :=
    resolveBinding_here L _ false t1 h1l (by rw [h1L]; rfl) (by rw [h1L]; simp [Env.bindingsMap, Std.HashMap.mem_iff_isSome_getElem?, hbs]) (by omega)
  have hset_s := setMutableBinding_decl L "s" (num (tri (k + 1))) false t1 b (some F) bs h1l h1L hbs
    (by simp [hsv]) hsm
  obtain ⟨t2, ht2⟩ : ∃ t2, t1.setEnv L (.decl (b.modify "s" fun bd => { bd with value := some (num (tri (k + 1))) })
      (some F)) = t2 := ⟨_, rfl⟩
  rw [ht2] at hset_s
  have hS2 : Shape L F N (some (num (tri (k + 1)))) (some (num k)) t2 := by
    rw [← ht2]
    exact shape_set L F N t1 b h1l h1f hLF h1L ⟨bF, o, ts, tv, fo, nt, bn, h1F, hbF, hbnv⟩ bs bi hbs hsm hbi him hbn
      _ _ _ _ (by simp) (by simp [ne_si, hiv]) (Or.inl rfl)
  have h2fuel : t2.fuel = t.fuel - 1 := by rw [← ht2, State.setEnv_fuel, h1fuel]
  -- `i = i + 1`
  obtain ⟨h2l, h2f, -, ⟨b2, h2L, ⟨bs2, hbs2, hsv2, hsm2⟩, ⟨bi2, hbi2, hiv2, him2⟩, hbn2⟩,
    ⟨bF2, o2, ts2, tv2, fo2, nt2, bn2, h2F, hbF2, hbnv2⟩⟩ := hS2
  have hi2 : identValue L "i" false t2 = .ok (num k) t2 :=
    identValue_decl_here L _ false t2 _ b2 _ bi2 h2l h2L hbi2 hiv2 (by omega)
  have hadd_i : addF (ofSmallInt k) (ofSmallInt 1) = ofSmallInt ((k : Int) + 1) := by
    rw [addF_int _ _ hkb (by simp [intBound]) (by simpa using hk1b)]
  have hri : resolveBinding L "i" false t2 = .ok (.env (some L) "i" false) t2 :=
    resolveBinding_here L _ false t2 h2l (by rw [h2L]; rfl) (by rw [h2L]; simp [Env.bindingsMap, Std.HashMap.mem_iff_isSome_getElem?, hbi2]) (by omega)
  have hset_i := setMutableBinding_decl L "i" (num ((k : Int) + 1)) false t2 b2 (some F) bi2 h2l h2L hbi2
    (by simp [hiv2]) him2
  obtain ⟨t3, ht3⟩ : ∃ t3, t2.setEnv L (.decl (b2.modify "i" fun bd => { bd with value := some (num ((k : Int) + 1)) })
      (some F)) = t3 := ⟨_, rfl⟩
  rw [ht3] at hset_i
  have hS3 : Shape L F N (some (num (tri (k + 1)))) (some (num ((k : Int) + 1))) t3 := by
    rw [← ht3]
    exact shape_set L F N t2 b2 h2l h2f hLF h2L ⟨bF2, o2, ts2, tv2, fo2, nt2, bn2, h2F, hbF2, hbnv2⟩ bs2 bi2 hbs2 hsm2
      hbi2 him2 hbn2 _ _ _ _ (by simp [ne_is, hsv2]) (by simp) (Or.inr rfl)
  have h3fuel : t3.fuel = t.fuel - 1 := by rw [← ht3, State.setEnv_fuel, h2fuel]
  refine ⟨t3, ?_, hS3, h3fuel⟩
  obtain ⟨j, hj⟩ : ∃ j, t1.fuel = j + 3 := ⟨t1.fuel - 3, by omega⟩
  have hj2 : t2.fuel = j + 3 := by rw [h2fuel, ← h1fuel, hj]
  have htick : M.tick t = .ok () t1 := by
    rw [← ht1]; simp [M.tick, show t.fuel ≠ 0 by omega]
  simp only [whileIter, M.bind_eq, M.bind_apply, htick, M.bindRes_ok, testD, bodyD, lexBody, Sem.binary, Sem.ident,
    hlex, hstr, hi1, hn1]
  simp [Sem.binaryOp, isLessThan, M.bind_eq, M.bind_apply, hlt, ofSmallInt_eq_nan, toBoolean, pure, M.pure, Sem.block,
    lexBody, Sem.stmts, M.repeatFrom, hj, M.loop, Sem.exprStmt, Sem.assign, Sem.identRef, Sem.inner, hlex, hstr, hrs,
    Sem.binary, Sem.ident, hs1, hi1, applyBinaryOp_add_num, hadd_s, putRefValue, hset_s, hri, hi2, Sem.lit, litValue,
    one_eq, hadd_i, hset_i, loopContinues, Compl.value?]

/-- The last iteration: `i < n` fails, the loop completes with its value so far. -/
theorem iter_exit (ctx : Ctx) (labels : Array JSStr) (L F : EnvId) (N : Nat) (hlex : ctx.lex = L)
    (hstr : ctx.strict = false) (hN : N < 2 ^ 26) (t : State) (v : Value)
    (hS : Shape L F N (some (num (tri N))) (some (num N)) t) (hf : 3 ≤ t.fuel) :
    ∃ t', whileIter testD bodyD labels ctx v t = .ok (.inr (.normal (some v))) t' ∧
      Shape L F N (some (num (tri N))) (some (num N)) t' ∧ t'.fuel = t.fuel - 1 := by
  have hS' := hS
  obtain ⟨hl, hfF, hLF, ⟨b, hL, -, ⟨bi, hbi, hiv, him⟩, hbn⟩, ⟨bF, o, ts, tv, fo, nt, bn, hFE, hbF, hbnv⟩⟩ := hS
  obtain ⟨t1, ht1⟩ : ∃ t1, ({ t with fuel := t.fuel - 1 } : State) = t1 := ⟨_, rfl⟩
  have h1l : L < t1.envs.size := by rw [← ht1]; exact hl
  have h1f : F < t1.envs.size := by rw [← ht1]; exact hfF
  have h1L : t1.envEntry L = .decl b (some F) := by rw [← ht1]; exact hL
  have h1F : t1.envEntry F = .func bF o ts tv fo nt := by rw [← ht1]; exact hFE
  have h1fuel : t1.fuel = t.fuel - 1 := by rw [← ht1]
  have hNb : (N : Int).natAbs < intBound := by simp only [intBound]; omega
  have hi1 : identValue L "i" false t1 = .ok (num N) t1 :=
    identValue_decl_here L _ false t1 _ b _ bi h1l h1L hbi hiv (by omega)
  have hn1 : identValue L "n" false t1 = .ok (num N) t1 :=
    identValue_decl_outer L F _ false t1 _ b bF bn o ts tv fo nt h1l h1L hbn h1f h1F hbF hbnv (by omega)
  have hlt : ltF (ofSmallInt N) (ofSmallInt N) = false := by rw [ltF_int _ _ hNb hNb]; simp
  have htick : M.tick t = .ok () t1 := by rw [← ht1]; simp [M.tick, show t.fuel ≠ 0 by omega]
  refine ⟨t1, ?_, by rw [← ht1]; exact hS', h1fuel⟩
  simp only [whileIter, M.bind_eq, M.bind_apply, htick, M.bindRes_ok, testD, Sem.binary, Sem.ident, hlex, hstr,
    hi1, hn1]
  simp [Sem.binaryOp, isLessThan, M.bind_eq, M.bind_apply, hlt, ofSmallInt_eq_nan, toBoolean, pure, M.pure]

/-- The loop: from `s = tri 0`, `i = 0`, it completes normally with `s = tri N`, `i = N`. -/
theorem loop_spec (ctx : Ctx) (L F : EnvId) (N : Nat) (hlex : ctx.lex = L) (hstr : ctx.strict = false)
    (hN : N < 2 ^ 26) (t : State) (hS : Shape L F N (some (num (tri 0))) (some (num (0 : Nat))) t)
    (hf : N + 5 ≤ t.fuel) :
    ∃ c t', Sem.whileS testD bodyD ctx t = .ok (Sem.breakToNormal c) t' ∧ (∃ w, c = Compl.normal (some w)) ∧
      Shape L F N (some (num (tri N))) (some (num N)) t' ∧ t'.fuel + N + 1 = t.fuel := by
  let I : Value → State → Prop := fun _ u =>
    ∃ k, k ≤ N ∧ Shape L F N (some (num (tri k))) (some (num k)) u ∧ u.fuel + k = t.fuel
  let Q : Compl → State → Prop := fun c u =>
    (∃ w, c = .normal (some w)) ∧ Shape L F N (some (num (tri N))) (some (num N)) u ∧ u.fuel + N + 1 = t.fuel
  let V : Value → State → Nat := fun _ u => u.fuel + N - t.fuel
  have hil : (Sem.inner ctx).lex = L := hlex
  have his : (Sem.inner ctx).strict = false := hstr
  have hstep : ∀ v u, I v u →
      (∃ v' u', whileIter testD bodyD ctx.labels (Sem.inner ctx) v u = .ok (.inl v') u' ∧ I v' u' ∧ V v' u' < V v u) ∨
      (∃ c u', whileIter testD bodyD ctx.labels (Sem.inner ctx) v u = .ok (.inr c) u' ∧ Q c u') := by
    intro v u ⟨k, hk, hSu, hfu⟩
    by_cases hkN : k < N
    · obtain ⟨u', h, hS', hf'⟩ := iter_cont (Sem.inner ctx) ctx.labels L F N k hil his hkN hN u v hSu (by omega)
      have hc : ((k + 1 : Nat) : Int) = (k : Int) + 1 := by omega
      refine Or.inl ⟨_, u', h, ⟨k + 1, hkN, by rw [hc]; exact hS', by omega⟩, by simp only [V]; omega⟩
    · have hkN' : k = N := by omega
      subst hkN'
      obtain ⟨u', h, hS', hf'⟩ := iter_exit (Sem.inner ctx) ctx.labels L F k hil his hN u v hSu (by omega)
      exact Or.inr ⟨_, u', h, ⟨v, rfl⟩, hS', by omega⟩
  exact whileS_inv testD bodyD ctx I Q V hstep t ⟨0, Nat.zero_le _, hS, by simp⟩ (by simp only [V]; omega)

/-- A `let x = 0` at the top of the body: initializes `x ∈ {s, i}` in `L`. -/
theorem let_zero (L F : EnvId) (N : Nat) (t : State) (x : JSStr) (sv iv sv' iv' : Option Value)
    (hS : Shape L F N sv iv t) (hx : x = "s" ∨ x = "i")
    (hsv : (if x = "s" then some (num 0) else sv) = sv') (hiv : (if x = "i" then some (num 0) else iv) = iv')
    (hf : t.fuel ≠ 0) :
    ∃ t', resolveBinding L x false t = .ok (.env (some L) x false) t ∧
      initializeBinding L x (num 0) t = .ok () t' ∧ Shape L F N sv' iv' t' ∧ t'.fuel = t.fuel := by
  obtain ⟨hl, hfF, hLF, ⟨b, hL, ⟨bs, hbs, hsv0, hsm⟩, ⟨bi, hbi, hiv0, him⟩, hbn⟩, hF⟩ := hS
  have hmem : (x ∈ b) := by
    rcases hx with rfl | rfl <;> simp [Std.HashMap.mem_iff_isSome_getElem?, hbs, hbi]
  refine ⟨_, resolveBinding_here L x false t hl (by rw [hL]; rfl) (by rw [hL]; simpa [Env.bindingsMap] using hmem) hf,
    by rw [initializeBinding_declLike L x _ t hl (by rw [hL]; rfl), hL], ?_, by simp⟩
  have := shape_set L F N t b hl hfF hLF hL hF bs bi hbs hsm hbi him hbn x (num 0) sv' iv'
    (by rw [← hsv]; split <;> simp_all) (by rw [← hiv]; split <;> simp_all) hx
  simpa [Env.withBindings] using this

/-- **`sum`'s body returns 0 + 1 + … + (N − 1)**, for every natural `N < 2^26`: started with `s` and `i`
declared (not yet initialized) in the body's lexical environment `L` and `n = N` in the function
environment `F` (as a call sets them up), with fuel for the loop's `N + 1` iterations. -/
theorem sum_spec (n : Nat) (ctx : Ctx) (L F : EnvId) (N : Nat) (hlex : ctx.lex = L) (hstr : ctx.strict = false)
    (hgen : ctx.isGen = false) (hN : N < 2 ^ 26) (s0 : State) (hS : Shape L F N none none s0)
    (hf : N + 10 ≤ s0.fuel) :
    ∃ s', SumGen.sum n ctx s0 = .ok (.ret (num (tri N))) s' := by
  obtain ⟨s1, hr1, hi1, hS1, hf1⟩ := let_zero L F N s0 "s" none none (some (num 0)) none hS (Or.inl rfl)
    (by simp) (by simp [ne_si]) (by omega)
  obtain ⟨s2, hr2, hi2, hS2, hf2⟩ := let_zero L F N s1 "i" (some (num 0)) none (some (num 0)) (some (num 0)) hS1
    (Or.inr rfl) (by simp [ne_is]) (by simp) (by omega)
  have hS2' : Shape L F N (some (num (tri 0))) (some (num (0 : Nat))) s2 := by simpa [tri] using hS2
  obtain ⟨c, s3, hw, ⟨w, hc⟩, hS3, hf3⟩ := loop_spec ctx L F N hlex hstr hN s2 hS2' (by omega)
  subst hc
  obtain ⟨h3l, -, -, ⟨b3, h3L, ⟨bs3, hbs3, hsv3, -⟩, -, -⟩, -⟩ := hS3
  have hs3 : identValue L "s" false s3 = .ok (num (tri N)) s3 :=
    identValue_decl_here L _ false s3 _ b3 _ bs3 h3l h3L hbs3 hsv3 (by omega)
  simp only [testD, bodyD] at hw
  obtain ⟨j, hj⟩ : ∃ j, s0.fuel = j + 5 := ⟨s0.fuel - 5, by omega⟩
  have hlu : (VarKind.let == VarKind.using) = false := by decide
  have hla : (VarKind.let == VarKind.awaitUsing) = false := by decide
  simp only [SumGen.sum, Sem.stmts, M.repeatFrom, hj, M.loop]
  simp [M.bind_eq, M.bind_apply, Sem.varDecl, Sem.inner, Sem.declLex, hlex, hstr, hr1, hr2, Sem.lit, litValue,
    zero_eq, initializeRefBinding, hi1, hi2, hlu, hla, M.forArr, pure, M.pure, hw, Sem.breakToNormal, Sem.ret,
    Sem.ident, hs3, hgen, Compl.updateEmpty]

/-- The same for the interpreter itself, on `sum`'s syntax tree (via the generated `sum_eq`). -/
theorem sum_interp_spec (n : Nat) (ctx : Ctx) (L F : EnvId) (N : Nat) (hlex : ctx.lex = L)
    (hstr : ctx.strict = false) (hgen : ctx.isGen = false) (hN : N < 2 ^ 26) (s0 : State)
    (hS : Shape L F N none none s0) (hf : N + 10 ≤ s0.fuel) :
    ∃ s', evalStmts (n + 35) ctx SumGen.sum_stmts s0 = .ok (.ret (num ((N * (N - 1) / 2 : Nat) : Int))) s' := by
  rw [← congrFun (SumGen.sum_eq n) ctx, ← tri_eq]
  exact sum_spec n ctx L F N hlex hstr hgen hN s0 hS hf

end SumProof
