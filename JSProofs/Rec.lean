import JSProofs.Nested
import JSProofs.RCGen

/-!
# Recursion: `sum(n)` = 0 + 1 + … + n, by induction (examples/rec.js)

```js
function sum(n) { if (n < 1) { return 0; } return n + sum(n - 1); }
sum(10);
```
`sum`'s call runs to `tsum n` for every `n` whose sum is below 2^26, with each recursive call answered one
driver level deeper (`sum_call`, by induction on `n`: the depth must be at least `n`); the script evaluates
to 55.
-/

open ES ES.Conv SumProof Script

namespace Rec

/-- 0 + 1 + … + n. -/
def tsum : Nat → Nat
  | 0 => 0
  | n + 1 => (n + 1) + tsum n

/-- `sum`'s parameter bound to `x`. -/
def pbn (x : F64) : Std.HashMap JSStr Binding :=
  ((∅ : Std.HashMap JSStr Binding).insert "n" { deletable := false }).modify "n" fun bd => { bd with value := some (.num x) }

theorem lexBase : lexicallyScoped #[(Stmt.ret (some (Expr.lit (Lit.num (F64.fin false 0 (-1074))))))] = #[] := by rfl

/-- **`sum`'s body, `n = 0`**: returns 0. -/
theorem sum_spec_base (nn : Nat) (ctx : Ctx) (s : State) (hstr : ctx.strict = false) (hgen : ctx.isGen = false)
    (ha : identValue ctx.lex "n" false s = .ok (num 0) s) (hf : 3 ≤ s.fuel) :
    RCGen.sum nn ctx s = .ok (.ret (num 0)) s := by
  obtain ⟨j, hj⟩ : ∃ j, s.fuel = j + 3 := ⟨s.fuel - 3, by omega⟩
  have hlt : ltF (ofSmallInt 0) (ofSmallInt 1) = true := by
    rw [ltF_int _ _ (by simp [intBound]) (by simp [intBound])]; decide
  simp only [RCGen.sum, Sem.stmts, M.repeatFrom, hj, M.loop]
  simp [M.bind_eq, M.bind_apply, Sem.ifS, Sem.inner, Sem.binary, Sem.ident, hstr, ha, Sem.lit, litValue, one_eq,
    Sem.binaryOp, isLessThan, hlt, toBoolean, ofSmallInt_eq_nan, Sem.block, lexBase, Sem.stmts, M.repeatFrom, hj,
    M.loop, Sem.ret, hgen, pure, M.pure, Compl.updateEmpty]
  rw [zero_eq]

/-- **`sum`'s body, `n = k + 1`** (`sum` the function `fS` on the global object): asks the driver to call
`sum(k)`; when that returns `y`, the body returns `k + 1 + y`. -/
theorem sum_spec_step (nn : Nat) (ctx : Ctx) (s : State) (L F ge g fS : Nat) (k : Nat) (gb : Std.HashMap JSStr Binding)
    (gtv : Value) (dS : FuncData) (b2 : Std.HashMap JSStr Binding) (ts : ThisStatus) (tv : Value) (fo : ObjId)
    (nt : Value) (hlex : ctx.lex = L) (hstr : ctx.strict = false) (hgen : ctx.isGen = false)
    (h1 : L < s.envs.size) (hE1 : s.envEntry L = .decl ∅ (some F))
    (h2 : F < s.envs.size) (hE2 : s.envEntry F = .func b2 (some ge) ts tv fo nt)
    (hb2 : b2[JSStr.ofString "sum"]? = none) (hx : identValue L "n" false s = .ok (num ((k : Int) + 1)) s)
    (h : ge < s.envs.size) (hE : s.envEntry ge = .global g gb gtv) (hgb : gb.contains "sum" = false)
    (hgb' : gb[JSStr.ofString "sum"]? = none) (hgbm : (JSStr.ofString "sum" ∈ gb) = False)
    (hgs : g < s.heap.size) (hk : (s.objEntry g).kind = .ordinary)
    (hp : (s.objEntry g).props.get? (.str "sum") = some (.data (.obj fS) true true false))
    (hfs : fS < s.heap.size) (hfk : (s.objEntry fS).kind = .func dS) (hkb : k + 1 < 2 ^ 26) (hf : 4 ≤ s.fuel) :
    ∃ K, RCGen.sum nn ctx s = .req (.call (.obj fS) .undefined #[num (k : Int)]) s K ∧
      ∀ y t, K (.normal (num y)) t = .ok (.ret (.num (addF (ofSmallInt ((k : Int) + 1)) (ofSmallInt y)))) t := by
  obtain ⟨j, hj⟩ : ∃ j, s.fuel = j + 3 := ⟨s.fuel - 3, by omega⟩
  have hk' : (s.objEntry g).kind.isPlain = true := by rw [hk]; rfl
  have hr := Nested.resolveBinding_body_global L F ge "sum" false s ∅ b2 ts tv fo nt g gb gtv _ h1 hE1 (by simp) h2 hE2
    hb2 h hE hgb hgbm hgs hk' hp (by omega)
  have hkb' : ((k : Int) + 1).natAbs < intBound := by simp only [intBound]; omega
  have hlt : ltF (ofSmallInt ((k : Int) + 1)) (ofSmallInt 1) = false := by
    rw [ltF_int _ _ hkb' (by simp [intBound])]; simp; omega
  have hsub : subF (ofSmallInt ((k : Int) + 1)) (ofSmallInt 1) = ofSmallInt (k : Int) := by
    rw [subF_nz _ _ hkb' (by simp [intBound]) (by omega) (by simp) (by simp only [intBound]; omega)]; congr 1; omega
  refine ⟨?K, ?h, ?_⟩
  case h =>
    conv =>
      lhs
      simp [RCGen.sum, Sem.stmts, M.repeatFrom, hj, M.loop, M.bind_eq, M.bind_apply, Sem.ifS, Sem.inner, Sem.binary,
        Sem.ident, hstr, hlex, hx, Sem.lit, litValue, one_eq, Sem.binaryOp, isLessThan, hlt, toBoolean,
        ofSmallInt_eq_nan, Sem.ret, hgen, Sem.call, Sem.identRef, hr, getRefValue, getBindingValue,
        readEnv_entry _ _ _ h, hE, hgb', hgbm, Obj'.hasProperty_entry_own _ _ _ hgs hk', hp, getProp,
        Obj'.get_entry_data _ _ _ _ hgs hk', ownDataValue, isOwnData, refThisValue, Sem.args, Sem.binaryOp_sub,
        applyBinaryOp_sub_num, hsub, isCallable, readObj_entry' _ _ _ hfs, hfk, ES.call, pure, M.pure,
        M.bindRes_ok, M.bindRes_req, M.loopRes_req, Compl.updateEmpty]
  intro y t
  simp [M.pure, pure, M.loopRes_inr, Compl.updateEmpty, hgen, M.bind_eq, M.bind_apply, M.bindRes_ok,
    applyBinaryOp_add_num]

theorem sum_fdi (f : ObjId) (d : FuncData) (env : EnvId) (s : State) (x : F64) (tv : Value)
    (hcode : d.code = RCGen.sum_func) (henv : env < s.envs.size)
    (hE : s.envEntry env = .func ∅ (some d.env) .initialized tv f .undefined)
    (hf : s.fuel ≠ 0) :
    ∃ ctx s', functionDeclarationInstantiation 999999 f d env #[.num x] s = .ok ctx s' ∧
      s'.envEntry env = .func (pbn x) (some d.env) .initialized tv f .undefined ∧
      ctx.lex = s.envs.size ∧ s'.envEntry ctx.lex = .decl ∅ (some env) ∧ ctx.var = env ∧
      ctx.strict = false ∧ ctx.isGen = false ∧ ctx.fn = some f ∧ s'.envs.size = s.envs.size + 1 ∧ s'.fuel = s.fuel ∧
      s'.heap = s.heap ∧ s'.realms = s.realms ∧ (∀ e, e < s.envs.size → e ≠ env → s'.envEntry e = s.envEntry e) := by
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
  refine ⟨?c, ?t, ?h, ?_⟩
  case h =>
    conv =>
      lhs
      simp only [functionDeclarationInstantiation, hcode]
      simp only [RCGen.sum_func, Func.strict, Func.params, Func.info, Func.body, Func.isAsync]
      simp [hr, hasBinding_declLike, createMutableBinding_declLike, hbe, newDeclEnv, pure,
        M.pure, hE, henv, hf]
  have hne : env ≠ s.envs.size := Nat.ne_of_lt henv
  simp [State.envEntry, State.setEnv, Array.getElem?_push, Array.getElem_push, Array.getElem_modify, henv, hne,
    pbn]
  intro e he hee
  simp [Nat.ne_of_lt he, Array.getElem?_modify, Ne.symm hee]

/-! ## The call, by induction -/

theorem tsum_le (k : Nat) : k ≤ tsum k := by
  induction k with
  | zero => simp [tsum]
  | succ k ih => simp only [tsum]; omega

/-- **The [[Call]] of `sum` with `k`** (`this` undefined), at driver depth `m + 1 ≥ k + 1`: runs, through `k`
nested calls of itself, to `tsum k`; the heap, the realms and the caller's environments are as they were, and
`k` steps of fuel are used (one per nested call). -/
theorem sum_call (eng : Engine) (ge g fS : Nat) (gb : Std.HashMap JSStr Binding) (gtv : Value) (dS : FuncData)
    (hcode : dS.code = RCGen.sum_func) (hcls : dS.isClassCtor = false) (hmode : dS.thisMode = .global)
    (hdenv : dS.env = ge) (hgb : gb.contains "sum" = false) (hgb' : gb[JSStr.ofString "sum"]? = none)
    (hgbm : (JSStr.ofString "sum" ∈ gb) = False) :
    ∀ (k m : Nat) (s : State), k ≤ m → tsum k < 2 ^ 26 → k + 8 ≤ s.fuel →
      (s.realms[dS.realm]!).globalEnv = ge → ge < s.envs.size → s.envEntry ge = .global g gb gtv →
      g < s.heap.size → (s.objEntry g).kind = .ordinary →
      (s.objEntry g).props.get? (.str "sum") = some (.data (.obj fS) true true false) →
      fS < s.heap.size → (s.objEntry fS).kind = .func dS →
      ∃ s', Nested.Runs eng (m + 1) (callECMA fS dS .undefined #[num (k : Int)] s) (num (tsum k : Int)) s' ∧
        s'.heap = s.heap ∧ s'.realms = s.realms ∧ s.envs.size ≤ s'.envs.size ∧
        (∀ e, e < s.envs.size → s'.envEntry e = s.envEntry e) ∧ s'.fuel + k = s.fuel := by
  intro k
  induction k with
  | zero =>
    intro m s _ _ hf hrd hge hgE hgs hk hp hfs hfk
    obtain ⟨s', h1, -, -, t', ⟨q1, q2, q3, q4, q5⟩, hh, hen, hfe, hrs⟩ := Calls.callECMA_undef
      (Q := fun t => t.heap = s.heap ∧ t.realms = s.realms ∧ s.envs.size ≤ t.envs.size ∧
        (∀ e, e < s.envs.size → t.envEntry e = s.envEntry e) ∧ t.fuel = s.fuel)
      fS dS s #[num ((0 : Nat) : Int)] (num ((tsum 0 : Nat) : Int)) g gb gtv hcls hmode (by rw [hcode]; rfl)
      (by rw [hcode]; rfl) (by rw [hrd]; exact hge) (by rw [hrd]; exact hgE)
      (fun t hlt hEt hold hheap hfu hrl _ => by
        obtain ⟨ctx, t1, hfdi, hB, hlex, hL, hvar, hstr, hgen, hfn, hsize, hfuel, hheap1, hrl1, hfe1⟩ :=
          sum_fdi fS dS s.envs.size t (ofSmallInt ((0 : Nat) : Int)) gtv hcode hlt hEt (by omega)
        have hl' : ctx.lex < t1.envs.size := by rw [hlex, hsize]; exact Nat.lt_succ_self _
        have he' : s.envs.size < t1.envs.size := by rw [hsize]; exact Nat.lt_succ_of_lt hlt
        have hxv : identValue ctx.lex "n" false t1 = .ok (num 0) t1 := by
          have := identValue_decl_func ctx.lex s.envs.size "n" false t1 (num ((0 : Nat) : Int)) _
            { value := some (num ((0 : Nat) : Int)), deletable := false } _ _ _ _ _ hl' hL he' hB
            (by simp [pbn, Std.HashMap.getElem?_modify]) rfl (by omega)
          simpa using this
        have hbody := sum_spec_base 999961 ctx t1 hstr hgen hxv (by omega)
        refine ⟨t1, ?_, hheap1.trans hheap, hrl1.trans hrl, by omega,
          fun e he => (hfe1 e (Nat.lt_trans he hlt) (Nat.ne_of_lt he)).trans (hold e he), hfuel.trans hfu⟩
        have hbd : dS.code.body = .stmts RCGen.sum_stmts := by rw [hcode]; rfl
        have hdisp : dS.code.info.fdi.usesDispose = false := by rw [hcode]; rfl
        have hbody' : evalStmts (999961 + 38) ctx RCGen.sum_stmts t1 = .ok (.ret (num 0)) t1 := by
          rw [← congrFun (RCGen.sum_eq 999961) ctx]; exact hbody
        simp only [evalDepth, evalFunctionBody, M.bind_eq, M.bind_apply, hfdi, M.bindRes_ok, hbd, hdisp,
          withDisposeScope]
        simp [hbody', pure, M.pure, tsum])
    refine ⟨s', by rw [h1]; exact Nested.Runs.ok _ _ _, hh.trans q1, hrs.trans q2, by rw [hen]; exact q3,
      fun e he => by simp only [State.envEntry, hen]; exact q4 e he, by rw [hfe]; simpa using q5⟩
  | succ k ih =>
    intro m s hkm htk hf hrd hge hgE hgs hk hp hfs hfk
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have htk' : tsum k < 2 ^ 26 := by simp only [tsum] at htk; omega
    have hkb : k + 1 < 2 ^ 26 := by simp only [tsum] at htk; omega
    obtain ⟨s', h1, -, -, t', ⟨q1, q2, q3, q4, q5⟩, hh, hen, hfe, hrs⟩ := Nested.callECMA_undef_runs eng (m' + 1 + 1)
      (Q := fun t => t.heap = s.heap ∧ t.realms = s.realms ∧ s.envs.size ≤ t.envs.size ∧
        (∀ e, e < s.envs.size → t.envEntry e = s.envEntry e) ∧ t.fuel + (k + 1) = s.fuel)
      fS dS s #[num ((k + 1 : Nat) : Int)] (num ((tsum (k + 1) : Nat) : Int)) g gb gtv hcls hmode (by rw [hcode]; rfl)
      (by rw [hcode]; rfl) (by rw [hrd]; exact hge) (by rw [hrd]; exact hgE)
      (fun t hlt hEt hold hheap hfu hrl _ => by
        have ho : ∀ y, t.objEntry y = s.objEntry y := by intro y; simp [State.objEntry, hheap]
        obtain ⟨ctx, t1, hfdi, hB, hlex, hL, hvar, hstr, hgen, hfn, hsize, hfuel, hheap1, hrl1, hfe1⟩ :=
          sum_fdi fS dS s.envs.size t (ofSmallInt ((k + 1 : Nat) : Int)) gtv hcode hlt hEt (by omega)
        have hl' : ctx.lex < t1.envs.size := by rw [hlex, hsize]; exact Nat.lt_succ_self _
        have he' : s.envs.size < t1.envs.size := by rw [hsize]; exact Nat.lt_succ_of_lt hlt
        have hxv : identValue ctx.lex "n" false t1 = .ok (num ((k : Int) + 1)) t1 := by
          have := identValue_decl_func ctx.lex s.envs.size "n" false t1 (num ((k + 1 : Nat) : Int)) _
            { value := some (num ((k + 1 : Nat) : Int)), deletable := false } _ _ _ _ _ hl' hL he' hB
            (by simp [pbn, Std.HashMap.getElem?_modify]) rfl (by omega)
          simpa using this
        have ho1 : ∀ y, t1.objEntry y = s.objEntry y := by intro y; rw [← ho]; simp [State.objEntry, hheap1]
        have hge1 : ge < t1.envs.size := by rw [hsize]; omega
        have hgne : ge ≠ s.envs.size := Nat.ne_of_lt hge
        have hgE1 : t1.envEntry ge = .global g gb gtv := by rw [hfe1 ge (by omega) hgne, hold ge hge]; exact hgE
        have hBg : t1.envEntry s.envs.size = .func (pbn (ofSmallInt ((k + 1 : Nat) : Int))) (some ge) .initialized gtv fS
            .undefined := by rw [hB, hdenv]
        have hps : (pbn (ofSmallInt ((k + 1 : Nat) : Int)))[JSStr.ofString "sum"]? = none := by
          have hns : (JSStr.ofString "n" = JSStr.ofString "sum") = False := by simp; decide
          simp [pbn, Std.HashMap.getElem?_modify, Std.HashMap.getElem?_insert, hns]
        obtain ⟨K, hreq, hK⟩ := sum_spec_step 999961 ctx t1 ctx.lex s.envs.size ge g fS k gb gtv dS _ .initialized gtv fS
          .undefined rfl hstr hgen hl' hL he' hBg hps hxv hge1 hgE1 hgb hgb' hgbm (by rw [hheap1, hheap]; exact hgs)
          (by rw [ho1]; exact hk) (by rw [ho1]; exact hp) (by rw [hheap1, hheap]; exact hfs) (by rw [ho1]; exact hfk)
          hkb (by omega)
        -- the recursive call, one level down, by the induction hypothesis
        obtain ⟨t1', ht1'⟩ : ∃ y, ({ t1 with fuel := t1.fuel - 1 } : State) = y := ⟨_, rfl⟩
        have hz1' : t1'.envs = t1.envs := by rw [← ht1']
        have ho1' : ∀ y, t1'.objEntry y = s.objEntry y := fun y => by rw [← ht1']; exact ho1 y
        obtain ⟨t2, hrun, hh2, hr2, hz2, he2, hf2⟩ := ih m' t1' (by omega) htk' (by rw [← ht1']; simp only; omega)
          (by rw [← ht1']; show (t1.realms[dS.realm]!).globalEnv = ge; rw [hrl1, hrl]; exact hrd)
          (by rw [hz1']; exact hge1) (by simp only [State.envEntry, hz1']; exact hgE1)
          (by rw [← ht1', hheap1, hheap]; exact hgs) (by rw [ho1']; exact hk) (by rw [ho1']; exact hp)
          (by rw [← ht1', hheap1, hheap]; exact hfs) (by rw [ho1']; exact hfk)
        have hdrive : ∀ cs, (drive eng (m' + 1) (callImpl eng (.obj fS) .undefined #[num (k : Int)] t1) cs).1 =
            .ok (num (tsum k : Int)) t2 := by
          intro cs
          rw [callImpl_func eng fS dS _ _ t1 (by rw [hheap1, hheap]; exact hfs) (by rw [ho1]; exact hfk) (by omega), ht1']
          exact Nested.drive_of_runs eng (m' + 1) _ _ _ hrun cs
        have htb : ((tsum k : Nat) : Int).natAbs < intBound := by simp only [intBound]; omega
        have hsum : addF (ofSmallInt ((k : Int) + 1)) (ofSmallInt (tsum k : Int)) = ofSmallInt ((tsum (k + 1) : Nat) : Int) := by
          rw [addF_int _ _ (by simp only [intBound]; omega) htb (by simp only [intBound, tsum] at htk ⊢; omega)]
          simp [tsum]
        refine ⟨t2, ?_, by rw [hh2, ← ht1']; exact hheap1.trans hheap, by rw [hr2, ← ht1']; exact hrl1.trans hrl,
          by rw [← ht1'] at hz2; simp at hz2; omega,
          fun e he => by
            rw [he2 e (by rw [hz1', hsize]; omega)]; simp only [State.envEntry, hz1']
            exact (hfe1 e (Nat.lt_trans he hlt) (Nat.ne_of_lt he)).trans (hold e he),
          by rw [← ht1'] at hf2; simp only at hf2; omega⟩
        have hbd : dS.code.body = .stmts RCGen.sum_stmts := by rw [hcode]; rfl
        have hdisp : dS.code.info.fdi.usesDispose = false := by rw [hcode]; rfl
        have hbody' : evalStmts (999961 + 38) ctx RCGen.sum_stmts t1 = .req (.call (.obj fS) .undefined #[num (k : Int)]) t1 K := by
          rw [← congrFun (RCGen.sum_eq 999961) ctx]; exact hreq
        simp only [evalDepth, evalFunctionBody, M.bind_eq, M.bind_apply, hfdi, M.bindRes_ok, hbd, hdisp, withDisposeScope,
          Bool.not_false, ↓reduceIte]
        rw [show (999999 : Nat) = 999961 + 38 from rfl, hbody']
        refine Nested.runs_bind eng _ (m' + 1 + 1) _ (Compl.ret (num ((tsum (k + 1) : Nat) : Int))) t2 ?_ _ _ (Nested.Runs.ok _ _ _)
        exact .call (m' + 1) _ _ _ t1 K _ t2 _ t2 hdrive (by rw [hK, hsum]; exact Nested.Runs.ok _ _ _))
    exact ⟨s', h1, hh.trans q1, hrs.trans q2, by rw [hen]; exact q3,
      fun e he => by simp only [State.envEntry, hen]; exact q4 e he, by rw [hfe]; exact q5⟩

/-! ## The whole script -/

abbrev l10 : F64 := F64.fin false 5629499534213120 (-49)
theorem l10_eq : l10 = ofSmallInt ((10 : Nat) : Int) := by decide
theorem tsum10 : tsum 10 = 55 := by decide
abbrev callSum : Sem.CStmt := Sem.exprStmt (Sem.call (Sem.identRef "sum")
  (Sem.args #[Sem.ArgD.expr (Sem.lit (Lit.num l10))]) false (CalleeDesc.ident "sum"))

theorem script_def (n : Nat) : RCGen.script n = Sem.stmts #[Sem.funDecl RCGen.sum_func, callSum] := rfl
theorem lexScoped : topLevelLexicallyScoped RCGen.script_stmts = #[] := by
  simp [topLevelLexicallyScoped, stmtLexScoped, RCGen.script_stmts]
theorem simple_sum : Inst.SimpleFn RCGen.sum_func "sum" := ⟨rfl, rfl, rfl, rfl, rfl⟩

def fs : List (Func × JSStr) := [(RCGen.sum_func, "sum")]

theorem varS : topLevelVarScoped RCGen.program.body = (fs.map fun p => VarScoped.func p.1).toArray := rfl
theorem lexS : topLevelLexicallyScoped RCGen.program.body =
    (([] : List JSStr).map fun x => LexScoped.binding .let (.ident x)).toArray := by
  rw [show RCGen.program.body = RCGen.script_stmts from rfl, lexScoped]; rfl
theorem annS : annexBFunctions RCGen.program.body ([] : List JSStr).toArray = #[] := rfl
theorem simpleS : ∀ p ∈ fs, Inst.SimpleFn p.1 p.2 := by
  intro p hp; simp only [fs, List.mem_cons, List.mem_nil_iff, or_false] at hp; rcases hp with rfl; exact simple_sum
theorem nodupS : (fs.map Prod.snd).Nodup := by decide

/-- **The whole program** (examples/rec.js): `sum(10)` recurses ten levels deep; the script evaluates to 55.
Started from a realm whose global object is an ordinary extensible object without `sum`. -/
theorem rc_script (eng : Engine) (s : State) (cs : Conts) (gb : Std.HashMap JSStr Binding) (gtv : Value)
    (fp : ObjId) (hge : s.curRealm.globalEnv < s.envs.size)
    (hE : s.envEntry s.curRealm.globalEnv = .global s.curRealm.globalObj gb gtv)
    (hgbs : gb.contains "sum" = false)
    (hgs : s.curRealm.globalObj < s.heap.size) (hk : (s.objEntry s.curRealm.globalObj).kind = .ordinary)
    (hx : (s.objEntry s.curRealm.globalObj).extensible = true)
    (hps : (s.objEntry s.curRealm.globalObj).props.get? (.str "sum") = none)
    (hfp : s.curRealm.intrinsics["%Function.prototype%"]? = some fp) (hf : 30 ≤ s.fuel) :
    ∃ s', (runM eng (scriptEvaluation RCGen.program) s cs).1 = .ok (num 55) s' := by
  let ge := s.curRealm.globalEnv
  let g := s.curRealm.globalObj
  let c := scriptCtx s false
  obtain ⟨t0, ht0⟩ : ∃ y, (scriptStart s RCGen.program).setEnv ge (.global g (insertLets gb []) gtv) = y := ⟨_, rfl⟩
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
  let fS := s.heap.size
  obtain ⟨dS, hfSk, hcS, hrS, hmS, hclsS, -, hdS⟩ := hfuns 0 (by decide)
  rw [hz0] at hfSk hszu hnames
  simp only [fs, List.length_cons, List.length_nil] at hszu
  simp only [Nat.mul_zero, Nat.add_zero] at hfSk
  have hpS : (u.objEntry g).props.get? (.str "sum") = some (.data (.obj fS) true true false) := hnames 0 (by decide)
  have hE1 : u.envEntry ge = .global g gb gtv := by
    have h1 : u.envEntry ge = t0.envEntry ge := by simp only [State.envEntry, heu]
    rw [h1, ← ht0, State.setEnv_envEntry_self _ _ _ (show ge < (scriptStart s RCGen.program).envs.size from hge)]
    simp [insertLets]
  have hgeu : ge < u.envs.size := by rw [heu]; exact hge0
  have hgu : g < u.heap.size := by rw [hszu]; exact Nat.lt_of_lt_of_le hgs (Nat.le_add_right _ _)
  have hfSu : fS < u.heap.size := by show s.heap.size < u.heap.size; rw [hszu]; omega
  have hgbs' : gb[JSStr.ofString "sum"]? = none := Std.HashMap.getElem?_eq_none (fun hm => by
    rw [Std.HashMap.mem_iff_contains, hgbs] at hm; exact Bool.false_ne_true hm)
  have hgbsm : (JSStr.ofString "sum" ∈ gb) = False := by simp [Std.HashMap.mem_iff_contains, hgbs]
  -- `sum(10)` asks for its call
  obtain ⟨K0, h0, hK0⟩ := Stmts.call_expr_req (Sem.inner c) u ge g fS "sum" gb gtv dS [(Sem.lit (Lit.num l10), .num l10)]
    (by intro p hp; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp; rcases hp with rfl; rfl)
    rfl rfl hgeu hE1 hgbs hgbs' hgbsm hgu hku hpS hfSu hfSk (by rw [hfuu, hfu0]; omega)
  obtain ⟨K4, h4, hK4⟩ := Stmts.exprStmt_req _ c u _ K0 h0 hK0
  -- the call: ten levels of recursion (`sum_call`)
  obtain ⟨u', hu'⟩ : ∃ y, ({ u with fuel := u.fuel - 1 } : State) = y := ⟨_, rfl⟩
  have hr' : u'.realms = s.realms := by rw [← hu']; exact hru.trans hr0
  have hz' : u'.envs = u.envs := by rw [← hu']
  have hou : ∀ y, u'.objEntry y = u.objEntry y := fun y => by rw [← hu']; rfl
  obtain ⟨s4, hrun, -⟩ := sum_call eng ge g fS gb gtv dS hcS hclsS hmS hdS hgbs hgbs' hgbsm 10 3998 u' (by decide)
    (by decide) (by rw [← hu']; simp only; rw [hfuu, hfu0]; omega) (by rw [hr', hrS, hrl0]; rfl)
    (by rw [hz']; exact hgeu) (by simp only [State.envEntry, hz']; exact hE1) (by rw [← hu']; exact hgu)
    (by rw [hou]; exact hku) (by rw [hou]; exact hpS) (by rw [← hu']; exact hfSu) (by rw [hou]; exact hfSk)
  rw [tsum10] at hrun
  have hnest : ∀ cs, (drive eng 3999 (callImpl eng (.obj fS) .undefined #[.num l10] u) cs).1 = .ok (num 55) s4 := by
    intro cs
    rw [l10_eq, callImpl_func eng fS dS _ _ u hfSu hfSk (by rw [hfuu, hfu0]; omega), hu']
    exact Nested.drive_of_runs eng 3999 _ _ _ hrun cs
  -- the script
  refine ⟨s4, script_value eng s cs RCGen.program fs [] gb gtv fp _ s4 rfl varS lexS annS simpleS nodupS hge hE
    (by intro p hp; simp only [fs, List.mem_cons, List.mem_nil_iff, or_false] at hp; rcases hp with rfl; exact hgbs)
    (by simp) hgs hk hx
    (by intro p hp; simp only [fs, List.mem_cons, List.mem_nil_iff, or_false] at hp; rcases hp with rfl; exact hps)
    (by simp) hfp ?_⟩
  have hu0 : scriptState s RCGen.program fs [] gb gtv fp = u := by rw [← hu, ← ht0]; rfl
  have hscript : evalStmts evalDepth (scriptCtx s false) RCGen.program.body u = RCGen.script 999953 c u := by
    rw [RCGen.script_eq]; rfl
  have h4' : callSum c u = .req (.call (.obj fS) .undefined #[.num l10]) u K4 := h4
  rw [hu0, hscript, script_def]
  refine _root_.Runs.script_runs eng _ _ _ (_root_.Runs.stmts_run eng c _ u _ s4 ?_ (by simp; rw [hfuu, hfu0]; omega))
  show _root_.Runs.StmtsRun eng c [Sem.funDecl RCGen.sum_func, callSum] u none (some (num 55)) s4
  refine .cons _ _ u u s4 none none _ (_root_.Runs.runs_funDecl eng _ c u rfl) ?_
  refine .cons _ _ u s4 s4 (some (num 55)) none _ ?_ (.nil _ _)
  rw [h4']
  exact Nested.runsTo_call_nested eng _ _ _ u K4 _ s4 _ s4 hnest (by rw [hK4]; exact _root_.Runs.runsTo_ok eng _ _)

end Rec
