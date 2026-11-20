import Proofs.LoopRuns
import Proofs.SumFor
import Proofs.AddTwice
import Proofs.SAGen
import Proofs.MoreCalls

/-!
# A loop that calls a function: `sumAdd(n)` = 0 + 1 + … + (n − 1), each step through `add`

```js
function add(a, b) { return a + b; }
function sumAdd(n) { let s = 0; for (let i = 0; i < n; i = i + 1) { s = add(s, i); } return s; }
sumAdd(10);
```
(examples/sum_add.js.) As `sumFor` (Proofs/SumFor.lean), but each iteration asks the driver to call `add`, so
the loop only *runs* (`Nested.Runs`): the loop rule `Nested.loop_runs`, each iteration's call answered one
level deeper, and `sumAdd`'s call proved for every `n`.
-/

open ES ES.Conv SumProof SumForProof

namespace SumAdd

def bodyA : Sem.CStmt := (Sem.block (lexicallyScoped #[(Stmt.expr (Expr.assign AssignOp.assign (Pattern.ident "s") (Expr.call (Expr.ident "add") #[(Arg.expr (Expr.ident "s")), (Arg.expr (Expr.ident "i"))] false false)))]) #[(Sem.exprStmt (Sem.assign (Sem.identRef "s") (Sem.call (Sem.identRef "add") (Sem.args #[(Sem.ArgD.expr (Sem.ident "s")), (Sem.ArgD.expr (Sem.ident "i"))]) false (CalleeDesc.ident "add"))))])

theorem lexBodyA : lexicallyScoped #[(Stmt.expr (Expr.assign AssignOp.assign (Pattern.ident "s") (Expr.call (Expr.ident "add") #[(Arg.expr (Expr.ident "s")), (Arg.expr (Expr.ident "i"))] false false)))] = #[] := by rfl

/-- The environments in an iteration with `i = iv`, `s = sv`: the copy `E` (holding `i`), the body's `L`
(holding `s`), the function record `F` (holding `n = N`, outer the global record `ge`); none holds `add`. -/
def ShapeA (E L F ge : EnvId) (N : Nat) (sv iv : Option Value) (t : State) : Prop :=
  E < t.envs.size ∧ L < t.envs.size ∧ F < t.envs.size ∧ ge < t.envs.size ∧ E ≠ L ∧ E ≠ F ∧ L ≠ F ∧ ge ≠ E ∧ ge ≠ L ∧
  (∃ bE bdi, t.envEntry E = .decl bE (some L) ∧ bE[JSStr.ofString "i"]? = some bdi ∧ bdi.value = iv ∧
    bdi.mutable = true ∧ bE[JSStr.ofString "s"]? = none ∧ bE[JSStr.ofString "n"]? = none ∧
    bE[JSStr.ofString "add"]? = none) ∧
  (∃ bL bds, t.envEntry L = .decl bL (some F) ∧ bL[JSStr.ofString "s"]? = some bds ∧ bds.value = sv ∧
    bds.mutable = true ∧ bL[JSStr.ofString "n"]? = none ∧ bL[JSStr.ofString "add"]? = none) ∧
  (∃ bF ts tv fo nt bn, t.envEntry F = .func bF (some ge) ts tv fo nt ∧ bF[JSStr.ofString "n"]? = some bn ∧
    bn.value = some (num N) ∧ bF[JSStr.ofString "add"]? = none)

/-- The global facts every iteration needs: `add` the function `fA` on the global object. -/
def GFrame (ge g fA : Nat) (gb : Std.HashMap JSStr Binding) (gtv : Value) (dA : FuncData) (t : State) : Prop :=
  t.envEntry ge = .global g gb gtv ∧ gb.contains "add" = false ∧ gb[JSStr.ofString "add"]? = none ∧
  (JSStr.ofString "add" ∈ gb) = False ∧ g < t.heap.size ∧ (t.objEntry g).kind = .ordinary ∧
  (t.objEntry g).props.get? (.str "add") = some (.data (.obj fA) true true false) ∧
  fA < t.heap.size ∧ (t.objEntry fA).kind = .func dA ∧ dA.code = AddGen.add_func ∧ dA.isClassCtor = false ∧
  dA.thisMode = .global ∧ (t.realms[dA.realm]!).globalEnv = ge

theorem gframe_of {ge g fA : Nat} {gb : Std.HashMap JSStr Binding} {gtv : Value} {dA : FuncData} {t w : State}
    (h : GFrame ge g fA gb gtv dA t) (he : w.envEntry ge = t.envEntry ge) (hh : w.heap = t.heap)
    (hr : w.realms = t.realms) : GFrame ge g fA gb gtv dA w := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
  have ho : ∀ x, w.objEntry x = t.objEntry x := fun x => by simp [State.objEntry, hh]
  exact ⟨by rw [he]; exact h1, h2, h3, h4, by rw [hh]; exact h5, by rw [ho]; exact h6, by rw [ho]; exact h7,
    by rw [hh]; exact h8, by rw [ho]; exact h9, h10, h11, h12, by rw [hr]; exact h13⟩

/-- `add`, from inside the loop: past `E`, `L` and `F`, on the global object. -/
theorem resolve_add (E L F ge : EnvId) (s : State) (bE bL bF : Std.HashMap JSStr Binding) (ts : ThisStatus)
    (tv : Value) (fo : ObjId) (nt : Value) (g fA : ObjId) (gb : Std.HashMap JSStr Binding) (gtv : Value)
    (hE : E < s.envs.size) (hEE : s.envEntry E = .decl bE (some L)) (hnE : bE[JSStr.ofString "add"]? = none)
    (hL : L < s.envs.size) (hLE : s.envEntry L = .decl bL (some F)) (hnL : bL[JSStr.ofString "add"]? = none)
    (hF : F < s.envs.size) (hFE : s.envEntry F = .func bF (some ge) ts tv fo nt)
    (hnF : bF[JSStr.ofString "add"]? = none)
    (hg : ge < s.envs.size) (hgE : s.envEntry ge = .global g gb gtv) (hb : gb.contains "add" = false)
    (hbm : (JSStr.ofString "add" ∈ gb) = False) (hgs : g < s.heap.size) (hk : (s.objEntry g).kind.isPlain = true)
    (hp : (s.objEntry g).props.get? (.str "add") = some (.data (.obj fA) true true false)) (hf : 4 ≤ s.fuel) :
    resolveBinding E "add" false s = .ok (.env (some ge) "add" false) s := by
  obtain ⟨k, hk1⟩ : ∃ k, s.fuel = k + 4 := ⟨s.fuel - 4, by omega⟩
  rw [resolveBinding_loop, hk1, resolveBody_skip _ E L _ false s bE hE hEE hnE,
    resolveBody_skip _ L F _ false s bL hL hLE hnL,
    Closure.resolveBody_skip_func _ F ge _ false s bF ts tv fo nt hF hFE hnF]
  simp [M.loop, resolveBody, M.bind_eq, M.bind_apply, hasBinding, readEnv_entry _ _ _ hg, hgE, hb, hbm,
    Obj'.hasProperty_entry_own _ _ _ hgs hk, hp, pure, M.pure]

/-- **One iteration that continues**: up to the call `add(s, i)` (with `s = tri k`, `i = k`), which it asks the
driver for; when the call returns `tri (k + 1)` in any state that kept the environments, it assigns `s`, makes
the next copy `E'` and increments `i` there. -/
theorem iterA_cont (ctx : Ctx) (labels : Array JSStr) (E L F ge : EnvId) (N k : Nat) (g fA : Nat)
    (gb : Std.HashMap JSStr Binding) (gtv : Value) (dA : FuncData)
    (hstr : ctx.strict = false) (hk : k < N) (hN : N < 2 ^ 26) (t : State) (v : Value)
    (hS : ShapeA E L F ge N (some (num (tri k))) (some (num k)) t) (hG : GFrame ge g fA gb gtv dA t)
    (hf : 6 ≤ t.fuel) :
    ∃ K, forIter SumForProof.testD SumForProof.updD bodyA labels ctx #["i"] (E, v) t =
        .req (.call (.obj fA) .undefined #[num (tri k), num k]) { t with fuel := t.fuel - 1 } K ∧
      ∀ w : State, t.envs.size ≤ w.envs.size → (∀ e, e < t.envs.size → w.envEntry e = t.envEntry e) →
        3 ≤ w.fuel →
        ∃ E' w', K (.normal (num (tri (k + 1)))) w = .ok (.inl (E', num (tri (k + 1)))) w' ∧
          ShapeA E' L F ge N (some (num (tri (k + 1)))) (some (num ((k : Int) + 1))) w' ∧
          w'.envEntry ge = w.envEntry ge ∧ w'.heap = w.heap ∧ w'.realms = w.realms ∧ w'.fuel = w.fuel := by
  obtain ⟨hE, hL, hF, hg, hEL, hEF, hLF, hgE, hgL, ⟨bE, bdi, hEE, hbi, hiv, him, hbs, hbn, hba⟩,
    ⟨bL, bds, hLE, hls, hsv, hsm, hln, hla⟩, ⟨bF, ts, tv, fo, nt, bn, hFE, hbF, hbnv, hbFa⟩⟩ := hS
  obtain ⟨hgEE, hgb, hgb', hgbm, hgs, hgk, hgp, hfs, hfk, -, -, -, -⟩ := hG
  have hgk' : (t.objEntry g).kind.isPlain = true := by rw [hgk]; rfl
  have hkb : (k : Int).natAbs < intBound := by simp only [intBound]; omega
  have hNb : (N : Int).natAbs < intBound := by simp only [intBound]; omega
  have hk1b : ((k : Int) + 1).natAbs < intBound := by simp only [intBound]; omega
  -- the tick
  obtain ⟨t1, ht1⟩ : ∃ t1, ({ t with fuel := t.fuel - 1 } : State) = t1 := ⟨_, rfl⟩
  have e1 : ∀ x, t1.envEntry x = t.envEntry x := by intro x; rw [← ht1]; rfl
  have o1 : ∀ x, t1.objEntry x = t.objEntry x := by intro x; rw [← ht1]; rfl
  have z1 : t1.envs.size = t.envs.size := by rw [← ht1]
  have hz1 : t1.heap.size = t.heap.size := by rw [← ht1]
  have f1 : t1.fuel = t.fuel - 1 := by rw [← ht1]
  have htick : M.tick t = .ok () t1 := by rw [← ht1]; simp [M.tick, show t.fuel ≠ 0 by omega]
  have h1E : E < t1.envs.size := by rw [z1]; exact hE
  have h1L : L < t1.envs.size := by rw [z1]; exact hL
  have h1F : F < t1.envs.size := by rw [z1]; exact hF
  have h1g : ge < t1.envs.size := by rw [z1]; exact hg
  -- the test: `i < n`
  have ri : identValue E "i" false t1 = .ok (num k) t1 :=
    identValue_skip0 E _ false t1 bdi _ h1E (by rw [e1, hEE]; rfl) (by rw [e1, hEE]; exact hbi) hiv (by omega)
  have rn : identValue E "n" false t1 = .ok (num N) t1 :=
    identValue_skip2 E L F _ false t1 bE bL bn _ h1E (by rw [e1]; exact hEE) hbn h1L
      (by rw [e1]; exact hLE) hln h1F (by rw [e1, hFE]; rfl) (by rw [e1, hFE]; exact hbF) hbnv (by omega)
  have hlt : ltF (ofSmallInt k) (ofSmallInt N) = true := by rw [ltF_int _ _ hkb hNb]; simp [hk]
  -- the body, up to the call: `s = add(s, i)`
  have rs : identValue E "s" false t1 = .ok (num (tri k)) t1 :=
    identValue_skip1 E L _ false t1 bE bds _ h1E (by rw [e1]; exact hEE) hbs h1L
      (by rw [e1, hLE]; rfl) (by rw [e1, hLE]; exact hls) hsv (by omega)
  have rrs : resolveBinding E "s" false t1 = .ok (.env (some L) "s" false) t1 :=
    resolveBinding_skip1 E L _ false t1 bE h1E (by rw [e1]; exact hEE) hbs h1L (by rw [e1, hLE]; rfl)
      (by rw [e1, hLE]; simp [Env.bindingsMap, Std.HashMap.contains_eq_isSome_getElem?, hls]) (by omega)
  have rra : resolveBinding E "add" false t1 = .ok (.env (some ge) "add" false) t1 :=
    resolve_add E L F ge t1 bE bL bF ts tv fo nt g fA gb gtv h1E (by rw [e1]; exact hEE) hba h1L (by rw [e1]; exact hLE)
      hla h1F (by rw [e1]; exact hFE) hbFa h1g (by rw [e1]; exact hgEE) hgb hgbm (by rw [hz1]; exact hgs)
      (by rw [o1]; exact hgk') (by rw [o1]; exact hgp) (by omega)
  have hgs1 : g < t1.heap.size := by rw [hz1]; exact hgs
  have hfs1 : fA < t1.heap.size := by rw [hz1]; exact hfs
  obtain ⟨j, hj⟩ : ∃ j, t1.fuel = j + 2 := ⟨t1.fuel - 2, by omega⟩
  rw [ht1]
  refine ⟨?K, ?h, ?_⟩
  case h =>
    conv =>
      lhs
      simp only [forIter, M.bind_eq, M.bind_apply, htick, M.bindRes_ok, SumForProof.testD, Sem.binary, Sem.ident, hstr, ri, rn]
      simp [Sem.binaryOp, isLessThan, M.bind_eq, M.bind_apply, hlt, ofSmallInt_eq_nan, toBoolean, pure, M.pure, bodyA,
        lexBodyA, Sem.block, Sem.stmts, M.repeatFrom, hj, M.loop, Sem.exprStmt, Sem.assign, Sem.identRef, Sem.inner,
        hstr, rrs, Sem.call, rra, getRefValue, getBindingValue, readEnv_entry _ _ _ h1g, e1, hgEE, hgb', hgbm,
        Obj'.hasProperty_entry_own _ _ _ hgs1 (by rw [o1]; exact hgk'), o1, hgp, getProp,
        Obj'.get_entry_data _ _ _ _ hgs1 (by rw [o1]; exact hgk'), ownDataValue, isOwnData, refThisValue, Sem.args,
        Sem.ident, rs, ri, isCallable, readObj_entry' _ _ _ hfs1, hfk, ES.call, M.bindRes_req, M.loopRes_req]
  intro w hsz hold hfw
  have wE : w.envEntry E = .decl bE (some L) := (hold E hE).trans hEE
  have wL : w.envEntry L = .decl bL (some F) := (hold L hL).trans hLE
  have wF : w.envEntry F = .func bF (some ge) ts tv fo nt := (hold F hF).trans hFE
  have hEw : E < w.envs.size := Nat.lt_of_lt_of_le hE hsz
  have hLw : L < w.envs.size := Nat.lt_of_lt_of_le hL hsz
  have hFw : F < w.envs.size := Nat.lt_of_lt_of_le hF hsz
  have hgw : ge < w.envs.size := Nat.lt_of_lt_of_le hg hsz
  -- `s = …`
  have hset_s := setMutableBinding_decl L "s" (num (tri (k + 1))) false w bL (some F) bds hLw wL hls (by simp [hsv]) hsm
  obtain ⟨w2, hw2⟩ : ∃ w2, w.setEnv L (.decl (bL.modify "s" fun bd => { bd with value := some (num (tri (k + 1))) })
      (some F)) = w2 := ⟨_, rfl⟩
  rw [hw2] at hset_s
  have z2 : w2.envs.size = w.envs.size := by rw [← hw2, State.setEnv_envs_size]
  have f2 : w2.fuel = w.fuel := by rw [← hw2, State.setEnv_fuel]
  have e2E : w2.envEntry E = .decl bE (some L) := by rw [← hw2, State.setEnv_envEntry_ne _ _ _ _ (Ne.symm hEL), wE]
  have e2L : w2.envEntry L = .decl (bL.modify "s" fun bd => { bd with value := some (num (tri (k + 1))) }) (some F) := by
    rw [← hw2]; exact State.setEnv_envEntry_self _ _ _ hLw
  have e2F : w2.envEntry F = .func bF (some ge) ts tv fo nt := by rw [← hw2, State.setEnv_envEntry_ne _ _ _ _ hLF, wF]
  have e2g : w2.envEntry ge = w.envEntry ge := by rw [← hw2, State.setEnv_envEntry_ne _ _ _ _ (Ne.symm hgL)]
  -- the copy of the loop environment
  have hpi := perIterationEnv_one "i" E L w2 bE bdi (num k) (by rw [z2]; exact hEw) e2E hbi hiv
  obtain ⟨E', hE'⟩ : ∃ E', w2.envs.size = E' := ⟨_, rfl⟩
  obtain ⟨bE', hbE'⟩ : ∃ b, ((∅ : Std.HashMap JSStr Binding).insert "i" { deletable := false }).modify "i"
    (fun bd => { bd with value := some (num k) }) = b := ⟨_, rfl⟩
  rw [hE', hbE'] at hpi
  obtain ⟨w3, hw3⟩ : ∃ w3, (w2.pushEnv (.decl {} (some L))).setEnv E' (.decl bE' (some L)) = w3 := ⟨_, rfl⟩
  rw [hw3] at hpi
  have z3 : w3.envs.size = w.envs.size + 1 := by rw [← hw3, State.setEnv_envs_size, State.pushEnv_size, z2]
  have f3 : w3.fuel = w.fuel := by rw [← hw3, State.setEnv_fuel, State.pushEnv_fuel, f2]
  have hE'lt : E' < w3.envs.size := by rw [z3, ← hE', z2]; exact Nat.lt_succ_self _
  have e3E' : w3.envEntry E' = .decl bE' (some L) := by
    rw [← hw3]; exact State.setEnv_envEntry_self _ _ _ (by rw [State.pushEnv_size, ← hE']; exact Nat.lt_succ_self _)
  have hbi' : bE'[JSStr.ofString "i"]? = some { value := some (num k), deletable := false } := by
    rw [← hbE']; simp [Std.HashMap.getElem?_modify]
  -- the update: `i = i + 1` in the copy
  have ri3 : identValue E' "i" false w3 = .ok (num k) w3 :=
    identValue_skip0 E' _ false w3 _ _ hE'lt (by rw [e3E']; rfl) (by rw [e3E']; exact hbi') rfl (by omega)
  have rri3 : resolveBinding E' "i" false w3 = .ok (.env (some E') "i" false) w3 := by
    obtain ⟨j, hj⟩ : ∃ j, w3.fuel = j + 1 := ⟨w3.fuel - 1, by omega⟩
    rw [resolveBinding_loop, hj, resolveBody_found j E' _ false w3 hE'lt (by rw [e3E']; rfl)
      (by rw [e3E']; simp [Env.bindingsMap, Std.HashMap.contains_eq_isSome_getElem?, hbi'])]
  have hadd_i : addF (ofSmallInt k) (ofSmallInt 1) = ofSmallInt ((k : Int) + 1) := by
    rw [addF_int _ _ hkb (by simp [intBound]) (by simpa using hk1b)]
  have hset_i := setMutableBinding_decl E' "i" (num ((k : Int) + 1)) false w3 bE' (some L) _ hE'lt e3E' hbi'
    (by simp) (by simp)
  obtain ⟨w4, hw4⟩ : ∃ w4, w3.setEnv E' (.decl (bE'.modify "i" fun bd => { bd with value := some (num ((k : Int) + 1)) })
      (some L)) = w4 := ⟨_, rfl⟩
  rw [hw4] at hset_i
  have z4 : w4.envs.size = w.envs.size + 1 := by rw [← hw4, State.setEnv_envs_size, z3]
  have f4 : w4.fuel = w.fuel := by rw [← hw4, State.setEnv_fuel, f3]
  have hLE' : L ≠ E' := by rw [← hE']; exact Nat.ne_of_lt (show L < w2.envs.size by rw [z2]; exact hLw)
  have hFE' : F ≠ E' := by rw [← hE']; exact Nat.ne_of_lt (show F < w2.envs.size by rw [z2]; exact hFw)
  have hgE' : ge ≠ E' := by rw [← hE']; exact Nat.ne_of_lt (show ge < w2.envs.size by rw [z2]; exact hgw)
  have e4 : ∀ x, x ≠ E' → x < w2.envs.size → w4.envEntry x = w2.envEntry x := by
    intro x hx hlt
    rw [← hw4, State.setEnv_envEntry_ne _ _ _ _ (Ne.symm hx), ← hw3, State.setEnv_envEntry_ne _ _ _ _ (Ne.symm hx),
      State.pushEnv_entry_lt _ _ _ hlt]
  have hS4 : ShapeA E' L F ge N (some (num (tri (k + 1)))) (some (num ((k : Int) + 1))) w4 := by
    refine ⟨by rw [z4, ← hE', z2]; exact Nat.lt_succ_self _, by rw [z4]; exact Nat.lt_succ_of_lt hLw,
      by rw [z4]; exact Nat.lt_succ_of_lt hFw, by rw [z4]; exact Nat.lt_succ_of_lt hgw, Ne.symm hLE', Ne.symm hFE', hLF,
      hgE', hgL, ?_, ?_, ?_⟩
    · refine ⟨bE'.modify "i" fun bd => { bd with value := some (num ((k : Int) + 1)) },
        { value := some (num ((k : Int) + 1)), deletable := false }, ?_, ?_, rfl, rfl, ?_, ?_, ?_⟩
      · rw [← hw4]; exact State.setEnv_envEntry_self _ _ _ hE'lt
      · rw [← hbE']; simp [Std.HashMap.getElem?_modify]
      · rw [← hbE']; simp [Std.HashMap.getElem?_modify, Std.HashMap.getElem?_insert, ne_is]
      · rw [← hbE']; simp [Std.HashMap.getElem?_modify, Std.HashMap.getElem?_insert, ne_in]
      · have hia : (JSStr.ofString "i" = JSStr.ofString "add") = False := by simp; decide
        rw [← hbE']; simp [Std.HashMap.getElem?_modify, Std.HashMap.getElem?_insert, hia]
    · refine ⟨bL.modify "s" fun bd => { bd with value := some (num (tri (k + 1))) },
        { bds with value := some (num (tri (k + 1))) }, ?_, ?_, rfl, hsm, ?_, ?_⟩
      · rw [e4 L hLE' (by rw [z2]; exact hLw), e2L]
      · simp [Std.HashMap.getElem?_modify, hls]
      · simp [Std.HashMap.getElem?_modify, ne_sn, hln]
      · have hsa : (JSStr.ofString "s" = JSStr.ofString "add") = False := by simp; decide
        simp [Std.HashMap.getElem?_modify, hsa, hla]
    · exact ⟨bF, ts, tv, fo, nt, bn, by rw [e4 F hFE' (by rw [z2]; exact hFw), e2F], hbF, hbnv, hbFa⟩
  refine ⟨E', w4, ?_, hS4, by rw [e4 ge hgE' (by rw [z2]; exact hgw), e2g],
    by rw [← hw4, ← hw3, ← hw2]; simp [State.setEnv, State.pushEnv],
    by rw [← hw4, ← hw3, ← hw2]; simp [State.setEnv, State.pushEnv], f4⟩
  simp [M.bind_eq, M.bind_apply, M.bindRes_ok, putRefValue, hset_s, M.loopRes_inr, M.loopRes_inl, M.loop, pure, M.pure,
    Compl.updateEmpty, loopContinues, Compl.value?, hpi, SumForProof.updD, Sem.assign, Sem.identRef, rri3, Sem.binary,
    Sem.ident, ri3, Sem.lit, litValue, one_eq, Sem.binaryOp, applyBinaryOp_add_num, hadd_i, hset_i]

/-- The last iteration: `i < n` fails. -/
theorem iterA_exit (ctx : Ctx) (labels : Array JSStr) (E L F ge : EnvId) (N : Nat) (hstr : ctx.strict = false)
    (hN : N < 2 ^ 26) (t : State) (v : Value)
    (hS : ShapeA E L F ge N (some (num (tri N))) (some (num N)) t) (hf : 4 ≤ t.fuel) :
    ∃ t', forIter SumForProof.testD SumForProof.updD bodyA labels ctx #["i"] (E, v) t = .ok (.inr (.normal (some v))) t' ∧
      ShapeA E L F ge N (some (num (tri N))) (some (num N)) t' ∧ t'.fuel = t.fuel - 1 ∧
      (∀ x, t'.envEntry x = t.envEntry x) ∧ t'.heap = t.heap ∧ t'.realms = t.realms := by
  have hS' := hS
  obtain ⟨hE, hL, hF, -, -, -, -, -, -, ⟨bE, bdi, hEE, hbi, hiv, -, -, hbn, -⟩, ⟨bL, -, hLE, -, -, -, hln, -⟩,
    ⟨bF, ts, tv, fo, nt, bn, hFE, hbF, hbnv, -⟩⟩ := hS
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
  refine ⟨t1, ?_, by rw [← ht1]; exact hS', f1, e1, by rw [← ht1], by rw [← ht1]⟩
  simp only [forIter, M.bind_eq, M.bind_apply, htick, M.bindRes_ok, SumForProof.testD, Sem.binary, Sem.ident, hstr, ri, rn]
  simp [Sem.binaryOp, isLessThan, M.bind_eq, M.bind_apply, hlt, ofSmallInt_eq_nan, toBoolean, pure, M.pure]

/-- **One iteration that continues, with the call answered**: the driver (at depth `m`) calls `add`, which
returns `tri k + k`; the iteration ends with `s = tri (k + 1)`, `i = k + 1`, two steps of fuel used (the
iteration's and the call's). -/
theorem iterA_step (eng : Engine) (m : Nat) (ctx : Ctx) (labels : Array JSStr) (E L F ge : EnvId) (N k : Nat)
    (g fA : Nat) (gb : Std.HashMap JSStr Binding) (gtv : Value) (dA : FuncData)
    (hstr : ctx.strict = false) (hk : k < N) (hN : N < 2 ^ 26) (t : State) (v : Value)
    (hS : ShapeA E L F ge N (some (num (tri k))) (some (num k)) t) (hG : GFrame ge g fA gb gtv dA t)
    (hf : 6 ≤ t.fuel) :
    ∃ E' w', Nested.Runs eng (m + 1) (forIter SumForProof.testD SumForProof.updD bodyA labels ctx #["i"] (E, v) t)
        (.inl (E', num (tri (k + 1)))) w' ∧
      ShapeA E' L F ge N (some (num (tri (k + 1)))) (some (num ((k : Int) + 1))) w' ∧
      GFrame ge g fA gb gtv dA w' ∧ w'.fuel + 2 = t.fuel := by
  obtain ⟨K, hreq, hK⟩ := iterA_cont ctx labels E L F ge N k g fA gb gtv dA hstr hk hN t v hS hG hf
  have hG' := hG
  obtain ⟨hgEE, -, -, -, -, -, -, hfs, hfk, hcode, hcls, hmode, hrd⟩ := hG
  have hg : ge < t.envs.size := hS.2.2.2.1
  obtain ⟨t1, ht1⟩ : ∃ t1, ({ t with fuel := t.fuel - 1 } : State) = t1 := ⟨_, rfl⟩
  rw [ht1] at hreq
  obtain ⟨t2, ht2⟩ : ∃ t2, ({ t1 with fuel := t1.fuel - 1 } : State) = t2 := ⟨_, rfl⟩
  have hkb : (k : Int).natAbs < intBound := by simp only [intBound]; omega
  have htb : ((tri k : Nat) : Int).natAbs < intBound := by
    have := tri_bound k N (Nat.le_of_lt hk) hN; simpa using this
  have htb1 : ((tri (k + 1) : Nat) : Int).natAbs < intBound := by
    have := tri_bound (k + 1) N hk hN; simpa using this
  have hadd_s : addF (ofSmallInt (tri k)) (ofSmallInt k) = ofSmallInt (tri (k + 1)) := by
    rw [addF_int _ _ htb hkb (by simpa [tri] using htb1)]; simp [tri]
  obtain ⟨s', hc, -, hh', hr', hz', he', hf'⟩ := AddTwice.add_call fA dA t2 (ofSmallInt (tri k)) (ofSmallInt k) g gb gtv
    hcode hcls hmode (by rw [← ht2, ← ht1]; simp only; rw [hrd]; exact hg)
    (by rw [← ht2, ← ht1]; simp only; rw [hrd]; exact hgEE) (by rw [← ht2, ← ht1]; simp only; omega)
  rw [hadd_s] at hc
  have himpl : callImpl eng (.obj fA) .undefined #[num (tri k), num k] t1 = .ok (num (tri (k + 1))) s' := by
    rw [callImpl_func eng fA dA _ _ t1 (by rw [← ht1]; exact hfs) (by rw [← ht1]; exact hfk) (by rw [← ht1]; simp only; omega),
      ht2]
    exact hc
  have hz2 : t2.envs.size = t.envs.size := by rw [← ht2, ← ht1]
  obtain ⟨E', w', hKw, hS', hge', hh'', hr'', hf''⟩ := hK s' (by rw [← hz2]; exact hz')
    (fun e he => by rw [he' e (by rw [hz2]; exact he)]; rw [← ht2, ← ht1]; rfl)
    (by rw [hf', ← ht2, ← ht1]; simp only; omega)
  refine ⟨E', w', ?_, hS', gframe_of hG' (by rw [hge', he' ge (by rw [hz2]; exact hg)]; rw [← ht2, ← ht1]; rfl)
    (by rw [hh'', hh', ← ht2, ← ht1]) (by rw [hr'', hr', ← ht2, ← ht1]),
    by rw [hf'', hf', ← ht2, ← ht1]; simp only; omega⟩
  rw [hreq]
  exact .call m _ _ _ t1 K _ s' _ w' (Nested.drive_callImpl_ok eng m _ _ _ t1 _ s' himpl) (by rw [hKw]; exact .ok _ _ _)

/-- **The loop** (iterations allowed: the fuel), from the first copy with `i = 0`, `s = tri 0`: runs, each
iteration's call answered at depth `m`, to a normal completion with `s = tri N`, `i = N`. -/
theorem loopA_runs (eng : Engine) (m : Nat) (ctx : Ctx) (labels : Array JSStr) (L F ge : EnvId) (N : Nat) (g fA : Nat)
    (gb : Std.HashMap JSStr Binding) (gtv : Value) (dA : FuncData) (hstr : ctx.strict = false) (hN : N < 2 ^ 26)
    (E0 : EnvId) (t : State) (hS : ShapeA E0 L F ge N (some (num (tri 0))) (some (num (0 : Nat))) t)
    (hG : GFrame ge g fA gb gtv dA t) (hf : 2 * N + 6 ≤ t.fuel) :
    ∃ c t', Nested.Runs eng (m + 1) (M.loop (forIter SumForProof.testD SumForProof.updD bodyA labels ctx #["i"])
        t.fuel (E0, .undefined) t) c t' ∧
      (∃ w, c = Compl.normal (some w)) ∧ (∃ E, ShapeA E L F ge N (some (num (tri N))) (some (num N)) t') ∧
      GFrame ge g fA gb gtv dA t' ∧ t'.fuel + 2 * N + 1 = t.fuel := by
  let I : EnvId × Value → State → Prop := fun st u =>
    ∃ k, k ≤ N ∧ ShapeA st.1 L F ge N (some (num (tri k))) (some (num k)) u ∧ GFrame ge g fA gb gtv dA u ∧
      u.fuel + 2 * k = t.fuel
  let Q : Compl → State → Prop := fun c u =>
    (∃ w, c = Compl.normal (some w)) ∧ (∃ E, ShapeA E L F ge N (some (num (tri N))) (some (num N)) u) ∧
      GFrame ge g fA gb gtv dA u ∧ u.fuel + 2 * N + 1 = t.fuel
  let V : EnvId × Value → State → Nat := fun _ u => u.fuel + 2 * N - t.fuel
  have hstep : ∀ st u, I st u →
      (∃ st' u', Nested.Runs eng (m + 1) (forIter SumForProof.testD SumForProof.updD bodyA labels ctx #["i"] st u)
        (.inl st') u' ∧ I st' u' ∧ V st' u' < V st u) ∨
      (∃ c u', Nested.Runs eng (m + 1) (forIter SumForProof.testD SumForProof.updD bodyA labels ctx #["i"] st u)
        (.inr c) u' ∧ Q c u') := by
    intro ⟨E, v⟩ u ⟨k, hk, hSu, hGu, hfu⟩
    by_cases hkN : k < N
    · obtain ⟨E', u', h, hS', hG', hf'⟩ := iterA_step eng m ctx labels E L F ge N k g fA gb gtv dA hstr hkN hN u v hSu hGu
        (by omega)
      have hc : ((k + 1 : Nat) : Int) = (k : Int) + 1 := by omega
      exact Or.inl ⟨(E', _), u', h, ⟨k + 1, hkN, by rw [hc]; exact hS', hG', by omega⟩, by simp only [V]; omega⟩
    · have hkN' : k = N := by omega
      subst hkN'
      obtain ⟨u', h, hS', hf', he', hh', hr'⟩ := iterA_exit ctx labels E L F ge k hstr hN u v hSu (by omega)
      have hG' : GFrame ge g fA gb gtv dA u' := gframe_of hGu (he' ge) hh' hr'
      exact Or.inr ⟨_, u', by rw [h]; exact .ok _ _ _, ⟨v, rfl⟩, ⟨E, hS'⟩, hG', by omega⟩
  exact Nested.loop_runs eng (m + 1) _ I Q V hstep t.fuel (E0, .undefined) t ⟨0, Nat.zero_le _, hS, hG, by simp⟩
    (by simp only [V]; omega)

/-- The environments before the loop: `L` binds `s` (value `sv`), not `i`, `n` or `add`; `F` binds `n = N`, not
`add`, its outer the global record `ge`. -/
def ShapeBA (L F ge : EnvId) (N : Nat) (sv : Option Value) (t : State) : Prop :=
  L < t.envs.size ∧ F < t.envs.size ∧ ge < t.envs.size ∧ L ≠ F ∧ ge ≠ L ∧
  (∃ bL bds, t.envEntry L = .decl bL (some F) ∧ bL[JSStr.ofString "s"]? = some bds ∧ bds.value = sv ∧
    bds.mutable = true ∧ bL[JSStr.ofString "n"]? = none ∧ bL[JSStr.ofString "i"]? = none ∧
    bL[JSStr.ofString "add"]? = none) ∧
  (∃ bF ts tv fo nt bn, t.envEntry F = .func bF (some ge) ts tv fo nt ∧ bF[JSStr.ofString "n"]? = some bn ∧
    bn.value = some (num N) ∧ bF[JSStr.ofString "add"]? = none)

/-- The `for` statement: from `s = 0`, it completes normally with `s = tri N`. -/
theorem forSA_runs (eng : Engine) (m : Nat) (ctx : Ctx) (L F ge : EnvId) (N : Nat) (g fA : Nat)
    (gb : Std.HashMap JSStr Binding) (gtv : Value) (dA : FuncData) (hlex : ctx.lex = L) (hstr : ctx.strict = false)
    (hN : N < 2 ^ 26) (t : State) (hS : ShapeBA L F ge N (some (num 0)) t) (hG : GFrame ge g fA gb gtv dA t)
    (hf : 2 * N + 8 ≤ t.fuel) :
    ∃ c t', Nested.Runs eng (m + 1) (Sem.forS initD SumForProof.testD SumForProof.updD bodyA ctx t)
        (Sem.breakToNormal c) t' ∧
      (∃ w, c = Compl.normal (some w)) ∧ (∃ E, ShapeA E L F ge N (some (num (tri N))) (some (num N)) t') ∧
      GFrame ge g fA gb gtv dA t' ∧ t'.fuel + 2 * N + 1 = t.fuel := by
  obtain ⟨hL, hF, hg, hLF, hgL, ⟨bL, bds, hLE, hls, hsv, hsm, hln, hli, hla⟩, hFn⟩ := hS
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
  have hS4 : ShapeA E1 L F ge N (some (num (tri 0))) (some (num (0 : Nat))) t4 := by
    have hE14 : E1 < t4.envs.size := by
      rw [← ht4, State.setEnv_envs_size, State.pushEnv_size, ← hE1]; exact Nat.lt_succ_self _
    have hL3 : L < t3.envs.size := by rw [z3]; exact Nat.lt_succ_of_lt hL
    have hF3 : F < t3.envs.size := by rw [z3]; exact Nat.lt_succ_of_lt hF
    have hLE1 : L ≠ E1 := by rw [← hE1]; exact Nat.ne_of_lt hL3
    have hFE1 : F ≠ E1 := by rw [← hE1]; exact Nat.ne_of_lt hF3
    have hg3 : ge < t3.envs.size := by rw [z3]; exact Nat.lt_succ_of_lt hg
    have hgE1 : ge ≠ E1 := by rw [← hE1]; exact Nat.ne_of_lt hg3
    have e4 : ∀ x, x ≠ E1 → x < t3.envs.size → t4.envEntry x = t3.envEntry x := by
      intro x hx hlt
      rw [← ht4, State.setEnv_envEntry_ne _ _ _ _ (Ne.symm hx), State.pushEnv_entry_lt _ _ _ hlt]
    refine ⟨hE14, by rw [← ht4, State.setEnv_envs_size, State.pushEnv_size]; exact Nat.lt_succ_of_lt hL3,
      by rw [← ht4, State.setEnv_envs_size, State.pushEnv_size]; exact Nat.lt_succ_of_lt hF3,
      by rw [← ht4, State.setEnv_envs_size, State.pushEnv_size]; exact Nat.lt_succ_of_lt hg3,
      Ne.symm hLE1, Ne.symm hFE1, hLF, hgE1, hgL, ?_, ?_, ?_⟩
    · refine ⟨_, { value := some (num 0), deletable := false },
        by rw [← ht4]; exact State.setEnv_envEntry_self _ _ _ (by rw [State.pushEnv_size, ← hE1]; exact Nat.lt_succ_self _),
        by simp [Std.HashMap.getElem?_modify], by simp [tri],
        rfl, by simp [Std.HashMap.getElem?_modify, Std.HashMap.getElem?_insert, ne_is],
        by simp [Std.HashMap.getElem?_modify, Std.HashMap.getElem?_insert, ne_in],
        by have hia : (JSStr.ofString "i" = JSStr.ofString "add") = False := by simp; decide
           simp [Std.HashMap.getElem?_modify, Std.HashMap.getElem?_insert, hia]⟩
    · exact ⟨bL, bds, by rw [e4 L hLE1 hL3, e3 L hL, hLE], hls, by simp [hsv, tri], hsm, hln, hla⟩
    · obtain ⟨bF, ts, tv, fo, nt, bn, hFE, hbF, hbnv, hbFa⟩ := hFn
      exact ⟨bF, ts, tv, fo, nt, bn, by rw [e4 F hFE1 hF3, e3 F hF, hFE], hbF, hbnv, hbFa⟩
  have hG4 : GFrame ge g fA gb gtv dA t4 := by
    have hg3 : ge < t3.envs.size := by rw [z3]; exact Nat.lt_succ_of_lt hg
    have hgE1 : ge ≠ E1 := by rw [← hE1]; exact Nat.ne_of_lt hg3
    refine gframe_of hG ?_ ?_ ?_
    · rw [← ht4, State.setEnv_envEntry_ne _ _ _ _ (Ne.symm hgE1), State.pushEnv_entry_lt _ _ _ hg3, e3 ge hg]
    · rw [← ht4, ← ht3, ← ht2, ← ht1]; simp [State.setEnv, State.pushEnv]
    · rw [← ht4, ← ht3, ← ht2, ← ht1]; simp [State.setEnv, State.pushEnv]
  -- the loop
  obtain ⟨c, t5, hloop, hc, hS5, hG5, hf5⟩ := loopA_runs eng m { Sem.inner ctx with strict := false } ctx.labels L F ge N
    g fA gb gtv dA rfl hN E1 t4 hS4 hG4 (by omega)
  rw [f4] at hloop
  refine ⟨c, t5, ?_, hc, hS5, hG5, by rw [← f4]; exact hf5⟩
  have hil : (Sem.inner ctx).lex = L := hlex
  simp only [hil, hE0, ht1]
  simp only [boundNames_ident, List.foldl_toArray', List.foldl_cons, List.foldl_nil, Array.foldl_toList,
    List.foldl, Array.empty_append, M.forArr_def, M.foldArr_toArray, M.foldList_cons, M.foldList_nil, hcm, M.bindRes_ok]
  have his : (Sem.inner ctx).strict = false := hstr
  simp only [Sem.varDecl, Sem.inner, M.bind_eq, M.bind_apply, M.forArr_def, M.foldArr_toArray, M.foldList_cons,
    M.foldList_nil, Sem.declLex, hstr, hr0, M.bindRes_ok, Sem.lit, litValue, zero_eq, pure, M.pure, initializeRefBinding,
    hin, h1, h2, Bool.false_eq_true, Bool.or_false, ↓reduceIte, hpi, M.repeatFrom, f4]
  exact Nested.runs_bind eng _ (m + 1) _ c t5 hloop _ _ (.ok _ _ _)

/-! ## `sumAdd`'s body and call -/

open MoreCalls in
theorem lexSumAdd : topLevelLexicallyScoped SAGen.sumAdd_stmts = #[.binding .let (.ident "s")] := by
  have hv : (VarKind.let == VarKind.var) = false := by decide
  simp [topLevelLexicallyScoped, stmtLexScoped, SAGen.sumAdd_stmts, hv]

open MoreCalls in
theorem sumAdd_fdi (f : ObjId) (d : FuncData) (env : EnvId) (s : State) (N : Nat) (tv : Value) (ge : EnvId)
    (hcode : d.code = SAGen.sumAdd_func) (henv : env < s.envs.size) (hdenv : d.env = ge) (hge : ge < s.envs.size)
    (hE : s.envEntry env = .func ∅ (some d.env) .initialized tv f .undefined)
    (hf : s.fuel ≠ 0) :
    ∃ ctx s', functionDeclarationInstantiation 999999 f d env #[num N] s = .ok ctx s' ∧
      ctx.lex = s.envs.size ∧ ctx.strict = false ∧ ctx.isGen = false ∧
      ShapeBA s.envs.size env ge N none s' ∧ s'.fuel = s.fuel ∧ s'.heap = s.heap ∧ s'.realms = s.realms ∧
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
  have hbody : SAGen.sumAdd_func.body = .stmts SAGen.sumAdd_stmts := rfl
  have hparams : SAGen.sumAdd_func.params = #[.mk (.ident "n") none false] := rfl
  have hstr : SAGen.sumAdd_func.strict = false := rfl
  have hasync : SAGen.sumAdd_func.isAsync = false := rfl
  have hgen : SAGen.sumAdd_func.isGenerator = false := rfl
  have hkind : SAGen.sumAdd_func.kind = .normal := rfl
  have hfdi : SAGen.sumAdd_func.info.fdi = { paramNames := #["n"], hasDuplicates := false, varNames := #[], hasFunctions := false, functionNames := #[], hasLexical := true, lexNames := #["s"], argumentsNeeded := false, hasAnnexB := false, usesDispose := false } := rfl
  have hk1 : (VarKind.let == VarKind.const) = false := by decide
  have hk2 : (VarKind.let == VarKind.using) = false := by decide
  have hk3 : (VarKind.let == VarKind.awaitUsing) = false := by decide
  have hphe : SAGen.sumAdd_func.info.paramsHaveExpressions = false := rfl
  refine ⟨?c, ?t, ?h, ?_⟩
  case h =>
    conv =>
      lhs
      simp only [functionDeclarationInstantiation, hcode, hbody, hparams, hstr, hfdi, hasync, hgen, hkind, hphe]
      simp [hr, hasBinding_declLike, createMutableBinding_declLike, hbe, newDeclEnv, pure,
        M.pure, hE, henv, hf, lexSumAdd, TotalCall.names_s, -allocEnv_apply, allocEnv_eq, LexScoped.isConstant,
        State.pushEnv_entry_at, State.setEnv_envEntry_self, hk1, hk2, hk3]
  have hne : s.envs.size ≠ env := Nat.ne_of_gt henv
  have hne' : env ≠ s.envs.size := Nat.ne_of_lt henv
  have hsa : (JSStr.ofString "s" = JSStr.ofString "add") = False := by simp; decide
  have hna : (JSStr.ofString "n" = JSStr.ofString "add") = False := by simp; decide
  refine ⟨rfl, rfl, rfl, ?_, by simp, by simp [State.setEnv, State.pushEnv], by simp [State.setEnv, State.pushEnv], ?_⟩
  · refine ⟨by simp, by simp; exact Nat.lt_succ_of_lt henv, by simp; exact Nat.lt_succ_of_lt hge, hne,
      Nat.ne_of_lt hge, ?_, ?_⟩
    · simp [State.setEnv_envEntry_self, Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert, ne_sn', ne_is, ne_in, ne_si, hsa]
    · simp [State.setEnv_envEntry_ne _ _ _ _ hne, State.pushEnv_entry_lt, State.setEnv_envEntry_self,
        henv, Std.HashMap.getElem?_modify, hdenv, Std.HashMap.getElem?_insert, hna]
  · intro e he hee
    simp [State.setEnv_envEntry_ne _ _ _ _ (show s.envs.size ≠ e by omega), State.pushEnv_entry_lt, he,
      State.setEnv_envEntry_ne _ _ _ _ (Ne.symm hee)]

abbrev letS : Sem.CStmt := Sem.varDecl #[Sem.declLex VarKind.let "s" (some (Sem.lit (Lit.num (F64.fin false 0 (-1074)))))]
abbrev retS : Sem.CStmt := Sem.ret (some (Sem.ident "s"))

theorem sumAdd_def (n : Nat) : SAGen.sumAdd n =
    Sem.stmts #[letS, Sem.forS initD SumForProof.testD SumForProof.updD bodyA, retS] := rfl

/-- **`sumAdd`'s body** runs (each `add` call answered at depth `m`) to `return tri N`, for every `N < 2^26`. -/
theorem sumAdd_spec (eng : Engine) (m nn : Nat) (ctx : Ctx) (L F ge : EnvId) (N : Nat) (g fA : Nat)
    (gb : Std.HashMap JSStr Binding) (gtv : Value) (dA : FuncData) (hlex : ctx.lex = L) (hstr : ctx.strict = false)
    (hgen : ctx.isGen = false) (hN : N < 2 ^ 26) (s0 : State) (hS : ShapeBA L F ge N none s0)
    (hG : GFrame ge g fA gb gtv dA s0) (hf : 2 * N + 12 ≤ s0.fuel) :
    ∃ s', Nested.Runs eng (m + 1) (SAGen.sumAdd nn ctx s0) (.ret (num (tri N))) s' := by
  obtain ⟨hL, hF, hg, hLF, hgL, ⟨bL, bds, hLE, hls, hsv, hsm, hln, hli, hla⟩, hFn⟩ := hS
  -- `let s = 0`
  have hr : resolveBinding L "s" false s0 = .ok (.env (some L) "s" false) s0 :=
    resolveBinding_here L _ false s0 hL (by rw [hLE]; rfl)
      (by rw [hLE]; simp [Env.bindingsMap, Std.HashMap.contains_eq_isSome_getElem?, hls]) (by omega)
  have hin := initializeBinding_declLike L "s" (num 0) s0 hL (by rw [hLE]; rfl)
  rw [hLE] at hin
  obtain ⟨s1, hs1⟩ : ∃ s1, s0.setEnv L ((Env.decl bL (some F)).withBindings
      (·.modify "s" fun bd => { bd with value := some (num 0) })) = s1 := ⟨_, rfl⟩
  rw [hs1] at hin
  have e1L : s1.envEntry L = .decl (bL.modify "s" fun bd => { bd with value := some (num 0) }) (some F) := by
    rw [← hs1, State.setEnv_envEntry_self _ _ _ hL]; rfl
  have hsa : (JSStr.ofString "s" = JSStr.ofString "add") = False := by simp; decide
  have hS1 : ShapeBA L F ge N (some (num 0)) s1 := by
    refine ⟨by rw [← hs1, State.setEnv_envs_size]; exact hL, by rw [← hs1, State.setEnv_envs_size]; exact hF,
      by rw [← hs1, State.setEnv_envs_size]; exact hg, hLF, hgL,
      ⟨_, { bds with value := some (num 0) }, e1L, by simp [Std.HashMap.getElem?_modify, hls], rfl, hsm,
        by simp [Std.HashMap.getElem?_modify, ne_sn, hln], by simp [Std.HashMap.getElem?_modify, ne_si, hli],
        by simp [Std.HashMap.getElem?_modify, hsa, hla]⟩, ?_⟩
    obtain ⟨bF, ts, tv, fo, nt, bn, hFE, hbF, hbnv, hbFa⟩ := hFn
    exact ⟨bF, ts, tv, fo, nt, bn, by rw [← hs1, State.setEnv_envEntry_ne _ _ _ _ hLF, hFE], hbF, hbnv, hbFa⟩
  have hG1 : GFrame ge g fA gb gtv dA s1 :=
    gframe_of hG (by rw [← hs1, State.setEnv_envEntry_ne _ _ _ _ (Ne.symm hgL)]) (by rw [← hs1]; simp [State.setEnv])
      (by rw [← hs1]; simp [State.setEnv])
  have f1 : s1.fuel = s0.fuel := by rw [← hs1, State.setEnv_fuel]
  have ha : letS ctx s0 = .ok (.normal none) s1 := by
    have hlu : (VarKind.let == VarKind.using) = false := by decide
    have hla' : (VarKind.let == VarKind.awaitUsing) = false := by decide
    simp [M.bind_eq, M.bind_apply, Sem.varDecl, Sem.inner, Sem.declLex, hlex, hstr, hr, Sem.lit, litValue,
      zero_eq, initializeRefBinding, hin, hlu, hla', M.forArr, pure, M.pure]
  -- the loop
  obtain ⟨c, s2, hfor, ⟨w, hc⟩, ⟨E, hS2⟩, -, hf2⟩ := forSA_runs eng m ctx L F ge N g fA gb gtv dA hlex hstr hN s1 hS1 hG1
    (by omega)
  subst hc
  obtain ⟨-, h2L, -, -, -, -, -, -, -, -, ⟨bL2, bds2, h2LE, hls2, hsv2, -, -, -⟩, -⟩ := hS2
  have hret : identValue L "s" false s2 = .ok (num (tri N)) s2 :=
    identValue_skip0 L _ false s2 bds2 _ h2L (by rw [h2LE]; rfl) (by rw [h2LE]; exact hls2) hsv2 (by omega)
  refine ⟨s2, ?_⟩
  rw [sumAdd_def]
  refine Nested.stmts3_runs eng (m + 1) _ _ _ ctx s0 s1 s2 s2 none (some w) _ ha hfor ?_ (by omega)
  simp [Sem.ret, Sem.inner, Sem.ident, hlex, hstr, hret, hgen, M.bind_eq, M.bind_apply, pure, M.pure]

/-- **The [[Call]] of `sumAdd` with `N`** (`this` undefined), at driver depth `m + 1`: runs, each of its `N` calls
of `add` answered at depth `m`, to `0 + 1 + … + (N − 1)`, for every `N < 2^26`. -/
theorem sumAdd_call (eng : Engine) (m : Nat) (fS : ObjId) (dS : FuncData) (s : State) (N : Nat) (ge g fA : Nat)
    (gb : Std.HashMap JSStr Binding) (gtv : Value) (dA : FuncData)
    (hcode : dS.code = SAGen.sumAdd_func) (hcls : dS.isClassCtor = false) (hmode : dS.thisMode = .global)
    (hdenv : dS.env = ge) (hrd : (s.realms[dS.realm]!).globalEnv = ge) (hge : ge < s.envs.size)
    (hG : GFrame ge g fA gb gtv dA s) (hN : N < 2 ^ 26) (hf : 2 * N + 14 ≤ s.fuel) :
    ∃ s', Nested.Runs eng (m + 1) (callECMA fS dS .undefined #[num N] s) (num (tri N)) s' := by
  have hG' := hG
  obtain ⟨hgE, -⟩ := hG
  obtain ⟨s', h1, -⟩ := Nested.callECMA_undef_runs eng (m + 1) (Q := fun _ => True) fS dS s #[num N] (num (tri N)) g gb gtv
    hcls hmode (by rw [hcode]; rfl) (by rw [hcode]; rfl) (by rw [hrd]; exact hge) (by rw [hrd]; exact hgE)
    (fun t hlt hEt hold hheap hfu hrl _ => by
      obtain ⟨ctx, t1, hfdi, hlex, hstr, hgen, hS, hfuel, hheap1, hrl1, hfe1⟩ :=
        sumAdd_fdi fS dS s.envs.size t N gtv ge hcode hlt hdenv (Nat.lt_trans hge hlt) hEt (by omega)
      have hG1 : GFrame ge g fA gb gtv dA t1 :=
        gframe_of hG' (by rw [hfe1 ge (Nat.lt_trans hge hlt) (Nat.ne_of_lt hge), hold ge hge]) (hheap1.trans hheap)
          (hrl1.trans hrl)
      obtain ⟨t2, hbody⟩ := sumAdd_spec eng m 999964 ctx t.envs.size s.envs.size ge N g fA gb gtv dA hlex hstr hgen hN
        t1 hS hG1 (by omega)
      refine ⟨t2, ?_, trivial⟩
      have hbd : dS.code.body = .stmts SAGen.sumAdd_stmts := by rw [hcode]; rfl
      have hdisp : dS.code.info.fdi.usesDispose = false := by rw [hcode]; rfl
      have hbody' : Nested.Runs eng (m + 1) (evalStmts (999964 + 35) ctx SAGen.sumAdd_stmts t1) (.ret (num (tri N))) t2 := by
        rw [← congrFun (SAGen.sumAdd_eq 999964) ctx]; exact hbody
      simp only [evalDepth, evalFunctionBody, M.bind_eq, M.bind_apply, hfdi, M.bindRes_ok, hbd, hdisp, withDisposeScope,
        Bool.not_false, ↓reduceIte]
      rw [show (999999 : Nat) = 999964 + 35 from rfl]
      exact Nested.runs_bind eng _ (m + 1) _ _ t2 hbody' _ _ (.ok _ _ _))
  exact ⟨s', h1⟩

/-! ## The whole script -/

open Script

abbrev l10 : F64 := F64.fin false 5629499534213120 (-49)
theorem l10_eq : l10 = ofSmallInt ((10 : Nat) : Int) := by decide
theorem tri10 : tri 10 = 45 := by decide
abbrev callSA : Sem.CStmt := Sem.exprStmt (Sem.call (Sem.identRef "sumAdd")
  (Sem.args #[Sem.ArgD.expr (Sem.lit (Lit.num l10))]) false (CalleeDesc.ident "sumAdd"))

theorem script_def (n : Nat) : SAGen.script n = Sem.stmts #[Sem.funDecl SAGen.add_func, Sem.funDecl SAGen.sumAdd_func,
    callSA] := rfl
theorem lexScoped : topLevelLexicallyScoped SAGen.script_stmts = #[] := by
  simp [topLevelLexicallyScoped, stmtLexScoped, SAGen.script_stmts]
theorem add_same : SAGen.add_func = AddGen.add_func := rfl

def fs : List (Func × JSStr) := [(SAGen.add_func, "add"), (SAGen.sumAdd_func, "sumAdd")]

theorem varS : topLevelVarScoped SAGen.program.body = (fs.map fun p => VarScoped.func p.1).toArray := rfl
theorem lexS : topLevelLexicallyScoped SAGen.program.body =
    (([] : List JSStr).map fun x => LexScoped.binding .let (.ident x)).toArray := by
  rw [show SAGen.program.body = SAGen.script_stmts from rfl, lexScoped]; rfl
theorem annS : annexBFunctions SAGen.program.body ([] : List JSStr).toArray = #[] := rfl
theorem simpleS : ∀ p ∈ fs, Inst.SimpleFn p.1 p.2 := by
  intro p hp; simp only [fs, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl
  · exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem nodupS : (fs.map Prod.snd).Nodup := by decide

theorem body_eq : SAGen.program.body = SAGen.script_stmts := rfl
theorem depth_eq : evalDepth = 999956 + 44 := rfl
theorem script_body (u : State) (c : Ctx) : evalStmts evalDepth c SAGen.program.body u = SAGen.script 999956 c u := by
  rw [SAGen.script_eq, body_eq, depth_eq]

/-- **The whole program** (examples/sum_add.js): `sumAdd(10)` runs its loop ten times, calling `add` in each
iteration; the script evaluates to 45. Started from a realm whose global object is an ordinary extensible
object without `add` or `sumAdd`. -/
theorem sa_script (eng : Engine) (s : State) (cs : Conts) (gb : Std.HashMap JSStr Binding) (gtv : Value)
    (fp : ObjId) (hge : s.curRealm.globalEnv < s.envs.size)
    (hE : s.envEntry s.curRealm.globalEnv = .global s.curRealm.globalObj gb gtv)
    (hgba : gb.contains "add" = false) (hgbs : gb.contains "sumAdd" = false)
    (hgs : s.curRealm.globalObj < s.heap.size) (hk : (s.objEntry s.curRealm.globalObj).kind = .ordinary)
    (hx : (s.objEntry s.curRealm.globalObj).extensible = true)
    (hpa : (s.objEntry s.curRealm.globalObj).props.get? (.str "add") = none)
    (hps : (s.objEntry s.curRealm.globalObj).props.get? (.str "sumAdd") = none)
    (hfp : s.curRealm.intrinsics["%Function.prototype%"]? = some fp) (hf : 60 ≤ s.fuel) :
    ∃ s', (runM eng (scriptEvaluation SAGen.program) s cs).1 = .ok (num 45) s' := by
  let ge := s.curRealm.globalEnv
  let g := s.curRealm.globalObj
  let c := scriptCtx s false
  obtain ⟨t0, ht0⟩ : ∃ y, (scriptStart s SAGen.program).setEnv ge (.global g (insertLets gb []) gtv) = y := ⟨_, rfl⟩
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
  let fA := s.heap.size
  let fS := s.heap.size + 2
  obtain ⟨dA, hfAk, hcA, hrA, hmA, hclsA, -, -⟩ := hfuns 0 (by decide)
  obtain ⟨dS, hfSk, hcS, hrS, hmS, hclsS, -, hdS⟩ := hfuns 1 (by decide)
  rw [hz0] at hfAk hfSk hszu hnames
  simp only [fs, List.length_cons, List.length_nil] at hszu
  simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one] at hfAk hfSk
  have hpA : (u.objEntry g).props.get? (.str "add") = some (.data (.obj fA) true true false) := hnames 0 (by decide)
  have hpS : (u.objEntry g).props.get? (.str "sumAdd") = some (.data (.obj fS) true true false) := hnames 1 (by decide)
  have hE1 : u.envEntry ge = .global g gb gtv := by
    have h1 : u.envEntry ge = t0.envEntry ge := by simp only [State.envEntry, heu]
    rw [h1, ← ht0, State.setEnv_envEntry_self _ _ _ (show ge < (scriptStart s SAGen.program).envs.size from hge)]
    simp [insertLets]
  have hgeu : ge < u.envs.size := by rw [heu]; exact hge0
  have hgu : g < u.heap.size := by rw [hszu]; exact Nat.lt_of_lt_of_le hgs (Nat.le_add_right _ _)
  have hfAu : fA < u.heap.size := by show s.heap.size < u.heap.size; rw [hszu]; omega
  have hfSu : fS < u.heap.size := by show s.heap.size + 2 < u.heap.size; rw [hszu]; omega
  have hgbs' : gb[JSStr.ofString "sumAdd"]? = none := Std.HashMap.getElem?_eq_none (fun hm => by
    rw [Std.HashMap.mem_iff_contains, hgbs] at hm; exact Bool.false_ne_true hm)
  have hgbsm : (JSStr.ofString "sumAdd" ∈ gb) = False := by simp [Std.HashMap.mem_iff_contains, hgbs]
  have hgba' : gb[JSStr.ofString "add"]? = none := Std.HashMap.getElem?_eq_none (fun hm => by
    rw [Std.HashMap.mem_iff_contains, hgba] at hm; exact Bool.false_ne_true hm)
  have hgbam : (JSStr.ofString "add" ∈ gb) = False := by simp [Std.HashMap.mem_iff_contains, hgba]
  -- `sumAdd(10)` asks for its call
  obtain ⟨K0, h0, hK0⟩ := Stmts.call_expr_req (Sem.inner c) u ge g fS "sumAdd" gb gtv dS [(Sem.lit (Lit.num l10), .num l10)]
    (by intro p hp; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp; rcases hp with rfl; rfl)
    rfl rfl hgeu hE1 hgbs hgbs' hgbsm hgu hku hpS hfSu hfSk (by rw [hfuu, hfu0]; omega)
  obtain ⟨K4, h4, hK4⟩ := Stmts.exprStmt_req _ c u _ K0 h0 hK0
  -- the call: ten iterations, each calling `add` (`sumAdd_call`)
  obtain ⟨u', hu'⟩ : ∃ y, ({ u with fuel := u.fuel - 1 } : State) = y := ⟨_, rfl⟩
  have hr' : u'.realms = s.realms := by rw [← hu']; exact hru.trans hr0
  have hz' : u'.envs = u.envs := by rw [← hu']
  have hou : ∀ y, u'.objEntry y = u.objEntry y := fun y => by rw [← hu']; rfl
  have hG : GFrame ge g fA gb gtv dA u' := ⟨by simp only [State.envEntry, hz']; exact hE1, hgba, hgba', hgbam,
    by rw [← hu']; exact hgu, by rw [hou]; exact hku, by rw [hou]; exact hpA, by rw [← hu']; exact hfAu,
    by rw [hou]; exact hfAk, hcA.trans add_same, hclsA, hmA, by rw [hr', hrA, hrl0]; rfl⟩
  obtain ⟨s4, hrun⟩ := sumAdd_call eng 3998 fS dS u' 10 ge g fA gb gtv dA hcS hclsS hmS hdS
    (by rw [hr', hrS, hrl0]; rfl) (by rw [hz']; exact hgeu) hG (by decide)
    (by rw [← hu']; simp only; rw [hfuu, hfu0]; omega)
  rw [tri10] at hrun
  have hnest : ∀ cs, (drive eng 3999 (callImpl eng (.obj fS) .undefined #[.num l10] u) cs).1 = .ok (num 45) s4 := by
    intro cs
    rw [l10_eq, callImpl_func eng fS dS _ _ u hfSu hfSk (by rw [hfuu, hfu0]; omega), hu']
    exact Nested.drive_of_runs eng 3999 _ _ _ hrun cs
  -- the script
  refine ⟨s4, script_value eng s cs SAGen.program fs [] gb gtv fp _ s4 rfl varS lexS annS simpleS nodupS hge hE
    (by intro p hp; simp only [fs, List.mem_cons, List.mem_nil_iff, or_false] at hp
        rcases hp with rfl | rfl
        · exact hgba
        · exact hgbs)
    (by simp) hgs hk hx
    (by intro p hp; simp only [fs, List.mem_cons, List.mem_nil_iff, or_false] at hp
        rcases hp with rfl | rfl
        · exact hpa
        · exact hps)
    (by simp) hfp ?_⟩
  have hu0 : scriptState s SAGen.program fs [] gb gtv fp = u := by rw [← hu, ← ht0]; rfl
  have hscript : evalStmts evalDepth (scriptCtx s false) SAGen.program.body u = SAGen.script 999956 c u :=
    script_body u c
  have h4' : callSA c u = .req (.call (.obj fS) .undefined #[.num l10]) u K4 := h4
  rw [hu0, hscript, script_def]
  refine _root_.Runs.script_runs eng _ _ _ (_root_.Runs.stmts_run eng c _ u _ s4 ?_ (by simp; rw [hfuu, hfu0]; omega))
  show _root_.Runs.StmtsRun eng c [Sem.funDecl SAGen.add_func, Sem.funDecl SAGen.sumAdd_func, callSA] u none
    (some (num 45)) s4
  refine .cons _ _ u u s4 none none _ (_root_.Runs.runs_funDecl eng _ c u rfl) ?_
  refine .cons _ _ u u s4 none none _ (_root_.Runs.runs_funDecl eng _ c u rfl) ?_
  refine .cons _ _ u s4 s4 (some (num 45)) none _ ?_ (.nil _ _)
  rw [h4']
  exact Nested.runsTo_call_nested eng _ _ _ u K4 _ s4 _ s4 hnest (by rw [hK4]; exact _root_.Runs.runsTo_ok eng _ _)

end SumAdd
