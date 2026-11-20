import Proofs.Method
import Proofs.CLGen

/-!
# Closures: a counter that outlives its maker (examples/closure.js)

```js
function make() { let n = 0; return function () { n = n + 1; return n; }; }
let c = make();
c();
c();
```
evaluates to 2: `make`'s call creates `n` in its body's lexical environment `L` and returns a function
object whose environment is `L`; after `make` returns, each `c()` reaches `n` through its own body's
records (block, then function) and the captured `L`, and updates it there.
-/

open ES ES.Conv SumProof

namespace Closure

/-! ## Reaching a captured variable -/

/-- A function record without the name: the walk continues at its outer record. -/
theorem identBody_skip_func (k : Nat) (env o : EnvId) (n : JSStr) (strict : Bool) (s : State)
    (b : Std.HashMap JSStr Binding) (ts : ThisStatus) (tv : Value) (fo : ObjId) (nt : Value)
    (h : env < s.envs.size) (hE : s.envEntry env = .func b (some o) ts tv fo nt) (hn : b[n]? = none) :
    M.loop (identBody n strict) (k + 1) env s = M.loop (identBody n strict) k o s := by
  simp [M.loop, identBody, M.bind_eq, M.bind_apply, readEnv_entry _ _ _ h, hE, hn, pure, M.pure]

theorem resolveBody_skip_func (k : Nat) (env o : EnvId) (n : JSStr) (strict : Bool) (s : State)
    (b : Std.HashMap JSStr Binding) (ts : ThisStatus) (tv : Value) (fo : ObjId) (nt : Value)
    (h : env < s.envs.size) (hE : s.envEntry env = .func b (some o) ts tv fo nt) (hn : b[n]? = none) :
    M.loop (resolveBody n strict) (k + 1) (some env) s = M.loop (resolveBody n strict) k (some o) s := by
  have hc : b.contains n = false := by simp [Std.HashMap.contains_eq_isSome_getElem?, hn]
  simp [M.loop, resolveBody, M.bind_eq, M.bind_apply, hasBinding, readEnv_entry _ _ _ h, hE, hc, Env.outer, pure,
    M.pure]

/-- A name in the captured environment `L`, read from a function body's block `L'` (outer: the function
record `F'`, outer: `L`). -/
theorem identValue_captured (L' F' L : EnvId) (n : JSStr) (strict : Bool) (s : State) (b1 b2 : Std.HashMap JSStr Binding)
    (ts : ThisStatus) (tv : Value) (fo : ObjId) (nt : Value) (bd : Binding) (v : Value)
    (h1 : L' < s.envs.size) (hE1 : s.envEntry L' = .decl b1 (some F')) (hn1 : b1[n]? = none)
    (h2 : F' < s.envs.size) (hE2 : s.envEntry F' = .func b2 (some L) ts tv fo nt) (hn2 : b2[n]? = none)
    (h : L < s.envs.size) (hk : (s.envEntry L).isDeclLike = true) (hb : (s.envEntry L).bindingsMap[n]? = some bd)
    (hv : bd.value = some v) (hf : 3 ≤ s.fuel) : identValue L' n strict s = .ok v s := by
  obtain ⟨k, hk1⟩ : ∃ k, s.fuel = k + 3 := ⟨s.fuel - 3, by omega⟩
  rw [identValue_loop, hk1, identBody_skip _ L' F' n strict s b1 h1 hE1 hn1,
    identBody_skip_func _ F' L n strict s b2 ts tv fo nt h2 hE2 hn2, identBody_found k L n strict s bd v h hk hb hv]

theorem resolveBinding_captured (L' F' L : EnvId) (n : JSStr) (strict : Bool) (s : State)
    (b1 b2 : Std.HashMap JSStr Binding) (ts : ThisStatus) (tv : Value) (fo : ObjId) (nt : Value)
    (h1 : L' < s.envs.size) (hE1 : s.envEntry L' = .decl b1 (some F')) (hn1 : b1[n]? = none)
    (h2 : F' < s.envs.size) (hE2 : s.envEntry F' = .func b2 (some L) ts tv fo nt) (hn2 : b2[n]? = none)
    (h : L < s.envs.size) (hk : (s.envEntry L).isDeclLike = true) (hb : (s.envEntry L).bindingsMap.contains n = true)
    (hf : 3 ≤ s.fuel) : resolveBinding L' n strict s = .ok (.env (some L) n strict) s := by
  obtain ⟨k, hk1⟩ : ∃ k, s.fuel = k + 3 := ⟨s.fuel - 3, by omega⟩
  rw [resolveBinding_loop, hk1, resolveBody_skip _ L' F' n strict s b1 h1 hE1 hn1,
    resolveBody_skip_func _ F' L n strict s b2 ts tv fo nt h2 hE2 hn2, resolveBody_found k L n strict s h hk hb]

/-! ## Function expressions -/

/-- **An anonymous function expression** (non-strict, normal, not async or a generator), in a context
without private names: the function object (environment: the current lexical environment; `name`: the
empty string) and its `prototype` object, allocated after the existing objects. -/
theorem instExpr (fn : Func) (t : State) (ctx : Ctx) (fp : ObjId) (hstr : fn.strict = false)
    (hasync : fn.isAsync = false) (hgen : fn.isGenerator = false) (hkind : fn.kind = .normal)
    (hname : fn.name = none) (hpriv : ctx.priv = #[])
    (hfp : t.curRealm.intrinsics["%Function.prototype%"]? = some fp) :
    instantiateFunctionExpr fn ctx none t =
      .ok (.obj t.heap.size) (Inst.instStateFn fn JSStr.empty t ctx.lex ctx.script fp) := by
  have hka : (FuncKind.normal == FuncKind.arrow) = false := by decide
  have hkn : (FuncKind.normal == FuncKind.normal) = true := by decide
  have hproto : intrinsic (functionProtoName fn) t = .ok fp t := by
    simp [intrinsic, hfp, functionProtoName, hasync, hgen]
  have hcreate : ordinaryFunctionCreate fp fn ctx.lex #[] ctx false t =
      .ok t.heap.size ((t.allocObj { proto := .obj fp, kind := .func (Inst.fnData fn t ctx.lex ctx.script) }).setProp
        t.heap.size (.str kLength) (.data (numV fn.info.expectedArgs) false false true)) := by
    simp [ordinaryFunctionCreate, alloc_eq, setOwn_eq, hstr, pure, M.pure, Inst.fnData, -alloc_apply]
  have hlegacy : ∀ (u : State) (fo : ObjId), addLegacyFunctionProps fo fn u =
      .ok () ((u.setProp fo (.str "arguments") (.data .null false false false)).setProp fo (.str "caller")
        (.data .null false false false)) := by
    intro u fo
    simp [addLegacyFunctionProps, setOwn_eq, hstr, hasync, hgen, hkind, hkn, pure, M.pure]
  simp only [instantiateFunctionExpr, M.bind_eq, M.bind_apply, hproto, M.bindRes_ok, hname, hkind, hka, hpriv]
  simp only [hcreate, M.bindRes_ok]
  simp [Inst.step_name_fn JSStr.empty, State.setProp_entry_self, State.allocObj_entry_new,
    PropMap.get?_insert_ne _ _ _ _ AddScript.kLength_ne_kName, hgen, hasync, hkn, hkind, AddScript.step_ctor, hlegacy,
    Inst.instStateFn, pure, M.pure]

/-! ## The closure's body -/

/-- The captured record after `n = v`. -/
abbrev setN (L : EnvId) (bL : Std.HashMap JSStr Binding) (o : Option EnvId) (v : Value) (s : State) : State :=
  s.setEnv L (.decl (bL.modify "n" fun bd => { bd with value := some v }) o)

/-- **The closure's body**, run from its block `L'` (outer: its function record `F'`, outer: the captured
`L`, where `n = k`): returns `k + 1`, and the only change is `n = k + 1` in `L`. -/
theorem fn1_spec (nn : Nat) (ctx : Ctx) (L' F' L : EnvId) (k : Nat) (hlex : ctx.lex = L') (hstr : ctx.strict = false)
    (hgen : ctx.isGen = false) (s0 : State) (b1 b2 bL : Std.HashMap JSStr Binding) (ts : ThisStatus) (tv : Value)
    (fo : ObjId) (nt : Value) (o : Option EnvId) (bd : Binding)
    (h1 : L' < s0.envs.size) (hE1 : s0.envEntry L' = .decl b1 (some F')) (hn1 : b1[JSStr.ofString "n"]? = none)
    (h2 : F' < s0.envs.size) (hE2 : s0.envEntry F' = .func b2 (some L) ts tv fo nt) (hn2 : b2[JSStr.ofString "n"]? = none)
    (h : L < s0.envs.size) (hEL : s0.envEntry L = .decl bL o) (hb : bL[JSStr.ofString "n"]? = some bd)
    (hv : bd.value = some (num k)) (hm : bd.mutable = true) (hL1 : L ≠ L') (hL2 : L ≠ F') (hk : k < 2 ^ 26)
    (hf : 4 ≤ s0.fuel) :
    CLGen.fn1 nn ctx s0 = .ok (.ret (num ((k : Int) + 1))) (setN L bL o (num ((k : Int) + 1)) s0) := by
  have hkb : (k : Int).natAbs < intBound := by simp only [intBound]; omega
  have hk1b : ((k : Int) + 1).natAbs < intBound := by simp only [intBound]; omega
  have hadd : addF (ofSmallInt k) (ofSmallInt 1) = ofSmallInt ((k : Int) + 1) := by
    rw [addF_int _ _ hkb (by simp [intBound]) (by simpa using hk1b)]
  have hdl : (s0.envEntry L).isDeclLike = true := by rw [hEL]; rfl
  have hrd := identValue_captured L' F' L "n" false s0 b1 b2 ts tv fo nt bd (num k) h1 hE1 hn1 h2 hE2 hn2 h hdl
    (by rw [hEL]; exact hb) hv (by omega)
  have hrr := resolveBinding_captured L' F' L "n" false s0 b1 b2 ts tv fo nt h1 hE1 hn1 h2 hE2 hn2 h hdl
    (by rw [hEL]; simp [Env.bindingsMap, Std.HashMap.contains_eq_isSome_getElem?, hb]) (by omega)
  have hset := setMutableBinding_decl L "n" (num ((k : Int) + 1)) false s0 bL o bd h hEL hb (by simp [hv]) hm
  obtain ⟨s1, hs1⟩ : ∃ x, setN L bL o (num ((k : Int) + 1)) s0 = x := ⟨_, rfl⟩
  rw [show s0.setEnv L _ = setN L bL o (num ((k : Int) + 1)) s0 from rfl, hs1] at hset
  rw [hs1]
  have hpe : putRefValue (.env (some L) "n" false) (num ((k : Int) + 1)) s0 = .ok () s1 := by
    simp [putRefValue, hset]
  have hrd1 : identValue L' "n" false s1 = .ok (num ((k : Int) + 1)) s1 := by
    have hz : s1.envs.size = s0.envs.size := by rw [← hs1]; simp
    refine identValue_captured L' F' L "n" false s1 b1 b2 ts tv fo nt { bd with value := some (num ((k : Int) + 1)) } _
      (by rw [hz]; exact h1) (by rw [← hs1, State.setEnv_envEntry_ne _ _ _ _ hL1]; exact hE1) hn1
      (by rw [hz]; exact h2) (by rw [← hs1, State.setEnv_envEntry_ne _ _ _ _ hL2]; exact hE2) hn2 (by rw [hz]; exact h)
      (by rw [← hs1, State.setEnv_envEntry_self _ _ _ h]; rfl)
      (by rw [← hs1, State.setEnv_envEntry_self _ _ _ h]; simp [Env.bindingsMap, Std.HashMap.getElem?_modify, hb]) rfl
      (by rw [← hs1, State.setEnv_fuel]; omega)
  obtain ⟨j, hj⟩ : ∃ j, s0.fuel = j + 3 := ⟨s0.fuel - 3, by omega⟩
  simp only [CLGen.fn1, Sem.stmts, M.repeatFrom, hj, M.loop]
  simp [M.bind_eq, M.bind_apply, Sem.exprStmt, Sem.assign, Sem.identRef, Sem.inner, hlex, hstr, hrr, Sem.binary,
    Sem.ident, hrd, Sem.lit, litValue, one_eq, Sem.binaryOp, applyBinaryOp_add_num, hadd, hpe, Sem.ret, hrd1, hgen,
    pure, M.pure, Compl.updateEmpty]

/-! ## The closure's call -/

theorem fn1_fdi (f : ObjId) (d : FuncData) (env : EnvId) (s : State) (tv : Value)
    (hcode : d.code = CLGen.fn1_func) (henv : env < s.envs.size)
    (hE : s.envEntry env = .func ∅ (some d.env) .initialized tv f .undefined) (hf : s.fuel ≠ 0) :
    ∃ ctx s', functionDeclarationInstantiation 999999 f d env #[] s = .ok ctx s' ∧
      ctx.lex = s.envs.size ∧ ctx.strict = false ∧ ctx.isGen = false ∧
      s.envs.size < s'.envs.size ∧ s'.envEntry s.envs.size = .decl ∅ (some env) ∧
      (∀ e, e < s.envs.size → s'.envEntry e = s.envEntry e) ∧
      s'.heap = s.heap ∧ s'.fuel = s.fuel ∧ s'.realms = s.realms := by
  have hr : Array.range 0 = [].toArray := by decide
  have hbody : CLGen.fn1_func.body = .stmts CLGen.fn1_stmts := rfl
  have hparams : CLGen.fn1_func.params = #[] := rfl
  have hstr : CLGen.fn1_func.strict = false := rfl
  have hasync : CLGen.fn1_func.isAsync = false := rfl
  have hgen : CLGen.fn1_func.isGenerator = false := rfl
  have hkind : CLGen.fn1_func.kind = .normal := rfl
  have hfdi : CLGen.fn1_func.info.fdi = { paramNames := #[], hasDuplicates := false, varNames := #[], hasFunctions := false, functionNames := #[], hasLexical := false, lexNames := #[], argumentsNeeded := false, hasAnnexB := false, usesDispose := false } := rfl
  have hphe : CLGen.fn1_func.info.paramsHaveExpressions = false := rfl
  refine ⟨?c, ?t, ?h, ?_⟩
  case h =>
    conv =>
      lhs
      simp only [functionDeclarationInstantiation, hcode, hbody, hparams, hstr, hfdi, hasync, hgen, hkind, hphe]
      simp [hr, newDeclEnv, pure, M.pure, -allocEnv_apply, allocEnv_eq]
  refine ⟨rfl, rfl, rfl, by simp, by simp, fun e he => ?_, by simp [State.pushEnv], by simp, by simp [State.pushEnv]⟩
  simp [State.pushEnv_entry_lt, he]

theorem fn1_body (f : ObjId) (d : FuncData) (env : EnvId) (s : State) (tv : Value) (k : Nat)
    (bL : Std.HashMap JSStr Binding) (o : Option EnvId) (bd : Binding)
    (hcode : d.code = CLGen.fn1_func) (henv : env < s.envs.size)
    (hE : s.envEntry env = .func ∅ (some d.env) .initialized tv f .undefined)
    (hL : d.env < s.envs.size) (hLe : d.env ≠ env) (hEL : s.envEntry d.env = .decl bL o)
    (hb : bL[JSStr.ofString "n"]? = some bd) (hv : bd.value = some (num k)) (hm : bd.mutable = true)
    (hk : k < 2 ^ 26) (hf : 6 ≤ s.fuel) :
    ∃ s', evalFunctionBody evalDepth f d env #[] s = .ok (num ((k : Int) + 1)) s' ∧
      s.envs.size ≤ s'.envs.size ∧ (∀ e, e < s.envs.size → e ≠ d.env → s'.envEntry e = s.envEntry e) ∧
      s'.envEntry d.env = .decl (bL.modify "n" fun bd => { bd with value := some (num ((k : Int) + 1)) }) o ∧
      s'.heap = s.heap ∧ s'.realms = s.realms ∧ s'.fuel = s.fuel := by
  obtain ⟨ctx, s1, hfdi, hlex, hstr, hgen, hlt1, hL1, hfe1, hh1, hfu1, hr1⟩ :=
    fn1_fdi f d env s tv hcode henv hE (by omega)
  have hbody := fn1_spec 999970 ctx s.envs.size env d.env k hlex hstr hgen s1 ∅ ∅ bL .initialized tv f .undefined o bd
    hlt1 hL1 (by simp) (Nat.lt_trans henv hlt1) (by rw [hfe1 env henv]; exact hE) (by simp)
    (Nat.lt_trans hL hlt1) (by rw [hfe1 _ hL]; exact hEL) hb hv hm (Nat.ne_of_lt hL) hLe hk (by omega)
  have hlt1' := hlt1
  refine ⟨setN d.env bL o (num ((k : Int) + 1)) s1, ?_, by simp only [setN, State.setEnv_envs_size]; omega,
    fun e he hee => by simp only [setN]; rw [State.setEnv_envEntry_ne _ _ _ _ (Ne.symm hee), hfe1 e he],
    by simp only [setN]; exact State.setEnv_envEntry_self _ _ _ (Nat.lt_trans hL hlt1),
    by simp [setN, hh1], by simp [setN, hr1], by simp [setN, hfu1]⟩
  have hbd : d.code.body = .stmts CLGen.fn1_stmts := by rw [hcode]; rfl
  have hdisp : d.code.info.fdi.usesDispose = false := by rw [hcode]; rfl
  have hbody' : evalStmts (999970 + 29) ctx CLGen.fn1_stmts s1 =
      .ok (.ret (num ((k : Int) + 1))) (setN d.env bL o (num ((k : Int) + 1)) s1) := by
    rw [← congrFun (CLGen.fn1_eq 999970) ctx]; exact hbody
  simp only [evalDepth, evalFunctionBody, M.bind_eq, M.bind_apply, hfdi, M.bindRes_ok, hbd, hdisp, withDisposeScope]
  simp [hbody', pure, M.pure]

/-- **The [[Call]] of the closure** (`this` undefined), its environment `d.env` holding `n = k`: returns
`k + 1`; afterwards `n = k + 1` there, and nothing else that existed changed. -/
theorem fn1_call (f : ObjId) (d : FuncData) (s : State) (k : Nat) (go : ObjId) (gb : Std.HashMap JSStr Binding)
    (gtv : Value) (bL : Std.HashMap JSStr Binding) (o : Option EnvId) (bd : Binding)
    (hcode : d.code = CLGen.fn1_func) (hcls : d.isClassCtor = false) (hmode : d.thisMode = .global)
    (hge : (s.realms[d.realm]!).globalEnv < s.envs.size)
    (hgE : s.envEntry (s.realms[d.realm]!).globalEnv = .global go gb gtv)
    (hL : d.env < s.envs.size) (hEL : s.envEntry d.env = .decl bL o)
    (hb : bL[JSStr.ofString "n"]? = some bd) (hv : bd.value = some (num k)) (hm : bd.mutable = true)
    (hk : k < 2 ^ 26) (hf : 6 ≤ s.fuel) :
    ∃ s', callECMA f d .undefined #[] s = .ok (num ((k : Int) + 1)) s' ∧ s'.realm = s.realm ∧
      s.envs.size ≤ s'.envs.size ∧ (∀ e, e < s.envs.size → e ≠ d.env → s'.envEntry e = s.envEntry e) ∧
      s'.envEntry d.env = .decl (bL.modify "n" fun bd => { bd with value := some (num ((k : Int) + 1)) }) o ∧
      s'.heap = s.heap ∧ s'.realms = s.realms ∧ s'.fuel = s.fuel := by
  obtain ⟨s', h1, h2, -, t', ⟨q1, q2, q3, q4, q5, q6⟩, hh, hen, hfe, hrs⟩ := Calls.callECMA_undef
    (Q := fun t => s.envs.size ≤ t.envs.size ∧ (∀ e, e < s.envs.size → e ≠ d.env → t.envEntry e = s.envEntry e) ∧
      t.envEntry d.env = .decl (bL.modify "n" fun bd => { bd with value := some (num ((k : Int) + 1)) }) o ∧
      t.heap = s.heap ∧ t.realms = s.realms ∧ t.fuel = s.fuel)
    f d s _ _ go gb gtv hcls hmode (by rw [hcode]; rfl) (by rw [hcode]; rfl) hge hgE
    (fun t hlt hEt hold hheap hfu hrl _ => by
      obtain ⟨t', hb', hz, hfe', hL', hh', hr', hfu'⟩ := fn1_body f d s.envs.size t gtv k bL o bd hcode hlt hEt
        (Nat.lt_trans hL hlt) (Nat.ne_of_lt hL) (by rw [hold _ hL]; exact hEL) hb hv hm hk (by omega)
      exact ⟨t', hb', by omega, fun e he hee => (hfe' e (Nat.lt_trans he hlt) hee).trans (hold e he), hL',
        hh'.trans hheap, hr'.trans hrl, hfu'.trans hfu⟩)
  exact ⟨s', h1, h2, by rw [hen]; exact q1, fun e he hee => by simp only [State.envEntry, hen]; exact q2 e he hee,
    by simp only [State.envEntry, hen]; exact q3, hh.trans q4, hrs.trans q5, hfe.trans q6⟩

/-! ## `make` -/

theorem lexMake : topLevelLexicallyScoped CLGen.make_stmts = #[.binding .let (.ident "n")] := by
  have hv : (VarKind.let == VarKind.var) = false := by decide
  simp [topLevelLexicallyScoped, stmtLexScoped, CLGen.make_stmts, hv]
theorem names_n : (LexScoped.binding .let (.ident "n")).names = #[JSStr.ofString "n"] := by rfl

theorem make_fdi (f : ObjId) (d : FuncData) (env : EnvId) (s : State) (tv : Value)
    (hcode : d.code = CLGen.make_func) (henv : env < s.envs.size)
    (hE : s.envEntry env = .func ∅ (some d.env) .initialized tv f .undefined)
    (hf : s.fuel ≠ 0) :
    ∃ ctx s', functionDeclarationInstantiation 999999 f d env #[] s = .ok ctx s' ∧
      ctx.lex = s.envs.size ∧ ctx.strict = false ∧ ctx.isGen = false ∧ ctx.priv = d.privEnv ∧ ctx.script = d.script ∧
      (s.envs.size < s'.envs.size ∧ s'.envEntry s.envs.size = .decl ((∅ : Std.HashMap JSStr Binding).insert "n" { deletable := false }) (some env)) ∧ s'.fuel = s.fuel ∧ s'.heap = s.heap ∧ s'.realms = s.realms ∧ s'.realm = s.realm ∧
      (∀ e, e < s.envs.size → e ≠ env → s'.envEntry e = s.envEntry e) := by
  have hr : Array.range 0 = [].toArray := by decide
  have hbe : ∀ ctx x v b, b.contains x = true →
      bindElement 999998 ctx (.ident x) none (.init (some env)) (M.pure v)
          (s.setEnv env (.func b (some d.env) .initialized tv f .undefined)) =
        .ok () (s.setEnv env (.func (b.modify x fun bd => { bd with value := some v })
          (some d.env) .initialized tv f .undefined)) := by
    intro ctx x v b hb
    have := bindElement_ident 999998 ctx x env v (s.setEnv env (.func b (some d.env) .initialized tv f .undefined))
      (by omega) (by simpa using henv) (by simp [henv]) (by simpa [henv] using hb) (by simpa using hf)
    simpa [henv] using this
  have hbody : CLGen.make_func.body = .stmts CLGen.make_stmts := rfl
  have hparams : CLGen.make_func.params = #[] := rfl
  have hstr : CLGen.make_func.strict = false := rfl
  have hasync : CLGen.make_func.isAsync = false := rfl
  have hgen : CLGen.make_func.isGenerator = false := rfl
  have hkind : CLGen.make_func.kind = .normal := rfl
  have hfdi : CLGen.make_func.info.fdi = { paramNames := #[], hasDuplicates := false, varNames := #[], hasFunctions := false, functionNames := #[], hasLexical := true, lexNames := #["n"], argumentsNeeded := false, hasAnnexB := false, usesDispose := false } := rfl
  have hk1 : (VarKind.let == VarKind.const) = false := by decide
  have hk2 : (VarKind.let == VarKind.using) = false := by decide
  have hk3 : (VarKind.let == VarKind.awaitUsing) = false := by decide
  have hphe : CLGen.make_func.info.paramsHaveExpressions = false := rfl
  refine ⟨?c, ?t, ?h, ?_⟩
  case h =>
    conv =>
      lhs
      simp only [functionDeclarationInstantiation, hcode, hbody, hparams, hstr, hfdi, hasync, hgen, hkind, hphe]
      simp [hr, hasBinding_declLike, createMutableBinding_declLike, hbe, newDeclEnv, pure,
        M.pure, hE, henv, hf, lexMake, names_n, -allocEnv_apply, allocEnv_eq, LexScoped.isConstant,
        State.pushEnv_entry_at, State.setEnv_envEntry_self, hk1, hk2, hk3]
  have hne : s.envs.size ≠ env := Nat.ne_of_gt henv
  have hne' : env ≠ s.envs.size := Nat.ne_of_lt henv
  refine ⟨rfl, rfl, rfl, rfl, rfl, ⟨by simp, by simp [State.setEnv_envEntry_self]⟩, by simp, by simp [State.setEnv, State.pushEnv], by simp [State.setEnv, State.pushEnv], by simp [State.setEnv, State.pushEnv], ?_⟩
  intro e he hee
  simp [State.setEnv_envEntry_ne _ _ _ _ (show s.envs.size ≠ e by omega), State.pushEnv_entry_lt, he]

/-- `make`'s body after `n` is initialized. -/
abbrev nState (L F : EnvId) (s : State) : State :=
  s.setEnv L (.decl (((∅ : Std.HashMap JSStr Binding).insert "n" { deletable := false }).modify "n"
    fun bd => { bd with value := some (num 0) }) (some F))

/-- **`make`'s body**, `n` declared in its block `L` (outer `F`): initializes `n = 0` and returns a new
function object (the next object) whose environment is `L`. -/
theorem make_spec (nn : Nat) (ctx : Ctx) (L F : EnvId) (fp : ObjId) (hlex : ctx.lex = L) (hstr : ctx.strict = false)
    (hgen : ctx.isGen = false) (hpriv : ctx.priv = #[]) (s0 : State) (hL : L < s0.envs.size)
    (hLE : s0.envEntry L = .decl ((∅ : Std.HashMap JSStr Binding).insert "n" { deletable := false }) (some F))
    (hfp : s0.curRealm.intrinsics["%Function.prototype%"]? = some fp) (hf : 4 ≤ s0.fuel) :
    CLGen.make nn ctx s0 = .ok (.ret (.obj s0.heap.size))
      (Inst.instStateFn CLGen.fn1_func JSStr.empty (nState L F s0) L ctx.script fp) := by
  have hil : (Sem.inner ctx).lex = L := hlex
  have his : (Sem.inner ctx).strict = false := hstr
  have hr : resolveBinding L "n" false s0 = .ok (.env (some L) "n" false) s0 :=
    resolveBinding_here L _ false s0 hL (by rw [hLE]; rfl) (by rw [hLE]; simp [Env.bindingsMap]) (by omega)
  have hin := initializeBinding_declLike L "n" (num 0) s0 hL (by rw [hLE]; rfl)
  rw [hLE] at hin
  have hin' : initializeBinding L "n" (num 0) s0 = .ok () (nState L F s0) := hin
  have hz : (nState L F s0).heap.size = s0.heap.size := by simp
  have hie : instantiateFunctionExpr CLGen.fn1_func (Sem.inner ctx) none (nState L F s0) =
      .ok (.obj s0.heap.size) (Inst.instStateFn CLGen.fn1_func JSStr.empty (nState L F s0) L ctx.script fp) := by
    rw [← hz, ← hlex]
    exact instExpr _ _ (Sem.inner ctx) fp rfl rfl rfl rfl rfl hpriv (by simpa using hfp)
  have hlu : (VarKind.let == VarKind.using) = false := by decide
  have hla : (VarKind.let == VarKind.awaitUsing) = false := by decide
  have hig : (Sem.inner ctx).isGen = false := hgen
  obtain ⟨j, hj⟩ : ∃ j, s0.fuel = j + 3 := ⟨s0.fuel - 3, by omega⟩
  simp only [CLGen.make, Sem.stmts, M.repeatFrom, hj, M.loop]
  simp [M.bind_eq, M.bind_apply, Sem.varDecl, M.forArr_def, M.foldArr_toArray, M.foldList_cons, M.foldList_nil,
    Sem.declLex, hil, his, hr, Sem.lit, litValue, zero_eq, initializeRefBinding, hin', hlu, hla, Sem.ret, Sem.func,
    hie, hig, pure, M.pure, Compl.updateEmpty]

/-- What `make`'s call leaves, relative to the state its body starts in (`L = s.envs.size`). -/
theorem make_body (f : ObjId) (d : FuncData) (env : EnvId) (s : State) (fp : ObjId) (tv : Value)
    (hcode : d.code = CLGen.make_func) (henv : env < s.envs.size)
    (hE : s.envEntry env = .func ∅ (some d.env) .initialized tv f .undefined) (hpriv : d.privEnv = #[])
    (hfp : s.curRealm.intrinsics["%Function.prototype%"]? = some fp) (hf : 6 ≤ s.fuel) :
    ∃ s', evalFunctionBody evalDepth f d env #[] s = .ok (.obj s.heap.size) s' ∧
      s.envs.size < s'.envs.size ∧
      s'.envEntry s.envs.size = .decl (((∅ : Std.HashMap JSStr Binding).insert "n" { deletable := false }).modify "n"
        fun bd => { bd with value := some (num 0) }) (some env) ∧
      (∀ e, e < s.envs.size → e ≠ env → s'.envEntry e = s.envEntry e) ∧
      s'.heap.size = s.heap.size + 2 ∧ (∀ x, x < s.heap.size → s'.objEntry x = s.objEntry x) ∧
      (∃ dC, (s'.objEntry s.heap.size).kind = .func dC ∧ dC.code = CLGen.fn1_func ∧ dC.env = s.envs.size ∧
        dC.realm = s.realm ∧ dC.thisMode = .global ∧ dC.isClassCtor = false) ∧
      s'.realms = s.realms ∧ s'.fuel = s.fuel := by
  obtain ⟨ctx, s1, hfdi, hlex, hstr, hgen, hpr, hsc, ⟨hlt1, hL1⟩, hfu1, hh1, hr1, hrl1, hfe1⟩ :=
    make_fdi f d env s tv hcode henv hE (by omega)
  have hz1 : s1.heap.size = s.heap.size := by rw [hh1]
  have hcr : s1.curRealm = s.curRealm := by simp only [State.curRealm, hr1, hrl1]
  have hbody := make_spec 999955 ctx s.envs.size env fp hlex hstr hgen (hpr.trans hpriv) s1 hlt1 hL1
    (by rw [hcr]; exact hfp) (by omega)
  rw [hz1] at hbody
  obtain ⟨s2, hs2⟩ : ∃ x, Inst.instStateFn CLGen.fn1_func JSStr.empty (nState s.envs.size env s1) s.envs.size ctx.script fp = x :=
    ⟨_, rfl⟩
  rw [hs2] at hbody
  have hN1 : (nState s.envs.size env s1).heap.size = s.heap.size := by simp [hz1]
  have he2 : s2.envs = (nState s.envs.size env s1).envs := by rw [← hs2, Inst.instStateFn_envs]
  have hE2 : ∀ e, s2.envEntry e = (nState s.envs.size env s1).envEntry e := by
    intro e; simp only [State.envEntry, he2]
  refine ⟨s2, ?_, by rw [he2]; simpa using hlt1, by rw [hE2]; exact State.setEnv_envEntry_self _ _ _ hlt1,
    fun e he hee => by rw [hE2, State.setEnv_envEntry_ne _ _ _ _ (Nat.ne_of_gt he), hfe1 e he hee],
    by rw [← hs2, Inst.instStateFn_size, hN1],
    fun x hx => by
      rw [← hs2, Inst.instStateFn_entry_lt _ _ _ _ _ _ _ (by rw [hN1]; exact hx)]; simp [State.objEntry, hh1],
    ⟨Inst.fnData CLGen.fn1_func (nState s.envs.size env s1) s.envs.size ctx.script,
      by rw [← hs2, ← hN1, Inst.instStateFn_func], Inst.fnData_code _ _ _ _, Inst.fnData_env _ _ _ _,
      by rw [Inst.fnData_realm]; simp [hrl1], Inst.fnData_thisMode _ _ _ _, Inst.fnData_isClassCtor _ _ _ _⟩,
    by rw [← hs2, Inst.instStateFn_realms]; simp [hr1], by rw [← hs2, Inst.instStateFn_fuel]; simp [hfu1]⟩
  have hbd : d.code.body = .stmts CLGen.make_stmts := by rw [hcode]; rfl
  have hdisp : d.code.info.fdi.usesDispose = false := by rw [hcode]; rfl
  have hbody' : evalStmts (999955 + 44) ctx CLGen.make_stmts s1 = .ok (.ret (.obj s.heap.size)) s2 := by
    rw [← congrFun (CLGen.make_eq 999955) ctx]; exact hbody
  simp only [evalDepth, evalFunctionBody, M.bind_eq, M.bind_apply, hfdi, M.bindRes_ok, hbd, hdisp, withDisposeScope]
  simp [hbody', pure, M.pure]

/-- `n`'s record after `let n = 0`. -/
abbrev nb : Std.HashMap JSStr Binding :=
  ((∅ : Std.HashMap JSStr Binding).insert "n" { deletable := false }).modify "n" fun bd => { bd with value := some (num 0) }

/-- **The [[Call]] of `make`** (`this` undefined): returns a new function object `fC` (the next object),
whose environment is a new record `L` holding `n = 0`; nothing else that existed changed. -/
theorem make_call (f : ObjId) (d : FuncData) (s : State) (fp go : ObjId) (gb : Std.HashMap JSStr Binding) (gtv : Value)
    (hcode : d.code = CLGen.make_func) (hcls : d.isClassCtor = false) (hmode : d.thisMode = .global)
    (hge : (s.realms[d.realm]!).globalEnv < s.envs.size)
    (hgE : s.envEntry (s.realms[d.realm]!).globalEnv = .global go gb gtv) (hpriv : d.privEnv = #[])
    (hfp : (s.realms[d.realm]!).intrinsics["%Function.prototype%"]? = some fp) (hf : 7 ≤ s.fuel) :
    ∃ s', callECMA f d .undefined #[] s = .ok (.obj s.heap.size) s' ∧ s'.realm = s.realm ∧
      (∃ L F, s.envs.size ≤ L ∧ L < s'.envs.size ∧ s'.envEntry L = .decl nb (some F) ∧
        ∃ dC, (s'.objEntry s.heap.size).kind = .func dC ∧ dC.code = CLGen.fn1_func ∧ dC.env = L ∧
          dC.realm = d.realm ∧ dC.thisMode = .global ∧ dC.isClassCtor = false) ∧
      (∀ e, e < s.envs.size → s'.envEntry e = s.envEntry e) ∧
      s'.heap.size = s.heap.size + 2 ∧ (∀ x, x < s.heap.size → s'.objEntry x = s.objEntry x) ∧
      s'.realms = s.realms ∧ s'.fuel = s.fuel := by
  obtain ⟨s', h1, h2, -, t', ⟨q1, q2, q3, q4, q5, q6⟩, hh, hen, hfe, hrs⟩ := Calls.callECMA_undef
    (Q := fun t => (∃ L F, s.envs.size ≤ L ∧ L < t.envs.size ∧ t.envEntry L = .decl nb (some F) ∧
        ∃ dC, (t.objEntry s.heap.size).kind = .func dC ∧ dC.code = CLGen.fn1_func ∧ dC.env = L ∧
          dC.realm = d.realm ∧ dC.thisMode = .global ∧ dC.isClassCtor = false) ∧
      (∀ e, e < s.envs.size → t.envEntry e = s.envEntry e) ∧ t.heap.size = s.heap.size + 2 ∧
      (∀ x, x < s.heap.size → t.objEntry x = s.objEntry x) ∧ t.realms = s.realms ∧ t.fuel = s.fuel)
    f d s _ _ go gb gtv hcls hmode (by rw [hcode]; rfl) (by rw [hcode]; rfl) hge hgE
    (fun t hlt hEt hold hheap hfu hrl hrlm => by
      have ho : ∀ x, t.objEntry x = s.objEntry x := by intro x; simp [State.objEntry, hheap]
      have hz : t.heap.size = s.heap.size := by rw [hheap]
      obtain ⟨t', hb, hlt', hL', hfe', hh', hoo, ⟨dC, hk1, hk2, hk3, hk4, hk5, hk6⟩, hr', hfu'⟩ :=
        make_body f d s.envs.size t fp gtv hcode hlt hEt hpriv
          (by simp only [State.curRealm, hrl, hrlm]; exact hfp) (by omega)
      rw [hz] at hb hh' hoo hk1
      exact ⟨t', hb, ⟨t.envs.size, s.envs.size, Nat.le_of_lt hlt, hlt', hL', dC, hk1, hk2, hk3, hk4.trans hrlm, hk5, hk6⟩,
        fun e he => (hfe' e (Nat.lt_trans he hlt) (Nat.ne_of_lt he)).trans (hold e he), hh',
        fun x hx => (hoo x hx).trans (ho x), hr'.trans hrl, hfu'.trans hfu⟩)
  obtain ⟨L, F, hL1, hL2, hL3, dC, hk1, hk2, hk3, hk4, hk5, hk6⟩ := q1
  have hoe : ∀ x, s'.objEntry x = t'.objEntry x := by intro x; simp [State.objEntry, hh]
  exact ⟨s', h1, h2, ⟨L, F, hL1, by rw [hen]; exact hL2, by simp only [State.envEntry, hen]; exact hL3,
      dC, by rw [hoe]; exact hk1, hk2, hk3, hk4, hk5, hk6⟩,
    fun e he => by simp only [State.envEntry, hen]; exact q2 e he, by rw [hh]; exact q3,
    fun x hx => (hoe x).trans (q4 x hx), hrs.trans q5, hfe.trans q6⟩

/-! ## The whole script -/

open Script

abbrev letC : Sem.CStmt := Sem.varDecl #[Sem.declLex VarKind.let "c" (some (Sem.call (Sem.identRef "make")
  (Sem.args #[]) false (CalleeDesc.ident "make")))]
abbrev callC : Sem.CStmt := Sem.exprStmt (Sem.call (Sem.identRef "c") (Sem.args #[]) false (CalleeDesc.ident "c"))

theorem script_def (n : Nat) : CLGen.script n = Sem.stmts #[Sem.funDecl CLGen.make_func, letC, callC, callC] := rfl
theorem lexScoped : topLevelLexicallyScoped CLGen.script_stmts = #[.binding .let (.ident "c")] := by
  have hv : (VarKind.let == VarKind.var) = false := by decide
  simp [topLevelLexicallyScoped, stmtLexScoped, CLGen.script_stmts, hv]
theorem simple_make : Inst.SimpleFn CLGen.make_func "make" := ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem ne_cm : (JSStr.ofString "c" = JSStr.ofString "make") = False := by simp; decide

def fs : List (Func × JSStr) := [(CLGen.make_func, "make")]

/-- **The whole program** (examples/closure.js), run as the engine runs a script: evaluates to 2.
Started from a realm whose global object is an ordinary extensible object without `c` or `make`. -/
theorem cl_script (eng : Engine) (s : State) (cs : Conts) (gb : Std.HashMap JSStr Binding) (gtv : Value)
    (fp : ObjId) (hge : s.curRealm.globalEnv < s.envs.size)
    (hE : s.envEntry s.curRealm.globalEnv = .global s.curRealm.globalObj gb gtv)
    (hgbc : gb.contains "c" = false) (hgbm : gb.contains "make" = false)
    (hgs : s.curRealm.globalObj < s.heap.size) (hk : (s.objEntry s.curRealm.globalObj).kind = .ordinary)
    (hx : (s.objEntry s.curRealm.globalObj).extensible = true)
    (hpc : (s.objEntry s.curRealm.globalObj).props.get? (.str "c") = none)
    (hpm : (s.objEntry s.curRealm.globalObj).props.get? (.str "make") = none)
    (hfp : s.curRealm.intrinsics["%Function.prototype%"]? = some fp) (hf : 30 ≤ s.fuel) :
    ∃ s', (runM eng (scriptEvaluation CLGen.program) s cs).1 = .ok (num 2) s' := by
  let ge := s.curRealm.globalEnv
  let g := s.curRealm.globalObj
  let c := scriptCtx s false
  -- the declarations
  obtain ⟨t0, ht0⟩ : ∃ x, (scriptStart s CLGen.program).setEnv ge (.global g (insertLets gb ["c"]) gtv) = x :=
    ⟨_, rfl⟩
  have ho0 : ∀ x, t0.objEntry x = s.objEntry x := by intro x; rw [← ht0, State.setEnv_objEntry]; rfl
  have hz0 : t0.heap.size = s.heap.size := by rw [← ht0, State.setEnv_heap_size]; rfl
  have hge0 : ge < t0.envs.size := by rw [← ht0, State.setEnv_envs_size]; exact hge
  have hgood : GoodG g fp t0 := ⟨by rw [hz0]; exact hgs, by rw [ho0]; exact hk, by rw [ho0]; exact hx,
    by rw [← ht0, State.setEnv_curRealm]; exact hfp⟩
  obtain ⟨⟨-, hku, -, -⟩, heu, hfuu, hru, hrlu, hszu, -, -, -, hnames, hfuns⟩ :=
    instAll_facts ge g s.scripts.size fp fs t0 hgood (by decide)
  obtain ⟨u, hu⟩ : ∃ x, instAll ge g s.scripts.size fp fs t0 = x := ⟨_, rfl⟩
  rw [hu] at hku heu hfuu hru hrlu hszu hnames hfuns
  have hfu0 : t0.fuel = s.fuel := by rw [← ht0, State.setEnv_fuel]; rfl
  have hrl0 : t0.realm = s.realm := by rw [← ht0, State.setEnv_realm]; rfl
  have hr0 : t0.realms = s.realms := by rw [← ht0, State.setEnv_realms]; rfl
  let fM := s.heap.size
  obtain ⟨dM, hfMk, hcM, hrM, hmM, hclsM, hpM⟩ := hfuns 0 (by decide)
  rw [hz0] at hfMk hszu hnames
  simp only [fs, List.length_cons, List.length_nil] at hszu
  simp only [Nat.mul_zero, Nat.add_zero] at hfMk
  have hpMk : (u.objEntry g).props.get? (.str "make") = some (.data (.obj fM) true true false) := hnames 0 (by decide)
  have hdr : dM.realm = s.realm := hrM.trans hrl0
  let gbL := gb.insert "c" { deletable := false }
  have hE1 : u.envEntry ge = .global g gbL gtv := by
    have h1 : u.envEntry ge = t0.envEntry ge := by simp only [State.envEntry, heu]
    rw [h1, ← ht0, State.setEnv_envEntry_self _ _ _ (show ge < (scriptStart s CLGen.program).envs.size from hge)]
    simp [insertLets, gbL]
  have hgeu : ge < u.envs.size := by rw [heu]; exact hge0
  have hgu : g < u.heap.size := by rw [hszu]; exact Nat.lt_of_lt_of_le hgs (Nat.le_add_right _ _)
  have hfMu : fM < u.heap.size := by show s.heap.size < u.heap.size; rw [hszu]; omega
  have hgbM' : gb[JSStr.ofString "make"]? = none := Std.HashMap.getElem?_eq_none (fun hm => by
    rw [Std.HashMap.mem_iff_contains, hgbm] at hm; exact Bool.false_ne_true hm)
  have hLm : gbL.contains "make" = false := by simp [gbL, Std.HashMap.contains_insert, hgbm, ne_cm]
  have hLm' : gbL[JSStr.ofString "make"]? = none := by simp [gbL, Std.HashMap.getElem?_insert, ne_cm, hgbM']
  have hLmm : (JSStr.ofString "make" ∈ gbL) = False := by simp [Std.HashMap.mem_iff_contains, hLm]
  -- `let c = make()`
  obtain ⟨K0, h0, hK0⟩ := Stmts.call_expr_req (Sem.inner c) u ge g fM "make" gbL gtv dM [] (by simp) rfl rfl hgeu hE1
    hLm hLm' hLmm hgu hku hpMk hfMu hfMk (by rw [hfuu, hfu0]; omega)
  obtain ⟨K3, h3, hK3⟩ := Stmts.let_req "c" _ c u ge g gbL gtv _ K0 rfl rfl hgeu hE1 (by simp [gbL])
    (by rw [hfuu, hfu0]; omega) h0 hK0
  obtain ⟨u', hu'⟩ : ∃ x, ({ u with fuel := u.fuel - 1 } : State) = x := ⟨_, rfl⟩
  have hr' : u'.realms = s.realms := by rw [← hu']; exact hru.trans hr0
  have hgeM : (u'.realms[dM.realm]!).globalEnv = ge := by rw [hr', hdr]; rfl
  have hz' : u'.envs = u.envs := by rw [← hu']
  obtain ⟨s3, hcall1, -, ⟨L, F, hL1, hL2, hL3, dC, hCk, hCc, hCe, hCr, hCm, hCcls⟩, he3, hh3, ho3, hr3, hf3⟩ :=
    make_call fM dM u' fp g gbL gtv hcM hclsM hmM (by rw [hgeM, hz']; exact hgeu)
      (by rw [hgeM]; simp only [State.envEntry, hz']; exact hE1) hpM
      (by rw [hr', hdr]; exact hfp) (by rw [← hu']; simp only; rw [hfuu, hfu0]; omega)
  let fC := u.heap.size
  have hAu : u'.heap.size = fC := by rw [← hu']
  rw [hAu] at hcall1 hCk hh3
  have himpl1 : callImpl eng (.obj fM) .undefined #[] u = .ok (.obj fC) s3 := by
    rw [callImpl_func eng fM dM _ _ u hfMu hfMk (by rw [hfuu, hfu0]; omega), hu']; exact hcall1
  -- `c` is initialized
  have hgeu' : ge < u'.envs.size := by rw [hz']; exact hgeu
  have hgeL : ge < L := Nat.lt_of_lt_of_le hgeu' hL1
  have hge3 : ge < s3.envs.size := Nat.lt_trans hgeL hL2
  have hE3 : s3.envEntry ge = .global g gbL gtv := by
    rw [he3 ge hgeu']; simp only [State.envEntry, hz']; exact hE1
  let gbC := gbL.modify "c" fun bd => { bd with value := some (.obj fC) }
  obtain ⟨w, hw⟩ : ∃ w, s3.setEnv ge (.global g gbC gtv) = w := ⟨_, rfl⟩
  have hK3' : K3 (.normal (.obj fC)) s3 = .ok (.normal none) w := by
    rw [← hw]; exact hK3 _ s3 gbL hge3 hE3 (by simp [gbL])
  have hEw : w.envEntry ge = .global g gbC gtv := by rw [← hw]; exact State.setEnv_envEntry_self _ _ _ hge3
  have hgew : ge < w.envs.size := by rw [← hw, State.setEnv_envs_size]; exact hge3
  have how : ∀ x, w.objEntry x = s3.objEntry x := by intro x; rw [← hw, State.setEnv_objEntry]
  have hhw : w.heap.size = fC + 2 := by rw [← hw, State.setEnv_heap_size, hh3]
  have hfCw : fC < w.heap.size := by rw [hhw]; omega
  have hfCkw : (w.objEntry fC).kind = .func dC := by rw [how]; exact hCk
  have hLw : L < w.envs.size := by rw [← hw, State.setEnv_envs_size]; exact hL2
  have hELw : w.envEntry L = .decl nb (some F) := by
    rw [← hw, State.setEnv_envEntry_ne _ _ _ _ (Nat.ne_of_lt hgeL)]; exact hL3
  have hfw : w.fuel = s.fuel - 1 := by
    rw [← hw, State.setEnv_fuel, hf3, ← hu']; simp only; rw [hfuu, hfu0]
  have hrw : w.realms = s.realms := by rw [← hw, State.setEnv_realms, hr3, hr']
  have hCb : gbC[JSStr.ofString "c"]? = some { value := some (.obj fC), deletable := false } := by
    simp [gbC, gbL, Std.HashMap.getElem?_modify]
  have hCmem : (JSStr.ofString "c" ∈ gbC) = True := by simp [gbC, gbL]
  have hdCr : dC.realm = s.realm := hCr.trans hdr
  -- the first `c()`: `n` from 0 to 1
  obtain ⟨K5, h5, hK5⟩ := Stmts.call_decl_req (Sem.inner c) w ge g fC "c" gbC gtv dC _ [] (by simp) rfl rfl hgew hEw
    hCmem hCb rfl hfCw hfCkw (by omega)
  obtain ⟨K6, h6, hK6⟩ := Stmts.exprStmt_req _ c w _ K5 h5 hK5
  obtain ⟨w', hw'⟩ : ∃ x, ({ w with fuel := w.fuel - 1 } : State) = x := ⟨_, rfl⟩
  have hgeC : (w'.realms[dC.realm]!).globalEnv = ge := by
    rw [← hw']; show (w.realms[dC.realm]!).globalEnv = ge; rw [hrw, hdCr]; rfl
  have hzw' : w'.envs = w.envs := by rw [← hw']
  obtain ⟨s4, hc1, -, hz4, he4, hL4, hh4, hr4, hf4⟩ := fn1_call fC dC w' 0 g gbC gtv nb (some F)
    { value := some (num 0), deletable := false } hCc hCcls hCm (by rw [hgeC, hzw']; exact hgew)
    (by rw [hgeC]; simp only [State.envEntry, hzw']; exact hEw) (by rw [hCe, hzw']; exact hLw)
    (by rw [hCe]; simp only [State.envEntry, hzw']; exact hELw) (by simp [nb, Std.HashMap.getElem?_modify]) rfl rfl
    (by decide) (by rw [← hw']; simp only; omega)
  have himpl2 : callImpl eng (.obj fC) .undefined #[] w = .ok (num (((0 : Nat) : Int) + 1)) s4 := by
    rw [callImpl_func eng fC dC _ _ w hfCw hfCkw (by omega), hw']; exact hc1
  -- the state after it
  have hge4 : ge < s4.envs.size := Nat.lt_of_lt_of_le (by rw [hzw']; exact hgew) hz4
  have hE4 : s4.envEntry ge = .global g gbC gtv := by
    rw [he4 ge (by rw [hzw']; exact hgew) (by rw [hCe]; exact Nat.ne_of_lt hgeL)]
    simp only [State.envEntry, hzw']; exact hEw
  have ho4 : ∀ x, s4.objEntry x = w.objEntry x := by intro x; simp only [State.objEntry, hh4]; rw [← hw']
  have hhs4 : s4.heap.size = w.heap.size := by rw [hh4, ← hw']
  have hf4' : s4.fuel = s.fuel - 2 := by rw [hf4, ← hw']; simp only; rw [hfw]; omega
  have hr4' : s4.realms = s.realms := hr4.trans (by rw [← hw']; exact hrw)
  -- the second `c()`: `n` from 1 to 2
  obtain ⟨K7, h7, hK7⟩ := Stmts.call_decl_req (Sem.inner c) s4 ge g fC "c" gbC gtv dC _ [] (by simp) rfl rfl hge4 hE4
    hCmem hCb rfl (by rw [hhs4]; exact hfCw) (by rw [ho4]; exact hfCkw) (by omega)
  obtain ⟨K8, h8, hK8⟩ := Stmts.exprStmt_req _ c s4 _ K7 h7 hK7
  obtain ⟨s4', hs4'⟩ : ∃ x, ({ s4 with fuel := s4.fuel - 1 } : State) = x := ⟨_, rfl⟩
  have hgeC' : (s4'.realms[dC.realm]!).globalEnv = ge := by
    rw [← hs4']; show (s4.realms[dC.realm]!).globalEnv = ge; rw [hr4', hdCr]; rfl
  have hzs4' : s4'.envs = s4.envs := by rw [← hs4']
  have hL4' : L < s4.envs.size := Nat.lt_of_lt_of_le (by rw [hzw']; exact hLw) hz4
  obtain ⟨s5, hc2, -⟩ := fn1_call fC dC s4' 1 g gbC gtv
    (nb.modify "n" fun bd => { bd with value := some (num (((0 : Nat) : Int) + 1)) }) (some F)
    { value := some (num (((0 : Nat) : Int) + 1)), deletable := false } hCc hCcls hCm
    (by rw [hgeC', hzs4']; exact hge4) (by rw [hgeC']; simp only [State.envEntry, hzs4']; exact hE4)
    (by rw [hCe, hzs4']; exact hL4') (by rw [hCe]; simp only [State.envEntry, hzs4']; rw [← hCe]; exact hL4)
    (by simp [nb, Std.HashMap.getElem?_modify]) (by simp) rfl (by decide) (by rw [← hs4']; simp only; omega)
  have himpl3 : callImpl eng (.obj fC) .undefined #[] s4 = .ok (num 2) s5 := by
    rw [callImpl_func eng fC dC _ _ s4 (by rw [hhs4]; exact hfCw) (by rw [ho4]; exact hfCkw) (by omega), hs4']
    exact hc2
  -- the script
  refine ⟨s5, script_value eng s cs CLGen.program fs ["c"] gb gtv fp _ s5 rfl rfl
    (by rw [show CLGen.program.body = CLGen.script_stmts from rfl, lexScoped]; rfl) rfl
    (by intro p hp; simp only [fs, List.mem_cons, List.mem_nil_iff, or_false] at hp; rcases hp with rfl; exact simple_make)
    (by decide) hge hE
    (by intro p hp; simp only [fs, List.mem_cons, List.mem_nil_iff, or_false] at hp; rcases hp with rfl; exact hgbm)
    (by simpa using hgbc) hgs hk hx
    (by intro p hp; simp only [fs, List.mem_cons, List.mem_nil_iff, or_false] at hp; rcases hp with rfl; exact hpm)
    (by simpa using hpc) hfp ?_⟩
  have hu0 : scriptState s CLGen.program fs ["c"] gb gtv fp = u := by rw [← hu, ← ht0]; rfl
  have hscript : evalStmts evalDepth (scriptCtx s false) CLGen.program.body u = CLGen.script 999947 c u := by
    rw [CLGen.script_eq]; rfl
  have h3' : letC c u = .req (.call (.obj fM) .undefined #[]) u K3 := h3
  have h6' : callC c w = .req (.call (.obj fC) .undefined #[]) w K6 := h6
  have h8' : callC c s4 = .req (.call (.obj fC) .undefined #[]) s4 K8 := h8
  rw [hu0, hscript, script_def]
  refine Runs.script_runs eng _ _ _ (Runs.stmts_run eng c _ u _ s5 ?_ (by simp; rw [hfuu, hfu0]; omega))
  show Runs.StmtsRun eng c [Sem.funDecl CLGen.make_func, letC, callC, callC] u none (some (num 2)) s5
  refine .cons _ _ u u s5 none none _ (Runs.runs_funDecl eng _ c u rfl) ?_
  refine .cons _ _ u w s5 none none _ ?_ ?_
  · rw [h3']; exact Runs.runsTo_req1 eng _ _ _ u K3 _ s3 _ w himpl1 hK3'
  refine .cons _ _ w s4 s5 (some (num (((0 : Nat) : Int) + 1))) none _ ?_ ?_
  · rw [h6']; exact Runs.runsTo_req1 eng _ _ _ w K6 _ s4 _ s4 himpl2 (hK6 _ s4)
  refine .cons _ _ s4 s5 s5 (some (num 2)) _ _ ?_ (.nil _ _)
  rw [h8']; exact Runs.runsTo_req1 eng _ _ _ s4 K8 _ s5 _ s5 himpl3 (hK8 _ s5)

end Closure
