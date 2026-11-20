import Proofs.Max
import Proofs.THGen

/-!
# Exceptions: `throw`, and `try`/`catch` (examples/throw.js)

```js
function check(x) { if (x < 0) { throw x; } return x; }
let r = 0;
try { r = check(0 - 7); } catch (e) { r = 0 - e; }
r;
```
`check`'s call returns `x` for every integer `x ≥ 0` and throws `x` for every `x < 0` (below 2^26 in
absolute value); the driver passes the throw to the call's continuation, the `try` statement catches it
and runs the `catch` clause with `e` bound; the script evaluates to 7.
-/

open ES ES.Conv SumProof Script
open Std (HashMap)

namespace Throw

/-- `check`'s parameter bound to `x`. -/
def pb1 (x : F64) : HashMap JSStr Binding :=
  ((∅ : HashMap JSStr Binding).insert "x" { deletable := false }).modify "x" fun bd => { bd with value := some (.num x) }

@[simp] theorem loopRes_err {σ α : Type} (next : σ → State → Res α) (e : Value) (s : State) :
    M.loopRes next (.err e s : Res (σ ⊕ α)) = .err e s := Eq.trans rfl rfl
@[simp] theorem bindRes_err {α β : Type} (f : α → M β) (e : Value) (s : State) :
    M.bindRes f (.err e s : Res α) = .err e s := Eq.trans rfl rfl

@[simp] theorem tryCatchRes_req {α : Type} (h : Value → M α) (r : Req) (s : State) (k : Outcome → State → Res α) :
    M.tryCatchRes h (.req r s k) = .req r s (fun o s' => M.tryCatchRes h (k o s')) := Eq.trans rfl rfl
@[simp] theorem tryCatchRes_err {α : Type} (h : Value → M α) (e : Value) (s : State) :
    M.tryCatchRes h (.err e s : Res α) = h e s := Eq.trans rfl rfl
@[simp] theorem tryCatchRes_ok {α : Type} (h : Value → M α) (a : α) (s : State) :
    M.tryCatchRes h (.ok a s) = .ok a s := Eq.trans rfl rfl

theorem lexThrow : lexicallyScoped #[(Stmt.throw (Expr.ident "x"))] = #[] := by rfl

/-- **`check`'s body, `x ≥ 0`**: returns `x`. -/
theorem check_spec_ok (nn : Nat) (ctx : Ctx) (s : State) (x : Int) (hstr : ctx.strict = false)
    (hgen : ctx.isGen = false) (ha : identValue ctx.lex "x" false s = .ok (num x) s) (hx : x.natAbs < intBound)
    (h0 : 0 ≤ x) (hf : 3 ≤ s.fuel) : THGen.check nn ctx s = .ok (.ret (num x)) s := by
  obtain ⟨j, hj⟩ : ∃ j, s.fuel = j + 3 := ⟨s.fuel - 3, by omega⟩
  have hlt := ltF_int x 0 hx (by simp [intBound])
  have hn : ¬ x < 0 := by omega
  simp only [THGen.check, Sem.stmts, M.repeatFrom, hj, M.loop]
  simp [M.bind_eq, M.bind_apply, Sem.ifS, Sem.inner, Sem.binary, Sem.ident, hstr, ha, Sem.lit, litValue, zero_eq,
    Sem.binaryOp, isLessThan, hlt, hn, toBoolean, ofSmallInt_eq_nan, Sem.ret, hgen, pure, M.pure, Compl.updateEmpty]

/-- **`check`'s body, `x < 0`**: throws `x`. -/
theorem check_spec_err (nn : Nat) (ctx : Ctx) (s : State) (x : Int) (hstr : ctx.strict = false)
    (ha : identValue ctx.lex "x" false s = .ok (num x) s) (hx : x.natAbs < intBound) (h0 : x < 0)
    (hf : 3 ≤ s.fuel) : THGen.check nn ctx s = .err (num x) s := by
  obtain ⟨j, hj⟩ : ∃ j, s.fuel = j + 3 := ⟨s.fuel - 3, by omega⟩
  have hlt := ltF_int x 0 hx (by simp [intBound])
  simp only [THGen.check, Sem.stmts, M.repeatFrom, hj, M.loop]
  simp [M.bind_eq, M.bind_apply, Sem.ifS, Sem.inner, Sem.binary, Sem.ident, hstr, ha, Sem.lit, litValue, zero_eq,
    Sem.binaryOp, isLessThan, hlt, h0, toBoolean, ofSmallInt_eq_nan, Sem.block, lexThrow, Sem.stmts, M.repeatFrom, hj,
    M.loop, Sem.throw, M.throwV, pure, M.pure]

theorem check_fdi (f : ObjId) (d : FuncData) (env : EnvId) (s : State) (x : F64) (tv : Value)
    (hcode : d.code = THGen.check_func) (henv : env < s.envs.size)
    (hE : s.envEntry env = .func ∅ (some d.env) .initialized tv f .undefined)
    (hf : s.fuel ≠ 0) :
    ∃ ctx s', functionDeclarationInstantiation 999999 f d env #[.num x] s = .ok ctx s' ∧
      s'.envEntry env = .func (pb1 x) (some d.env) .initialized tv f .undefined ∧
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
      simp only [THGen.check_func, Func.strict, Func.params, Func.info, Func.body, Func.isAsync]
      simp [hr, hasBinding_declLike, createMutableBinding_declLike, hbe, newDeclEnv, pure,
        M.pure, hE, henv, hf]
  have hne : env ≠ s.envs.size := Nat.ne_of_lt henv
  simp [State.envEntry, State.setEnv, Array.getElem?_push, Array.getElem_push, Array.getElem_modify, henv, hne,
    pb1]
  intro e he hee
  simp [Nat.ne_of_lt he, Array.getElem?_modify, Ne.symm hee]

/-- The parameter, read in `check`'s body. -/
theorem check_read (f : ObjId) (d : FuncData) (env : EnvId) (s : State) (x : Int) (tv : Value)
    (hcode : d.code = THGen.check_func) (henv : env < s.envs.size)
    (hE : s.envEntry env = .func ∅ (some d.env) .initialized tv f .undefined) (hf : 4 ≤ s.fuel) :
    ∃ ctx s', functionDeclarationInstantiation 999999 f d env #[num x] s = .ok ctx s' ∧
      identValue ctx.lex "x" false s' = .ok (num x) s' ∧ ctx.strict = false ∧ ctx.isGen = false ∧
      s'.envs.size = s.envs.size + 1 ∧ s'.fuel = s.fuel ∧ s'.heap = s.heap ∧ s'.realms = s.realms ∧
      (∀ e, e < s.envs.size → e ≠ env → s'.envEntry e = s.envEntry e) := by
  obtain ⟨ctx, s', hfdi, hB, hlex, hL, hvar, hstrict, hgen, hfn, hsize, hfuel, hheap, hrl, hfe⟩ :=
    check_fdi f d env s (ofSmallInt x) tv hcode henv hE (by omega)
  have hl' : ctx.lex < s'.envs.size := by rw [hlex, hsize]; exact Nat.lt_succ_self _
  have he' : env < s'.envs.size := by rw [hsize]; exact Nat.lt_succ_of_lt henv
  refine ⟨ctx, s', hfdi, ?_, hstrict, hgen, hsize, hfuel, hheap, hrl, hfe⟩
  exact identValue_decl_func ctx.lex env "x" false s' (num x) _ { value := some (num x), deletable := false } _ _ _ _ _
    hl' hL he' hB (by simp [pb1, Std.HashMap.getElem?_modify]) rfl (by omega)

/-- The frame of `check`'s call, relative to the caller `s`. -/
def CFrame (s t : State) : Prop :=
  t.heap = s.heap ∧ t.realms = s.realms ∧ s.envs.size ≤ t.envs.size ∧
    (∀ e, e < s.envs.size → t.envEntry e = s.envEntry e) ∧ t.fuel = s.fuel

theorem check_bodyFrame (s t t' : State) (hlt : s.envs.size < t.envs.size)
    (hold : ∀ e, e < s.envs.size → t.envEntry e = s.envEntry e) (hheap : t.heap = s.heap) (hfu : t.fuel = s.fuel)
    (hrl : t.realms = s.realms) (hsz : t'.envs.size = t.envs.size + 1) (hfu' : t'.fuel = t.fuel)
    (hh' : t'.heap = t.heap) (hr' : t'.realms = t.realms)
    (hfe : ∀ e, e < t.envs.size → e ≠ s.envs.size → t'.envEntry e = t.envEntry e) : CFrame s t' :=
  ⟨hh'.trans hheap, hr'.trans hrl, by omega,
    fun e he => (hfe e (Nat.lt_trans he hlt) (Nat.ne_of_lt he)).trans (hold e he), hfu'.trans hfu⟩

theorem cframe_out (s s' t' : State) (hh : s'.heap = t'.heap) (hen : s'.envs = t'.envs) (hfe : s'.fuel = t'.fuel)
    (hrs : s'.realms = t'.realms) (hq : CFrame s t') : CFrame s s' := by
  obtain ⟨q1, q2, q3, q4, q5⟩ := hq
  exact ⟨hh.trans q1, hrs.trans q2, by rw [hen]; exact q3, fun e he => by simp only [State.envEntry, hen]; exact q4 e he,
    hfe.trans q5⟩

/-- **The [[Call]] of `check` with `x ≥ 0`**: returns `x`. -/
theorem check_call_ok (f : ObjId) (d : FuncData) (s : State) (x : Int) (go : ObjId) (gb : HashMap JSStr Binding)
    (gtv : Value) (hcode : d.code = THGen.check_func) (hcls : d.isClassCtor = false) (hmode : d.thisMode = .global)
    (hge : (s.realms[d.realm]!).globalEnv < s.envs.size)
    (hgE : s.envEntry (s.realms[d.realm]!).globalEnv = .global go gb gtv)
    (hx : x.natAbs < intBound) (h0 : 0 ≤ x) (hf : 4 ≤ s.fuel) :
    ∃ s', callECMA f d .undefined #[num x] s = .ok (num x) s' ∧ CFrame s s' := by
  obtain ⟨s', h1, -, -, t', hQ, hh, hen, hfe, hrs⟩ := Calls.callECMA_undef (Q := CFrame s)
    f d s #[num x] (num x) go gb gtv hcls hmode (by rw [hcode]; rfl) (by rw [hcode]; rfl) hge hgE
    (fun t hlt hEt hold hheap hfu hrl _ => by
      obtain ⟨ctx, t', hfdi, hrx, hstr, hgen, hsz, hfu', hh', hr', hfe'⟩ :=
        check_read f d s.envs.size t x gtv hcode hlt hEt (by omega)
      have hbody := check_spec_ok 999973 ctx t' x hstr hgen hrx hx h0 (by omega)
      refine ⟨t', ?_, check_bodyFrame s t t' hlt hold hheap hfu hrl hsz hfu' hh' hr' hfe'⟩
      have hbd : d.code.body = .stmts THGen.check_stmts := by rw [hcode]; rfl
      have hdisp : d.code.info.fdi.usesDispose = false := by rw [hcode]; rfl
      have hbody' : evalStmts (999973 + 26) ctx THGen.check_stmts t' = .ok (.ret (num x)) t' := by
        rw [← congrFun (THGen.check_eq 999973) ctx]; exact hbody
      simp only [evalDepth, evalFunctionBody, M.bind_eq, M.bind_apply, hfdi, M.bindRes_ok, hbd, hdisp, withDisposeScope]
      simp [hbody', pure, M.pure])
  exact ⟨s', h1, cframe_out s s' t' hh hen hfe hrs hQ⟩

/-- **The [[Call]] of `check` with `x < 0`**: throws `x`. -/
theorem check_call_err (f : ObjId) (d : FuncData) (s : State) (x : Int) (go : ObjId) (gb : HashMap JSStr Binding)
    (gtv : Value) (hcode : d.code = THGen.check_func) (hcls : d.isClassCtor = false) (hmode : d.thisMode = .global)
    (hge : (s.realms[d.realm]!).globalEnv < s.envs.size)
    (hgE : s.envEntry (s.realms[d.realm]!).globalEnv = .global go gb gtv)
    (hx : x.natAbs < intBound) (h0 : x < 0) (hf : 4 ≤ s.fuel) :
    ∃ s', callECMA f d .undefined #[num x] s = .err (num x) s' ∧ CFrame s s' := by
  obtain ⟨s', h1, -, -, t', hQ, hh, hen, hfe, hrs⟩ := Calls.callECMA_undef_err (Q := CFrame s)
    f d s #[num x] (num x) go gb gtv hcls hmode (by rw [hcode]; rfl) (by rw [hcode]; rfl) hge hgE
    (fun t hlt hEt hold hheap hfu hrl _ => by
      obtain ⟨ctx, t', hfdi, hrx, hstr, hgen, hsz, hfu', hh', hr', hfe'⟩ :=
        check_read f d s.envs.size t x gtv hcode hlt hEt (by omega)
      have hbody := check_spec_err 999973 ctx t' x hstr hrx hx h0 (by omega)
      refine ⟨t', ?_, check_bodyFrame s t t' hlt hold hheap hfu hrl hsz hfu' hh' hr' hfe'⟩
      have hbd : d.code.body = .stmts THGen.check_stmts := by rw [hcode]; rfl
      have hdisp : d.code.info.fdi.usesDispose = false := by rw [hcode]; rfl
      have hbody' : evalStmts (999973 + 26) ctx THGen.check_stmts t' = .err (num x) t' := by
        rw [← congrFun (THGen.check_eq 999973) ctx]; exact hbody
      simp only [evalDepth, evalFunctionBody, M.bind_eq, M.bind_apply, hfdi, M.bindRes_ok, hbd, hdisp, withDisposeScope]
      simp [hbody', pure, M.pure])
  exact ⟨s', h1, cframe_out s s' t' hh hen hfe hrs hQ⟩

/-! ## Bindings for the `catch` clause -/

theorem bindPattern_ident_init (m : Nat) (ctx : Ctx) (x : JSStr) (e : EnvId) (v : Value) (s : State)
    (hm : 1 ≤ m) (h : e < s.envs.size) (hk : (s.envEntry e).isDeclLike = true)
    (hb : (s.envEntry e).bindingsMap.contains x = true) (hf : s.fuel ≠ 0) :
    bindPattern m ctx (.ident x) v (.init (some e)) s =
      .ok () (s.setEnv e ((s.envEntry e).withBindings (·.modify x fun bd => { bd with value := some v }))) := by
  obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  simp only [bindPattern, M.bind_eq, M.bind_apply, resolveBinding_here e x ctx.strict s h hk hb hf, M.bindRes_ok]
  simp only [putTarget, initializeRefBinding]
  exact initializeBinding_declLike e x v s h hk

/-- Assigning to a `let` binding of the global record. -/
theorem setMutableBinding_global_decl (env : EnvId) (n : JSStr) (v : Value) (strict : Bool) (s : State) (g : ObjId)
    (b : HashMap JSStr Binding) (tv : Value) (bd : Binding) (h : env < s.envs.size)
    (hE : s.envEntry env = .global g b tv) (hb : b[n]? = some bd) (hc : b.contains n = true)
    (hv : bd.value.isSome = true) (hm : bd.mutable = true) :
    setMutableBinding env n v strict s =
      .ok () (s.setEnv env (.global g (b.modify n fun bd => { bd with value := some v }) tv)) := by
  cases hvv : bd.value with
  | none => simp [hvv] at hv
  | some w =>
    have hmem : (n ∈ b) = True := by simp [Std.HashMap.mem_iff_contains, hc]
    have hbn : ∀ hm : n ∈ b, b[n]'hm = bd := fun hm => by
      have := Std.HashMap.getElem?_eq_some_getElem (m := b) hm
      rw [hb] at this; exact (Option.some.inj this).symm
    simp [setMutableBinding, M.bind_eq, M.bind_apply, readEnv_entry _ _ s h, hE, hc, hmem, declSetMutable, hbn, hvv, hm,
      -modifyEnv_apply, modifyEnv_eq_setEnv _ _ _ h, Env.withBindings]

/-- A name of the global record's declarative part, resolved from a declarative record inside it. -/
theorem resolveBinding_decl_global (e1 ge : EnvId) (n : JSStr) (strict : Bool) (s : State) (b1 : HashMap JSStr Binding)
    (g : ObjId) (b : HashMap JSStr Binding) (tv : Value) (h1 : e1 < s.envs.size)
    (hE1 : s.envEntry e1 = .decl b1 (some ge)) (hn1 : b1[n]? = none) (h : ge < s.envs.size)
    (hE : s.envEntry ge = .global g b tv) (hbm : (n ∈ b) = True) (hf : 2 ≤ s.fuel) :
    resolveBinding e1 n strict s = .ok (.env (some ge) n strict) s := by
  obtain ⟨k, hk1⟩ : ∃ k, s.fuel = k + 2 := ⟨s.fuel - 2, by omega⟩
  rw [resolveBinding_loop, hk1, resolveBody_skip _ e1 ge n strict s b1 h1 hE1 hn1]
  simp [M.loop, resolveBody, M.bind_eq, M.bind_apply, hasBinding, readEnv_entry _ _ _ h, hE, hbm, pure, M.pure]

/-! ## The `try` statement -/

abbrev zero0 : F64 := F64.fin false 0 (-1074)
abbrev l7 : F64 := F64.fin false 7881299347898368 (-50)

/-- The `try` statement as the script writes it (`n`: the script's depth, for the catch parameter's binding). -/
abbrev tryT (n : Nat) : Sem.CStmt := (Sem.tryS (Sem.block (lexicallyScoped #[(Stmt.expr (Expr.assign AssignOp.assign (Pattern.ident "r") (Expr.call (Expr.ident "check") #[(Arg.expr (Expr.binary BinOp.sub (Expr.lit (Lit.num (zero0))) (Expr.lit (Lit.num (l7)))))] false false)))]) #[(Sem.exprStmt (Sem.assign (Sem.identRef "r") (Sem.call (Sem.identRef "check") (Sem.args #[(Sem.ArgD.expr (Sem.binary BinOp.sub (Sem.lit (Lit.num (zero0))) (Sem.lit (Lit.num (l7)))))]) false (CalleeDesc.ident "check"))))]) (some { param := (some (Pattern.ident "e")), bind := (fun c v => bindPattern (n + 35) c (Pattern.ident "e") v (.init (some c.lex))), body := (Sem.block (lexicallyScoped #[(Stmt.expr (Expr.assign AssignOp.assign (Pattern.ident "r") (Expr.binary BinOp.sub (Expr.lit (Lit.num (zero0))) (Expr.ident "e"))))]) #[(Sem.exprStmt (Sem.assign (Sem.identRef "r") (Sem.binary BinOp.sub (Sem.lit (Lit.num (zero0))) (Sem.ident "e"))))]) : Sem.CatchD }) none)

theorem lexTry : lexicallyScoped #[(Stmt.expr (Expr.assign AssignOp.assign (Pattern.ident "r") (Expr.call (Expr.ident "check") #[(Arg.expr (Expr.binary BinOp.sub (Expr.lit (Lit.num zero0)) (Expr.lit (Lit.num l7))))] false false)))] = #[] := by rfl
theorem lexCatch : lexicallyScoped #[(Stmt.expr (Expr.assign AssignOp.assign (Pattern.ident "r") (Expr.binary BinOp.sub (Expr.lit (Lit.num zero0)) (Expr.ident "e"))))] = #[] := by rfl
theorem m7 : subF zero0 l7 = ofSmallInt (-7) := by decide
theorem p7 : subF zero0 (ofSmallInt (-7)) = ofSmallInt 7 := by decide

/-- **The `try` statement** asks the driver to call `check` with -7 (`r` a `let` of the global record, `check`
bound on the global object). -/
theorem try_req (n : Nat) (c : Ctx) (u : State) (ge g fo : Nat) (gb : HashMap JSStr Binding) (gtv : Value) (d : FuncData)
    (hlex : c.lex = ge) (hstr : c.strict = false) (hge : ge < u.envs.size)
    (hE : u.envEntry ge = .global g gb gtv) (hrm : (JSStr.ofString "r" ∈ gb) = True)
    (hgc : gb.contains "check" = false) (hgc' : gb[JSStr.ofString "check"]? = none)
    (hgcm : (JSStr.ofString "check" ∈ gb) = False) (hgs : g < u.heap.size) (hk : (u.objEntry g).kind = .ordinary)
    (hp : (u.objEntry g).props.get? (.str "check") = some (.data (.obj fo) true true false))
    (hfs : fo < u.heap.size) (hfk : (u.objEntry fo).kind = .func d) (hf : 4 ≤ u.fuel) :
    ∃ K, tryT n c u = .req (.call (.obj fo) .undefined #[num (-7)]) u K ∧
      ∀ (w1 : State) (gbw : HashMap JSStr Binding) (bdw : Binding), ge < w1.envs.size →
        w1.envEntry ge = .global g gbw gtv → gbw[JSStr.ofString "r"]? = some bdw →
        gbw.contains "r" = true → bdw.value.isSome = true → bdw.mutable = true → 4 ≤ w1.fuel →
        ∃ w3, K (.throw (num (-7))) w1 = .ok (.normal (some (num 7))) w3 ∧
          w3.envEntry ge = .global g (gbw.modify "r" fun bd => { bd with value := some (num 7) }) gtv ∧
          ge < w3.envs.size ∧ w3.fuel = w1.fuel ∧ w3.heap = w1.heap ∧ w3.realms = w1.realms := by
  obtain ⟨j, hj⟩ : ∃ j, u.fuel = j + 3 := ⟨u.fuel - 3, by omega⟩
  have hk' : (u.objEntry g).kind.isPlain = true := by rw [hk]; rfl
  have hrr := Global.resolveBinding_global_decl ge "r" false u g gb gtv hge hE hrm (by omega)
  have hrc := Global.resolveBinding_global_obj ge "check" false u g gb gtv _ hge hE hgc hgcm hgs hk' hp (by omega)
  refine ⟨?K, ?h, ?_⟩
  case h =>
   conv =>
    lhs
    simp [Sem.tryS, Sem.inner, M.attempt, M.tryCatch, M.bind_eq, M.bind_apply, Sem.block, lexTry, Sem.stmts,
    M.repeatFrom, hj, M.loop, Sem.exprStmt, Sem.assign, Sem.identRef, hlex, hstr, hrr, Sem.call, hrc, getRefValue,
    getBindingValue, readEnv_entry _ _ _ hge, hE, hgc', hgcm, Obj'.hasProperty_entry_own _ _ _ hgs hk', hp, getProp,
    Obj'.get_entry_data _ _ _ _ hgs hk', refThisValue, Sem.args, Sem.binary, Sem.lit, litValue, Sem.binaryOp_sub,
    applyBinaryOp_sub_num, m7, isCallable, readObj_entry' _ _ _ hfs, hfk, ES.call, pure, M.pure, M.bindRes_ok,
    M.bindRes_req, M.loopRes_req, Functor.map]
   all_goals first | exact hp | skip
  intro w1 gbw bdw hge1 hE1 hbw hbc hbv hbm hf1
  -- the catch clause's record `E`, with `e = -7`
  let E := w1.envs.size
  obtain ⟨t1, ht1⟩ : ∃ x, w1.pushEnv (.decl ∅ (some ge)) = x := ⟨_, rfl⟩
  have hE1' : E < t1.envs.size := by rw [← ht1]; simp [E]
  have e1E : t1.envEntry E = .decl ∅ (some ge) := by rw [← ht1]; exact State.pushEnv_entry_new _ _
  have hcm := createMutableBinding_declLike E "e" false t1 hE1' (by rw [e1E]; rfl)
  rw [e1E] at hcm
  obtain ⟨t2, ht2⟩ : ∃ x, t1.setEnv E ((Env.decl ∅ (some ge)).withBindings (·.insert "e" { deletable := false })) = x :=
    ⟨_, rfl⟩
  rw [ht2] at hcm
  have hE2 : E < t2.envs.size := by rw [← ht2, State.setEnv_envs_size]; exact hE1'
  have e2E : t2.envEntry E = .decl ((∅ : HashMap JSStr Binding).insert "e" { deletable := false }) (some ge) := by
    rw [← ht2, State.setEnv_envEntry_self _ _ _ hE1']; rfl
  obtain ⟨t3, ht3⟩ : ∃ x, t2.setEnv E ((Env.decl ((∅ : HashMap JSStr Binding).insert "e" { deletable := false }) (some ge)).withBindings
      (·.modify "e" fun bd => { bd with value := some (num (-7)) })) = x := ⟨_, rfl⟩
  have hbp : ∀ ctx', bindPattern (n + 35) ctx' (.ident "e") (num (-7)) (.init (some w1.envs.size)) t2 = .ok () t3 := by
    intro ctx'
    have := bindPattern_ident_init (n + 35) ctx' "e" E (num (-7)) t2 (by omega) hE2
      (by rw [e2E]; rfl) (by rw [e2E]; simp [Env.bindingsMap]) (by rw [← ht2, State.setEnv_fuel, ← ht1]; simp; omega)
    rw [e2E, ht3] at this; exact this
  have hE3 : E < t3.envs.size := by rw [← ht3, State.setEnv_envs_size]; exact hE2
  have e3E : t3.envEntry E = .decl (((∅ : HashMap JSStr Binding).insert "e" { deletable := false }).modify "e"
      fun bd => { bd with value := some (num (-7)) }) (some ge) := by rw [← ht3, State.setEnv_envEntry_self _ _ _ hE2]; rfl
  have hgeE : ge ≠ E := Nat.ne_of_lt hge1
  have hge3 : ge < t3.envs.size := by rw [← ht3, State.setEnv_envs_size, ← ht2, State.setEnv_envs_size, ← ht1]; simp; omega
  have hE3g : t3.envEntry ge = .global g gbw gtv := by
    rw [← ht3, State.setEnv_envEntry_ne _ _ _ _ (Ne.symm hgeE), ← ht2, State.setEnv_envEntry_ne _ _ _ _ (Ne.symm hgeE), ← ht1,
      State.pushEnv_entry_lt _ _ _ hge1]; exact hE1
  have hf3 : t3.fuel = w1.fuel := by rw [← ht3, State.setEnv_fuel, ← ht2, State.setEnv_fuel, ← ht1]; simp
  -- `r = 0 - e`
  have hrm' : (JSStr.ofString "r" ∈ gbw) = True := by simp [Std.HashMap.mem_iff_contains, hbc]
  have hre : (((∅ : HashMap JSStr Binding).insert "e" { deletable := false }).modify "e"
      fun bd => { bd with value := some (num (-7)) })[JSStr.ofString "r"]? = none := by
    simp [Std.HashMap.getElem?_modify, Std.HashMap.getElem?_insert]; decide
  have hrr3 := resolveBinding_decl_global E ge "r" false t3 _ g gbw gtv hE3 e3E hre hge3 hE3g hrm' (by omega)
  have hev3 : identValue E "e" false t3 = .ok (num (-7)) t3 :=
    identValue_skip0 E _ false t3 { value := some (num (-7)), deletable := false } _ hE3 (by rw [e3E]; rfl)
      (by rw [e3E]; simp [Env.bindingsMap, Std.HashMap.getElem?_modify]) rfl (by omega)
  have hset := setMutableBinding_global_decl ge "r" (num 7) false t3 g gbw gtv bdw hge3 hE3g hbw hbc hbv hbm
  obtain ⟨t4, ht4⟩ : ∃ x, t3.setEnv ge (.global g (gbw.modify "r" fun bd => { bd with value := some (num 7) }) gtv) = x :=
    ⟨_, rfl⟩
  rw [ht4] at hset
  have hpe : putRefValue (.env (some ge) "r" false) (num 7) t3 = .ok () t4 := by simp [putRefValue, hset]
  refine ⟨t4, ?_, by rw [← ht4]; exact State.setEnv_envEntry_self _ _ _ hge3, by rw [← ht4, State.setEnv_envs_size]; exact hge3,
    by rw [← ht4, State.setEnv_fuel, hf3], by rw [← ht4, ← ht3, ← ht2, ← ht1]; simp [State.setEnv, State.pushEnv],
    by rw [← ht4, ← ht3, ← ht2, ← ht1]; simp [State.setEnv, State.pushEnv]⟩
  obtain ⟨j3, hj3⟩ : ∃ j, t3.fuel = j + 3 := ⟨t3.fuel - 3, by omega⟩
  have hisn : isSentinel (num (-7)) WK.genReturn = false := rfl
  simp only [E] at hcm hrr3 hev3
  have hbnN : boundNamesN declDepth (Pattern.ident (JSStr.ofString "e")) = #[JSStr.ofString "e"] := rfl
  simp [M.bindRes, M.bind_eq, M.bind_apply, hisn, M.attempt, M.tryCatch, Functor.map, newDeclEnv_eq, ht1, boundNames,
    hbnN, M.foldArr_toArray, M.foldList_cons, M.foldList_nil, hcm, hbp, Sem.block, lexCatch, Sem.stmts, M.repeatFrom, hj3, M.loop, Sem.exprStmt, Sem.inner, Sem.assign,
    Sem.identRef, hstr, hrr3, Sem.binary, Sem.lit, litValue, Sem.ident, hev3, Sem.binaryOp_sub, applyBinaryOp_sub_num,
    p7, hpe, pure, M.pure, Compl.updateEmpty, M.bindRes_ok]

/-! ## The whole script -/

abbrev letR0 : Sem.CStmt := Sem.varDecl #[Sem.declLex VarKind.let "r" (some (Sem.lit (Lit.num zero0)))]
abbrev lastR : Sem.CStmt := Sem.exprStmt (Sem.ident "r")

theorem script_def (n : Nat) : THGen.script n = Sem.stmts #[Sem.funDecl THGen.check_func, letR0, tryT n, lastR] := rfl
theorem lexScoped : topLevelLexicallyScoped THGen.script_stmts = #[.binding .let (.ident "r")] := by
  have hv : (VarKind.let == VarKind.var) = false := by decide
  simp [topLevelLexicallyScoped, stmtLexScoped, THGen.script_stmts, hv]
theorem simple_check : Inst.SimpleFn THGen.check_func "check" := ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem ne_rc : (JSStr.ofString "r" = JSStr.ofString "check") = False := by simp; decide

def fs : List (Func × JSStr) := [(THGen.check_func, "check")]

/-- **The whole program** (examples/throw.js), run as the engine runs a script: `check(0 - 7)` throws -7, the
`catch` clause sets `r = 0 - e`, and the script evaluates to 7. Started from a realm whose global object is an
ordinary extensible object without `r` or `check`. -/
theorem th_script (eng : Engine) (s : State) (cs : Conts) (gb : HashMap JSStr Binding) (gtv : Value)
    (fp : ObjId) (hge : s.curRealm.globalEnv < s.envs.size)
    (hE : s.envEntry s.curRealm.globalEnv = .global s.curRealm.globalObj gb gtv)
    (hgbr : gb.contains "r" = false) (hgbc : gb.contains "check" = false)
    (hgs : s.curRealm.globalObj < s.heap.size) (hk : (s.objEntry s.curRealm.globalObj).kind = .ordinary)
    (hx : (s.objEntry s.curRealm.globalObj).extensible = true)
    (hpr : (s.objEntry s.curRealm.globalObj).props.get? (.str "r") = none)
    (hpc : (s.objEntry s.curRealm.globalObj).props.get? (.str "check") = none)
    (hfp : s.curRealm.intrinsics["%Function.prototype%"]? = some fp) (hf : 20 ≤ s.fuel) :
    ∃ s', (runM eng (scriptEvaluation THGen.program) s cs).1 = .ok (num 7) s' := by
  let ge := s.curRealm.globalEnv
  let g := s.curRealm.globalObj
  let c := scriptCtx s false
  -- the declarations
  obtain ⟨t0, ht0⟩ : ∃ x, (scriptStart s THGen.program).setEnv ge (.global g (insertLets gb ["r"]) gtv) = x :=
    ⟨_, rfl⟩
  have ho0 : ∀ x, t0.objEntry x = s.objEntry x := by intro x; rw [← ht0, State.setEnv_objEntry]; rfl
  have hz0 : t0.heap.size = s.heap.size := by rw [← ht0, State.setEnv_heap_size]; rfl
  have hge0 : ge < t0.envs.size := by rw [← ht0, State.setEnv_envs_size]; exact hge
  have hgood : GoodG g fp t0 := ⟨by rw [hz0]; exact hgs, by rw [ho0]; exact hk, by rw [ho0]; exact hx,
    by rw [← ht0, State.setEnv_curRealm]; exact hfp⟩
  obtain ⟨⟨-, hku, -, -⟩, heu, hfuu, hru, -, hszu, -, -, -, hnames, hfuns⟩ :=
    instAll_facts ge g s.scripts.size fp fs t0 hgood (by decide)
  obtain ⟨u, hu⟩ : ∃ x, instAll ge g s.scripts.size fp fs t0 = x := ⟨_, rfl⟩
  rw [hu] at hku heu hfuu hru hszu hnames hfuns
  have hfu0 : t0.fuel = s.fuel := by rw [← ht0, State.setEnv_fuel]; rfl
  have hrl0 : t0.realm = s.realm := by rw [← ht0, State.setEnv_realm]; rfl
  have hr0 : t0.realms = s.realms := by rw [← ht0, State.setEnv_realms]; rfl
  let fC := s.heap.size
  obtain ⟨dC, hfCk, hcC, hrC, hmC, hclsC, -⟩ := hfuns 0 (by decide)
  rw [hz0] at hfCk hszu hnames
  simp only [fs, List.length_cons, List.length_nil] at hszu
  simp only [Nat.mul_zero, Nat.add_zero] at hfCk
  have hpC : (u.objEntry g).props.get? (.str "check") = some (.data (.obj fC) true true false) := hnames 0 (by decide)
  have hdr : dC.realm = s.realm := hrC.trans hrl0
  let gbL := gb.insert "r" { deletable := false }
  have hE1 : u.envEntry ge = .global g gbL gtv := by
    have h1 : u.envEntry ge = t0.envEntry ge := by simp only [State.envEntry, heu]
    rw [h1, ← ht0, State.setEnv_envEntry_self _ _ _ (show ge < (scriptStart s THGen.program).envs.size from hge)]
    simp [insertLets, gbL]
  have hgeu : ge < u.envs.size := by rw [heu]; exact hge0
  have hgu : g < u.heap.size := by rw [hszu]; exact Nat.lt_of_lt_of_le hgs (Nat.le_add_right _ _)
  have hfCu : fC < u.heap.size := by show s.heap.size < u.heap.size; rw [hszu]; omega
  -- `let r = 0`
  let gb0 := gbL.modify "r" fun bd => { bd with value := some (num 0) }
  obtain ⟨u2, hu2⟩ : ∃ x, u.setEnv ge (.global g gb0 gtv) = x := ⟨_, rfl⟩
  have hlet : letR0 c u = .ok (.normal none) u2 := by
    have hr := Global.resolveBinding_global_decl ge "r" false u g gbL gtv hgeu hE1 (by simp [gbL])
      (by rw [hfuu, hfu0]; omega)
    have hin := Global.initializeBinding_global ge "r" (num 0) u g gbL gtv hgeu hE1 (by simp [gbL])
    rw [show u.setEnv ge _ = u2 from hu2] at hin
    have hlu : (VarKind.let == VarKind.using) = false := by decide
    have hla : (VarKind.let == VarKind.awaitUsing) = false := by decide
    simp [Sem.varDecl, M.forArr_def, M.foldArr_toArray, M.foldList_cons, M.foldList_nil, Sem.declLex, Sem.inner,
      M.bind_eq, M.bind_apply, hr, Sem.lit, litValue, zero_eq, initializeRefBinding, hin, hlu, hla, pure, M.pure, c,
      scriptCtx, AddScript.gdiCtx, ge]
  have ho2 : ∀ x, u2.objEntry x = u.objEntry x := by intro x; rw [← hu2, State.setEnv_objEntry]
  have hz2 : u2.heap.size = u.heap.size := by rw [← hu2, State.setEnv_heap_size]
  have hge2 : ge < u2.envs.size := by rw [← hu2, State.setEnv_envs_size]; exact hgeu
  have hE2 : u2.envEntry ge = .global g gb0 gtv := by rw [← hu2]; exact State.setEnv_envEntry_self _ _ _ hgeu
  have hf2 : u2.fuel = s.fuel := by rw [← hu2, State.setEnv_fuel, hfuu, hfu0]
  have hr2 : u2.realms = s.realms := by rw [← hu2, State.setEnv_realms, hru, hr0]
  have hgbc' : gb[JSStr.ofString "check"]? = none := Std.HashMap.getElem?_eq_none (fun hm => by
    rw [Std.HashMap.mem_iff_contains, hgbc] at hm; exact Bool.false_ne_true hm)
  have h0c : gb0.contains "check" = false := by simp [gb0, gbL, Std.HashMap.contains_insert, hgbc, ne_rc]
  have h0c' : gb0[JSStr.ofString "check"]? = none := by
    simp [gb0, gbL, Std.HashMap.getElem?_modify, Std.HashMap.getElem?_insert, ne_rc, hgbc']
  have h0cm : (JSStr.ofString "check" ∈ gb0) = False := by simp [Std.HashMap.mem_iff_contains, h0c]
  have h0r : gb0[JSStr.ofString "r"]? = some { value := some (num 0), deletable := false } := by
    simp [gb0, gbL, Std.HashMap.getElem?_modify]
  -- the `try` statement: `check(0 - 7)` throws -7
  obtain ⟨K, hreq, hK⟩ := try_req 999962 c u2 ge g fC gb0 gtv dC rfl rfl hge2 hE2 (by simp [gb0, gbL]) h0c h0c' h0cm
    (by rw [hz2]; exact hgu) (by rw [ho2]; exact hku) (by rw [ho2]; exact hpC) (by rw [hz2]; exact hfCu)
    (by rw [ho2]; exact hfCk) (by omega)
  obtain ⟨u2', hu2'⟩ : ∃ x, ({ u2 with fuel := u2.fuel - 1 } : State) = x := ⟨_, rfl⟩
  have hgeC : (u2'.realms[dC.realm]!).globalEnv = ge := by rw [← hu2']; show (u2.realms[dC.realm]!).globalEnv = ge; rw [hr2, hdr]; rfl
  have hz2' : u2'.envs = u2.envs := by rw [← hu2']
  obtain ⟨s3, hcall, q1, q2, q3, q4, q5⟩ := check_call_err fC dC u2' (-7) g gb0 gtv hcC hclsC hmC
    (by rw [hgeC, hz2']; exact hge2) (by rw [hgeC]; simp only [State.envEntry, hz2']; exact hE2) (by decide) (by decide)
    (by rw [← hu2']; simp only; omega)
  have himpl : callImpl eng (.obj fC) .undefined #[num (-7)] u2 = .err (num (-7)) s3 := by
    rw [callImpl_func eng fC dC _ _ u2 (by rw [hz2]; exact hfCu) (by rw [ho2]; exact hfCk) (by omega), hu2']; exact hcall
  have hge3 : ge < s3.envs.size := Nat.lt_of_lt_of_le (by rw [hz2']; exact hge2) q3
  have hE3 : s3.envEntry ge = .global g gb0 gtv := by rw [q4 ge (by rw [hz2']; exact hge2)]; simp only [State.envEntry, hz2']; exact hE2
  have hf3 : s3.fuel = s.fuel - 1 := by rw [q5, ← hu2']; simp only; rw [hf2]
  obtain ⟨w3, hK3, hEw3, hgew3, hfw3, -, -⟩ := hK s3 gb0 _ hge3 hE3 h0r (by simp [gb0, gbL]) rfl rfl (by omega)
  -- `r;`
  have hrv := Global.identValue_global_decl ge "r" false w3 g _ gtv { value := some (num 7), deletable := false } (num 7)
    hgew3 hEw3 (by simp [gb0, gbL, Std.HashMap.getElem?_modify]) (by simp [gb0, gbL]) rfl (by omega)
  have hlast : lastR c w3 = .ok (.normal (some (num 7))) w3 := by
    simp [Sem.exprStmt, Sem.ident, Sem.inner, c, scriptCtx, AddScript.gdiCtx, ge, hrv, pure, M.pure, M.bind_eq, M.bind_apply]
  -- the script
  refine ⟨w3, script_value eng s cs THGen.program fs ["r"] gb gtv fp _ w3 rfl rfl
    (by rw [show THGen.program.body = THGen.script_stmts from rfl, lexScoped]; rfl) rfl
    (by intro p hp; simp only [fs, List.mem_cons, List.mem_nil_iff, or_false] at hp; rcases hp with rfl; exact simple_check)
    (by decide) hge hE
    (by intro p hp; simp only [fs, List.mem_cons, List.mem_nil_iff, or_false] at hp; rcases hp with rfl; exact hgbc)
    (by simpa using hgbr) hgs hk hx
    (by intro p hp; simp only [fs, List.mem_cons, List.mem_nil_iff, or_false] at hp; rcases hp with rfl; exact hpc)
    (by simpa using hpr) hfp ?_⟩
  have hu0 : scriptState s THGen.program fs ["r"] gb gtv fp = u := by rw [← hu, ← ht0]; rfl
  have hscript : evalStmts evalDepth (scriptCtx s false) THGen.program.body u = THGen.script 999962 c u := by
    rw [THGen.script_eq]; rfl
  rw [hu0, hscript, script_def]
  refine Runs.script_runs eng _ _ _ (Runs.stmts_run eng c _ u _ w3 ?_ (by simp; rw [hfuu, hfu0]; omega))
  show Runs.StmtsRun eng c [Sem.funDecl THGen.check_func, letR0, tryT 999962, lastR] u none (some (num 7)) w3
  refine .cons _ _ u u w3 none none _ (Runs.runs_funDecl eng _ c u rfl) ?_
  refine .cons _ _ u u2 w3 none none _ (by rw [hlet]; exact Runs.runsTo_ok eng _ _) ?_
  refine .cons _ _ u2 w3 w3 (some (num 7)) none _ ?_ ?_
  · rw [hreq]; exact Runs.runsTo_call_err eng _ _ _ u2 K _ s3 _ w3 himpl (by rw [hK3]; exact Runs.runsTo_ok eng _ _)
  refine .cons _ _ w3 w3 w3 (some (num 7)) _ _ (by rw [hlast]; exact Runs.runsTo_ok eng _ _) (.nil _ _)

end Throw
