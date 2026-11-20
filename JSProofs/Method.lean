import JSProofs.Runs
import JSProofs.Stmts
import JSProofs.MEGen

/-!
# Objects with methods: `o.inc()` with `this` (examples/method.js)

```js
function inc() { this.n = this.n + 1; return this.n; }
let o = { n: 0, inc: inc };
o.inc();
o.inc();
```
evaluates to 2: the object literal creates `o` with data properties `n` and `inc`; `o.inc()` calls the
function with `this = o`, whose body reads and writes `this.n`.
-/

open ES ES.Conv SumProof

namespace Method

/-! ## `this` and own properties -/

/-- `this` in a block of a function's body: through the declarative record `L` to the function record
`F`, whose this value is bound. -/
theorem resolveThis_decl (L F : EnvId) (s : State) (b : Std.HashMap JSStr Binding) (bF : Std.HashMap JSStr Binding)
    (o : Option EnvId) (tv : Value) (fo : ObjId) (nt : Value) (hL : L < s.envs.size) (hF : F < s.envs.size)
    (hLE : s.envEntry L = .decl b (some F)) (hFE : s.envEntry F = .func bF o .initialized tv fo nt)
    (hf : 2 ≤ s.fuel) : resolveThisBinding L s = .ok tv s := by
  obtain ⟨k, hk⟩ : ∃ k, s.fuel = k + 2 := ⟨s.fuel - 2, by omega⟩
  have hni : (ThisStatus.initialized == ThisStatus.lexical) = false := by decide
  have hnu : (ThisStatus.initialized == ThisStatus.uninitialized) = false := by decide
  simp [resolveThisBinding, getThisEnvironment, M.repeatFrom, hk, M.loop, M.bind_eq, M.bind_apply,
    readEnv_entry _ _ _ hL, readEnv_entry _ _ _ hF, hLE, hFE, Env.outer, hni, hnu, pure, M.pure]

/-- `o.key = v` for an own writable data property of an ordinary object: the property's value is replaced. -/
theorem putRefValue_own (o : ObjId) (key : JSStr) (strict : Bool) (v v0 : Value) (e c : Bool) (s : State)
    (h : o < s.heap.size) (hk : (s.objEntry o).kind.isPlain = true)
    (hp : (s.objEntry o).props.get? (.str key) = some (.data v0 true e c)) :
    putRefValue (.prop (.obj o) (.str key) strict none) v s =
      .ok () (s.setProp o (.str key) (.data v true e c)) := by
  have hset := Obj'.set_entry_own o (.str key) v s h hk (by simp [hp, isOwnWritableData])
  simp [putRefValue, Value.isNullish, toPropertyKey, M.bind_eq, M.bind_apply, hset,
    ordinaryDefineOwnProperty_value _ _ _ _ _ _ _ h hp, pure, M.pure]

/-! ## `inc`'s body -/

/-- **`inc`'s body**, run with `this` an ordinary object `O` whose `n` is `k`: returns `k + 1`, and the only
change is `O.n = k + 1`. -/
theorem inc_spec (nn : Nat) (ctx : Ctx) (L F O : Nat) (k : Nat) (hlex : ctx.lex = L) (hstr : ctx.strict = false)
    (hgen : ctx.isGen = false) (s0 : State) (b bF : Std.HashMap JSStr Binding) (o : Option EnvId) (fo : ObjId)
    (nt : Value) (hL : L < s0.envs.size) (hF : F < s0.envs.size) (hLE : s0.envEntry L = .decl b (some F))
    (hFE : s0.envEntry F = .func bF o .initialized (.obj O) fo nt)
    (hO : O < s0.heap.size) (hOk : (s0.objEntry O).kind = .ordinary)
    (hOn : (s0.objEntry O).props.get? (.str "n") = some (.data (num k) true true true)) (hk : k < 2 ^ 26)
    (hf : 4 ≤ s0.fuel) :
    MEGen.inc nn ctx s0 = .ok (.ret (num ((k : Int) + 1))) (s0.setProp O (.str "n") (.data (num ((k : Int) + 1)) true true true)) := by
  have hkp : (s0.objEntry O).kind.isPlain = true := by rw [hOk]; rfl
  have hkb : (k : Int).natAbs < intBound := by simp only [intBound]; omega
  have hk1b : ((k : Int) + 1).natAbs < intBound := by simp only [intBound]; omega
  have hadd : addF (ofSmallInt k) (ofSmallInt 1) = ofSmallInt ((k : Int) + 1) := by
    rw [addF_int _ _ hkb (by simp [intBound]) (by simpa using hk1b)]
  have hth := resolveThis_decl L F s0 b bF o (.obj O) fo nt hL hF hLE hFE (by omega)
  have hget := getRefValue_prop O "n" false s0
  rw [Obj'.get_entry_data O _ _ s0 hO hkp (by simp [hOn, isOwnData])] at hget
  have hput := putRefValue_own O "n" false (num ((k : Int) + 1)) (num k) true true s0 hO hkp hOn
  obtain ⟨s1, hs1⟩ : ∃ s1, s0.setProp O (.str "n") (.data (num ((k : Int) + 1)) true true true) = s1 := ⟨_, rfl⟩
  rw [hs1] at hput ⊢
  have hO1 : O < s1.heap.size := by rw [← hs1]; simpa using hO
  have hth1 : resolveThisBinding L s1 = .ok (.obj O) s1 := by
    refine resolveThis_decl L F s1 b bF o (.obj O) fo nt (by rw [← hs1]; simpa using hL) (by rw [← hs1]; simpa using hF)
      ?_ ?_ (by rw [← hs1, State.setProp_fuel]; omega)
    · simp only [State.envEntry, ← hs1, State.setProp_envs]; exact hLE
    · simp only [State.envEntry, ← hs1, State.setProp_envs]; exact hFE
  have hget1 := getRefValue_prop O "n" false s1
  rw [Obj'.get_entry_data O _ _ s1 hO1 (by rw [← hs1, State.setProp_entry_self _ _ _ _ hO]; simp [hkp])
    (by rw [← hs1, State.setProp_entry_self _ _ _ _ hO]; simp [isOwnData])] at hget1
  obtain ⟨j, hj⟩ : ∃ j, s0.fuel = j + 3 := ⟨s0.fuel - 3, by omega⟩
  simp only [MEGen.inc, Sem.stmts, M.repeatFrom, hj, M.loop]
  simp [M.bind_eq, M.bind_apply, Sem.exprStmt, Sem.assign, Sem.memberRef, Sem.inner, Sem.this, hlex, hstr, hth,
    Value.isNullish, Sem.binary, Sem.getValue, hget, ownDataValue, Sem.lit, litValue, one_eq, Sem.binaryOp,
    applyBinaryOp_add_num, hadd, hput, Sem.ret, hth1, hget1, hgen, pure, M.pure, Compl.updateEmpty, hOn]
  rw [← hs1, State.setProp_entry_self _ _ _ _ hO]; simp

/-! ## The call of `inc` -/

theorem inc_fdi (f : ObjId) (d : FuncData) (env : EnvId) (s : State) (tv : Value)
    (hcode : d.code = MEGen.inc_func) (henv : env < s.envs.size)
    (hE : s.envEntry env = .func ∅ (some d.env) .initialized tv f .undefined) (hf : s.fuel ≠ 0) :
    ∃ ctx s', functionDeclarationInstantiation 999999 f d env #[] s = .ok ctx s' ∧
      ctx.lex = s.envs.size ∧ ctx.strict = false ∧ ctx.isGen = false ∧
      s.envs.size < s'.envs.size ∧ s'.envEntry s.envs.size = .decl ∅ (some env) ∧
      (∀ e, e < s.envs.size → s'.envEntry e = s.envEntry e) ∧
      s'.heap = s.heap ∧ s'.fuel = s.fuel ∧ s'.realms = s.realms := by
  have hr : Array.range 0 = [].toArray := by decide
  have hbody : MEGen.inc_func.body = .stmts MEGen.inc_stmts := rfl
  have hparams : MEGen.inc_func.params = #[] := rfl
  have hstr : MEGen.inc_func.strict = false := rfl
  have hasync : MEGen.inc_func.isAsync = false := rfl
  have hgen : MEGen.inc_func.isGenerator = false := rfl
  have hkind : MEGen.inc_func.kind = .normal := rfl
  have hfdi : MEGen.inc_func.info.fdi = { paramNames := #[], hasDuplicates := false, varNames := #[], hasFunctions := false, functionNames := #[], hasLexical := false, lexNames := #[], argumentsNeeded := false, hasAnnexB := false, usesDispose := false } := rfl
  have hphe : MEGen.inc_func.info.paramsHaveExpressions = false := rfl
  refine ⟨?c, ?t, ?h, ?_⟩
  case h =>
    conv =>
      lhs
      simp only [functionDeclarationInstantiation, hcode, hbody, hparams, hstr, hfdi, hasync, hgen, hkind, hphe]
      simp [hr, newDeclEnv, pure, M.pure, -allocEnv_apply, allocEnv_eq]
  refine ⟨rfl, rfl, rfl, by simp, by simp, fun e he => ?_, by simp [State.pushEnv], by simp, by simp [State.pushEnv]⟩
  simp [State.pushEnv_entry_lt, he]

/-- The object `O` after `this.n = k + 1`. -/
abbrev bump (O : ObjId) (k : Nat) (s : State) : State := s.setProp O (.str "n") (.data (num ((k : Int) + 1)) true true true)

theorem inc_body (f : ObjId) (d : FuncData) (env : EnvId) (s : State) (O : ObjId) (k : Nat)
    (hcode : d.code = MEGen.inc_func) (henv : env < s.envs.size)
    (hE : s.envEntry env = .func ∅ (some d.env) .initialized (.obj O) f .undefined)
    (hO : O < s.heap.size) (hOk : (s.objEntry O).kind = .ordinary)
    (hOn : (s.objEntry O).props.get? (.str "n") = some (.data (num k) true true true)) (hk : k < 2 ^ 26)
    (hf : 6 ≤ s.fuel) :
    ∃ s', evalFunctionBody evalDepth f d env #[] s = .ok (num ((k : Int) + 1)) s' ∧
      s.envs.size ≤ s'.envs.size ∧ (∀ e, e < s.envs.size → s'.envEntry e = s.envEntry e) ∧
      s'.heap.size = s.heap.size ∧ (∀ x, s'.objEntry x = (bump O k s).objEntry x) ∧
      s'.realms = s.realms ∧ s'.fuel = s.fuel := by
  obtain ⟨ctx, s1, hfdi, hlex, hstr, hgen, hlt1, hL1, hfe1, hh1, hfu1, hr1⟩ :=
    inc_fdi f d env s (.obj O) hcode henv hE (by omega)
  have ho1 : ∀ x, s1.objEntry x = s.objEntry x := by intro x; simp [State.objEntry, hh1]
  have hbody := inc_spec 999970 ctx s.envs.size env O k hlex hstr hgen s1 ∅ ∅ (some d.env) f .undefined hlt1
    (Nat.lt_trans henv hlt1) hL1 (by rw [hfe1 env henv]; exact hE) (by rw [hh1]; exact hO) (by rw [ho1]; exact hOk)
    (by rw [ho1]; exact hOn) hk (by omega)
  refine ⟨bump O k s1, ?_, by simp only [bump, State.setProp_envs]; omega,
    fun e he => by simp only [State.envEntry, bump, State.setProp_envs]; exact hfe1 e he,
    by simp [bump, State.setProp, hh1], fun x => by simp [bump, State.setProp, State.objEntry, hh1],
    by simp [bump, hr1], by simp [bump, hfu1]⟩
  have hbd : d.code.body = .stmts MEGen.inc_stmts := by rw [hcode]; rfl
  have hdisp : d.code.info.fdi.usesDispose = false := by rw [hcode]; rfl
  have hbody' : evalStmts (999970 + 29) ctx MEGen.inc_stmts s1 = .ok (.ret (num ((k : Int) + 1))) (bump O k s1) := by
    rw [← congrFun (MEGen.inc_eq 999970) ctx]; exact hbody
  simp only [evalDepth, evalFunctionBody, M.bind_eq, M.bind_apply, hfdi, M.bindRes_ok, hbd, hdisp, withDisposeScope]
  simp [hbody', pure, M.pure]

/-- **The [[Call]] of `inc` with `this = O`**: returns `k + 1`; afterwards `O.n = k + 1`, and nothing else
that existed changed. -/
theorem inc_call (f : ObjId) (d : FuncData) (s : State) (O : ObjId) (k : Nat)
    (hcode : d.code = MEGen.inc_func) (hcls : d.isClassCtor = false) (hmode : d.thisMode = .global)
    (hO : O < s.heap.size) (hOk : (s.objEntry O).kind = .ordinary)
    (hOn : (s.objEntry O).props.get? (.str "n") = some (.data (num k) true true true)) (hk : k < 2 ^ 26)
    (hf : 6 ≤ s.fuel) :
    ∃ s', callECMA f d (.obj O) #[] s = .ok (num ((k : Int) + 1)) s' ∧ s'.realm = s.realm ∧
      s.envs.size ≤ s'.envs.size ∧ (∀ e, e < s.envs.size → s'.envEntry e = s.envEntry e) ∧
      s'.heap.size = s.heap.size ∧ (∀ x, s'.objEntry x = (bump O k s).objEntry x) ∧
      s'.realms = s.realms ∧ s'.fuel = s.fuel := by
  obtain ⟨s', h1, h2, -, t', ⟨q1, q2, q3, q4, q5, q6⟩, hh, hen, hfe, hrs⟩ := Calls.callECMA_obj
    (Q := fun t => s.envs.size ≤ t.envs.size ∧ (∀ e, e < s.envs.size → t.envEntry e = s.envEntry e) ∧
      t.heap.size = s.heap.size ∧ (∀ x, t.objEntry x = (bump O k s).objEntry x) ∧ t.realms = s.realms ∧
      t.fuel = s.fuel)
    f d s _ _ O hcls hmode (by rw [hcode]; rfl) (by rw [hcode]; rfl)
    (fun t hlt hEt hold hheap hfu hrl _ => by
      have ho : ∀ x, t.objEntry x = s.objEntry x := by intro x; simp [State.objEntry, hheap]
      obtain ⟨t', hb, hz, hfe, hhs, hoo, hrr, hfu'⟩ := inc_body f d s.envs.size t O k hcode hlt hEt
        (by rw [hheap]; exact hO) (by rw [ho]; exact hOk) (by rw [ho]; exact hOn) hk (by omega)
      refine ⟨t', hb, by omega, fun e he => (hfe e (Nat.lt_trans he hlt)).trans (hold e he),
        by rw [hhs, hheap], fun x => ?_, hrr.trans hrl, hfu'.trans hfu⟩
      rw [hoo x]; simp [bump, State.setProp, State.objEntry, hheap])
  exact ⟨s', h1, h2, by rw [hen]; exact q1, fun e he => by simp only [State.envEntry, hen]; exact q2 e he,
    by rw [hh]; exact q3, fun x => by simp only [State.objEntry, hh]; exact q4 x, hrs.trans q5, hfe.trans q6⟩

/-! ## `let o = { n: 0, inc: inc }` -/

theorem cdp_ordinary (o : ObjId) (k : PropKey) (v : Value) (t : State) (h : o < t.heap.size)
    (hk : (t.objEntry o).kind.isPlain = true) (hx : (t.objEntry o).extensible = true)
    (hn : (t.objEntry o).props.get? k = none) :
    createDataPropertyOrThrow o k v t = .ok () (t.setProp o k (.data v true true true)) := by
  simp only [createDataPropertyOrThrow, createDataProperty, Obj'.defineOwnProperty_entry _ _ _ _ h hk, M.bind_eq,
    M.bind_apply]
  rw [ordinaryDefineOwnProperty_new _ _ _ _ _ _ _ h hx hn]
  simp [pure, M.pure]

/-- The object literal as the script writes it. -/
abbrev objE : Sem.CExpr := Sem.object #[Sem.PropD.init (Sem.KeyD.name (PropName.ident "n"))
  (fun _ => Sem.lit (Lit.num (F64.fin false 0 (-1074)))),
  Sem.PropD.init (Sem.KeyD.name (PropName.ident "inc")) (fun _ => Sem.ident "inc")]

/-- The state once the object literal has run: the new object `O = u.heap.size` with `n = 0` and
`inc` the function `fI`. -/
def objState (u : State) (fI : ObjId) : State :=
  ((u.allocObj { proto := .obj u.curRealm.objectProto }).setProp u.heap.size (.str "n")
    (.data (num 0) true true true)).setProp u.heap.size (.str "inc") (.data (.obj fI) true true true)

theorem ne_n_inc : PropKey.str (JSStr.ofString "n") ≠ PropKey.str (JSStr.ofString "inc") := by
  intro h; injection h with h; revert h; decide

/-- **`let o = { n: 0, inc: inc }`** at the top level (`o` declared in the global record, `inc` bound on
the global object): a new ordinary object with those two properties, bound to `o`. -/
theorem let_obj (c : Ctx) (u : State) (ge g fI : Nat) (gb : Std.HashMap JSStr Binding) (gtv : Value)
    (hlex : c.lex = ge) (hstr : c.strict = false) (hge : ge < u.envs.size) (hE : u.envEntry ge = .global g gb gtv)
    (hbm : (JSStr.ofString "o" ∈ gb) = True) (hgi : gb.contains "inc" = false)
    (hgim : (JSStr.ofString "inc" ∈ gb) = False) (hgi' : gb[JSStr.ofString "inc"]? = none)
    (hgs : g < u.heap.size) (hk : (u.objEntry g).kind = .ordinary)
    (hp : (u.objEntry g).props.get? (.str "inc") = some (.data (.obj fI) true true false)) (hf : 2 ≤ u.fuel) :
    Sem.varDecl #[Sem.declLex VarKind.let "o" (some objE)] c u =
      .ok (.normal none) ((objState u fI).setEnv ge (.global g (gb.modify "o" fun bd =>
        { bd with value := some (.obj u.heap.size) }) gtv)) := by
  have hk' : (u.objEntry g).kind.isPlain = true := by rw [hk]; rfl
  have hr := Global.resolveBinding_global_decl ge "o" false u g gb gtv hge hE hbm (by omega)
  let O := u.heap.size
  obtain ⟨t1, ht1⟩ : ∃ x, u.allocObj { proto := .obj u.curRealm.objectProto } = x := ⟨_, rfl⟩
  have hO1 : O < t1.heap.size := by rw [← ht1]; simp [State.allocObj, O]
  have hE1 : t1.objEntry O = { proto := .obj u.curRealm.objectProto } := by
    rw [← ht1]; exact State.allocObj_entry_new _ _
  have hc1 := cdp_ordinary O (.str "n") (num 0) t1 hO1 (by simp [hE1]) (by simp [hE1]) (by simp [hE1])
  obtain ⟨t2, ht2⟩ : ∃ x, t1.setProp O (.str "n") (.data (num 0) true true true) = x := ⟨_, rfl⟩
  rw [ht2] at hc1
  have hO2 : O < t2.heap.size := by rw [← ht2]; simpa using hO1
  have hE2 : t2.objEntry O = ({ proto := .obj u.curRealm.objectProto } : Obj).withProps
      (·.insert (.str "n") (.data (num 0) true true true)) := by
    rw [← ht2, State.setProp_entry_self _ _ _ _ hO1, hE1]
  have hgO : g ≠ O := Nat.ne_of_lt hgs
  have hog2 : t2.objEntry g = u.objEntry g := by
    rw [← ht2, State.setProp_entry_ne _ _ _ _ _ (Ne.symm hgO), ← ht1, State.allocObj_entry_lt _ _ _ hgs]
  have hz2 : t2.heap.size = u.heap.size + 1 := by rw [← ht2, ← ht1]; simp [State.allocObj, State.setProp]
  have hf2 : t2.fuel = u.fuel := by rw [← ht2, State.setProp_fuel, ← ht1]; simp [State.allocObj]
  have he2 : t2.envs = u.envs := by rw [← ht2, State.setProp_envs, ← ht1]; simp [State.allocObj]
  have hinc : identValue ge "inc" false t2 = .ok (.obj fI) t2 :=
    Global.identValue_global_obj ge "inc" false t2 g gb gtv _ _ _ _ (by rw [he2]; exact hge)
      (by simp only [State.envEntry, he2]; exact hE) hgi hgim hgi' (by rw [hz2]; exact Nat.lt_succ_of_lt hgs)
      (by rw [hog2]; exact hk') (by rw [hog2]; exact hp) (by rw [hf2]; exact hf)
  have hc2 := cdp_ordinary O (.str "inc") (.obj fI) t2 hO2 (by rw [hE2]; rfl) (by rw [hE2]; rfl)
    (by rw [hE2, Obj.withProps_props, PropMap.get?_insert_ne _ _ _ _ ne_n_inc]; simp)
  obtain ⟨t3, ht3⟩ : ∃ x, t2.setProp O (.str "inc") (.data (.obj fI) true true true) = x := ⟨_, rfl⟩
  rw [ht3] at hc2
  have he3 : t3.envs = u.envs := by rw [← ht3, State.setProp_envs, he2]
  have hin := Global.initializeBinding_global ge "o" (.obj O) t3 g gb gtv (by rw [he3]; exact hge)
    (by simp only [State.envEntry, he3]; exact hE) (Std.HashMap.mem_iff_contains.mp (of_eq_true hbm))
  have hst : objState u fI = t3 := by rw [← ht3, ← ht2, ← ht1]; rfl
  rw [hst]
  simp only [O] at hc1 hc2 hin
  have hlu : (VarKind.let == VarKind.using) = false := by decide
  have hla : (VarKind.let == VarKind.awaitUsing) = false := by decide
  have hnk : Sem.propKey (Sem.KeyD.name (PropName.ident "n")) = fun _ => pure (PropKey.str "n") := rfl
  have hik : Sem.propKey (Sem.KeyD.name (PropName.ident "inc")) = fun _ => pure (PropKey.str "inc") := rfl
  simp [Sem.varDecl, M.forArr_def, M.foldArr_toArray, M.foldList_cons, M.foldList_nil, Sem.declLex, Sem.inner, hlex,
    hstr, hr, Sem.object, newObject_eq, ht1, hnk, hik, Sem.lit, litValue, zero_eq, hc1, Sem.ident, hinc, hc2,
    initializeRefBinding, hin, hlu, hla, pure, M.pure, M.bind_eq, M.bind_apply, M.bindRes_ok]

theorem objState_facts (u : State) (fI : ObjId) :
    (objState u fI).heap.size = u.heap.size + 1 ∧
    (∀ x, x < u.heap.size → (objState u fI).objEntry x = u.objEntry x) ∧
    ((objState u fI).objEntry u.heap.size).kind = .ordinary ∧
    ((objState u fI).objEntry u.heap.size).props.get? (.str "n") = some (.data (num 0) true true true) ∧
    ((objState u fI).objEntry u.heap.size).props.get? (.str "inc") = some (.data (.obj fI) true true true) ∧
    (objState u fI).envs = u.envs ∧ (objState u fI).fuel = u.fuel ∧ (objState u fI).realms = u.realms := by
  have hlt : u.heap.size < (u.allocObj { proto := .obj u.curRealm.objectProto }).heap.size := by simp [State.allocObj]
  have hlt2 : u.heap.size < ((u.allocObj { proto := .obj u.curRealm.objectProto }).setProp u.heap.size (.str "n")
      (.data (num 0) true true true)).heap.size := by simpa using hlt
  refine ⟨by simp [objState, State.allocObj, State.setProp], fun x hx => ?_, ?_, ?_, ?_, by simp [objState, State.allocObj],
    by simp [objState, State.allocObj], by simp [objState, State.allocObj]⟩
  · have hne : u.heap.size ≠ x := Nat.ne_of_gt hx
    simp only [objState]
    rw [State.setProp_entry_ne _ _ _ _ _ hne, State.setProp_entry_ne _ _ _ _ _ hne, State.allocObj_entry_lt _ _ _ hx]
  · simp only [objState]
    rw [State.setProp_entry_self _ _ _ _ hlt2, State.setProp_entry_self _ _ _ _ hlt, State.allocObj_entry_new]; rfl
  · simp only [objState]
    rw [State.setProp_entry_self _ _ _ _ hlt2, State.setProp_entry_self _ _ _ _ hlt, State.allocObj_entry_new]
    simp [PropMap.get?_insert_ne _ _ _ _ ne_n_inc.symm]
  · simp only [objState]
    rw [State.setProp_entry_self _ _ _ _ hlt2, State.setProp_entry_self _ _ _ _ hlt, State.allocObj_entry_new]
    simp

/-! ## The whole script -/

open Script

abbrev callInc : Sem.CStmt := Sem.exprStmt (Sem.call (Sem.memberRef (Sem.ident "o") (Sem.Key.name "inc") false)
  (Sem.args #[]) false (CalleeDesc.prop "inc"))

theorem script_def (n : Nat) : MEGen.script n = Sem.stmts #[Sem.funDecl MEGen.inc_func,
    Sem.varDecl #[Sem.declLex VarKind.let "o" (some objE)], callInc, callInc] := rfl

theorem lexScoped : topLevelLexicallyScoped MEGen.script_stmts = #[.binding .let (.ident "o")] := by
  have hv : (VarKind.let == VarKind.var) = false := by decide
  simp [topLevelLexicallyScoped, stmtLexScoped, MEGen.script_stmts, hv]
theorem simple_inc : Inst.SimpleFn MEGen.inc_func "inc" := ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem ne_oi : (JSStr.ofString "o" = JSStr.ofString "inc") = False := by simp; decide

def fs : List (Func × JSStr) := [(MEGen.inc_func, "inc")]

/-- **The whole program** (examples/method.js), run as the engine runs a script: evaluates to 2.
Started from a realm whose global object is an ordinary extensible object without `o` or `inc`. -/
theorem me_script (eng : Engine) (s : State) (cs : Conts) (gb : Std.HashMap JSStr Binding) (gtv : Value)
    (fp : ObjId) (hge : s.curRealm.globalEnv < s.envs.size)
    (hE : s.envEntry s.curRealm.globalEnv = .global s.curRealm.globalObj gb gtv)
    (hgbo : gb.contains "o" = false) (hgbi : gb.contains "inc" = false)
    (hgs : s.curRealm.globalObj < s.heap.size) (hk : (s.objEntry s.curRealm.globalObj).kind = .ordinary)
    (hx : (s.objEntry s.curRealm.globalObj).extensible = true)
    (hpo : (s.objEntry s.curRealm.globalObj).props.get? (.str "o") = none)
    (hpi : (s.objEntry s.curRealm.globalObj).props.get? (.str "inc") = none)
    (hfp : s.curRealm.intrinsics["%Function.prototype%"]? = some fp) (hf : 20 ≤ s.fuel) :
    ∃ s', (runM eng (scriptEvaluation MEGen.program) s cs).1 = .ok (num 2) s' := by
  let ge := s.curRealm.globalEnv
  let g := s.curRealm.globalObj
  let c := scriptCtx s false
  -- the declarations
  obtain ⟨t0, ht0⟩ : ∃ x, (scriptStart s MEGen.program).setEnv ge (.global g (insertLets gb ["o"]) gtv) = x :=
    ⟨_, rfl⟩
  have ho0 : ∀ x, t0.objEntry x = s.objEntry x := by intro x; rw [← ht0, State.setEnv_objEntry]; rfl
  have hz0 : t0.heap.size = s.heap.size := by rw [← ht0, State.setEnv_heap_size]; rfl
  have hge0 : ge < t0.envs.size := by rw [← ht0, State.setEnv_envs_size]; exact hge
  have hgood : GoodG g fp t0 := ⟨by rw [hz0]; exact hgs, by rw [ho0]; exact hk, by rw [ho0]; exact hx,
    by rw [← ht0, State.setEnv_curRealm]; exact hfp⟩
  obtain ⟨⟨-, hku, -, -⟩, heu, hfuu, -, -, hszu, -, -, -, hnames, hfuns⟩ :=
    instAll_facts ge g s.scripts.size fp fs t0 hgood (by decide)
  obtain ⟨u, hu⟩ : ∃ x, instAll ge g s.scripts.size fp fs t0 = x := ⟨_, rfl⟩
  rw [hu] at hku heu hfuu hszu hnames hfuns
  have hfu0 : t0.fuel = s.fuel := by rw [← ht0, State.setEnv_fuel]; rfl
  let fI := s.heap.size
  obtain ⟨dI, hfIk, hcI, -, hmI, hclsI, -, -⟩ := hfuns 0 (by decide)
  rw [hz0] at hfIk hszu hnames
  simp only [fs, List.length_cons, List.length_nil] at hszu
  simp only [Nat.mul_zero, Nat.add_zero] at hfIk
  have hpI : (u.objEntry g).props.get? (.str "inc") = some (.data (.obj fI) true true false) := hnames 0 (by decide)
  let gbL := gb.insert "o" { deletable := false }
  have hE1 : u.envEntry ge = .global g gbL gtv := by
    have h1 : u.envEntry ge = t0.envEntry ge := by simp only [State.envEntry, heu]
    rw [h1, ← ht0, State.setEnv_envEntry_self _ _ _ (show ge < (scriptStart s MEGen.program).envs.size from hge)]
    simp [insertLets, gbL]
  have hgeu : ge < u.envs.size := by rw [heu]; exact hge0
  have hgu : g < u.heap.size := by rw [hszu]; exact Nat.lt_of_lt_of_le hgs (Nat.le_add_right _ _)
  have hfIu : fI < u.heap.size := by show s.heap.size < u.heap.size; rw [hszu]; omega
  have hgbI' : gb[JSStr.ofString "inc"]? = none := Std.HashMap.getElem?_eq_none (fun hm => by
    rw [Std.HashMap.mem_iff_contains, hgbi] at hm; exact Bool.false_ne_true hm)
  have hLi : gbL.contains "inc" = false := by simp [gbL, Std.HashMap.contains_insert, hgbi, ne_oi]
  have hLi' : gbL[JSStr.ofString "inc"]? = none := by simp [gbL, Std.HashMap.getElem?_insert, ne_oi, hgbI']
  have hLim : (JSStr.ofString "inc" ∈ gbL) = False := by simp [Std.HashMap.mem_iff_contains, hLi]
  -- `let o = { n: 0, inc: inc }`
  have h3 := let_obj c u ge g fI gbL gtv rfl rfl hgeu hE1 (by simp [gbL]) hLi hLim hLi' hgu hku hpI
    (by rw [hfuu, hfu0]; omega)
  let O := u.heap.size
  let gbO := gbL.modify "o" fun bd => { bd with value := some (.obj O) }
  obtain ⟨u2, hu2⟩ : ∃ x, (objState u fI).setEnv ge (.global g gbO gtv) = x := ⟨_, rfl⟩
  rw [hu2] at h3
  obtain ⟨hzO, hoO, hkO, hnO, hiO, heO, hfO, -⟩ := objState_facts u fI
  have ho2 : ∀ x, u2.objEntry x = (objState u fI).objEntry x := by intro x; rw [← hu2, State.setEnv_objEntry]
  have hz2 : u2.heap.size = O + 1 := by rw [← hu2, State.setEnv_heap_size, hzO]
  have hge2 : ge < u2.envs.size := by rw [← hu2, State.setEnv_envs_size, heO]; exact hgeu
  have hE2 : u2.envEntry ge = .global g gbO gtv := by
    rw [← hu2]; exact State.setEnv_envEntry_self _ _ _ (by rw [heO]; exact hgeu)
  have hf2 : u2.fuel = s.fuel := by rw [← hu2, State.setEnv_fuel, hfO, hfuu, hfu0]
  have hO2 : O < u2.heap.size := by rw [hz2]; exact Nat.lt_succ_self _
  have hfI2 : fI < u2.heap.size := by rw [hz2]; exact Nat.lt_succ_of_lt hfIu
  have hfIk2 : (u2.objEntry fI).kind = .func dI := by rw [ho2, hoO fI hfIu]; exact hfIk
  have hOb : gbO[JSStr.ofString "o"]? = some { value := some (.obj O), deletable := false } := by
    simp [gbO, gbL, Std.HashMap.getElem?_modify]
  have hOm : (JSStr.ofString "o" ∈ gbO) = True := by simp [gbO, gbL]
  have hcodeI : dI.code = MEGen.inc_func := hcI
  -- the first `o.inc()`: `this = O`, `n` from 0 to 1
  have hro2 := Global.identValue_global_decl ge "o" false u2 g gbO gtv _ (.obj O) hge2 hE2 hOb hOm rfl (by omega)
  obtain ⟨K5, h5, hK5⟩ := Stmts.method_call_req (Sem.inner c) u2 (Sem.ident "o") O fI "inc" dI (.prop "inc") []
    hro2 (by simp) rfl hO2 (by rw [ho2, hkO]; rfl) true true true (by rw [ho2]; exact hiO) hfI2 hfIk2
  obtain ⟨K6, h6, hK6⟩ := Stmts.exprStmt_req _ c u2 _ K5 h5 hK5
  obtain ⟨u2', hu2'⟩ : ∃ x, ({ u2 with fuel := u2.fuel - 1 } : State) = x := ⟨_, rfl⟩
  have hou2 : ∀ x, u2'.objEntry x = u2.objEntry x := fun x => by rw [← hu2']; rfl
  obtain ⟨s3, hc1, -, hz3, he3, hh3, ho3, -, hf3⟩ := inc_call fI dI u2' O 0 hcodeI hclsI hmI
    (by rw [← hu2']; exact hO2) (by rw [hou2, ho2, hkO]) (by rw [hou2, ho2]; exact hnO) (by decide)
    (by rw [← hu2']; simp only; omega)
  have himpl1 : callImpl eng (.obj fI) (.obj O) #[] u2 = .ok (num 1) s3 := by
    rw [callImpl_func eng fI dI _ _ u2 hfI2 hfIk2 (by omega), hu2']; exact hc1
  -- the state after it
  have hO3 : ∀ x, x ≠ O → s3.objEntry x = u2.objEntry x := by
    intro x hx; rw [ho3 x]; simp only [bump]; rw [State.setProp_entry_ne _ _ _ _ _ (Ne.symm hx), hou2]
  have hO3e : s3.objEntry O = (u2.objEntry O).withProps (·.insert (.str "n") (.data (num ((0 : Nat) + 1 : Int)) true true true)) := by
    rw [ho3 O]; simp only [bump]; rw [State.setProp_entry_self _ _ _ _ (by rw [← hu2']; exact hO2), hou2]
  have hz3' : s3.heap.size = u2.heap.size := by rw [hh3, ← hu2']
  have hf3' : s3.fuel = s.fuel - 1 := by rw [hf3, ← hu2']; simp only; rw [hf2]
  have hge3 : ge < s3.envs.size := Nat.lt_of_lt_of_le (by rw [← hu2']; exact hge2) hz3
  have hE3 : s3.envEntry ge = .global g gbO gtv := by
    rw [he3 ge (by rw [← hu2']; exact hge2)]; rw [← hu2']; exact hE2
  have hfO : fI ≠ O := Nat.ne_of_lt hfIu
  -- the second `o.inc()`: `n` from 1 to 2
  have hro3 := Global.identValue_global_decl ge "o" false s3 g gbO gtv _ (.obj O) hge3 hE3 hOb hOm rfl (by omega)
  obtain ⟨K7, h7, hK7⟩ := Stmts.method_call_req (Sem.inner c) s3 (Sem.ident "o") O fI "inc" dI (.prop "inc") []
    hro3 (by simp) rfl (by rw [hz3']; exact hO2) (by rw [hO3e, Obj.withProps_kind, ho2, hkO]; rfl) true true true
    (by rw [hO3e, Obj.withProps_props, PropMap.get?_insert_ne _ _ _ _ ne_n_inc, ho2]; exact hiO)
    (by rw [hz3']; exact hfI2) (by rw [hO3 fI hfO]; exact hfIk2)
  obtain ⟨K8, h8, hK8⟩ := Stmts.exprStmt_req _ c s3 _ K7 h7 hK7
  obtain ⟨s3', hs3'⟩ : ∃ x, ({ s3 with fuel := s3.fuel - 1 } : State) = x := ⟨_, rfl⟩
  have hos3 : ∀ x, s3'.objEntry x = s3.objEntry x := fun x => by rw [← hs3']; rfl
  obtain ⟨s4, hc2, -⟩ := inc_call fI dI s3' O 1 hcodeI hclsI hmI
    (by rw [← hs3', hz3']; exact hO2) (by rw [hos3, hO3e, Obj.withProps_kind, ho2, hkO])
    (by rw [hos3, hO3e, Obj.withProps_props]; simp)
    (by decide) (by rw [← hs3']; simp only; omega)
  have himpl2 : callImpl eng (.obj fI) (.obj O) #[] s3 = .ok (num 2) s4 := by
    rw [callImpl_func eng fI dI _ _ s3 (by rw [hz3']; exact hfI2) (by rw [hO3 fI hfO]; exact hfIk2) (by omega), hs3']
    exact hc2
  -- the script
  refine ⟨s4, script_value eng s cs MEGen.program fs ["o"] gb gtv fp _ s4 rfl rfl
    (by rw [show MEGen.program.body = MEGen.script_stmts from rfl, lexScoped]; rfl) rfl
    (by intro p hp; simp only [fs, List.mem_cons, List.mem_nil_iff, or_false] at hp; rcases hp with rfl; exact simple_inc)
    (by decide) hge hE
    (by intro p hp; simp only [fs, List.mem_cons, List.mem_nil_iff, or_false] at hp; rcases hp with rfl; exact hgbi)
    (by simpa using hgbo) hgs hk hx
    (by intro p hp; simp only [fs, List.mem_cons, List.mem_nil_iff, or_false] at hp; rcases hp with rfl; exact hpi)
    (by simpa using hpo) hfp ?_⟩
  have hu0 : scriptState s MEGen.program fs ["o"] gb gtv fp = u := by rw [← hu, ← ht0]; rfl
  have hscript : evalStmts evalDepth (scriptCtx s false) MEGen.program.body u = MEGen.script 999962 c u := by
    rw [MEGen.script_eq]; rfl
  have h6' : callInc c u2 = .req (.call (.obj fI) (.obj O) #[]) u2 K6 := h6
  have h8' : callInc c s3 = .req (.call (.obj fI) (.obj O) #[]) s3 K8 := h8
  rw [hu0, hscript, script_def]
  refine Runs.script_runs eng _ _ _ (Runs.stmts_run eng c _ u _ s4 ?_ (by simp; rw [hfuu, hfu0]; omega))
  show Runs.StmtsRun eng c [Sem.funDecl MEGen.inc_func, Sem.varDecl #[Sem.declLex VarKind.let "o" (some objE)],
    callInc, callInc] u none (some (num 2)) s4
  refine .cons _ _ u u s4 none none _ (Runs.runs_funDecl eng _ c u rfl) ?_
  refine .cons _ _ u u2 s4 none none _ (by rw [h3]; exact Runs.runsTo_ok eng _ _) ?_
  refine .cons _ _ u2 s3 s4 (some (num 1)) none _ ?_ ?_
  · rw [h6']; exact Runs.runsTo_req1 eng _ _ _ u2 K6 _ s3 _ s3 himpl1 (hK6 _ s3)
  refine .cons _ _ s3 s4 s4 (some (num 2)) _ _ ?_ (.nil _ _)
  rw [h8']; exact Runs.runsTo_req1 eng _ _ _ s3 K8 _ s4 _ s4 himpl2 (hK8 _ s4)

end Method
