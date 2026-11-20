import Proofs.AddTwice
import Proofs.MXGen

/-!
# Control flow: `max(a, b)` for all integer inputs (examples/max.js)

```js
function max(a, b) { if (a < b) { return b; } return a; }
let m = max(3, 7);
max(m, 5);
```
`max`'s call returns the larger of its arguments for every pair of integers below 2^26 in absolute
value (`max_call`, both branches of the `if`); the script evaluates to 7.
-/

open ES ES.Conv SumProof Script
open Std (HashMap)
open Global (identValue_global_decl l3 l5)
open Stmts (call_expr_req exprStmt_req let_req)
open AddCall (paramBindings)

namespace Max

theorem lexIf : lexicallyScoped #[(Stmt.ret (some (Expr.ident "b")))] = #[] := by rfl

/-- **`max`'s body**, `a = x` and `b = y` integers: returns `max x y`, by either branch of the `if`. -/
theorem max_spec (nn : Nat) (ctx : Ctx) (s : State) (x y : Int) (hstr : ctx.strict = false) (hgen : ctx.isGen = false)
    (ha : identValue ctx.lex "a" false s = .ok (num x) s) (hb : identValue ctx.lex "b" false s = .ok (num y) s)
    (hx : x.natAbs < intBound) (hy : y.natAbs < intBound) (hf : 3 ≤ s.fuel) :
    MXGen.max nn ctx s = .ok (.ret (num (max x y))) s := by
  obtain ⟨j, hj⟩ : ∃ j, s.fuel = j + 3 := ⟨s.fuel - 3, by omega⟩
  have hlt := ltF_int x y hx hy
  simp only [MXGen.max, Sem.stmts, M.repeatFrom, hj, M.loop]
  by_cases hxy : x < y
  · have hm : max x y = y := by omega
    simp [M.bind_eq, M.bind_apply, Sem.ifS, Sem.inner, Sem.binary, Sem.ident, hstr, ha, hb, Sem.binaryOp, isLessThan,
      hlt, hxy, toBoolean, ofSmallInt_eq_nan, Sem.block, lexIf, Sem.stmts, M.repeatFrom, hj, M.loop, Sem.ret, hgen,
      pure, M.pure, Compl.updateEmpty, hm]
  · have hm : max x y = x := by omega
    simp [M.bind_eq, M.bind_apply, Sem.ifS, Sem.inner, Sem.binary, Sem.ident, hstr, ha, hb, Sem.binaryOp, isLessThan,
      hlt, hxy, toBoolean, ofSmallInt_eq_nan, Sem.ret, hgen, pure, M.pure, Compl.updateEmpty, hm]

theorem max_fdi (f : ObjId) (d : FuncData) (env : EnvId) (s : State) (x y : F64) (tv : Value)
    (hcode : d.code = MXGen.max_func) (henv : env < s.envs.size)
    (hE : s.envEntry env = .func ∅ (some d.env) .initialized tv f .undefined)
    (hf : s.fuel ≠ 0) :
    ∃ ctx s', functionDeclarationInstantiation 999999 f d env #[.num x, .num y] s = .ok ctx s' ∧
      s'.envEntry env = .func (paramBindings x y) (some d.env) .initialized tv f .undefined ∧
      ctx.lex = s.envs.size ∧ s'.envEntry ctx.lex = .decl ∅ (some env) ∧ ctx.var = env ∧
      ctx.strict = false ∧ ctx.isGen = false ∧ ctx.fn = some f ∧ s'.envs.size = s.envs.size + 1 ∧ s'.fuel = s.fuel ∧
      s'.heap = s.heap ∧ s'.realms = s.realms ∧ (∀ e, e < s.envs.size → e ≠ env → s'.envEntry e = s.envEntry e) := by
  have hr : Array.range 2 = [0, 1].toArray := by decide
  have hbe : ∀ ctx x v b, b.contains x = true →
      bindElement 999998 ctx (.ident x) none (.init (some env)) (M.pure v)
          (s.setEnv env (.func b (some d.env) .initialized tv f .undefined)) =
        .ok () (s.setEnv env (.func (b.modify x fun bd => { bd with value := some v })
          (some d.env) .initialized tv f .undefined)) := by
    intro ctx x v b hb
    have := bindElement_ident 999998 ctx x env v (s.setEnv env (.func b (some d.env) .initialized tv f .undefined))
      (by omega) (by simpa using henv) (by simp [henv]) (by simpa [henv] using hb) (by simpa using hf)
    simpa [henv] using this
  have hab : (JSStr.ofString "a" = JSStr.ofString "b") = False := by simp; decide
  refine ⟨?c, ?t, ?h, ?_⟩
  case h =>
    conv =>
      lhs
      simp only [functionDeclarationInstantiation, hcode]
      simp only [MXGen.max_func, Func.strict, Func.params, Func.info, Func.body, Func.isAsync]
      simp [hr, hasBinding_declLike, createMutableBinding_declLike, hbe, newDeclEnv, pure,
        M.pure, hE, henv, hf, hab]
  have hne : env ≠ s.envs.size := Nat.ne_of_lt henv
  simp [State.envEntry, State.setEnv, Array.getElem?_push, Array.getElem_push, Array.getElem_modify, henv, hne,
    paramBindings]
  intro e he hee
  simp [Nat.ne_of_lt he, Array.getElem?_modify, Ne.symm hee]

/-- `max`'s body as a call runs it. -/
theorem max_body (f : ObjId) (d : FuncData) (env : EnvId) (s : State) (x y : Int) (tv : Value)
    (hcode : d.code = MXGen.max_func) (henv : env < s.envs.size)
    (hE : s.envEntry env = .func ∅ (some d.env) .initialized tv f .undefined)
    (hx : x.natAbs < intBound) (hy : y.natAbs < intBound) (hf : 3 ≤ s.fuel) :
    ∃ s', evalFunctionBody evalDepth f d env #[num x, num y] s = .ok (num (max x y)) s' ∧
      s'.envs.size = s.envs.size + 1 ∧ s'.fuel = s.fuel ∧ s'.heap = s.heap ∧ s'.realms = s.realms ∧
      (∀ e, e < s.envs.size → e ≠ env → s'.envEntry e = s.envEntry e) := by
  obtain ⟨ctx, s', hfdi, hB, hlex, hL, hvar, hstrict, hgen, hfn, hsize, hfuel, hheap, hrl, hfe⟩ :=
    max_fdi f d env s (ofSmallInt x) (ofSmallInt y) tv hcode henv hE (by omega)
  have hl' : ctx.lex < s'.envs.size := by rw [hlex, hsize]; exact Nat.lt_succ_self _
  have he' : env < s'.envs.size := by rw [hsize]; exact Nat.lt_succ_of_lt henv
  have hread : ∀ (n : JSStr) (v : F64), ((paramBindings (ofSmallInt x) (ofSmallInt y))[n]?).bind (·.value) = some (.num v) →
      identValue ctx.lex n false s' = .ok (.num v) s' := by
    intro n v h
    cases hb : (paramBindings (ofSmallInt x) (ofSmallInt y))[n]? with
    | none => simp [hb] at h
    | some bd =>
      simp only [hb, Option.bind_some] at h
      exact identValue_decl_func ctx.lex env n false s' (.num v) _ bd _ _ _ _ _ hl' hL he' hB hb h (by omega)
  have hab : (JSStr.ofString "b" == JSStr.ofString "a") = false := by decide
  have ha : identValue ctx.lex "a" false s' = .ok (num x) s' := by
    apply hread; simp [paramBindings, Std.HashMap.getElem_modify, Std.HashMap.getElem_insert, hab]
  have hb : identValue ctx.lex "b" false s' = .ok (num y) s' := by
    apply hread; simp [paramBindings, Std.HashMap.getElem_modify, Std.HashMap.getElem_insert, hab]
  have hbody := max_spec 999973 ctx s' x y hstrict hgen ha hb hx hy (by omega)
  refine ⟨s', ?_, hsize, hfuel, hheap, hrl, hfe⟩
  have hbd : d.code.body = .stmts MXGen.max_stmts := by rw [hcode]; rfl
  have hdisp : d.code.info.fdi.usesDispose = false := by rw [hcode]; rfl
  have hbody' : evalStmts (999973 + 26) ctx MXGen.max_stmts s' = .ok (.ret (num (max x y))) s' := by
    rw [← congrFun (MXGen.max_eq 999973) ctx]; exact hbody
  simp only [evalDepth, evalFunctionBody, M.bind_eq, M.bind_apply, hfdi, M.bindRes_ok, hbd, hdisp, withDisposeScope]
  simp [hbody', pure, M.pure]

/-- **The [[Call]] of `max`** (`this` undefined) with integers `x`, `y` below 2^26 in absolute value: returns
`max x y`, and leaves the heap, the realms, the caller's environments and the fuel as they were. -/
theorem max_call (f : ObjId) (d : FuncData) (s : State) (x y : Int) (go : ObjId) (gb : HashMap JSStr Binding)
    (gtv : Value) (hcode : d.code = MXGen.max_func) (hcls : d.isClassCtor = false) (hmode : d.thisMode = .global)
    (hge : (s.realms[d.realm]!).globalEnv < s.envs.size)
    (hgE : s.envEntry (s.realms[d.realm]!).globalEnv = .global go gb gtv)
    (hx : x.natAbs < intBound) (hy : y.natAbs < intBound) (hf : 3 ≤ s.fuel) :
    ∃ s', callECMA f d .undefined #[num x, num y] s = .ok (num (max x y)) s' ∧ s'.realm = s.realm ∧
      s'.heap = s.heap ∧ s'.realms = s.realms ∧ s.envs.size ≤ s'.envs.size ∧
      (∀ e, e < s.envs.size → s'.envEntry e = s.envEntry e) ∧ s'.fuel = s.fuel := by
  obtain ⟨s', h1, h2, -, t', ⟨q1, q2, q3, q4, q5⟩, hh, hen, hfe, hrs⟩ := Calls.callECMA_undef
    (Q := fun t => t.heap = s.heap ∧ t.realms = s.realms ∧ s.envs.size ≤ t.envs.size ∧
      (∀ e, e < s.envs.size → t.envEntry e = s.envEntry e) ∧ t.fuel = s.fuel)
    f d s _ _ go gb gtv hcls hmode (by rw [hcode]; rfl) (by rw [hcode]; rfl) hge hgE
    (fun t hlt hEt hold hheap hfu hrl _ => by
      obtain ⟨t', hb, hsz, hfu', hh', hr', hfe'⟩ := max_body f d s.envs.size t x y gtv hcode hlt hEt hx hy (by omega)
      exact ⟨t', hb, hh'.trans hheap, hr'.trans hrl, by omega,
        fun e he => (hfe' e (Nat.lt_trans he hlt) (Nat.ne_of_lt he)).trans (hold e he), hfu'.trans hfu⟩)
  exact ⟨s', h1, h2, hh.trans q1, hrs.trans q2, by rw [hen]; exact q3,
    fun e he => by simp only [State.envEntry, hen]; exact q4 e he, hfe.trans q5⟩

abbrev l7 : F64 := F64.fin false 7881299347898368 (-50)

/-- The script's statements, as written. -/
abbrev letM : Sem.CStmt := Sem.varDecl #[Sem.declLex VarKind.let "m" (some (Sem.call (Sem.identRef "max")
  (Sem.args #[Sem.ArgD.expr (Sem.lit (Lit.num l3)), Sem.ArgD.expr (Sem.lit (Lit.num l7))]) false
  (CalleeDesc.ident "max")))]
abbrev maxM5 : Sem.CStmt := Sem.exprStmt (Sem.call (Sem.identRef "max")
  (Sem.args #[Sem.ArgD.expr (Sem.ident "m"), Sem.ArgD.expr (Sem.lit (Lit.num l5))]) false (CalleeDesc.ident "max"))

theorem script_def (n : Nat) : MXGen.script n = Sem.stmts #[Sem.funDecl MXGen.max_func, letM, maxM5] := rfl

theorem ne_mm : (JSStr.ofString "m" = JSStr.ofString "max") = False := by simp; decide
theorem simple_max : Inst.SimpleFn MXGen.max_func "max" := ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem l3_eq : l3 = ofSmallInt 3 := by decide
theorem l7_eq : l7 = ofSmallInt 7 := by decide
theorem l5_eq : l5 = ofSmallInt 5 := by decide
theorem lexScoped : topLevelLexicallyScoped MXGen.script_stmts = #[.binding .let (.ident "m")] := by
  have hv : (VarKind.let == VarKind.var) = false := by decide
  simp [topLevelLexicallyScoped, stmtLexScoped, MXGen.script_stmts, hv]

/-- The script's declarations. -/
def fs : List (Func × JSStr) := [(MXGen.max_func, "max")]

/-- **The whole program** (examples/max.js), run as the engine runs a script: evaluates to 7.
Started from a realm whose global object is an ordinary extensible object without `m` or `max`. -/
theorem mx_script (eng : Engine) (s : State) (cs : Conts) (gb : HashMap JSStr Binding) (gtv : Value) (fp : ObjId)
    (hge : s.curRealm.globalEnv < s.envs.size)
    (hE : s.envEntry s.curRealm.globalEnv = .global s.curRealm.globalObj gb gtv)
    (hgbm : gb.contains "m" = false) (hgbx : gb.contains "max" = false)
    (hgs : s.curRealm.globalObj < s.heap.size) (hk : (s.objEntry s.curRealm.globalObj).kind = .ordinary)
    (hx : (s.objEntry s.curRealm.globalObj).extensible = true)
    (hpm : (s.objEntry s.curRealm.globalObj).props.get? (.str "m") = none)
    (hpx : (s.objEntry s.curRealm.globalObj).props.get? (.str "max") = none)
    (hfp : s.curRealm.intrinsics["%Function.prototype%"]? = some fp) (hf : 10 ≤ s.fuel) :
    ∃ s', (runM eng (scriptEvaluation MXGen.program) s cs).1 = .ok (num 7) s' := by
  let ge := s.curRealm.globalEnv
  let g := s.curRealm.globalObj
  let c := scriptCtx s false
  -- the state after the declarations
  obtain ⟨t0, ht0⟩ : ∃ x, (scriptStart s MXGen.program).setEnv ge (.global g (insertLets gb ["m"]) gtv) = x :=
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
  have hrl0 : t0.realm = s.realm := by rw [← ht0, State.setEnv_realm]; rfl
  have hr0 : t0.realms = s.realms := by rw [← ht0, State.setEnv_realms]; rfl
  have hfu0 : t0.fuel = s.fuel := by rw [← ht0, State.setEnv_fuel]; rfl
  let fA := s.heap.size
  obtain ⟨dA, hfAk, hcA, hrA, hmA, hclsA, -⟩ := hfuns 0 (by decide)
  rw [hz0] at hfAk hszu hnames
  simp only [fs, List.length_cons, List.length_nil] at hszu
  simp only [Nat.mul_zero, Nat.add_zero] at hfAk
  have hpA : (u.objEntry g).props.get? (.str "max") = some (.data (.obj fA) true true false) := hnames 0 (by decide)
  have hcodeA : dA.code = MXGen.max_func := hcA
  have hdr : dA.realm = s.realm := hrA.trans hrl0
  let gbL := gb.insert "m" { deletable := false }
  have hE1 : u.envEntry ge = .global g gbL gtv := by
    have h1 : u.envEntry ge = t0.envEntry ge := by simp only [State.envEntry, heu]
    rw [h1, ← ht0, State.setEnv_envEntry_self _ _ _ (show ge < (scriptStart s MXGen.program).envs.size from hge)]
    simp [insertLets, gbL]
  have hgeu : ge < u.envs.size := by rw [heu]; exact hge0
  have hgu : g < u.heap.size := by rw [hszu]; exact Nat.lt_of_lt_of_le hgs (Nat.le_add_right _ _)
  have hfAu : fA < u.heap.size := by show s.heap.size < u.heap.size; rw [hszu]; omega
  have hga : gb[JSStr.ofString "max"]? = none := Std.HashMap.getElem?_eq_none (fun hm => by
    rw [Std.HashMap.mem_iff_contains, hgbx] at hm; exact Bool.false_ne_true hm)
  have hLa : gbL.contains "max" = false := by simp [gbL, Std.HashMap.contains_insert, hgbx, ne_mm]
  have hLa' : gbL[JSStr.ofString "max"]? = none := by simp [gbL, Std.HashMap.getElem?_insert, ne_mm, hga]
  have hLam : (JSStr.ofString "max" ∈ gbL) = False := by simp [Std.HashMap.mem_iff_contains, hLa]
  -- `let r = add(1, 2)` asks for its call
  obtain ⟨K0, h0, hK0⟩ := call_expr_req (Sem.inner c) u ge g fA "max" gbL gtv dA
    [(Sem.lit (Lit.num l3), .num l3), (Sem.lit (Lit.num l7), .num l7)]
    (by intro p hp; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp; rcases hp with rfl | rfl <;> rfl)
    rfl rfl hgeu hE1 hLa hLa' hLam hgu hku hpA hfAu hfAk (by rw [hfuu, hfu0]; omega)
  obtain ⟨K3, h3, hK3⟩ := let_req "m" _ c u ge g gbL gtv _ K0 rfl rfl hgeu hE1 (by simp [gbL])
    (by rw [hfuu, hfu0]; omega) h0 hK0
  -- the call of `add` with 1 and 2
  obtain ⟨u', hu'⟩ : ∃ x, ({ u with fuel := u.fuel - 1 } : State) = x := ⟨_, rfl⟩
  have hr' : u'.realms = s.realms := by rw [← hu']; exact hru.trans hr0
  have hgeA : (u'.realms[dA.realm]!).globalEnv = ge := by rw [hr', hdr]; rfl
  have hz' : u'.envs = u.envs := by rw [← hu']
  obtain ⟨s3, hcall1, -, hh3, hr3, hz3, he3, hf3⟩ := max_call fA dA u' 3 7 g gbL gtv hcodeA
    hclsA hmA (by rw [hgeA, hz']; exact hgeu) (by rw [hgeA]; simp only [State.envEntry, hz']; exact hE1)
    (by decide) (by decide) (by rw [← hu']; simp only; rw [hfuu, hfu0]; omega)
  rw [show max (3 : Int) 7 = 7 from by decide] at hcall1
  -- `r` is initialized
  have hge3 : ge < s3.envs.size := Nat.lt_of_lt_of_le (by rw [hz']; exact hgeu) hz3
  have hE3 : s3.envEntry ge = .global g gbL gtv := by
    rw [he3 ge (by rw [hz']; exact hgeu)]; simp only [State.envEntry, hz']; exact hE1
  let three := ofSmallInt 7
  have himpl1 : callImpl eng (.obj fA) .undefined #[.num l3, .num l7] u =
      .ok (.num three) s3 := by
    rw [l3_eq, l7_eq, callImpl_func eng fA dA _ _ u hfAu hfAk (by rw [hfuu, hfu0]; omega), hu']; exact hcall1
  let gbR := gbL.modify "m" fun bd => { bd with value := some (.num three) }
  obtain ⟨w, hw⟩ : ∃ w, s3.setEnv ge (.global g gbR gtv) = w := ⟨_, rfl⟩
  have hK3' : K3 (.normal (.num three)) s3 = .ok (.normal none) w := by
    rw [← hw]; exact hK3 _ s3 gbL hge3 hE3 (by simp [gbL])
  have hEw : w.envEntry ge = .global g gbR gtv := by rw [← hw]; exact State.setEnv_envEntry_self _ _ _ hge3
  have hgew : ge < w.envs.size := by rw [← hw, State.setEnv_envs_size]; exact hge3
  have how : ∀ x, w.objEntry x = u.objEntry x := by
    intro x; rw [← hw, State.setEnv_objEntry]; simp only [State.objEntry, hh3]; rw [← hu']
  have hhw : w.heap.size = u.heap.size := by rw [← hw, State.setEnv_heap_size, hh3, ← hu']
  have hfw : w.fuel = s.fuel - 1 := by rw [← hw, State.setEnv_fuel, hf3, ← hu']; simp only; rw [hfuu, hfu0]
  have hrw : w.realms = s.realms := by rw [← hw, State.setEnv_realms, hr3, hr']
  have hRa : gbR.contains "max" = false := by simp [gbR, hLa]
  have hRa' : gbR[JSStr.ofString "max"]? = none := by simp [gbR, Std.HashMap.getElem?_modify, ne_mm, hLa']
  have hRam : (JSStr.ofString "max" ∈ gbR) = False := by simp [Std.HashMap.mem_iff_contains, hRa]
  have hRr : gbR[JSStr.ofString "m"]? = some { value := some (.num three), deletable := false } := by
    simp [gbR, gbL, Std.HashMap.getElem?_modify]
  -- `add(r, 4)` asks for its call
  have hrv := identValue_global_decl ge "m" false w g gbR gtv _ (.num three) hgew hEw hRr (by simp [gbR, gbL]) rfl
    (by omega)
  obtain ⟨K5, h5, hK5⟩ := call_expr_req (Sem.inner c) w ge g fA "max" gbR gtv dA
    [(Sem.ident "m", .num three), (Sem.lit (Lit.num l5), .num l5)]
    (by intro p hp; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
        rcases hp with rfl | rfl
        · exact hrv
        · rfl)
    rfl rfl hgew hEw hRa hRa' hRam (by rw [hhw]; exact hgu) (by rw [how]; exact hku) (by rw [how]; exact hpA)
    (by rw [hhw]; exact hfAu) (by rw [how]; exact hfAk) (by omega)
  obtain ⟨K4, h4, hK4⟩ := exprStmt_req _ c w _ K5 h5 hK5
  -- the call of `add` with 3 and 4
  obtain ⟨w', hw'⟩ : ∃ x, ({ w with fuel := w.fuel - 1 } : State) = x := ⟨_, rfl⟩
  have hgeA' : (w'.realms[dA.realm]!).globalEnv = ge := by
    rw [← hw']; show (w.realms[dA.realm]!).globalEnv = ge; rw [hrw, hdr]; rfl
  have hzw' : w'.envs = w.envs := by rw [← hw']
  obtain ⟨s4, hcall2, -⟩ := max_call fA dA w' 7 5 g gbR gtv hcodeA hclsA hmA
    (by rw [hgeA', hzw']; exact hgew) (by rw [hgeA']; simp only [State.envEntry, hzw']; exact hEw)
    (by decide) (by decide) (by rw [← hw']; simp only; omega)
  rw [show max (7 : Int) 5 = 7 from by decide] at hcall2
  have himpl2 : callImpl eng (.obj fA) .undefined #[.num three, .num l5] w = .ok (num 7) s4 := by
    rw [l5_eq, callImpl_func eng fA dA _ _ w (by rw [hhw]; exact hfAu) (by rw [how]; exact hfAk) (by omega), hw']
    exact hcall2
  -- the script
  refine ⟨s4, script_value eng s cs MXGen.program fs ["m"] gb gtv fp _ s4 rfl rfl
    (by rw [show MXGen.program.body = MXGen.script_stmts from rfl, lexScoped]; rfl) rfl
    (by intro p hp; simp only [fs, List.mem_cons, List.mem_nil_iff, or_false] at hp; rcases hp with rfl; exact simple_max)
    (by decide) hge hE
    (by intro p hp; simp only [fs, List.mem_cons, List.mem_nil_iff, or_false] at hp; rcases hp with rfl; exact hgbx)
    (by simpa using hgbm) hgs hk hx
    (by intro p hp; simp only [fs, List.mem_cons, List.mem_nil_iff, or_false] at hp; rcases hp with rfl; exact hpx)
    (by simpa using hpm) hfp ?_⟩
  have hu0 : scriptState s MXGen.program fs ["m"] gb gtv fp = u := by rw [← hu, ← ht0]; rfl
  have hscript : evalStmts evalDepth (scriptCtx s false) MXGen.program.body u = MXGen.script 999965 c u := by
    rw [MXGen.script_eq]; rfl
  -- the statements, one by one (`Runs.stmts_run`)
  have h3' : letM c u = .req (.call (.obj fA) .undefined #[.num l3, .num l7]) u K3 := h3
  have h4' : maxM5 c w = .req (.call (.obj fA) .undefined #[.num three, .num l5]) w K4 := h4
  rw [hu0, hscript, script_def]
  refine Runs.script_runs eng _ _ _ (Runs.stmts_run eng c _ u _ s4 ?_ (by simp; rw [hfuu, hfu0]; omega))
  show Runs.StmtsRun eng c [Sem.funDecl MXGen.max_func, letM, maxM5] u none (some (num 7)) s4
  refine .cons (Sem.funDecl MXGen.max_func) _ u u s4 none none _ (Runs.runs_funDecl eng _ c u rfl) ?_
  refine .cons letM _ u w s4 none none _ ?_ ?_
  · rw [h3']; exact Runs.runsTo_req1 eng _ _ _ u K3 _ s3 _ w himpl1 hK3'
  refine .cons maxM5 _ w s4 s4 (some (num 7)) none _ ?_ (.nil _ _)
  rw [h4']; exact Runs.runsTo_req1 eng _ _ _ w K4 _ s4 _ s4 himpl2 (hK4 _ s4)

end Max
