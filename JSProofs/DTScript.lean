import JSProofs.Runs
import JSProofs.DTGen

/-!
# A whole script: `double(b)` then `total(b)` (examples/double_total.js)

```js
function total(a) { … }  function double(a) { … }
let b = [3, 4, 5];
double(b);
total(b);
```

Run as the engine runs a script (ScriptEvaluation, its two call requests answered by the driver),
it evaluates to 24: `double` doubles the array in place (and changes nothing else that `total(b)`
reads: `Frame`), then `total` sums it.
-/

open ES ES.Conv SumProof SumForProof TotalProof DoubleProof
open Std (HashMap)

open Global Script

namespace DTScript

/-! ## Declarations -/

theorem lexScoped : topLevelLexicallyScoped DTGen.script_stmts = #[.binding .let (.ident "b")] := by
  have hv : (VarKind.let == VarKind.var) = false := by decide
  simp [topLevelLexicallyScoped, stmtLexScoped, DTGen.script_stmts, hv]
theorem simple_total : Inst.SimpleFn DTGen.total_func "total" := ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem simple_double : Inst.SimpleFn DTGen.double_func "double" := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ## The statements -/


/-- The array's elements: 3, 4, 5. -/
def xs3 (j : Nat) : Nat := j + 3

def ps : List (Sem.CExpr × Value) :=
  [(Sem.lit (Lit.num l3), .num l3), (Sem.lit (Lit.num l4), .num l4), (Sem.lit (Lit.num l5), .num l5)]

theorem ps_ev : ∀ p ∈ ps, ∀ (ctx : Ctx) (u : State), p.1 ctx u = .ok p.2 u := by
  intro p hp ctx u
  simp only [ps, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl <;> rfl

theorem ps_vals (j : Nat) (hj : j < 3) :
    (([Value.num l3, .num l4, .num l5])[j]?).getD .undefined = num (xs3 j) := by
  obtain rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  · show Value.num l3 = Value.num (ofSmallInt ((0 + 3 : Nat) : Int)); congr 1
  · show Value.num l4 = Value.num (ofSmallInt ((1 + 3 : Nat) : Int)); congr 1
  · show Value.num l5 = Value.num (ofSmallInt ((2 + 3 : Nat) : Int)); congr 1

/-- `let b = [3, 4, 5]`, `b` declared (uninitialized) in the global record: a new array (the next
object) bound to `b`. -/
theorem let_b (c : Ctx) (u : State) (ge g : Nat) (gb : HashMap JSStr Binding) (gtv : Value)
    (hlex : c.lex = ge) (hstr : c.strict = false) (hge : ge < u.envs.size) (hE : u.envEntry ge = .global g gb gtv)
    (hbm : (JSStr.ofString "b" ∈ gb) = True) (hf : u.fuel ≠ 0) :
    ∃ u', Sem.varDecl #[Sem.declLex VarKind.let "b" (some (Sem.array #[Sem.ElemD.expr (Sem.lit (Lit.num l3)),
        Sem.ElemD.expr (Sem.lit (Lit.num l4)), Sem.ElemD.expr (Sem.lit (Lit.num l5))]))] c u = .ok (.normal none) u' ∧
      u'.envEntry ge = .global g (gb.modify "b" fun bd => { bd with value := some (.obj u.heap.size) }) gtv ∧
      ArrayObj u.heap.size 3 (fun j => num (xs3 j)) u' ∧ u'.envs.size = u.envs.size ∧
      u'.heap.size = u.heap.size + 1 ∧ (∀ o, o < u.heap.size → u'.objEntry o = u.objEntry o) ∧ u'.fuel = u.fuel ∧
      (∀ e, e ≠ ge → u'.envEntry e = u.envEntry e) ∧ u'.realms = u.realms := by
  have hil : (Sem.inner c).lex = ge := hlex
  have his : (Sem.inner c).strict = false := hstr
  have hr := resolveBinding_global_decl ge "b" false u g gb gtv hge hE hbm hf
  obtain ⟨t1, hlit, hA1, he1, hf1, hz1, ho1, hr1, -⟩ := array_literal (Sem.inner c) ps (fun p hp u => ps_ev p hp _ u)
    (by simp [ps]) u
  simp only [ps, List.map_cons, List.map_nil, List.length_cons, List.length_nil] at hlit hA1
  have hl1 : ge < t1.envs.size := by rw [he1]; exact hge
  have hE1 : t1.envEntry ge = .global g gb gtv := by simp only [State.envEntry, he1]; exact hE
  have hin := initializeBinding_global ge "b" (.obj u.heap.size) t1 g gb gtv hl1 hE1
    (Std.HashMap.mem_iff_contains.mp (of_eq_true hbm))
  obtain ⟨t2, ht2⟩ : ∃ t2, t1.setEnv ge (.global g (gb.modify "b" fun bd => { bd with value := some (.obj u.heap.size) })
      gtv) = t2 := ⟨_, rfl⟩
  rw [ht2] at hin
  have hlu : (VarKind.let == VarKind.using) = false := by decide
  have hla : (VarKind.let == VarKind.awaitUsing) = false := by decide
  refine ⟨t2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by rw [← ht2, State.setEnv_realms, hr1]⟩
  · simp only [Sem.varDecl, M.bind_eq, M.bind_apply, M.forArr_def, M.foldArr_toArray, M.foldList_cons, M.foldList_nil]
    simp only [Sem.declLex, M.bind_eq, M.bind_apply, hil, his, hr, M.bindRes_ok, hlit]
    simp [initializeRefBinding, hin, hlu, hla, M.bindRes_ok, M.foldList_nil, pure, M.pure]
  · rw [← ht2]; exact State.setEnv_envEntry_self _ _ _ hl1
  · obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hA1
    refine ⟨by rw [← ht2, State.setEnv_heap_size]; exact a1, by rw [← ht2, State.setEnv_objEntry]; exact a2,
      by rw [← ht2, State.setEnv_objEntry]; exact a3, by rw [← ht2, State.setEnv_objEntry]; exact a4,
      fun j hj => by
        rw [← ht2, State.setEnv_objEntry, a5 j hj]; exact congrArg (fun v => some (Property.data v true true true)) (ps_vals j hj),
      fun j hj hjb => by rw [← ht2, State.setEnv_objEntry]; exact a6 j hj hjb⟩
  · rw [← ht2, State.setEnv_envs_size, he1]
  · rw [← ht2, State.setEnv_heap_size, hz1]
  · intro o ho; rw [← ht2, State.setEnv_objEntry, ho1 o ho]
  · rw [← ht2, State.setEnv_fuel, hf1]
  · intro e he; rw [← ht2, State.setEnv_envEntry_ne _ _ _ _ (Ne.symm he)]; simp only [State.envEntry, he1]

/-- The array literal and the two calls, as the script writes them. -/
abbrev arr3 : Sem.CExpr := Sem.array #[Sem.ElemD.expr (Sem.lit (Lit.num l3)), Sem.ElemD.expr (Sem.lit (Lit.num l4)),
  Sem.ElemD.expr (Sem.lit (Lit.num l5))]

theorem script_def (n : Nat) : DTGen.script n = Sem.stmts #[Sem.funDecl DTGen.total_func,
    Sem.funDecl DTGen.double_func, Sem.varDecl #[Sem.declLex VarKind.let "b" (some arr3)], callOf "double",
    callOf "total"] := rfl

theorem psum24 : psum (fun j => 2 * xs3 j) 3 = 24 := by decide

theorem total_same : DTGen.total_func = TotalGen.total_func := rfl
theorem isDouble_dt : MoreCalls.IsDouble DTGen.double_func := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## The whole script -/

/-- The script's declarations. -/
def fs : List (Func × JSStr) := [(DTGen.total_func, "total"), (DTGen.double_func, "double")]

/-- **The whole program** (examples/double_total.js), run as the engine runs a script: ScriptEvaluation,
with its two call requests answered by the driver, evaluates to 24. Started from a realm whose global
object is an ordinary extensible object without `b`, `total` or `double`. -/
theorem dt_script (eng : Engine) (s : State) (cs : Conts) (gb : HashMap JSStr Binding) (gtv : Value) (fp : ObjId)
    (hge : s.curRealm.globalEnv < s.envs.size)
    (hE : s.envEntry s.curRealm.globalEnv = .global s.curRealm.globalObj gb gtv)
    (hgbb : gb.contains "b" = false) (hgbt : gb.contains "total" = false) (hgbd : gb.contains "double" = false)
    (hgs : s.curRealm.globalObj < s.heap.size) (hk : (s.objEntry s.curRealm.globalObj).kind = .ordinary)
    (hx : (s.objEntry s.curRealm.globalObj).extensible = true)
    (hpb : (s.objEntry s.curRealm.globalObj).props.get? (.str "b") = none)
    (hpt : (s.objEntry s.curRealm.globalObj).props.get? (.str "total") = none)
    (hpd : (s.objEntry s.curRealm.globalObj).props.get? (.str "double") = none)
    (hfp : s.curRealm.intrinsics["%Function.prototype%"]? = some fp) (hf : 24 ≤ s.fuel) :
    ∃ s', (runM eng (scriptEvaluation DTGen.program) s cs).1 = .ok (num 24) s' := by
  let ge := s.curRealm.globalEnv
  let g := s.curRealm.globalObj
  let c := scriptCtx s false
  -- the state after the declarations (`Script.instAll_facts`)
  obtain ⟨t0, ht0⟩ : ∃ x, (scriptStart s DTGen.program).setEnv ge (.global g (insertLets gb ["b"]) gtv) = x :=
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
  let fT := s.heap.size
  let fD := s.heap.size + 2
  obtain ⟨dT, hfTk, hcT, hrT, hmT, hclsT, -, -⟩ := hfuns 0 (by decide)
  obtain ⟨dD, hfDk, hcD, hrD, hmD, hclsD, -, -⟩ := hfuns 1 (by decide)
  rw [hz0] at hfTk hfDk hszu hnames
  simp only [fs, List.length_cons, List.length_nil] at hszu
  simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one] at hfTk hfDk
  have hpt1 : (u.objEntry g).props.get? (.str "total") = some (.data (.obj fT) true true false) := hnames 0 (by decide)
  have hpd1 : (u.objEntry g).props.get? (.str "double") = some (.data (.obj fD) true true false) := hnames 1 (by decide)
  have hcodeT : dT.code = TotalGen.total_func := hcT.trans total_same
  have hcodeD : MoreCalls.IsDouble dD.code := by rw [hcD]; exact isDouble_dt
  have hdr : dD.realm = s.realm := hrD.trans hrl0
  have htrl : dT.realm = s.realm := hrT.trans hrl0
  let gbL := gb.insert "b" { deletable := false }
  have hE1 : u.envEntry ge = .global g gbL gtv := by
    have h1 : u.envEntry ge = t0.envEntry ge := by simp only [State.envEntry, heu]
    rw [h1, ← ht0, State.setEnv_envEntry_self _ _ _ (show ge < (scriptStart s DTGen.program).envs.size from hge)]
    simp [insertLets, gbL]
  have hgeu : ge < u.envs.size := by rw [heu]; exact hge0
  have hgu : g < u.heap.size := by rw [hszu]; exact Nat.lt_of_lt_of_le hgs (Nat.le_add_right _ _)
  have hfTu : fT < u.heap.size := by show s.heap.size < u.heap.size; rw [hszu]; omega
  have hfDu : fD < u.heap.size := by show s.heap.size + 2 < u.heap.size; rw [hszu]; omega
  -- `let b = [3, 4, 5]`
  obtain ⟨u2, h3, hE2, hA2, hz2, hsz2, ho2, hfu2, -, hrl2⟩ := let_b c u ge g gbL gtv rfl rfl hgeu hE1 (by simp [gbL])
    (by rw [hfuu, hfu0]; omega)
  let A := u.heap.size
  have hE2' : u2.envEntry ge = .global g (gb2 gb A) gtv := hE2
  have hge2 : ge < u2.envs.size := by rw [hz2]; exact hgeu
  have hgA : g ≠ A := Nat.ne_of_lt hgu
  have hfTA : fT ≠ A := Nat.ne_of_lt hfTu
  have hk2 : (u2.objEntry g).kind = .ordinary := by rw [ho2 g hgu]; exact hku
  have hpd2 : (u2.objEntry g).props.get? (.str "double") = some (.data (.obj fD) true true false) := by
    rw [ho2 g hgu]; exact hpd1
  have hpt2 : (u2.objEntry g).props.get? (.str "total") = some (.data (.obj fT) true true false) := by
    rw [ho2 g hgu]; exact hpt1
  have hfD2 : fD < u2.heap.size := by rw [hsz2]; exact Nat.lt_succ_of_lt hfDu
  have hfT2 : fT < u2.heap.size := by rw [hsz2]; exact Nat.lt_succ_of_lt hfTu
  have hfDk2 : (u2.objEntry fD).kind = .func dD := by rw [ho2 fD hfDu]; exact hfDk
  have hfTk2 : (u2.objEntry fT).kind = .func dT := by rw [ho2 fT hfTu]; exact hfTk
  have hgu2 : g < u2.heap.size := by rw [hsz2]; exact Nat.lt_succ_of_lt hgu
  have hfuel2 : u2.fuel = s.fuel := by rw [hfu2, hfuu, hfu0]
  -- `double(b)` asks for its call
  obtain ⟨K4, h4, hK4⟩ := call_req c u2 ge g fD A "double" (gb2 gb A) gtv dD _ rfl rfl hge2 hE2'
    (gb2_contains gb A _ ne_bd hgbd) (gb2_get gb A _ ne_bd hgbd) (gb2_mem gb A _ ne_bd hgbd) (gb2_b gb A)
    (gb2_mem_b gb A) rfl hgu2 hk2 hpd2 hfD2 hfDk2 (by omega)
  -- the call of `double`
  obtain ⟨u2', hu2'⟩ : ∃ x, ({ u2 with fuel := u2.fuel - 1 } : State) = x := ⟨_, rfl⟩
  have hr2' : u2'.realms = s.realms := by rw [← hu2']; exact hrl2.trans (hru.trans hr0)
  have hgeD : (u2'.realms[dD.realm]!).globalEnv = ge := by rw [hr2', hdr]; rfl
  have hz2' : u2'.envs = u2.envs := by rw [← hu2']
  obtain ⟨s3, hcallD, -, -, hA3, hfr3, hfu3⟩ := MoreCalls.double_call fD dD u2' A 3 xs3 g (gb2 gb A) gtv
    hcodeD hclsD hmD (by rw [hgeD, hz2']; exact hge2) (by rw [hgeD]; simp only [State.envEntry, hz2']; exact hE2')
    (by decide) (by intro j hj; simp only [xs3]; omega)
    (MoreCalls.arrayObj_of_heap A 3 _ u2 u2' (by rw [← hu2']) hA2) (by rw [← hu2']; simp only; omega)
  have himplD : callImpl eng (.obj fD) .undefined #[.obj A] u2 = .ok .undefined s3 := by
    rw [callImpl_func eng fD dD _ _ u2 hfD2 hfDk2 (by omega), hu2']; exact hcallD
  -- `total(b)` asks for its call, in the state `double` left
  obtain ⟨hz3, he3, hh3, ho3, hr3⟩ := hfr3
  have hge3 : ge < s3.envs.size := Nat.lt_of_lt_of_le (by rw [hz2']; exact hge2) hz3
  have hE3 : s3.envEntry ge = .global g (gb2 gb A) gtv := by
    rw [he3 ge (by rw [hz2']; exact hge2)]; simp only [State.envEntry, hz2']; exact hE2'
  have hobj : ∀ o, o ≠ A → s3.objEntry o = u2.objEntry o := by
    intro o ho; rw [ho3 o ho, ← hu2']; rfl
  have hhs3 : s3.heap.size = u2.heap.size := by rw [hh3, ← hu2']
  have hfuel3 : s3.fuel + 4 = s.fuel - 1 := by rw [← hfuel2]; rw [← hu2'] at hfu3; simpa using hfu3
  obtain ⟨K5, h5, hK5⟩ := call_req c s3 ge g fT A "total" (gb2 gb A) gtv dT _ rfl rfl hge3 hE3
    (gb2_contains gb A _ ne_bt hgbt) (gb2_get gb A _ ne_bt hgbt) (gb2_mem gb A _ ne_bt hgbt) (gb2_b gb A)
    (gb2_mem_b gb A) rfl (by rw [hhs3]; exact hgu2) (by rw [hobj g hgA]; exact hk2) (by rw [hobj g hgA]; exact hpt2)
    (by rw [hhs3]; exact hfT2) (by rw [hobj fT hfTA]; exact hfTk2) (by omega)
  -- the call of `total`
  obtain ⟨s3', hs3'⟩ : ∃ x, ({ s3 with fuel := s3.fuel - 1 } : State) = x := ⟨_, rfl⟩
  have hr3' : s3'.realms = s.realms := by rw [← hs3']; exact hr3.trans hr2'
  have hgeT : (s3'.realms[dT.realm]!).globalEnv = ge := by rw [hr3', htrl]; rfl
  have hz3' : s3'.envs = s3.envs := by rw [← hs3']
  obtain ⟨s4, hcallT, -, -⟩ := TotalCall.total_call fT dT s3' A 3 (fun j => 2 * xs3 j) g (gb2 gb A) gtv hcodeT hclsT
    hmT (by rw [hgeT, hz3']; exact hge3) (by rw [hgeT]; simp only [State.envEntry, hz3']; exact hE3)
    (by decide) (by intro j hj; simp only [xs3]; omega)
    (isArray_of_arrayObj A 3 _ s3' (MoreCalls.arrayObj_of_heap A 3 _ s3 s3' (by rw [← hs3']) hA3))
    (by rw [← hs3']; simp only; omega)
  have himplT : callImpl eng (.obj fT) .undefined #[.obj A] s3 = .ok (num (psum (fun j => 2 * xs3 j) 3)) s4 := by
    rw [callImpl_func eng fT dT _ _ s3 (by rw [hhs3]; exact hfT2) (by rw [hobj fT hfTA]; exact hfTk2) (by omega), hs3']
    exact hcallT
  -- the script (`Script.script_value`), with the driver
  refine ⟨s4, script_value eng s cs DTGen.program fs ["b"] gb gtv fp _ s4 rfl rfl
    (by rw [show DTGen.program.body = DTGen.script_stmts from rfl, lexScoped]; rfl) rfl
    (by intro p hp; simp only [fs, List.mem_cons, List.mem_nil_iff, or_false] at hp
        rcases hp with rfl | rfl
        · exact simple_total
        · exact simple_double)
    (by decide) hge hE
    (by intro p hp; simp only [fs, List.mem_cons, List.mem_nil_iff, or_false] at hp; rcases hp with rfl | rfl <;> assumption)
    (by simpa using hgbb) hgs hk hx
    (by intro p hp; simp only [fs, List.mem_cons, List.mem_nil_iff, or_false] at hp; rcases hp with rfl | rfl <;> assumption)
    (by simpa using hpb) hfp ?_⟩
  have hu0 : scriptState s DTGen.program fs ["b"] gb gtv fp = u := by rw [← hu, ← ht0]; rfl
  have hscript : evalStmts evalDepth (scriptCtx s false) DTGen.program.body u = DTGen.script 999956 c u := by
    rw [DTGen.script_eq]; rfl
  rw [psum24] at himplT
  have h4' : callOf "double" c u2 = .req (.call (.obj fD) .undefined #[.obj A]) u2 K4 := h4
  have h5' : callOf "total" c s3 = .req (.call (.obj fT) .undefined #[.obj A]) s3 K5 := h5
  rw [hu0, hscript, script_def]
  refine Runs.script_runs eng _ _ _ (Runs.stmts_run eng c _ u _ s4 ?_ (by simp; rw [hfuu, hfu0]; omega))
  show Runs.StmtsRun eng c [Sem.funDecl DTGen.total_func, Sem.funDecl DTGen.double_func,
    Sem.varDecl #[Sem.declLex VarKind.let "b" (some arr3)], callOf "double", callOf "total"] u none
    (some (num 24)) s4
  refine .cons _ _ u u s4 none none _ (Runs.runs_funDecl eng _ c u rfl) ?_
  refine .cons _ _ u u s4 none none _ (Runs.runs_funDecl eng _ c u rfl) ?_
  refine .cons _ _ u u2 s4 none none _ (by rw [h3]; exact Runs.runsTo_ok eng _ _) ?_
  refine .cons _ _ u2 s3 s4 (some .undefined) none _ ?_ ?_
  · rw [h4']; exact Runs.runsTo_req1 eng _ _ _ u2 K4 _ s3 _ s3 himplD (hK4 _ s3)
  refine .cons _ _ s3 s4 s4 (some (num 24)) _ _ ?_ (.nil _ _)
  rw [h5']; exact Runs.runsTo_req1 eng _ _ _ s3 K5 _ s4 _ s4 himplT (hK5 _ s4)

end DTScript
