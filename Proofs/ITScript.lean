import Proofs.Runs
import Proofs.IotaCall
import Proofs.ITGen

/-!
# A whole script: `let b = iota(5); total(b);` (examples/iota_total.js)

Run as the engine runs a script (ScriptEvaluation, its two call requests answered by the driver), it
evaluates to 10 = 0 + 1 + 2 + 3 + 4: `iota(5)` builds a new array (its writes go through
`Array.prototype`'s chain, assumed to have no index property below 5), `b` is bound to it, and
`total(b)` sums it. The declarations and ScriptEvaluation are the generic `Script.script_value` and
`Script.instAll_facts`.
-/

open ES ES.Conv SumProof SumForProof TotalProof
open Std (HashMap)
open Global (resolveBinding_global_obj createMutableBinding_global initializeBinding_global identValue_global_decl
  resolveBinding_global_decl call_req gb2 gb2_b gb2_mem_b gb2_contains gb2_get gb2_mem isArray_of_arrayObj ne_bt l5
  callOf)

namespace ITScript

theorem lexScoped : topLevelLexicallyScoped ITGen.script_stmts = #[.binding .let (.ident "b")] := by
  have hv : (VarKind.let == VarKind.var) = false := by decide
  simp [topLevelLexicallyScoped, stmtLexScoped, ITGen.script_stmts, hv]


theorem simple_total : Inst.SimpleFn ITGen.total_func "total" := ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem simple_iota : Inst.SimpleFn ITGen.iota_func "iota" := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem total_same : ITGen.total_func = TotalGen.total_func := rfl
theorem isIota_it : IotaCall.IsIota ITGen.iota_func := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## The statements -/

theorem ne_bi : (JSStr.ofString "b" = JSStr.ofString "iota") = False := by simp; decide
theorem l5_eq : l5 = ofSmallInt 5 := by decide

abbrev letIota : Sem.CStmt := Sem.varDecl #[Sem.declLex VarKind.let "b" (some (Sem.call (Sem.identRef "iota")
  (Sem.args #[Sem.ArgD.expr (Sem.lit (Lit.num l5))]) false (CalleeDesc.ident "iota")))]

/-- `let b = iota(5)`, `b` declared in the global record and `iota` bound on the global object: asks
the driver to call `iota` with 5; when the call returns `v` (in a state where the global record is
still there), `b` is initialized to `v`. -/
theorem let_call_req (c : Ctx) (u : State) (ge g fo : Nat) (gb : HashMap JSStr Binding) (gtv : Value) (d : FuncData)
    (hlex : c.lex = ge) (hstr : c.strict = false) (hge : ge < u.envs.size) (hE : u.envEntry ge = .global g gb gtv)
    (hbm : (JSStr.ofString "b" ∈ gb) = True) (hgi : gb.contains "iota" = false) (hgi' : gb[JSStr.ofString "iota"]? = none)
    (hgim : (JSStr.ofString "iota" ∈ gb) = False) (hgs : g < u.heap.size) (hk : (u.objEntry g).kind = .ordinary)
    (hp : (u.objEntry g).props.get? (.str "iota") = some (.data (.obj fo) true true false))
    (hfs : fo < u.heap.size) (hfk : (u.objEntry fo).kind = .func d) (hf : 2 ≤ u.fuel) :
    ∃ K, letIota c u = .req (.call (.obj fo) .undefined #[.num l5]) u K ∧
      ∀ v w gbw, ge < w.envs.size → w.envEntry ge = .global g gbw gtv → gbw.contains "b" = true →
        K (.normal v) w = .ok (.normal none) (w.setEnv ge (.global g (gbw.modify "b" fun bd =>
          { bd with value := some v }) gtv)) := by
  obtain ⟨k, hk2⟩ : ∃ k, u.fuel = k + 2 := ⟨u.fuel - 2, by omega⟩
  have hk' : (u.objEntry g).kind.isPlain = true := by rw [hk]; rfl
  have hr := resolveBinding_global_decl ge "b" false u g gb gtv hge hE hbm (by omega)
  have hri := resolveBinding_global_obj ge "iota" false u g gb gtv _ hge hE hgi hgim hgs hk' hp (by omega)
  have hlu : (VarKind.let == VarKind.using) = false := by decide
  have hla : (VarKind.let == VarKind.awaitUsing) = false := by decide
  refine ⟨?K, ?h, ?_⟩
  case h =>
    conv =>
      lhs
      simp [Sem.varDecl, Sem.declLex, Sem.inner, hlex, hstr, hr, M.forArr_def, M.foldArr_toArray, M.foldList_cons,
        M.foldList_nil, Sem.call, Sem.identRef, hri, readEnv_entry _ _ _ hge, hE, hgi,
        Obj'.hasProperty_entry_own _ _ _ hgs hk', hp, getRefValue, getBindingValue, hgi', getProp,
        Obj'.get_entry_data _ _ _ _ hgs hk', refThisValue, Sem.args, Sem.lit, litValue, isCallable,
        readObj_entry' _ _ _ hfs, hfk, ES.call, pure, M.pure, hgim, M.repeatFrom, hk2, M.loop, M.bind_eq, M.bind_apply,
        M.bindRes_ok, M.bindRes_req]
  intro v w gbw hgew hEw hbw
  simp [initializeRefBinding, initializeBinding_global ge "b" v w g gbw gtv hgew hEw hbw, hlu, hla, pure, M.pure,
    M.bind_eq, M.bind_apply, M.bindRes_ok, M.foldList_nil]

theorem script_def (n : Nat) : ITGen.script n = Sem.stmts #[Sem.funDecl ITGen.total_func,
    Sem.funDecl ITGen.iota_func, letIota, callOf "total"] := rfl

theorem psum10 : psum (fun j => j) 5 = 10 := by decide

/-! ## The whole script -/

open Script

/-- The script's declarations. -/
def fs : List (Func × JSStr) := [(ITGen.total_func, "total"), (ITGen.iota_func, "iota")]

/-- **The whole program** (examples/iota_total.js), run as the engine runs a script: ScriptEvaluation,
with its two call requests answered by the driver, evaluates to 10. Started from a realm whose global
object is an ordinary extensible object without `b`, `total` or `iota`, and in which no object on
`Array.prototype`'s chain has an index property below 5. -/
theorem it_script (eng : Engine) (s : State) (cs : Conts) (gb : HashMap JSStr Binding) (gtv : Value) (fp : ObjId)
    (hge : s.curRealm.globalEnv < s.envs.size)
    (hE : s.envEntry s.curRealm.globalEnv = .global s.curRealm.globalObj gb gtv)
    (hgbb : gb.contains "b" = false) (hgbt : gb.contains "total" = false) (hgbi : gb.contains "iota" = false)
    (hgs : s.curRealm.globalObj < s.heap.size) (hk : (s.objEntry s.curRealm.globalObj).kind = .ordinary)
    (hx : (s.objEntry s.curRealm.globalObj).extensible = true)
    (hpb : (s.objEntry s.curRealm.globalObj).props.get? (.str "b") = none)
    (hpt : (s.objEntry s.curRealm.globalObj).props.get? (.str "total") = none)
    (hpi : (s.objEntry s.curRealm.globalObj).props.get? (.str "iota") = none)
    (hfp : s.curRealm.intrinsics["%Function.prototype%"]? = some fp)
    (hP : ∀ j < 5, AbsentChain s 2 s.curRealm.arrayProto (PropKey.ofNat j)) (hf : 30 ≤ s.fuel) :
    ∃ s', (runM eng (scriptEvaluation ITGen.program) s cs).1 = .ok (num 10) s' := by
  let ge := s.curRealm.globalEnv
  let g := s.curRealm.globalObj
  let c := scriptCtx s false
  -- the state after the declarations (`Script.instAll_facts`)
  obtain ⟨t0, ht0⟩ : ∃ x, (scriptStart s ITGen.program).setEnv ge (.global g (insertLets gb ["b"]) gtv) = x :=
    ⟨_, rfl⟩
  have ho0 : ∀ x, t0.objEntry x = s.objEntry x := by intro x; rw [← ht0, State.setEnv_objEntry]; rfl
  have hz0 : t0.heap.size = s.heap.size := by rw [← ht0, State.setEnv_heap_size]; rfl
  have hge0 : ge < t0.envs.size := by rw [← ht0, State.setEnv_envs_size]; exact hge
  have hgood : GoodG g fp t0 := ⟨by rw [hz0]; exact hgs, by rw [ho0]; exact hk, by rw [ho0]; exact hx,
    by rw [← ht0, State.setEnv_curRealm]; exact hfp⟩
  obtain ⟨⟨-, hku, -, -⟩, heu, hfuu, hru, hrlu, hszu, hou, hpru, hkeep, hnames, hfuns⟩ :=
    instAll_facts ge g s.scripts.size fp fs t0 hgood (by decide)
  obtain ⟨u, hu⟩ : ∃ x, instAll ge g s.scripts.size fp fs t0 = x := ⟨_, rfl⟩
  rw [hu] at hku heu hfuu hru hrlu hszu hou hpru hkeep hnames hfuns
  have hrl0 : t0.realm = s.realm := by rw [← ht0, State.setEnv_realm]; rfl
  have hr0 : t0.realms = s.realms := by rw [← ht0, State.setEnv_realms]; rfl
  have hfu0 : t0.fuel = s.fuel := by rw [← ht0, State.setEnv_fuel]; rfl
  let fT := s.heap.size
  let fI := s.heap.size + 2
  obtain ⟨dT, hfTk, hcT, hrT, hmT, hclsT, -, -⟩ := hfuns 0 (by decide)
  obtain ⟨dI, hfIk, hcI, hrI, hmI, hclsI, -, -⟩ := hfuns 1 (by decide)
  rw [hz0] at hfTk hfIk hszu hnames
  simp only [fs, List.length_cons, List.length_nil] at hszu
  simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one] at hfTk hfIk
  have hpt1 : (u.objEntry g).props.get? (.str "total") = some (.data (.obj fT) true true false) := hnames 0 (by decide)
  have hpi1 : (u.objEntry g).props.get? (.str "iota") = some (.data (.obj fI) true true false) := hnames 1 (by decide)
  have hcodeT : dT.code = TotalGen.total_func := hcT.trans total_same
  have hcodeI : IotaCall.IsIota dI.code := by rw [hcI]; exact isIota_it
  have hir : dI.realm = s.realm := hrI.trans hrl0
  have htrl : dT.realm = s.realm := hrT.trans hrl0
  let gbL := gb.insert "b" { deletable := false }
  have hE1 : u.envEntry ge = .global g gbL gtv := by
    have h1 : u.envEntry ge = t0.envEntry ge := by simp only [State.envEntry, heu]
    rw [h1, ← ht0, State.setEnv_envEntry_self _ _ _ (show ge < (scriptStart s ITGen.program).envs.size from hge)]
    simp [insertLets, gbL]
  have hgeu : ge < u.envs.size := by rw [heu]; exact hge0
  have hgu : g < u.heap.size := by rw [hszu]; exact Nat.lt_of_lt_of_le hgs (Nat.le_add_right _ _)
  have hfTu : fT < u.heap.size := by show s.heap.size < u.heap.size; rw [hszu]; omega
  have hfIu : fI < u.heap.size := by show s.heap.size + 2 < u.heap.size; rw [hszu]; omega
  have hLb : (JSStr.ofString "b" ∈ gbL) = True := by simp [gbL]
  have hLi : gbL.contains "iota" = false := by simp [gbL, Std.HashMap.contains_insert, hgbi, ne_bi]
  have hLi' : gbL[JSStr.ofString "iota"]? = none := by
    have : gb[JSStr.ofString "iota"]? = none := Std.HashMap.getElem?_eq_none (fun hm => by
      rw [Std.HashMap.mem_iff_contains, hgbi] at hm; exact Bool.false_ne_true hm)
    simp [gbL, Std.HashMap.getElem?_insert, ne_bi, this]
  have hLim : (JSStr.ofString "iota" ∈ gbL) = False := by simp [Std.HashMap.mem_iff_contains, hLi]
  -- `let b = iota(5)` asks for its call
  obtain ⟨K3, h3, hK3⟩ := let_call_req c u ge g fI gbL gtv dI rfl rfl hgeu hE1 hLb hLi hLi' hLim hgu hku hpi1 hfIu
    hfIk (by rw [hfuu, hfu0]; omega)
  -- the call of `iota`
  obtain ⟨u', hu'⟩ : ∃ x, ({ u with fuel := u.fuel - 1 } : State) = x := ⟨_, rfl⟩
  have hr' : u'.realms = s.realms := by rw [← hu']; exact hru.trans hr0
  have hgeI : (u'.realms[dI.realm]!).globalEnv = ge := by rw [hr', hir]; rfl
  have hz' : u'.envs = u.envs := by rw [← hu']
  have hou' : ∀ x, u'.objEntry x = u.objEntry x := fun x => by rw [← hu']; rfl
  have hPI : ∀ j < 5, AbsentChain u' 2 (u'.realms[dI.realm]!).arrayProto (PropKey.ofNat j) := by
    intro j hj
    have hap : (u'.realms[dI.realm]!).arrayProto = s.curRealm.arrayProto := by rw [hr', hir]; rfl
    rw [hap]
    refine absentChain_mono_key s u' _ (fun x hx => ?_) ?_ 2 _ (hP j hj)
    · rw [hou' x]
      by_cases hxg : x = g
      · subst hxg
        refine ⟨by rw [hku, hk], by rw [hpru, ho0], ?_⟩
        rw [hkeep _ (fun p hp => ?_), ho0]
        simp only [fs, List.mem_cons, List.mem_nil_iff, or_false] at hp
        rcases hp with rfl | rfl
        · exact Ne.symm (name_ne_index "total" (by decide) j (by omega))
        · exact Ne.symm (name_ne_index "iota" (by decide) j (by omega))
      · rw [hou x (by rw [hz0]; exact hx) hxg, ho0]; exact ⟨rfl, rfl, rfl⟩
    · rw [← hu']; show s.heap.size ≤ u.heap.size; rw [hszu]; exact Nat.le_add_right _ _
  obtain ⟨s3, hcallI, -, -, hA3, hz3, he3, hhs3, ho3, hr3, hfu3⟩ := IotaCall.iota_call fI dI u' 5 g gbL gtv
    hcodeI hclsI hmI (by rw [hgeI, hz']; exact hgeu) (by rw [hgeI]; simp only [State.envEntry, hz']; exact hE1)
    (by decide) hPI (by rw [← hu']; simp only; rw [hfuu, hfu0]; omega)
  let A := u.heap.size
  have hAu : u'.heap.size = A := by rw [← hu']
  rw [hAu] at hcallI hA3 hhs3
  have himplI : callImpl eng (.obj fI) .undefined #[.num l5] u = .ok (.obj A) s3 := by
    rw [l5_eq, callImpl_func eng fI dI _ _ u hfIu hfIk (by rw [hfuu, hfu0]; omega), hu']; exact hcallI
  -- `b` is initialized
  have hge3 : ge < s3.envs.size := Nat.lt_of_lt_of_le (by rw [hz']; exact hgeu) hz3
  have hE3 : s3.envEntry ge = .global g gbL gtv := by
    rw [he3 ge (by rw [hz']; exact hgeu)]; simp only [State.envEntry, hz']; exact hE1
  obtain ⟨w, hw⟩ : ∃ w, s3.setEnv ge (.global g (gbL.modify "b" fun bd => { bd with value := some (.obj A) }) gtv) = w :=
    ⟨_, rfl⟩
  have hK3' : K3 (.normal (.obj A)) s3 = .ok (.normal none) w := by
    rw [← hw]; exact hK3 _ s3 gbL hge3 hE3 (by simp [gbL])
  have hEw : w.envEntry ge = .global g (gb2 gb A) gtv := by rw [← hw]; exact State.setEnv_envEntry_self _ _ _ hge3
  have hgew : ge < w.envs.size := by rw [← hw, State.setEnv_envs_size]; exact hge3
  have how : ∀ x, x < A → w.objEntry x = u.objEntry x := by
    intro x hx; rw [← hw, State.setEnv_objEntry, ho3 x (by rw [hAu]; exact hx), hou']
  have hhw : w.heap.size = A + 1 := by rw [← hw, State.setEnv_heap_size, hhs3]
  have hfw : w.fuel + 6 = s.fuel - 1 := by
    rw [← hw, State.setEnv_fuel]; rw [← hu'] at hfu3; simp only at hfu3; rw [hfuu, hfu0] at hfu3; omega
  have hAw : ArrayObj A 5 (fun j => num j) w := by
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hA3
    exact ⟨by rw [← hw, State.setEnv_heap_size]; exact a1, by rw [← hw, State.setEnv_objEntry]; exact a2,
      by rw [← hw, State.setEnv_objEntry]; exact a3, by rw [← hw, State.setEnv_objEntry]; exact a4,
      fun j hj => by rw [← hw, State.setEnv_objEntry]; exact a5 j hj,
      fun j hj hjb => by rw [← hw, State.setEnv_objEntry]; exact a6 j hj hjb⟩
  have hrw : w.realms = s.realms := by rw [← hw, State.setEnv_realms, hr3, hr']
  -- `total(b)` asks for its call
  obtain ⟨K4, h4, hK4⟩ := call_req c w ge g fT A "total" (gb2 gb A) gtv dT _ rfl rfl hgew hEw
    (gb2_contains gb A _ ne_bt hgbt) (gb2_get gb A _ ne_bt hgbt) (gb2_mem gb A _ ne_bt hgbt) (gb2_b gb A)
    (gb2_mem_b gb A) rfl (by rw [hhw]; exact Nat.lt_succ_of_lt hgu) (by rw [how g hgu]; exact hku)
    (by rw [how g hgu]; exact hpt1) (by rw [hhw]; exact Nat.lt_succ_of_lt hfTu) (by rw [how fT hfTu]; exact hfTk)
    (by omega)
  -- the call of `total`
  obtain ⟨w', hw'⟩ : ∃ x, ({ w with fuel := w.fuel - 1 } : State) = x := ⟨_, rfl⟩
  have hgeT : (w'.realms[dT.realm]!).globalEnv = ge := by
    rw [← hw']; show (w.realms[dT.realm]!).globalEnv = ge; rw [hrw, htrl]; rfl
  have hzw' : w'.envs = w.envs := by rw [← hw']
  obtain ⟨s4, hcallT, -, -⟩ := TotalCall.total_call fT dT w' A 5 (fun j => j) g (gb2 gb A) gtv hcodeT hclsT hmT
    (by rw [hgeT, hzw']; exact hgew) (by rw [hgeT]; simp only [State.envEntry, hzw']; exact hEw)
    (by decide) (by intro j hj; omega)
    (isArray_of_arrayObj A 5 _ w' (MoreCalls.arrayObj_of_heap A 5 _ w w' (by rw [← hw']) hAw))
    (by rw [← hw']; simp only; omega)
  have himplT : callImpl eng (.obj fT) .undefined #[.obj A] w = .ok (num (psum (fun j => j) 5)) s4 := by
    rw [callImpl_func eng fT dT _ _ w (by rw [hhw]; exact Nat.lt_succ_of_lt hfTu) (by rw [how fT hfTu]; exact hfTk)
      (by omega), hw']
    exact hcallT
  -- the script (`Script.script_value`), with the driver
  refine ⟨s4, script_value eng s cs ITGen.program fs ["b"] gb gtv fp _ s4 rfl rfl
    (by rw [show ITGen.program.body = ITGen.script_stmts from rfl, lexScoped]; rfl) rfl
    (by intro p hp; simp only [fs, List.mem_cons, List.mem_nil_iff, or_false] at hp
        rcases hp with rfl | rfl
        · exact simple_total
        · exact simple_iota)
    (by decide) hge hE
    (by intro p hp; simp only [fs, List.mem_cons, List.mem_nil_iff, or_false] at hp; rcases hp with rfl | rfl <;> assumption)
    (by simpa using hgbb) hgs hk hx
    (by intro p hp; simp only [fs, List.mem_cons, List.mem_nil_iff, or_false] at hp; rcases hp with rfl | rfl <;> assumption)
    (by simpa using hpb) hfp ?_⟩
  have hu0 : scriptState s ITGen.program fs ["b"] gb gtv fp = u := by rw [← hu, ← ht0]; rfl
  have hscript : evalStmts evalDepth (scriptCtx s false) ITGen.program.body u = ITGen.script 999956 c u := by
    rw [ITGen.script_eq]; rfl
  rw [psum10] at himplT
  have h4' : callOf "total" c w = .req (.call (.obj fT) .undefined #[.obj A]) w K4 := h4
  rw [hu0, hscript, script_def]
  refine Runs.script_runs eng _ _ _ (Runs.stmts_run eng c _ u _ s4 ?_ (by simp; rw [hfuu, hfu0]; omega))
  show Runs.StmtsRun eng c [Sem.funDecl ITGen.total_func, Sem.funDecl ITGen.iota_func, letIota, callOf "total"] u
    none (some (num 10)) s4
  refine .cons _ _ u u s4 none none _ (Runs.runs_funDecl eng _ c u rfl) ?_
  refine .cons _ _ u u s4 none none _ (Runs.runs_funDecl eng _ c u rfl) ?_
  refine .cons _ _ u w s4 none none _ ?_ ?_
  · rw [h3]; exact Runs.runsTo_req1 eng _ _ _ u K3 _ s3 _ w himplI hK3'
  refine .cons _ _ w s4 s4 (some (num 10)) _ _ ?_ (.nil _ _)
  rw [h4']; exact Runs.runsTo_req1 eng _ _ _ w K4 _ s4 _ s4 himplT (hK4 _ s4)

end ITScript
