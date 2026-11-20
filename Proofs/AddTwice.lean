import Proofs.Script
import Proofs.Stmts
import Proofs.ATGen
import Proofs.AddCall
import Proofs.Runs

/-!
# `let r = add(1, 2); add(r, 4);` evaluates to 7 (examples/add_twice.js)

Built from the generic pieces only: the declarations (`Script.script_value`, `Script.instAll_facts`),
the call expressions (`Stmts.call_expr_req`, with a literal and a variable as arguments), `let r = …`
(`Stmts.let_req`) and the expression statement (`Stmts.exprStmt_req`).
-/

open ES ES.Conv SumProof Script
open Std (HashMap)
open Global (identValue_global_decl l4)
open Stmts (call_expr_req exprStmt_req let_req)

namespace AddTwice

/-- The [[Call]] of `add`, and what it leaves alone: the heap, the realms, the caller's environments, the fuel. -/
theorem add_call (f : ObjId) (d : FuncData) (s : State) (x y : F64) (go : ObjId) (gb : HashMap JSStr Binding)
    (gtv : Value) (hcode : d.code = AddGen.add_func) (hcls : d.isClassCtor = false) (hmode : d.thisMode = .global)
    (hge : (s.realms[d.realm]!).globalEnv < s.envs.size)
    (hgE : s.envEntry (s.realms[d.realm]!).globalEnv = .global go gb gtv) (hf : 2 ≤ s.fuel) :
    ∃ s', callECMA f d .undefined #[.num x, .num y] s = .ok (.num (addF x y)) s' ∧ s'.realm = s.realm ∧
      s'.heap = s.heap ∧ s'.realms = s.realms ∧ s.envs.size ≤ s'.envs.size ∧
      (∀ e, e < s.envs.size → s'.envEntry e = s.envEntry e) ∧ s'.fuel = s.fuel := by
  obtain ⟨s', h1, h2, -, t', ⟨q1, q2, q3, q4, q5⟩, hh, hen, hfe, hrs⟩ := Calls.callECMA_undef
    (Q := fun t => t.heap = s.heap ∧ t.realms = s.realms ∧ s.envs.size ≤ t.envs.size ∧
      (∀ e, e < s.envs.size → t.envEntry e = s.envEntry e) ∧ t.fuel = s.fuel)
    f d s _ _ go gb gtv hcls hmode (by rw [hcode]; rfl) (by rw [hcode]; rfl) hge hgE
    (fun t hlt hEt hold hheap hfu hrl _ => by
      obtain ⟨t', hb, hsz, hfu', hh', hr', hfe'⟩ := AddCall.add_body f d s.envs.size t x y gtv hcode hlt hEt (by omega)
      exact ⟨t', hb, hh'.trans hheap, hr'.trans hrl, by omega,
        fun e he => (hfe' e (Nat.lt_trans he hlt) (Nat.ne_of_lt he)).trans (hold e he), hfu'.trans hfu⟩)
  exact ⟨s', h1, h2, hh.trans q1, hrs.trans q2, by rw [hen]; exact q3,
    fun e he => by simp only [State.envEntry, hen]; exact q4 e he, hfe.trans q5⟩

/-- The script's statements, as written. -/
abbrev letR : Sem.CStmt := Sem.varDecl #[Sem.declLex VarKind.let "r" (some (Sem.call (Sem.identRef "add")
  (Sem.args #[Sem.ArgD.expr (Sem.lit (Lit.num AddScript.one)), Sem.ArgD.expr (Sem.lit (Lit.num AddScript.two))]) false
  (CalleeDesc.ident "add")))]
abbrev addR4 : Sem.CStmt := Sem.exprStmt (Sem.call (Sem.identRef "add")
  (Sem.args #[Sem.ArgD.expr (Sem.ident "r"), Sem.ArgD.expr (Sem.lit (Lit.num l4))]) false (CalleeDesc.ident "add"))

theorem script_def (n : Nat) : ATGen.script n = Sem.stmts #[Sem.funDecl ATGen.add_func, letR, addR4] := rfl

theorem ne_ra : (JSStr.ofString "r" = JSStr.ofString "add") = False := by simp; decide
theorem add_same : ATGen.add_func = AddGen.add_func := rfl
theorem simple_add : Inst.SimpleFn ATGen.add_func "add" := ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem seven : addF (addF AddScript.one AddScript.two) l4 = ofSmallInt 7 := by decide
theorem lexScoped : topLevelLexicallyScoped ATGen.script_stmts = #[.binding .let (.ident "r")] := by
  have hv : (VarKind.let == VarKind.var) = false := by decide
  simp [topLevelLexicallyScoped, stmtLexScoped, ATGen.script_stmts, hv]

/-- The script's declarations. -/
def fs : List (Func × JSStr) := [(ATGen.add_func, "add")]

/-- **The whole program** (examples/add_twice.js), run as the engine runs a script: evaluates to 7.
Started from a realm whose global object is an ordinary extensible object without `r` or `add`. -/
theorem at_script (eng : Engine) (s : State) (cs : Conts) (gb : HashMap JSStr Binding) (gtv : Value) (fp : ObjId)
    (hge : s.curRealm.globalEnv < s.envs.size)
    (hE : s.envEntry s.curRealm.globalEnv = .global s.curRealm.globalObj gb gtv)
    (hgbr : gb.contains "r" = false) (hgba : gb.contains "add" = false)
    (hgs : s.curRealm.globalObj < s.heap.size) (hk : (s.objEntry s.curRealm.globalObj).kind = .ordinary)
    (hx : (s.objEntry s.curRealm.globalObj).extensible = true)
    (hpr : (s.objEntry s.curRealm.globalObj).props.get? (.str "r") = none)
    (hpa : (s.objEntry s.curRealm.globalObj).props.get? (.str "add") = none)
    (hfp : s.curRealm.intrinsics["%Function.prototype%"]? = some fp) (hf : 10 ≤ s.fuel) :
    ∃ s', (runM eng (scriptEvaluation ATGen.program) s cs).1 = .ok (num 7) s' := by
  let ge := s.curRealm.globalEnv
  let g := s.curRealm.globalObj
  let c := scriptCtx s false
  -- the state after the declarations
  obtain ⟨t0, ht0⟩ : ∃ x, (scriptStart s ATGen.program).setEnv ge (.global g (insertLets gb ["r"]) gtv) = x :=
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
  obtain ⟨dA, hfAk, hcA, hrA, hmA, hclsA⟩ := hfuns 0 (by decide)
  rw [hz0] at hfAk hszu hnames
  simp only [fs, List.length_cons, List.length_nil] at hszu
  simp only [Nat.mul_zero, Nat.add_zero] at hfAk
  have hpA : (u.objEntry g).props.get? (.str "add") = some (.data (.obj fA) true true false) := hnames 0 (by decide)
  have hcodeA : dA.code = AddGen.add_func := hcA.trans add_same
  have hdr : dA.realm = s.realm := hrA.trans hrl0
  let gbL := gb.insert "r" { deletable := false }
  have hE1 : u.envEntry ge = .global g gbL gtv := by
    have h1 : u.envEntry ge = t0.envEntry ge := by simp only [State.envEntry, heu]
    rw [h1, ← ht0, State.setEnv_envEntry_self _ _ _ (show ge < (scriptStart s ATGen.program).envs.size from hge)]
    simp [insertLets, gbL]
  have hgeu : ge < u.envs.size := by rw [heu]; exact hge0
  have hgu : g < u.heap.size := by rw [hszu]; exact Nat.lt_of_lt_of_le hgs (Nat.le_add_right _ _)
  have hfAu : fA < u.heap.size := by show s.heap.size < u.heap.size; rw [hszu]; omega
  have hga : gb[JSStr.ofString "add"]? = none := Std.HashMap.getElem?_eq_none (fun hm => by
    rw [Std.HashMap.mem_iff_contains, hgba] at hm; exact Bool.false_ne_true hm)
  have hLa : gbL.contains "add" = false := by simp [gbL, Std.HashMap.contains_insert, hgba, ne_ra]
  have hLa' : gbL[JSStr.ofString "add"]? = none := by simp [gbL, Std.HashMap.getElem?_insert, ne_ra, hga]
  have hLam : (JSStr.ofString "add" ∈ gbL) = False := by simp [Std.HashMap.mem_iff_contains, hLa]
  -- `let r = add(1, 2)` asks for its call
  obtain ⟨K0, h0, hK0⟩ := call_expr_req (Sem.inner c) u ge g fA "add" gbL gtv dA
    [(Sem.lit (Lit.num AddScript.one), .num AddScript.one), (Sem.lit (Lit.num AddScript.two), .num AddScript.two)]
    (by intro p hp; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp; rcases hp with rfl | rfl <;> rfl)
    rfl rfl hgeu hE1 hLa hLa' hLam hgu hku hpA hfAu hfAk (by rw [hfuu, hfu0]; omega)
  obtain ⟨K3, h3, hK3⟩ := let_req "r" _ c u ge g gbL gtv _ K0 rfl rfl hgeu hE1 (by simp [gbL])
    (by rw [hfuu, hfu0]; omega) h0 hK0
  -- the call of `add` with 1 and 2
  obtain ⟨u', hu'⟩ : ∃ x, ({ u with fuel := u.fuel - 1 } : State) = x := ⟨_, rfl⟩
  have hr' : u'.realms = s.realms := by rw [← hu']; exact hru.trans hr0
  have hgeA : (u'.realms[dA.realm]!).globalEnv = ge := by rw [hr', hdr]; rfl
  have hz' : u'.envs = u.envs := by rw [← hu']
  obtain ⟨s3, hcall1, -, hh3, hr3, hz3, he3, hf3⟩ := add_call fA dA u' AddScript.one AddScript.two g gbL gtv hcodeA
    hclsA hmA (by rw [hgeA, hz']; exact hgeu) (by rw [hgeA]; simp only [State.envEntry, hz']; exact hE1)
    (by rw [← hu']; simp only; rw [hfuu, hfu0]; omega)
  -- `r` is initialized
  have hge3 : ge < s3.envs.size := Nat.lt_of_lt_of_le (by rw [hz']; exact hgeu) hz3
  have hE3 : s3.envEntry ge = .global g gbL gtv := by
    rw [he3 ge (by rw [hz']; exact hgeu)]; simp only [State.envEntry, hz']; exact hE1
  let three := addF AddScript.one AddScript.two
  have himpl1 : callImpl eng (.obj fA) .undefined #[.num AddScript.one, .num AddScript.two] u =
      .ok (.num three) s3 := by
    rw [callImpl_func eng fA dA _ _ u hfAu hfAk (by rw [hfuu, hfu0]; omega), hu']; exact hcall1
  let gbR := gbL.modify "r" fun bd => { bd with value := some (.num three) }
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
  have hRa : gbR.contains "add" = false := by simp [gbR, hLa]
  have hRa' : gbR[JSStr.ofString "add"]? = none := by simp [gbR, Std.HashMap.getElem?_modify, ne_ra, hLa']
  have hRam : (JSStr.ofString "add" ∈ gbR) = False := by simp [Std.HashMap.mem_iff_contains, hRa]
  have hRr : gbR[JSStr.ofString "r"]? = some { value := some (.num three), deletable := false } := by
    simp [gbR, gbL, Std.HashMap.getElem?_modify]
  -- `add(r, 4)` asks for its call
  have hrv := identValue_global_decl ge "r" false w g gbR gtv _ (.num three) hgew hEw hRr (by simp [gbR, gbL]) rfl
    (by omega)
  obtain ⟨K5, h5, hK5⟩ := call_expr_req (Sem.inner c) w ge g fA "add" gbR gtv dA
    [(Sem.ident "r", .num three), (Sem.lit (Lit.num l4), .num l4)]
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
  obtain ⟨s4, hcall2, -⟩ := add_call fA dA w' three l4 g gbR gtv hcodeA hclsA hmA
    (by rw [hgeA', hzw']; exact hgew) (by rw [hgeA']; simp only [State.envEntry, hzw']; exact hEw)
    (by rw [← hw']; simp only; omega)
  have himpl2 : callImpl eng (.obj fA) .undefined #[.num three, .num l4] w = .ok (num 7) s4 := by
    rw [callImpl_func eng fA dA _ _ w (by rw [hhw]; exact hfAu) (by rw [how]; exact hfAk) (by omega), hw',
      show num 7 = .num (addF three l4) from (congrArg Value.num seven).symm]
    exact hcall2
  -- the script
  refine ⟨s4, script_value eng s cs ATGen.program fs ["r"] gb gtv fp _ s4 rfl rfl
    (by rw [show ATGen.program.body = ATGen.script_stmts from rfl, lexScoped]; rfl) rfl
    (by intro p hp; simp only [fs, List.mem_cons, List.mem_nil_iff, or_false] at hp; rcases hp with rfl; exact simple_add)
    (by decide) hge hE
    (by intro p hp; simp only [fs, List.mem_cons, List.mem_nil_iff, or_false] at hp; rcases hp with rfl; exact hgba)
    (by simpa using hgbr) hgs hk hx
    (by intro p hp; simp only [fs, List.mem_cons, List.mem_nil_iff, or_false] at hp; rcases hp with rfl; exact hpa)
    (by simpa using hpr) hfp ?_⟩
  have hu0 : scriptState s ATGen.program fs ["r"] gb gtv fp = u := by rw [← hu, ← ht0]; rfl
  have hscript : evalStmts evalDepth (scriptCtx s false) ATGen.program.body u = ATGen.script 999965 c u := by
    rw [ATGen.script_eq]; rfl
  -- the statements, one by one (`Runs.stmts_run`)
  have h3' : letR c u = .req (.call (.obj fA) .undefined #[.num AddScript.one, .num AddScript.two]) u K3 := h3
  have h4' : addR4 c w = .req (.call (.obj fA) .undefined #[.num three, .num l4]) w K4 := h4
  rw [hu0, hscript, script_def]
  refine Runs.script_runs eng _ _ _ (Runs.stmts_run eng c _ u _ s4 ?_ (by simp; rw [hfuu, hfu0]; omega))
  show Runs.StmtsRun eng c [Sem.funDecl ATGen.add_func, letR, addR4] u none (some (num 7)) s4
  refine .cons (Sem.funDecl ATGen.add_func) _ u u s4 none none _ (Runs.runs_funDecl eng _ c u rfl) ?_
  refine .cons letR _ u w s4 none none _ ?_ ?_
  · rw [h3']; exact Runs.runsTo_req1 eng _ _ _ u K3 _ s3 _ w himpl1 hK3'
  refine .cons addR4 _ w s4 s4 (some (num 7)) none _ ?_ (.nil _ _)
  rw [h4']; exact Runs.runsTo_req1 eng _ _ _ w K4 _ s4 _ s4 himpl2 (hK4 _ s4)

end AddTwice
