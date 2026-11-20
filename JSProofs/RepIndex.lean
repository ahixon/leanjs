import JSProofs.Rep
import JSProofs.RIGen

/-!
# Indexing a string: `rep(n)[k]` (examples/rep_index.js)

```js
function rep(n) { let s = ""; for (let i = 0; i < n; i = i + 1) { s = s + "ab"; } return s; }
rep(5)[3];
```
`s[k]` on a primitive string is its code unit at `k` (`getRefValue_str_index`); for `rep(n)` that is "a" at even
`k` and "b" at odd `k`, for every `k < 2n` (`rep_index`). The script evaluates to "b".
-/

open ES ES.Conv SumProof

namespace RepIndex

open Rep

/-- The characters of "ab" repeated `n` times. -/
abbrev L (n : Nat) : List Char := (String.join (List.replicate n "ab")).toList

theorem ab_toList : "ab".toList = ['a', 'b'] := by decide

theorem L_succ (n : Nat) : L (n + 1) = ['a', 'b'] ++ L n := by
  simp only [L, List.replicate_succ, String.join_cons, String.toList_append, ab_toList]

theorem L_length (n : Nat) : (L n).length = 2 * n := by
  induction n with
  | zero => rfl
  | succ k ih => rw [L_succ]; simp [ih]; omega

theorem L_get (n : Nat) : ∀ k (hk : k < (L n).length), (L n)[k] = if k % 2 = 0 then 'a' else 'b' := by
  induction n with
  | zero => intro k hk; simp [L_length] at hk
  | succ m ih =>
    intro k hk
    have e : L (m + 1) = ['a', 'b'] ++ L m := L_succ m
    simp only [e]
    rcases k with _ | _ | k
    · rfl
    · rfl
    · have hk' : k < (L m).length := by
        have h2 := hk; rw [e, List.length_append, L_length] at h2; rw [L_length]; simp at h2; omega
      simp only [List.cons_append, List.getElem_cons_succ, List.nil_append]
      rw [ih k hk']
      have : (k + 1 + 1) % 2 = k % 2 := by omega
      rw [this]

theorem L_small (n : Nat) : ∀ c ∈ L n, c.toNat < 256 := by
  intro c hc
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hc
  rw [L_get n k hk]; split <;> decide

/-- **`rep(n)[k]`**, for every `k < 2n`: "a" at even positions, "b" at odd ones. -/
theorem rep_index (n k : Nat) (hk : k < 2 * n) (hk10 : k < 10 ^ 10) (strict : Bool) (s : State) :
    getRefValue (.prop (.str (reps n)) (.num (ofSmallInt (k : Int))) strict none) s =
      .ok (.str (if k % 2 = 0 then JSStr.ofString "a" else JSStr.ofString "b")) s := by
  rw [getRefValue_str_index (reps n) k (by rw [reps_length]; exact hk) hk10]
  have hr : reps n = JSStr.ofList (L n) := by rw [reps_eq]; rfl
  have hkl : k < (L n).length := by rw [L_length]; exact hk
  rw [hr, JSStr.slice_ofList (L n) (L_small n) k hkl, L_get n k hkl]
  split <;> rfl


/-! ## The whole script -/

open Script

abbrev l5 : F64 := F64.fin false 5629499534213120 (-50)
theorem l5_eq : l5 = ofSmallInt ((5 : Nat) : Int) := by decide
abbrev callRep : Sem.CExpr := Sem.call (Sem.identRef "rep") (Sem.args #[Sem.ArgD.expr (Sem.lit (Lit.num l5))]) false
  (CalleeDesc.ident "rep")
abbrev l3 : F64 := F64.fin false 6755399441055744 (-51)
theorem l3_eq : l3 = ofSmallInt ((3 : Nat) : Int) := by decide
abbrev lenStmt : Sem.CStmt := Sem.exprStmt (Sem.getValue (Sem.memberRef callRep (Sem.Key.computed (Sem.lit (Lit.num l3))) false))
theorem rep_same : RIGen.rep_func = RPGen.rep_func := rfl

theorem script_def (n : Nat) : RIGen.script n = Sem.stmts #[Sem.funDecl RIGen.rep_func, lenStmt] := rfl
theorem lexScoped : topLevelLexicallyScoped RIGen.script_stmts = #[] := by
  simp [topLevelLexicallyScoped, stmtLexScoped, RIGen.script_stmts]

def fs : List (Func × JSStr) := [(RIGen.rep_func, "rep")]

theorem varS : topLevelVarScoped RIGen.program.body = (fs.map fun p => VarScoped.func p.1).toArray := rfl
theorem lexS : topLevelLexicallyScoped RIGen.program.body =
    (([] : List JSStr).map fun x => LexScoped.binding .let (.ident x)).toArray := by
  rw [show RIGen.program.body = RIGen.script_stmts from rfl, lexScoped]; rfl
theorem annS : annexBFunctions RIGen.program.body ([] : List JSStr).toArray = #[] := rfl
theorem simpleS : ∀ p ∈ fs, Inst.SimpleFn p.1 p.2 := by
  intro p hp; simp only [fs, List.mem_cons, List.mem_nil_iff, or_false] at hp; rcases hp with rfl
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem nodupS : (fs.map Prod.snd).Nodup := by decide
theorem body_eq : RIGen.program.body = RIGen.script_stmts := rfl
theorem depth_eq : evalDepth = 999956 + 44 := rfl
theorem script_body (u : State) (c : Ctx) : evalStmts evalDepth c RIGen.program.body u = RIGen.script 999956 c u := by
  rw [RIGen.script_eq, body_eq, depth_eq]

/-- **`rep(5)[3]`**: asks the driver to call `rep`; when it returns `rep(5)`, the statement's value is "b". -/
theorem len_req (c : Ctx) (u : State) (r : Req) (K0 : Outcome → State → Res Value)
    (h0 : callRep (Sem.inner c) u = .req r u K0) (hK0 : ∀ v t, K0 (.normal v) t = .ok v t) :
    ∃ K, lenStmt c u = .req r u K ∧
      ∀ t, K (.normal (.str (reps 5))) t = .ok (.normal (some (.str (JSStr.ofString "b")))) t := by
  refine ⟨?K, ?h, ?_⟩
  case h =>
    conv =>
      lhs
      simp only [lenStmt, Sem.exprStmt, Sem.getValue, Sem.memberRef, M.bind_eq, M.bind_apply, h0, M.bindRes_req]
  intro t
  have hi := RepIndex.rep_index 5 3 (by decide) (by decide) c.strict t
  simp only [show (3 : Nat) % 2 = 0 ↔ False by decide, if_false] at hi
  rw [← l3_eq] at hi
  simp [hK0, Value.isNullish, Sem.lit, litValue, hi, M.bind_eq, M.bind_apply, pure, M.pure, Sem.inner]

/-- **The whole program** (examples/rep_index.js): `rep(5)[3]` evaluates to "b". Started from a realm whose global
object is an ordinary extensible object without `rep`. -/
theorem ri_script (eng : Engine) (s : State) (cs : Conts) (gb : Std.HashMap JSStr Binding) (gtv : Value)
    (fp : ObjId) (hge : s.curRealm.globalEnv < s.envs.size)
    (hE : s.envEntry s.curRealm.globalEnv = .global s.curRealm.globalObj gb gtv)
    (hgbs : gb.contains "rep" = false)
    (hgs : s.curRealm.globalObj < s.heap.size) (hk : (s.objEntry s.curRealm.globalObj).kind = .ordinary)
    (hx : (s.objEntry s.curRealm.globalObj).extensible = true)
    (hps : (s.objEntry s.curRealm.globalObj).props.get? (.str "rep") = none)
    (hfp : s.curRealm.intrinsics["%Function.prototype%"]? = some fp) (hf : 30 ≤ s.fuel) :
    ∃ s', (runM eng (scriptEvaluation RIGen.program) s cs).1 = .ok (.str (JSStr.ofString "b")) s' := by
  let ge := s.curRealm.globalEnv
  let g := s.curRealm.globalObj
  let c := scriptCtx s false
  obtain ⟨t0, ht0⟩ : ∃ y, (scriptStart s RIGen.program).setEnv ge (.global g (insertLets gb []) gtv) = y := ⟨_, rfl⟩
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
  let fR := s.heap.size
  obtain ⟨dR, hfRk, hcR, hrR, hmR, hclsR, -, -⟩ := hfuns 0 (by decide)
  rw [hz0] at hfRk hszu hnames
  simp only [fs, List.length_cons, List.length_nil] at hszu
  simp only [Nat.mul_zero, Nat.add_zero] at hfRk
  have hpR : (u.objEntry g).props.get? (.str "rep") = some (.data (.obj fR) true true false) := hnames 0 (by decide)
  have hE1 : u.envEntry ge = .global g gb gtv := by
    have h1 : u.envEntry ge = t0.envEntry ge := by simp only [State.envEntry, heu]
    rw [h1, ← ht0, State.setEnv_envEntry_self _ _ _ (show ge < (scriptStart s RIGen.program).envs.size from hge)]
    simp [insertLets]
  have hgeu : ge < u.envs.size := by rw [heu]; exact hge0
  have hgu : g < u.heap.size := by rw [hszu]; exact Nat.lt_of_lt_of_le hgs (Nat.le_add_right _ _)
  have hfRu : fR < u.heap.size := by show s.heap.size < u.heap.size; rw [hszu]; omega
  have hgbs' : gb[JSStr.ofString "rep"]? = none := Std.HashMap.getElem?_eq_none (fun hm => by
    rw [Std.HashMap.mem_iff_contains, hgbs] at hm; exact Bool.false_ne_true hm)
  have hgbsm : (JSStr.ofString "rep" ∈ gb) = False := by simp [Std.HashMap.mem_iff_contains, hgbs]
  -- `rep(5)` asks for its call
  obtain ⟨K0, h0, hK0⟩ := Stmts.call_expr_req (Sem.inner c) u ge g fR "rep" gb gtv dR
    [(Sem.lit (Lit.num l5), .num l5)]
    (by intro p hp; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp; rcases hp with rfl; rfl)
    rfl rfl hgeu hE1 hgbs hgbs' hgbsm hgu hku hpR hfRu hfRk (by rw [hfuu, hfu0]; omega)
  obtain ⟨K4, h4, hK4⟩ := len_req c u _ K0 h0 hK0
  -- the call (`rep_call`)
  obtain ⟨u', hu'⟩ : ∃ y, ({ u with fuel := u.fuel - 1 } : State) = y := ⟨_, rfl⟩
  have hr' : u'.realms = s.realms := by rw [← hu']; exact hru.trans hr0
  have hz' : u'.envs = u.envs := by rw [← hu']
  obtain ⟨s4, hc4⟩ := rep_call fR dR u' 5 g gb gtv (hcR.trans rep_same) hclsR hmR (by rw [hr', hrR, hrl0, hz']; exact hgeu)
    (by rw [hr', hrR, hrl0]; simp only [State.envEntry, hz']; exact hE1) (by decide)
    (by rw [← hu']; simp only; rw [hfuu, hfu0]; omega)
  have himpl : callImpl eng (.obj fR) .undefined #[.num l5] u = .ok (.str (reps 5)) s4 := by
    rw [l5_eq, callImpl_func eng fR dR _ _ u hfRu hfRk (by rw [hfuu, hfu0]; omega), hu']
    exact hc4
  -- the script
  refine ⟨s4, script_value eng s cs RIGen.program fs [] gb gtv fp _ s4 rfl varS lexS annS simpleS nodupS hge hE
    (by intro p hp; simp only [fs, List.mem_cons, List.mem_nil_iff, or_false] at hp; rcases hp with rfl; exact hgbs)
    (by simp) hgs hk hx
    (by intro p hp; simp only [fs, List.mem_cons, List.mem_nil_iff, or_false] at hp; rcases hp with rfl; exact hps)
    (by simp) hfp ?_⟩
  have hu0 : scriptState s RIGen.program fs [] gb gtv fp = u := by rw [← hu, ← ht0]; rfl
  rw [hu0, script_body, script_def]
  refine _root_.Runs.script_runs eng _ _ _ (_root_.Runs.stmts_run eng c _ u _ s4 ?_ (by simp; rw [hfuu, hfu0]; omega))
  show _root_.Runs.StmtsRun eng c [Sem.funDecl RIGen.rep_func, lenStmt] u none (some (.str (JSStr.ofString "b"))) s4
  refine .cons _ _ u u s4 none none _ (_root_.Runs.runs_funDecl eng _ c u rfl) ?_
  refine .cons _ _ u s4 s4 (some (.str (JSStr.ofString "b"))) none _ ?_ (.nil _ _)
  rw [h4]
  exact _root_.Runs.runsTo_req1 eng _ _ _ u K4 _ s4 _ s4 himpl (hK4 s4)

end RepIndex
