import Proofs.Iota
import Proofs.MoreCalls

/-!
# Calling `iota`: `iota(N)` returns a new array holding `0, …, N − 1`

FunctionDeclarationInstantiation binds `n` and declares `a` in a new lexical environment; the body
(`IotaProof.iota_interp_spec`); the [[Call]] (`Calls.callECMA_undef`). The call also states what it
leaves alone, for a caller that goes on: the caller's environments and older objects, the realms.
-/

open ES ES.Conv SumProof IotaProof

namespace IotaCall

theorem lexIota : topLevelLexicallyScoped IotaGen.iota_stmts = #[.binding .let (.ident "a")] := by
  have hv : (VarKind.let == VarKind.var) = false := by decide
  simp [topLevelLexicallyScoped, stmtLexScoped, IotaGen.iota_stmts, hv]

/-- The facts about a function's code that `iota`'s proofs use (its source span and id may differ). -/
def IsIota (c : Func) : Prop :=
  c.body = .stmts IotaGen.iota_stmts ∧ c.params = #[.mk (.ident "n") none false] ∧ c.strict = false ∧
  c.isAsync = false ∧ c.isGenerator = false ∧ c.kind = .normal ∧
  c.info.fdi = { paramNames := #["n"], hasDuplicates := false, varNames := #[], hasFunctions := false, functionNames := #[], hasLexical := true, lexNames := #["a"], argumentsNeeded := false, hasAnnexB := false, usesDispose := false } ∧
  c.info.paramsHaveExpressions = false

theorem isIota_iota : IsIota IotaGen.iota_func := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem ne_an' : (JSStr.ofString "a" = JSStr.ofString "n") = False := by simp; decide

theorem iota_fdi (f : ObjId) (d : FuncData) (env : EnvId) (s : State) (N : Nat) (tv : Value)
    (hcode : IsIota d.code) (henv : env < s.envs.size)
    (hE : s.envEntry env = .func ∅ (some d.env) .initialized tv f .undefined)
    (hf : s.fuel ≠ 0) :
    ∃ ctx s', functionDeclarationInstantiation 999999 f d env #[num N] s = .ok ctx s' ∧
      ctx.lex = s.envs.size ∧ ctx.strict = false ∧ ctx.isGen = false ∧
      s.envs.size < s'.envs.size ∧ env < s'.envs.size ∧
      s'.envEntry s.envs.size = .decl ((∅ : Std.HashMap JSStr Binding).insert "a" { deletable := false }) (some env) ∧
      (∃ bF o ts tv fo nt bn, s'.envEntry env = .func bF o ts tv fo nt ∧ bF[JSStr.ofString "n"]? = some bn ∧
        bn.value = some (num N)) ∧
      s'.fuel = s.fuel ∧ s'.heap = s.heap ∧ s'.realms = s.realms ∧ s'.realm = s.realm ∧
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
  obtain ⟨hbody, hparams, hstr, hasync, hgen, hkind, hfdi, hphe⟩ := hcode
  have hk1 : (VarKind.let == VarKind.const) = false := by decide
  have hk2 : (VarKind.let == VarKind.using) = false := by decide
  have hk3 : (VarKind.let == VarKind.awaitUsing) = false := by decide
  refine ⟨?c, ?t, ?h, ?_⟩
  case h =>
    conv =>
      lhs
      simp only [functionDeclarationInstantiation, hbody, hparams, hstr, hfdi, hasync, hgen, hkind, hphe]
      simp [hr, hasBinding_declLike, createMutableBinding_declLike, hbe, newDeclEnv, pure,
        M.pure, hE, henv, hf, lexIota, MoreCalls.names_a, -allocEnv_apply, allocEnv_eq, LexScoped.isConstant,
        State.pushEnv_entry_at, State.setEnv_envEntry_self, hk1, hk2, hk3]
  have hne : s.envs.size ≠ env := Nat.ne_of_gt henv
  refine ⟨rfl, rfl, rfl, by simp, by simp; exact Nat.lt_succ_of_lt henv, by simp [State.setEnv_envEntry_self], ?_,
    by simp, by simp [State.setEnv, State.pushEnv], by simp [State.setEnv, State.pushEnv],
    by simp [State.setEnv, State.pushEnv], ?_⟩
  · simp [State.setEnv_envEntry_ne _ _ _ _ hne, State.pushEnv_entry_lt, State.setEnv_envEntry_self,
      henv, Std.HashMap.getElem?_modify]
  · intro e he hee
    simp [State.setEnv_envEntry_ne _ _ _ _ (show s.envs.size ≠ e by omega), State.pushEnv_entry_lt, he,
      State.setEnv_envEntry_ne _ _ _ _ (Ne.symm hee)]

/-- `iota`'s body as a call runs it: returns the next object, the array `0, …, N − 1`. -/
theorem iota_body (f : ObjId) (d : FuncData) (env : EnvId) (s : State) (N : Nat) (tv : Value)
    (hcode : IsIota d.code) (henv : env < s.envs.size)
    (hE : s.envEntry env = .func ∅ (some d.env) .initialized tv f .undefined) (hN : N < 2 ^ 26)
    (hP : ∀ j < N, AbsentChain s 2 s.curRealm.arrayProto (PropKey.ofNat j)) (hf : N + 12 ≤ s.fuel) :
    ∃ s', evalFunctionBody evalDepth f d env #[num N] s = .ok (.obj s.heap.size) s' ∧
      ArrayObj s.heap.size N (fun j => num j) s' ∧
      s.envs.size ≤ s'.envs.size ∧ (∀ e, e < s.envs.size → e ≠ env → s'.envEntry e = s.envEntry e) ∧
      s'.heap.size = s.heap.size + 1 ∧ (∀ x, x < s.heap.size → s'.objEntry x = s.objEntry x) ∧
      s'.realms = s.realms ∧ s'.fuel + N + 1 = s.fuel := by
  obtain ⟨ctx, s1, hfdi, hlex, hstr, hgen, hlt1, henv1, hL1, hF1, hfu1, hh1, hr1, hrl1, hfe1⟩ :=
    iota_fdi f d env s N tv hcode henv hE (by omega)
  have hcr : s1.curRealm = s.curRealm := by simp only [State.curRealm, hr1, hrl1]
  have ho1 : ∀ x, s1.objEntry x = s.objEntry x := by intro x; simp [State.objEntry, hh1]
  have hP1 : ∀ j < N, AbsentChain s1 2 s1.curRealm.arrayProto (PropKey.ofNat j) := fun j hj => by
    rw [hcr]; exact absentChain_mono s s1 _ (fun x _ => ho1 x) (by rw [hh1]; exact Nat.le_refl _) 2 _ (hP j hj)
  have hLF : s.envs.size ≠ env := Nat.ne_of_gt henv
  obtain ⟨s2, hbody, hA, hz, hfe, hhs, ho, hrr, hfu⟩ := iota_interp_spec 999964 ctx s.envs.size env N hlex hstr hgen hN
    s1 hlt1 henv1 hLF _ { deletable := false } hL1 (by simp)
    (by simp [Std.HashMap.getElem?_insert, ne_an']) (by simp [Std.HashMap.getElem?_insert, IotaProof.ne_ai]) hF1 hP1
    (by omega)
  rw [hh1] at hbody hA hhs ho
  refine ⟨s2, ?_, hA, Nat.le_trans (Nat.le_of_lt hlt1) hz,
    fun e he hee => (hfe e (Nat.lt_trans he hlt1) (Nat.ne_of_lt he)).trans (hfe1 e he hee),
    hhs, fun x hx => (ho x hx).trans (ho1 x), hrr.trans hr1, by rw [hfu, hfu1]⟩
  have hbd : d.code.body = .stmts IotaGen.iota_stmts := hcode.1
  have hdisp : d.code.info.fdi.usesDispose = false := by rw [hcode.2.2.2.2.2.2.1]
  simp only [evalDepth, evalFunctionBody, M.bind_eq, M.bind_apply, hfdi, M.bindRes_ok, hbd, hdisp, withDisposeScope]
  simp [hbody, pure, M.pure]

/-- **The [[Call]] of `iota`** with `this` undefined: returns a new array (the next object) holding
`0, …, N − 1`, provided `Array.prototype`'s chain (in the callee's realm) has no index property below
`N`. It leaves the caller's environments, the older objects and the realms as they were, and uses
`N + 1` fuel. -/
theorem iota_call (f : ObjId) (d : FuncData) (s : State) (N : Nat) (go : ObjId)
    (gb : Std.HashMap JSStr Binding) (gtv : Value)
    (hcode : IsIota d.code) (hcls : d.isClassCtor = false) (hmode : d.thisMode = .global)
    (hge : (s.realms[d.realm]!).globalEnv < s.envs.size)
    (hgE : s.envEntry (s.realms[d.realm]!).globalEnv = .global go gb gtv) (hN : N < 2 ^ 26)
    (hP : ∀ j < N, AbsentChain s 2 (s.realms[d.realm]!).arrayProto (PropKey.ofNat j)) (hf : N + 12 ≤ s.fuel) :
    ∃ s', callECMA f d .undefined #[num N] s = .ok (.obj s.heap.size) s' ∧ s'.realm = s.realm ∧
      s'.script = s.script ∧ ArrayObj s.heap.size N (fun j => num j) s' ∧
      s.envs.size ≤ s'.envs.size ∧ (∀ e, e < s.envs.size → s'.envEntry e = s.envEntry e) ∧
      s'.heap.size = s.heap.size + 1 ∧ (∀ x, x < s.heap.size → s'.objEntry x = s.objEntry x) ∧
      s'.realms = s.realms ∧ s'.fuel + N + 1 = s.fuel := by
  obtain ⟨s', h1, h2, h3, t', hQ, hh, hen, hfe, hrs⟩ := Calls.callECMA_undef
    (Q := fun t => ArrayObj s.heap.size N (fun j => num j) t ∧ s.envs.size ≤ t.envs.size ∧
      (∀ e, e < s.envs.size → t.envEntry e = s.envEntry e) ∧ t.heap.size = s.heap.size + 1 ∧
      (∀ x, x < s.heap.size → t.objEntry x = s.objEntry x) ∧ t.realms = s.realms ∧ t.fuel + N + 1 = s.fuel)
    f d s _ _ go gb gtv hcls hmode hcode.2.2.2.1 hcode.2.2.2.2.1 hge hgE
    (fun t hlt hEt hold hheap hfu hrl hrlm => by
      have ho : ∀ x, t.objEntry x = s.objEntry x := by intro x; simp [State.objEntry, hheap]
      have hPt : ∀ j < N, AbsentChain t 2 t.curRealm.arrayProto (PropKey.ofNat j) := fun j hj => by
        have hc : t.curRealm = s.realms[d.realm]! := by simp only [State.curRealm, hrl, hrlm]
        rw [hc]; exact absentChain_mono s t _ (fun x _ => ho x) (by rw [hheap]; exact Nat.le_refl _) 2 _ (hP j hj)
      obtain ⟨t', hb, hA, hz, hfe, hhs, hoo, hrr, hfu'⟩ := iota_body f d s.envs.size t N gtv hcode hlt hEt hN hPt
        (by omega)
      rw [hheap] at hb hA hhs hoo
      exact ⟨t', hb, hA, Nat.le_trans (Nat.le_of_lt hlt) hz,
        fun e he => (hfe e (Nat.lt_trans he hlt) (Nat.ne_of_lt he)).trans (hold e he), hhs,
        fun x hx => (hoo x hx).trans (ho x), hrr.trans hrl, by rw [hfu', hfu]⟩)
  obtain ⟨q1, q2, q3, q4, q5, q6, q7⟩ := hQ
  have hoe : ∀ x, s'.objEntry x = t'.objEntry x := by intro x; simp [State.objEntry, hh]
  refine ⟨s', h1, h2, h3, MoreCalls.arrayObj_of_heap _ N _ t' s' hh q1, by rw [hen]; exact q2,
    fun e he => by simp only [State.envEntry, hen]; exact q3 e he, by rw [hh]; exact q4,
    fun x hx => (hoe x).trans (q5 x hx), hrs.trans q6, by rw [hfe]; exact q7⟩

end IotaCall
