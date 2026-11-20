import JSProofs.TotalCall
import JSProofs.Double
import JSProofs.ArrayWriteEx

/-!
# Calling `sumFor`, `double`, and `f`

As for `total` (Proofs/TotalCall.lean): FunctionDeclarationInstantiation gives the shape each body
proof starts from; the body through `evalFunctionBody`; the [[Call]] through `Calls.callECMA_undef`.
-/

open ES ES.Conv SumProof SumForProof TotalProof DoubleProof

namespace MoreCalls

theorem lexSumFor : topLevelLexicallyScoped SumForGen.sumFor_stmts = #[.binding .let (.ident "s")] := by
  have hv : (VarKind.let == VarKind.var) = false := by decide
  simp [topLevelLexicallyScoped, stmtLexScoped, SumForGen.sumFor_stmts, hv]

theorem lexF : topLevelLexicallyScoped ArrayWriteGen.f_stmts = #[.binding .let (.ident "a")] := by
  have hv : (VarKind.let == VarKind.var) = false := by decide
  simp [topLevelLexicallyScoped, stmtLexScoped, ArrayWriteGen.f_stmts, hv]

theorem names_a : (LexScoped.binding .let (.ident "a")).names = #[JSStr.ofString "a"] := by rfl

/-- The facts about a function's code that `double`'s proofs use (its source span and id may differ). -/
def IsDouble (c : Func) : Prop :=
  c.body = .stmts DoubleGen.double_stmts ∧ c.params = #[.mk (.ident "a") none false] ∧ c.strict = false ∧
  c.isAsync = false ∧ c.isGenerator = false ∧ c.kind = .normal ∧
  c.info.fdi = { paramNames := #["a"], hasDuplicates := false, varNames := #[], hasFunctions := false, functionNames := #[], hasLexical := false, lexNames := #[], argumentsNeeded := false, hasAnnexB := false, usesDispose := false } ∧
  c.info.paramsHaveExpressions = false

theorem isDouble_double : IsDouble DoubleGen.double_func := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem ne_sn' : (JSStr.ofString "s" = JSStr.ofString "n") = False := by simp; decide

theorem sumFor_fdi (f : ObjId) (d : FuncData) (env : EnvId) (s : State) (N : Nat) (tv : Value)
    (hcode : d.code = SumForGen.sumFor_func) (henv : env < s.envs.size)
    (hE : s.envEntry env = .func ∅ (some d.env) .initialized tv f .undefined)
    (hf : s.fuel ≠ 0) :
    ∃ ctx s', functionDeclarationInstantiation 999999 f d env #[num N] s = .ok ctx s' ∧
      ctx.lex = s.envs.size ∧ ctx.strict = false ∧ ctx.isGen = false ∧
      ShapeB s.envs.size env N none s' ∧ s'.fuel = s.fuel ∧ s'.heap = s.heap ∧
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
  have hbody : SumForGen.sumFor_func.body = .stmts SumForGen.sumFor_stmts := rfl
  have hparams : SumForGen.sumFor_func.params = #[.mk (.ident "n") none false] := rfl
  have hstr : SumForGen.sumFor_func.strict = false := rfl
  have hasync : SumForGen.sumFor_func.isAsync = false := rfl
  have hgen : SumForGen.sumFor_func.isGenerator = false := rfl
  have hkind : SumForGen.sumFor_func.kind = .normal := rfl
  have hfdi : SumForGen.sumFor_func.info.fdi = { paramNames := #["n"], hasDuplicates := false, varNames := #[], hasFunctions := false, functionNames := #[], hasLexical := true, lexNames := #["s"], argumentsNeeded := false, hasAnnexB := false, usesDispose := false } := rfl
  have hk1 : (VarKind.let == VarKind.const) = false := by decide
  have hk2 : (VarKind.let == VarKind.using) = false := by decide
  have hk3 : (VarKind.let == VarKind.awaitUsing) = false := by decide
  have hphe : SumForGen.sumFor_func.info.paramsHaveExpressions = false := rfl
  refine ⟨?c, ?t, ?h, ?_⟩
  case h =>
    conv =>
      lhs
      simp only [functionDeclarationInstantiation, hcode, hbody, hparams, hstr, hfdi, hasync, hgen, hkind, hphe]
      simp [hr, hasBinding_declLike, createMutableBinding_declLike, hbe, newDeclEnv, pure,
        M.pure, hE, henv, hf, lexSumFor, TotalCall.names_s, -allocEnv_apply, allocEnv_eq, LexScoped.isConstant,
        State.pushEnv_entry_at, State.setEnv_envEntry_self, hk1, hk2, hk3]
  have hne : s.envs.size ≠ env := Nat.ne_of_gt henv
  have hne' : env ≠ s.envs.size := Nat.ne_of_lt henv
  refine ⟨rfl, rfl, rfl, ?_, by simp, by simp [State.setEnv, State.pushEnv], ?_⟩
  · refine ⟨by simp, by simp; exact Nat.lt_succ_of_lt henv, hne, ?_, ?_⟩
    · simp [State.setEnv_envEntry_self, Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert, ne_sn', ne_is, ne_in, ne_si]
    · simp [State.setEnv_envEntry_ne _ _ _ _ hne, State.pushEnv_entry_lt, State.setEnv_envEntry_self,
        henv, Std.HashMap.getElem?_modify]
  · intro e he hee
    simp [State.setEnv_envEntry_ne _ _ _ _ (show s.envs.size ≠ e by omega), State.pushEnv_entry_lt, he,
      State.setEnv_envEntry_ne _ _ _ _ (Ne.symm hee)]

theorem double_fdi (f : ObjId) (d : FuncData) (env : EnvId) (s : State) (A : ObjId) (tv : Value)
    (hcode : IsDouble d.code) (henv : env < s.envs.size)
    (hE : s.envEntry env = .func ∅ (some d.env) .initialized tv f .undefined)
    (hf : s.fuel ≠ 0) :
    ∃ ctx s', functionDeclarationInstantiation 999999 f d env #[.obj A] s = .ok ctx s' ∧
      ctx.lex = s.envs.size ∧ ctx.strict = false ∧ ctx.isGen = false ∧
      ShapeBD s.envs.size env A s' ∧ s'.fuel = s.fuel ∧ s'.heap = s.heap ∧ s'.realms = s.realms ∧
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
        M.pure, hE, henv, hf, -allocEnv_apply, allocEnv_eq, LexScoped.isConstant,
        State.pushEnv_entry_at, State.setEnv_envEntry_self, hk1, hk2, hk3]
  have hne : s.envs.size ≠ env := Nat.ne_of_gt henv
  have hne' : env ≠ s.envs.size := Nat.ne_of_lt henv
  refine ⟨rfl, rfl, rfl, ?_, by simp, by simp [State.setEnv, State.pushEnv], by simp [State.setEnv, State.pushEnv], ?_⟩
  · refine ⟨by simp, by simp; exact Nat.lt_succ_of_lt henv, hne, ?_, ?_⟩
    · simp [State.pushEnv_entry_at]
    · simp [State.setEnv_envEntry_ne _ _ _ _ hne, State.pushEnv_entry_lt, State.setEnv_envEntry_self,
        henv, Std.HashMap.getElem?_modify]
  · intro e he hee
    simp [State.setEnv_envEntry_ne _ _ _ _ (show s.envs.size ≠ e by omega), State.pushEnv_entry_lt, he,
      State.setEnv_envEntry_ne _ _ _ _ (Ne.symm hee)]

theorem f_fdi (f : ObjId) (d : FuncData) (env : EnvId) (s : State) (tv : Value)
    (hcode : d.code = ArrayWriteGen.f_func) (henv : env < s.envs.size)
    (hE : s.envEntry env = .func ∅ (some d.env) .initialized tv f .undefined)
    (hf : s.fuel ≠ 0) :
    ∃ ctx s', functionDeclarationInstantiation 999999 f d env #[] s = .ok ctx s' ∧
      ctx.lex = s.envs.size ∧ ctx.strict = false ∧ ctx.isGen = false ∧
      (s.envs.size < s'.envs.size ∧ s'.envEntry s.envs.size = .decl ((∅ : Std.HashMap JSStr Binding).insert "a" { deletable := false }) (some env)) ∧ s'.fuel = s.fuel ∧ s'.heap = s.heap ∧
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
  have hbody : ArrayWriteGen.f_func.body = .stmts ArrayWriteGen.f_stmts := rfl
  have hparams : ArrayWriteGen.f_func.params = #[] := rfl
  have hstr : ArrayWriteGen.f_func.strict = false := rfl
  have hasync : ArrayWriteGen.f_func.isAsync = false := rfl
  have hgen : ArrayWriteGen.f_func.isGenerator = false := rfl
  have hkind : ArrayWriteGen.f_func.kind = .normal := rfl
  have hfdi : ArrayWriteGen.f_func.info.fdi = { paramNames := #[], hasDuplicates := false, varNames := #[], hasFunctions := false, functionNames := #[], hasLexical := true, lexNames := #["a"], argumentsNeeded := false, hasAnnexB := false, usesDispose := false } := rfl
  have hk1 : (VarKind.let == VarKind.const) = false := by decide
  have hk2 : (VarKind.let == VarKind.using) = false := by decide
  have hk3 : (VarKind.let == VarKind.awaitUsing) = false := by decide
  have hphe : ArrayWriteGen.f_func.info.paramsHaveExpressions = false := rfl
  refine ⟨?c, ?t, ?h, ?_⟩
  case h =>
    conv =>
      lhs
      simp only [functionDeclarationInstantiation, hcode, hbody, hparams, hstr, hfdi, hasync, hgen, hkind, hphe]
      simp [hr, hasBinding_declLike, createMutableBinding_declLike, hbe, newDeclEnv, pure,
        M.pure, hE, henv, hf, lexF, names_a, -allocEnv_apply, allocEnv_eq, LexScoped.isConstant,
        State.pushEnv_entry_at, State.setEnv_envEntry_self, hk1, hk2, hk3]
  have hne : s.envs.size ≠ env := Nat.ne_of_gt henv
  have hne' : env ≠ s.envs.size := Nat.ne_of_lt henv
  refine ⟨rfl, rfl, rfl, ⟨by simp, by simp [State.setEnv_envEntry_self]⟩, by simp, by simp [State.setEnv, State.pushEnv], ?_⟩
  intro e he hee
  simp [State.setEnv_envEntry_ne _ _ _ _ (show s.envs.size ≠ e by omega), State.pushEnv_entry_lt, he]

/-- `sumFor`'s body as a call runs it: returns N(N−1)/2. -/
theorem sumFor_body (f : ObjId) (d : FuncData) (env : EnvId) (s : State) (N : Nat) (tv : Value)
    (hcode : d.code = SumForGen.sumFor_func) (henv : env < s.envs.size)
    (hE : s.envEntry env = .func ∅ (some d.env) .initialized tv f .undefined)
    (hN : N < 2 ^ 26) (hf : N + 12 ≤ s.fuel) :
    ∃ s', evalFunctionBody evalDepth f d env #[num N] s = .ok (num ((N * (N - 1) / 2 : Nat) : Int)) s' := by
  obtain ⟨ctx, s', hfdi, hlex, hstr, hgen, hS, hfuel, -, -⟩ := sumFor_fdi f d env s N tv hcode henv hE (by omega)
  obtain ⟨s'', hbody⟩ := sumFor_interp_spec 999964 ctx s.envs.size env N hlex hstr hgen hN s' hS (by omega)
  refine ⟨s'', ?_⟩
  have hbd : d.code.body = .stmts SumForGen.sumFor_stmts := by rw [hcode]; rfl
  have hdisp : d.code.info.fdi.usesDispose = false := by rw [hcode]; rfl
  simp only [evalDepth, evalFunctionBody, M.bind_eq, M.bind_apply, hfdi, M.bindRes_ok, hbd, hdisp, withDisposeScope]
  simp [hbody, pure, M.pure]

/-- **The [[Call]] of `sumFor`** with `this` undefined: returns N(N−1)/2. -/
theorem sumFor_call (f : ObjId) (d : FuncData) (s : State) (N : Nat) (go : ObjId)
    (gb : Std.HashMap JSStr Binding) (gtv : Value)
    (hcode : d.code = SumForGen.sumFor_func) (hcls : d.isClassCtor = false) (hmode : d.thisMode = .global)
    (hge : (s.realms[d.realm]!).globalEnv < s.envs.size)
    (hgE : s.envEntry (s.realms[d.realm]!).globalEnv = .global go gb gtv)
    (hN : N < 2 ^ 26) (hf : N + 12 ≤ s.fuel) :
    ∃ s', callECMA f d .undefined #[num N] s = .ok (num ((N * (N - 1) / 2 : Nat) : Int)) s' ∧
      s'.realm = s.realm ∧ s'.script = s.script :=
  let ⟨s', h1, h2, h3, _⟩ := Calls.callECMA_undef (Q := fun _ => True) f d s _ _ go gb gtv hcls hmode
    (by rw [hcode]; rfl) (by rw [hcode]; rfl) hge hgE
    (fun t hlt hEt _ _ hfu _ _ =>
      let ⟨t', ht'⟩ := sumFor_body f d s.envs.size t N gtv hcode hlt hEt hN (by omega)
      ⟨t', ht', trivial⟩)
  ⟨s', h1, h2, h3⟩

theorem arrayObj_of_heap (A : ObjId) (len : Nat) (xs : Nat → Value) (t u : State) (h : u.heap = t.heap)
    (hA : ArrayObj A len xs t) : ArrayObj A len xs u := by
  have ho : ∀ o, u.objEntry o = t.objEntry o := by intro o; simp [State.objEntry, h]
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hA
  exact ⟨by rw [h]; exact a1, by rw [ho]; exact a2, by rw [ho]; exact a3, by rw [ho]; exact a4,
    fun j hj => by rw [ho]; exact a5 j hj, fun j hj hjb => by rw [ho]; exact a6 j hj hjb⟩

/-- `double`'s body as a call runs it: returns `undefined`, every element doubled. -/
theorem double_body (f : ObjId) (d : FuncData) (env : EnvId) (s : State) (A : ObjId) (len : Nat) (xs : Nat → Nat)
    (tv : Value) (hcode : IsDouble d.code) (henv : env < s.envs.size)
    (hE : s.envEntry env = .func ∅ (some d.env) .initialized tv f .undefined)
    (hlen : len < 2 ^ 26) (hx : ∀ j < len, xs j < 2 ^ 26) (hA : ArrayObj A len (fun j => num (xs j)) s)
    (hf : len + 12 ≤ s.fuel) :
    ∃ s', evalFunctionBody evalDepth f d env #[.obj A] s = .ok .undefined s' ∧
      ArrayObj A len (fun j => num ((2 * xs j : Nat) : Int)) s' ∧
      s.envs.size ≤ s'.envs.size ∧ (∀ e < s.envs.size, e ≠ env → s'.envEntry e = s.envEntry e) ∧
      s'.heap.size = s.heap.size ∧ (∀ o, o ≠ A → s'.objEntry o = s.objEntry o) ∧ s'.fuel + len + 1 = s.fuel ∧
      s'.realms = s.realms := by
  obtain ⟨ctx, s', hfdi, hlex, hstr, hgen, hS, hfuel, hheap, hrl, hfe⟩ := double_fdi f d env s A tv hcode henv hE (by omega)
  obtain ⟨w, s'', hbody, hA'', hfr, hfu⟩ := double_interp_spec 999964 ctx s.envs.size env A len xs hlex hstr hlen hx s' hS
    (arrayObj_of_heap A len _ s s' hheap hA) (by omega)
  have hL := hS.1
  refine ⟨s'', ?_, hA'', Nat.le_of_lt (Nat.lt_of_lt_of_le hL hfr.1),
    fun e he hne => (hfr.2.1 e (Nat.lt_trans he hL)).trans (hfe e he hne),
    hfr.2.2.1.trans (by rw [hheap]), fun o ho => (hfr.2.2.2.1 o ho).trans (by simp [State.objEntry, hheap]),
    by rw [hfu, hfuel], hfr.2.2.2.2.trans hrl⟩
  have hbd : d.code.body = .stmts DoubleGen.double_stmts := hcode.1
  have hdisp : d.code.info.fdi.usesDispose = false := by rw [hcode.2.2.2.2.2.2.1]
  simp only [evalDepth, evalFunctionBody, M.bind_eq, M.bind_apply, hfdi, M.bindRes_ok, hbd, hdisp, withDisposeScope]
  simp [hbody, pure, M.pure]

/-- **The [[Call]] of `double`**: returns `undefined`, and afterwards the array holds every element doubled. -/
theorem double_call (f : ObjId) (d : FuncData) (s : State) (A : ObjId) (len : Nat) (xs : Nat → Nat) (go : ObjId)
    (gb : Std.HashMap JSStr Binding) (gtv : Value)
    (hcode : IsDouble d.code) (hcls : d.isClassCtor = false) (hmode : d.thisMode = .global)
    (hge : (s.realms[d.realm]!).globalEnv < s.envs.size)
    (hgE : s.envEntry (s.realms[d.realm]!).globalEnv = .global go gb gtv)
    (hlen : len < 2 ^ 26) (hx : ∀ j < len, xs j < 2 ^ 26) (hA : ArrayObj A len (fun j => num (xs j)) s)
    (hf : len + 12 ≤ s.fuel) :
    ∃ s', callECMA f d .undefined #[.obj A] s = .ok .undefined s' ∧ s'.realm = s.realm ∧ s'.script = s.script ∧
      ArrayObj A len (fun j => num ((2 * xs j : Nat) : Int)) s' ∧ Frame A s s' ∧ s'.fuel + len + 1 = s.fuel := by
  obtain ⟨s', h1, h2, h3, t', hQ, hh, hen, hfe, hrs⟩ := Calls.callECMA_undef
    (Q := fun t => ArrayObj A len (fun j => num ((2 * xs j : Nat) : Int)) t ∧ Frame A s t ∧ t.fuel + len + 1 = s.fuel)
    f d s _ _ go gb gtv
    hcls hmode hcode.2.2.2.1 hcode.2.2.2.2.1 hge hgE
    (fun t hlt hEt hold hheap hfu hrl _ => by
      obtain ⟨t', hb, hA', hz, hfe, hh', ho, hfu', hrl'⟩ := double_body f d s.envs.size t A len xs gtv hcode hlt hEt hlen hx
        (arrayObj_of_heap A len _ s t hheap hA) (by omega)
      refine ⟨t', hb, hA', ⟨Nat.le_trans (Nat.le_of_lt hlt) hz,
        fun e he => (hfe e (Nat.lt_trans he hlt) (Nat.ne_of_lt he)).trans (hold e he),
        hh'.trans (by rw [hheap]), fun o hoA => (ho o hoA).trans (by simp [State.objEntry, hheap]),
        hrl'.trans hrl⟩,
        by rw [hfu', hfu]⟩)
  obtain ⟨hQA, ⟨hQ1, hQ2, hQ3, hQ4, hQ6⟩, hQ5⟩ := hQ
  exact ⟨s', h1, h2, h3, arrayObj_of_heap A len _ t' s' hh hQA,
    ⟨by rw [hen]; exact hQ1, fun e he => by simp only [State.envEntry, hen]; exact hQ2 e he,
      by rw [hh]; exact hQ3, fun o ho => by simp only [State.objEntry, hh]; exact hQ4 o ho, by rw [hrs]; exact hQ6⟩,
    by rw [hfe]; exact hQ5⟩

/-- `f`'s body as a call runs it: returns 9. -/
theorem f_body (fo : ObjId) (d : FuncData) (env : EnvId) (s : State) (tv : Value)
    (hcode : d.code = ArrayWriteGen.f_func) (henv : env < s.envs.size)
    (hE : s.envEntry env = .func ∅ (some d.env) .initialized tv fo .undefined) (hf : 4 ≤ s.fuel) :
    ∃ s', evalFunctionBody evalDepth fo d env #[] s = .ok (.num (ofSmallInt 9)) s' := by
  obtain ⟨ctx, s', hfdi, hlex, hstr, hgen, ⟨hl, hL⟩, hfuel, -, -⟩ := f_fdi fo d env s tv hcode henv hE (by omega)
  obtain ⟨s'', hbody⟩ := ArrayWriteEx.f_interp_spec 999961 ctx s.envs.size (some env) _ { deletable := false }
    hlex hstr hgen s' hl hL (by simp) rfl (by omega)
  refine ⟨s'', ?_⟩
  have hbd : d.code.body = .stmts ArrayWriteGen.f_stmts := by rw [hcode]; rfl
  have hdisp : d.code.info.fdi.usesDispose = false := by rw [hcode]; rfl
  simp only [evalDepth, evalFunctionBody, M.bind_eq, M.bind_apply, hfdi, M.bindRes_ok, hbd, hdisp, withDisposeScope]
  simp [hbody, pure, M.pure]

/-- **The [[Call]] of `f`**: returns 9. -/
theorem f_call (fo : ObjId) (d : FuncData) (s : State) (go : ObjId) (gb : Std.HashMap JSStr Binding) (gtv : Value)
    (hcode : d.code = ArrayWriteGen.f_func) (hcls : d.isClassCtor = false) (hmode : d.thisMode = .global)
    (hge : (s.realms[d.realm]!).globalEnv < s.envs.size)
    (hgE : s.envEntry (s.realms[d.realm]!).globalEnv = .global go gb gtv) (hf : 4 ≤ s.fuel) :
    ∃ s', callECMA fo d .undefined #[] s = .ok (.num (ofSmallInt 9)) s' ∧ s'.realm = s.realm ∧ s'.script = s.script :=
  let ⟨s', h1, h2, h3, _⟩ := Calls.callECMA_undef (Q := fun _ => True) fo d s _ _ go gb gtv hcls hmode
    (by rw [hcode]; rfl) (by rw [hcode]; rfl) hge hgE
    (fun t hlt hEt _ _ hfu _ _ =>
      let ⟨t', ht'⟩ := f_body fo d s.envs.size t gtv hcode hlt hEt (by omega)
      ⟨t', ht', trivial⟩)
  ⟨s', h1, h2, h3⟩

end MoreCalls
