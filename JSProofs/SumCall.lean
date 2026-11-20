import JSProofs.Sum
import JSProofs.AddCall

/-!
# Calling `sum`: the full call returns 0 + 1 + … + (N − 1)

FunctionDeclarationInstantiation binds the parameter `n` in the function environment and creates
`s` and `i` (uninitialized) in a new lexical environment: exactly `SumProof.Shape … none none`, where
`SumProof.sum_spec` starts. Then the body (`evalFunctionBody`) and the [[Call]] (`callECMA`).
-/

open ES ES.Conv SumProof

namespace SumCall

theorem lexDecls : topLevelLexicallyScoped SumGen.sum_stmts =
    #[.binding .let (.ident "s"), .binding .let (.ident "i")] := by
  have hv : (VarKind.let == VarKind.var) = false := by decide
  simp [topLevelLexicallyScoped, stmtLexScoped, SumGen.sum_stmts, hv]
theorem names_s : (LexScoped.binding .let (.ident "s")).names = #[JSStr.ofString "s"] := by rfl
theorem names_i : (LexScoped.binding .let (.ident "i")).names = #[JSStr.ofString "i"] := by rfl

theorem ne_ns : (JSStr.ofString "n" = JSStr.ofString "s") = False := by simp; decide
theorem ne_ni : (JSStr.ofString "n" = JSStr.ofString "i") = False := by simp; decide

theorem sum_fdi (f : ObjId) (d : FuncData) (env : EnvId) (s : State) (N : Nat) (tv : Value)
    (hcode : d.code = SumGen.sum_func) (henv : env < s.envs.size)
    (hE : s.envEntry env = .func ∅ (some d.env) .initialized tv f .undefined)
    (hf : s.fuel ≠ 0) :
    ∃ ctx s', functionDeclarationInstantiation 999999 f d env #[num N] s = .ok ctx s' ∧
      ctx.lex = s.envs.size ∧ ctx.strict = false ∧ ctx.isGen = false ∧
      Shape s.envs.size env N none none s' ∧ s'.fuel = s.fuel ∧ s'.envs.size = s.envs.size + 1 := by
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
  have hbody : SumGen.sum_func.body = .stmts SumGen.sum_stmts := rfl
  have hparams : SumGen.sum_func.params = #[.mk (.ident "n") none false] := rfl
  have hstr : SumGen.sum_func.strict = false := rfl
  have hasync : SumGen.sum_func.isAsync = false := rfl
  have hgen : SumGen.sum_func.isGenerator = false := rfl
  have hkind : SumGen.sum_func.kind = .normal := rfl
  have hfdi : SumGen.sum_func.info.fdi = { paramNames := #["n"], hasDuplicates := false, varNames := #[], hasFunctions := false, functionNames := #[], hasLexical := true, lexNames := #["s", "i"], argumentsNeeded := false, hasAnnexB := false, usesDispose := false } := rfl
  have hk1 : (VarKind.let == VarKind.const) = false := by decide
  have hk2 : (VarKind.let == VarKind.using) = false := by decide
  have hk3 : (VarKind.let == VarKind.awaitUsing) = false := by decide
  have hphe : SumGen.sum_func.info.paramsHaveExpressions = false := rfl
  refine ⟨?c, ?t, ?h, ?_⟩
  case h =>
    conv =>
      lhs
      simp only [functionDeclarationInstantiation, hcode, hbody, hparams, hstr, hfdi, hasync, hgen, hkind, hphe]
      simp [hr, hasBinding_declLike, createMutableBinding_declLike, hbe, newDeclEnv, pure,
        M.pure, hE, henv, hf, lexDecls, names_s, names_i, -allocEnv_apply, allocEnv_eq, LexScoped.isConstant,
        State.pushEnv_entry_at, State.setEnv_envEntry_self, hk1, hk2, hk3]
  have hne : s.envs.size ≠ env := Nat.ne_of_gt henv
  have hne' : env ≠ s.envs.size := Nat.ne_of_lt henv
  refine ⟨rfl, rfl, rfl, ?_, by simp, by simp⟩
  refine ⟨by simp, by simp; exact Nat.lt_succ_of_lt henv, hne, ?_, ?_⟩
  · simp [State.setEnv_envEntry_self, Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert, ne_si, ne_is, ne_sn,
      ne_in]
  · simp [State.setEnv_envEntry_ne _ _ _ _ hne, State.pushEnv_entry_lt, State.setEnv_envEntry_self,
      henv, Std.HashMap.getElem?_modify]

/-- `sum`'s body, run as a call runs it: called with `N` in a fresh function environment, it returns
`N(N−1)/2`. -/
theorem sum_body (f : ObjId) (d : FuncData) (env : EnvId) (s : State) (N : Nat) (tv : Value)
    (hcode : d.code = SumGen.sum_func) (henv : env < s.envs.size)
    (hE : s.envEntry env = .func ∅ (some d.env) .initialized tv f .undefined)
    (hN : N < 2 ^ 26) (hf : N + 10 ≤ s.fuel) :
    ∃ s', evalFunctionBody evalDepth f d env #[num N] s = .ok (num ((N * (N - 1) / 2 : Nat) : Int)) s' := by
  obtain ⟨ctx, s', hfdi, hlex, hstr, hgen, hS, hfuel, -⟩ := sum_fdi f d env s N tv hcode henv hE (by omega)
  obtain ⟨s'', hbody⟩ := sum_interp_spec 999964 ctx s.envs.size env N hlex hstr hgen hN s' hS (by omega)
  refine ⟨s'', ?_⟩
  have hbd : d.code.body = .stmts SumGen.sum_stmts := by rw [hcode]; rfl
  have hdisp : d.code.info.fdi.usesDispose = false := by rw [hcode]; rfl
  simp only [evalDepth, evalFunctionBody, M.bind_eq, M.bind_apply, hfdi, M.bindRes_ok, hbd, hdisp,
    withDisposeScope]
  simp [hbody, pure, M.pure]

/-- **The [[Call]] of `sum`** with `this` undefined (a plain call `sum(N)`) returns `N(N−1)/2`, for every
natural `N < 2^26` given enough fuel. -/
theorem sum_call (f : ObjId) (d : FuncData) (s : State) (N : Nat) (go : ObjId)
    (gb : Std.HashMap JSStr Binding) (gtv : Value)
    (hcode : d.code = SumGen.sum_func) (hcls : d.isClassCtor = false) (hmode : d.thisMode = .global)
    (hge : (s.realms[d.realm]!).globalEnv < s.envs.size)
    (hgE : s.envEntry (s.realms[d.realm]!).globalEnv = .global go gb gtv)
    (hN : N < 2 ^ 26) (hf : N + 10 ≤ s.fuel) :
    ∃ s', callECMA f d .undefined #[num N] s = .ok (num ((N * (N - 1) / 2 : Nat) : Int)) s' ∧
      s'.realm = s.realm ∧ s'.script = s.script := by
  let ge := (s.realms[d.realm]!).globalEnv
  let s1 : State := { s with realm := d.realm, script := d.script }
  let env := s.envs.size
  let E0 : Env := .func {} (some d.env) .uninitialized .undefined f .undefined
  let s2 : State := { s1 with envs := s1.envs.push E0 }
  let s3 := s2.setEnv env (.func {} (some d.env) .initialized gtv f .undefined)
  have hgl : (ThisMode.global == ThisMode.lexical) = false := by decide
  have hgs : (ThisMode.global == ThisMode.strict) = false := by decide
  have hnew : newFunctionEnv f d .undefined s1 = .ok env s2 := by
    simp [hgl, newFunctionEnv, hmode, s2, s1, E0, env]
  have henv2 : env < s2.envs.size := by simp [s2, s1, env]
  have hge2 : ge < s2.envs.size := by simp [s2, s1]; exact Nat.lt_succ_of_lt hge
  have hgE2 : s2.envEntry ge = .global go gb gtv := by
    have hne : ge ≠ s.envs.size := Nat.ne_of_lt hge
    simp only [State.envEntry] at hgE ⊢
    simp [s2, s1, Array.getElem?_push, hne, ge] at hgE ⊢
    exact hgE
  have hbind : ordinaryCallBindThis d env .undefined s2 = .ok () s3 := by
    simp only [ordinaryCallBindThis, hmode]
    have hnn : (Value.undefined).isNullish = true := rfl
    have hui : (ThisStatus.uninitialized == ThisStatus.initialized) = false := by decide
    have hrl : (s2.realms[d.realm]!).globalEnv = ge := rfl
    simp [hgl, hgs, hnn, hui, M.bind_eq, M.bind_apply, bindThisValue, readEnv_entry _ _ _ henv2, pure, M.pure,
      modifyEnv_eq_setEnv _ _ _ henv2, s3, hrl, readEnv_entry _ _ _ hge2, hgE2]
    simp [hui, State.envEntry, s2, s1, E0, env, modifyEnv, State.setEnv]
  have henv3 : env < s3.envs.size := by simp [s3, s2, s1, env]
  have hE3 : s3.envEntry env = .func ∅ (some d.env) .initialized gtv f .undefined := by
    simp [s3, henv2]
  obtain ⟨s4, hbody⟩ := sum_body f d env s3 N gtv hcode henv3 hE3 hN (by simp [s3, s2, s1]; omega)
  have hasync : d.code.isAsync = false := by rw [hcode]; rfl
  have hgen : d.code.isGenerator = false := by rw [hcode]; rfl
  refine ⟨{ s4 with realm := s.realm, script := s.script }, ?_, rfl, rfl⟩
  simp only [callECMA, hcls, inCallee, M.bind_eq, M.bind_apply, M.readS_apply, M.bindRes_ok, M.modify_apply]
  simp [M.bind_apply, hnew, hbind, hasync, hgen, hbody, M.attempt, M.tryCatch_apply, pure, M.pure, s1]

end SumCall
