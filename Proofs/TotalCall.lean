import Proofs.Total
import Proofs.Calls

/-!
# Calling `total`: `total(a)` returns the sum of `a`'s elements

FunctionDeclarationInstantiation binds `a` to the array and creates `s` (uninitialized): the shape
`TotalProof.total_spec` starts from. Then the body and the [[Call]] (`Calls.callECMA_undef`).
-/

open ES ES.Conv SumProof SumForProof TotalProof

namespace TotalCall

theorem lexDecls : topLevelLexicallyScoped TotalGen.total_stmts = #[.binding .let (.ident "s")] := by
  have hv : (VarKind.let == VarKind.var) = false := by decide
  simp [topLevelLexicallyScoped, stmtLexScoped, TotalGen.total_stmts, hv]

theorem names_s : (LexScoped.binding .let (.ident "s")).names = #[JSStr.ofString "s"] := by rfl

theorem total_fdi (f : ObjId) (d : FuncData) (env : EnvId) (s : State) (A : ObjId) (tv : Value)
    (hcode : d.code = TotalGen.total_func) (henv : env < s.envs.size)
    (hE : s.envEntry env = .func ∅ (some d.env) .initialized tv f .undefined)
    (hf : s.fuel ≠ 0) :
    ∃ ctx s', functionDeclarationInstantiation 999999 f d env #[.obj A] s = .ok ctx s' ∧
      ctx.lex = s.envs.size ∧ ctx.strict = false ∧ ctx.isGen = false ∧
      ShapeBT s.envs.size env A none s' ∧ s'.fuel = s.fuel ∧ s'.heap = s.heap ∧
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
  have hbody : TotalGen.total_func.body = .stmts TotalGen.total_stmts := rfl
  have hparams : TotalGen.total_func.params = #[.mk (.ident "a") none false] := rfl
  have hstr : TotalGen.total_func.strict = false := rfl
  have hasync : TotalGen.total_func.isAsync = false := rfl
  have hgen : TotalGen.total_func.isGenerator = false := rfl
  have hkind : TotalGen.total_func.kind = .normal := rfl
  have hfdi : TotalGen.total_func.info.fdi = { paramNames := #["a"], hasDuplicates := false, varNames := #[], hasFunctions := false, functionNames := #[], hasLexical := true, lexNames := #["s"], argumentsNeeded := false, hasAnnexB := false, usesDispose := false } := rfl
  have hk1 : (VarKind.let == VarKind.const) = false := by decide
  have hk2 : (VarKind.let == VarKind.using) = false := by decide
  have hk3 : (VarKind.let == VarKind.awaitUsing) = false := by decide
  have hphe : TotalGen.total_func.info.paramsHaveExpressions = false := rfl
  refine ⟨?c, ?t, ?h, ?_⟩
  case h =>
    conv =>
      lhs
      simp only [functionDeclarationInstantiation, hcode, hbody, hparams, hstr, hfdi, hasync, hgen, hkind, hphe]
      simp [hr, hasBinding_declLike, createMutableBinding_declLike, hbe, newDeclEnv, pure,
        M.pure, hE, henv, hf, lexDecls, names_s, -allocEnv_apply, allocEnv_eq, LexScoped.isConstant,
        State.pushEnv_entry_at, State.setEnv_envEntry_self, hk1, hk2, hk3]
  have hne : s.envs.size ≠ env := Nat.ne_of_gt henv
  have hne' : env ≠ s.envs.size := Nat.ne_of_lt henv
  refine ⟨rfl, rfl, rfl, ?_, by simp, by simp [State.setEnv, State.pushEnv], ?_⟩
  · refine ⟨by simp, by simp; exact Nat.lt_succ_of_lt henv, hne, ?_, ?_⟩
    · simp [State.setEnv_envEntry_self, Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert, ne_sa, ne_is, ne_ia, ne_si]
    · simp [State.setEnv_envEntry_ne _ _ _ _ hne, State.pushEnv_entry_lt, State.setEnv_envEntry_self,
        henv, Std.HashMap.getElem?_modify]
  · intro e he hee
    simp [State.setEnv_envEntry_ne _ _ _ _ (show s.envs.size ≠ e by omega), State.pushEnv_entry_lt, he,
      State.setEnv_envEntry_ne _ _ _ _ (Ne.symm hee)]

theorem isArray_of_heap (A : ObjId) (len : Nat) (xs : Nat → Nat) (t u : State) (h : u.heap = t.heap)
    (hA : IsArray A len xs t) : IsArray A len xs u := by
  have ho : ∀ o, u.objEntry o = t.objEntry o := by intro o; simp [State.objEntry, h]
  obtain ⟨a1, a2, a3, a4⟩ := hA
  exact ⟨by rw [h]; exact a1, by rw [ho]; exact a2, by rw [ho]; exact a3, fun j hj => by rw [ho]; exact a4 j hj⟩

/-- `total`'s body, run as a call runs it: with `a` an array of naturals, it returns their sum. -/
theorem total_body (f : ObjId) (d : FuncData) (env : EnvId) (s : State) (A : ObjId) (len : Nat) (xs : Nat → Nat)
    (tv : Value) (hcode : d.code = TotalGen.total_func) (henv : env < s.envs.size)
    (hE : s.envEntry env = .func ∅ (some d.env) .initialized tv f .undefined)
    (hlen : len < 2 ^ 26) (hx : ∀ j < len, xs j < 2 ^ 26) (hA : IsArray A len xs s) (hf : len + 12 ≤ s.fuel) :
    ∃ s', evalFunctionBody evalDepth f d env #[.obj A] s = .ok (num (psum xs len)) s' := by
  obtain ⟨ctx, s', hfdi, hlex, hstr, hgen, hS, hfuel, hheap, -⟩ := total_fdi f d env s A tv hcode henv hE (by omega)
  obtain ⟨s'', hbody⟩ := total_interp_spec 999964 ctx s.envs.size env A len xs hlex hstr hgen hlen hx s' hS
    (isArray_of_heap A len xs s s' hheap hA) (by omega)
  refine ⟨s'', ?_⟩
  have hbd : d.code.body = .stmts TotalGen.total_stmts := by rw [hcode]; rfl
  have hdisp : d.code.info.fdi.usesDispose = false := by rw [hcode]; rfl
  simp only [evalDepth, evalFunctionBody, M.bind_eq, M.bind_apply, hfdi, M.bindRes_ok, hbd, hdisp, withDisposeScope]
  simp [hbody, pure, M.pure]

/-- **The [[Call]] of `total`** with `this` undefined and an array of naturals: returns their sum. -/
theorem total_call (f : ObjId) (d : FuncData) (s : State) (A : ObjId) (len : Nat) (xs : Nat → Nat) (go : ObjId)
    (gb : Std.HashMap JSStr Binding) (gtv : Value)
    (hcode : d.code = TotalGen.total_func) (hcls : d.isClassCtor = false) (hmode : d.thisMode = .global)
    (hge : (s.realms[d.realm]!).globalEnv < s.envs.size)
    (hgE : s.envEntry (s.realms[d.realm]!).globalEnv = .global go gb gtv)
    (hlen : len < 2 ^ 26) (hx : ∀ j < len, xs j < 2 ^ 26) (hA : IsArray A len xs s) (hf : len + 12 ≤ s.fuel) :
    ∃ s', callECMA f d .undefined #[.obj A] s = .ok (num (psum xs len)) s' ∧
      s'.realm = s.realm ∧ s'.script = s.script :=
  let ⟨s', h1, h2, h3, _⟩ := Calls.callECMA_undef (Q := fun _ => True) f d s _ _ go gb gtv hcls hmode
    (by rw [hcode]; rfl) (by rw [hcode]; rfl) hge hgE
    (fun t hlt hEt _ hheap hfu =>
      let ⟨t', ht'⟩ := total_body f d s.envs.size t A len xs gtv hcode hlt hEt hlen hx
        (isArray_of_heap A len xs s t hheap hA) (by omega)
      ⟨t', ht', trivial⟩)
  ⟨s', h1, h2, h3⟩

end TotalCall
