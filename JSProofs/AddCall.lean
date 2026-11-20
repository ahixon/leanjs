import JSProofs.Env
import JSProofs.Add

/-!
# Calling `add`: FunctionDeclarationInstantiation binds its parameters

For `function add(a, b) { return a + b }` (examples/add.js), with a function environment `env`
that has no bindings yet: FunctionDeclarationInstantiation creates `a` and `b` in `env`,
initializes them to the arguments, and makes the body's lexical environment.
-/

open ES
open Std (HashMap)

namespace AddCall

/-- The parameters' bindings after FunctionDeclarationInstantiation: `a ↦ x`, `b ↦ y`. -/
def paramBindings (x y : F64) : HashMap JSStr Binding :=
  ((((∅ : HashMap JSStr Binding).insert "a" { deletable := false }).insert "b" { deletable := false }).modify
    "a" fun bd => { bd with value := some (.num x) }).modify "b" fun bd => { bd with value := some (.num y) }

/-- FunctionDeclarationInstantiation for `add` called with two Numbers, in a fresh function
environment `env`: it binds `a` and `b` there and returns a context whose lexical environment is a
new, empty declarative environment inside `env`. -/
theorem add_fdi (f : ObjId) (d : FuncData) (env : EnvId) (s : State) (x y : F64) (tv : Value)
    (hcode : d.code = AddGen.add_func) (henv : env < s.envs.size)
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
      simp only [AddGen.add_func, Func.strict, Func.params, Func.info, Func.body, Func.isAsync]
      simp [hr, hasBinding_declLike, createMutableBinding_declLike, hbe, newDeclEnv, pure,
        M.pure, hE, henv, hf, hab]
  have hne : env ≠ s.envs.size := Nat.ne_of_lt henv
  simp [State.envEntry, State.setEnv, Array.getElem?_push, Array.getElem_push, Array.getElem_modify, henv, hne,
    paramBindings]
  intro e he hee
  simp [Nat.ne_of_lt he, Array.getElem?_modify, Ne.symm hee]

/-- `add`'s body, run as a call runs it (FunctionDeclarationInstantiation, then the statements):
called with Numbers `x` and `y` in a fresh function environment, it returns `x + y`. -/
theorem add_body (f : ObjId) (d : FuncData) (env : EnvId) (s : State) (x y : F64) (tv : Value)
    (hcode : d.code = AddGen.add_func) (henv : env < s.envs.size)
    (hE : s.envEntry env = .func ∅ (some d.env) .initialized tv f .undefined)
    (hf : 2 ≤ s.fuel) :
    ∃ s', evalFunctionBody evalDepth f d env #[.num x, .num y] s = .ok (.num (Conv.addF x y)) s' ∧
      s'.envs.size = s.envs.size + 1 ∧ s'.fuel = s.fuel ∧ s'.heap = s.heap ∧ s'.realms = s.realms ∧
      (∀ e, e < s.envs.size → e ≠ env → s'.envEntry e = s.envEntry e) := by
  obtain ⟨ctx, s', hfdi, hB, hlex, hL, hvar, hstrict, hgen, hfn, hsize, hfuel, hheap, hrl, hfe⟩ :=
    add_fdi f d env s x y tv hcode henv hE (by omega)
  have hl' : ctx.lex < s'.envs.size := by rw [hlex, hsize]; exact Nat.lt_succ_self _
  have he' : env < s'.envs.size := by rw [hsize]; exact Nat.lt_succ_of_lt henv
  have hread : ∀ (n : JSStr) (v : F64), ((paramBindings x y)[n]?).bind (·.value) = some (.num v) →
      identValue ctx.lex n ctx.strict s' = .ok (.num v) s' := by
    intro n v h
    cases hb : (paramBindings x y)[n]? with
    | none => simp [hb] at h
    | some bd =>
      simp only [hb, Option.bind_some] at h
      exact identValue_decl_func ctx.lex env n ctx.strict s' (.num v) (paramBindings x y) bd _ _ _ _ _
        hl' hL he' hB hb h (by omega)
  have hab : (JSStr.ofString "b" == JSStr.ofString "a") = false := by decide
  have ha : identValue ctx.lex "a" ctx.strict s' = .ok (.num x) s' := by
    apply hread
    simp [paramBindings, Std.HashMap.getElem_modify, Std.HashMap.getElem_insert, hab]
  have hb : identValue ctx.lex "b" ctx.strict s' = .ok (.num y) s' := by
    apply hread
    simp [paramBindings, Std.HashMap.getElem_modify, Std.HashMap.getElem_insert, hab]
  obtain ⟨k, hk⟩ : ∃ k, s'.fuel = k + 1 := ⟨s'.fuel - 1, by omega⟩
  have hbody := AddProof.add_interp_spec 999976 k ctx s' x y ha hb hgen hk
  refine ⟨s', ?_, hsize, hfuel, hheap, hrl, hfe⟩
  have hbd : d.code.body = .stmts AddGen.add_stmts := by rw [hcode]; rfl
  have hdisp : d.code.info.fdi.usesDispose = false := by rw [hcode]; rfl
  simp only [evalDepth, evalFunctionBody, M.bind_eq, M.bind_apply, hfdi, M.bindRes_ok, hbd, hdisp,
    withDisposeScope]
  simp [hbody, pure, M.pure]

/-- The [[Call]] of `add` (a non-strict function declaration's object `f`) with an object as
`this` and two Numbers: it returns `x + y`, and the caller's realm and script are restored. -/
theorem add_call (f : ObjId) (d : FuncData) (o : ObjId) (s : State) (x y : F64)
    (hcode : d.code = AddGen.add_func) (hcls : d.isClassCtor = false) (hmode : d.thisMode = .global)
    (hf : 2 ≤ s.fuel) :
    ∃ s', callECMA f d (.obj o) #[.num x, .num y] s = .ok (.num (Conv.addF x y)) s' ∧
      s'.realm = s.realm ∧ s'.script = s.script ∧ s'.fuel = s.fuel := by
  -- the states: in the callee's realm, with the function environment, with `this` bound
  let s1 : State := { s with realm := d.realm, script := d.script }
  let env := s.envs.size
  let E0 : Env := .func {} (some d.env) .uninitialized .undefined f .undefined
  let s2 : State := { s1 with envs := s1.envs.push E0 }
  let s3 := s2.setEnv env (.func {} (some d.env) .initialized (.obj o) f .undefined)
  have hgl : (ThisMode.global == ThisMode.lexical) = false := by decide
  have hgs : (ThisMode.global == ThisMode.strict) = false := by decide
  have hnew : newFunctionEnv f d .undefined s1 = .ok env s2 := by
    simp [hgl, newFunctionEnv, hmode, s2, s1, E0, env]
  have henv2 : env < s2.envs.size := by simp [s2, s1, env]
  have hbind : ordinaryCallBindThis d env (.obj o) s2 = .ok () s3 := by
    simp only [ordinaryCallBindThis, hmode]
    have hnn : (Value.obj o).isNullish = false := rfl
    have hui : (ThisStatus.uninitialized == ThisStatus.initialized) = false := by decide
    simp [hgl, hgs, hnn, hui, M.bind_eq, M.bind_apply, toObject, bindThisValue, readEnv_entry _ _ _ henv2, pure, M.pure,
      modifyEnv_eq_setEnv _ _ _ henv2, s3]
    simp [hui, State.envEntry, s2, s1, E0, env, modifyEnv, State.setEnv]
  have henv3 : env < s3.envs.size := by simp [s3, s2, s1, env]
  have hE3 : s3.envEntry env = .func ∅ (some d.env) .initialized (.obj o) f .undefined := by
    simp [s3, henv2]
  obtain ⟨s4, hbody, -, hfuel4, -, -, -⟩ :=
    add_body f d env s3 x y (.obj o) hcode henv3 hE3 (by simp [s3, s2, s1]; omega)
  have hasync : d.code.isAsync = false := by rw [hcode]; rfl
  have hgen : d.code.isGenerator = false := by rw [hcode]; rfl
  refine ⟨{ s4 with realm := s.realm, script := s.script }, ?_, rfl, rfl, ?_⟩
  · simp only [callECMA, hcls, inCallee, M.bind_eq, M.bind_apply, M.readS_apply, M.bindRes_ok,
      M.modify_apply]
    simp [M.bind_apply, hnew, hbind, hasync, hgen, hbody, M.attempt, M.tryCatch_apply, pure, M.pure, s1]
  · simp [hfuel4, s3, s2, s1]

/-- The [[Call]] of `add` with `this` undefined (a plain call `add(x, y)`): a sloppy function's
`this` is then the global environment's this value. Returns `x + y`. -/
theorem add_call_undef (f : ObjId) (d : FuncData) (s : State) (x y : F64) (go : ObjId)
    (gb : Std.HashMap JSStr Binding) (gtv : Value)
    (hcode : d.code = AddGen.add_func) (hcls : d.isClassCtor = false) (hmode : d.thisMode = .global)
    (hge : (s.realms[d.realm]!).globalEnv < s.envs.size)
    (hgE : s.envEntry (s.realms[d.realm]!).globalEnv = .global go gb gtv)
    (hf : 2 ≤ s.fuel) :
    ∃ s', callECMA f d .undefined #[.num x, .num y] s = .ok (.num (Conv.addF x y)) s' ∧
      s'.realm = s.realm ∧ s'.script = s.script ∧ s'.fuel = s.fuel := by
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
  obtain ⟨s4, hbody, -, hfuel4⟩ :=
    add_body f d env s3 x y gtv hcode henv3 hE3 (by simp [s3, s2, s1]; omega)
  have hasync : d.code.isAsync = false := by rw [hcode]; rfl
  have hgen : d.code.isGenerator = false := by rw [hcode]; rfl
  refine ⟨{ s4 with realm := s.realm, script := s.script }, ?_, rfl, rfl, ?_⟩
  · simp only [callECMA, hcls, inCallee, M.bind_eq, M.bind_apply, M.readS_apply, M.bindRes_ok,
      M.modify_apply]
    simp [M.bind_apply, hnew, hbind, hasync, hgen, hbody, M.attempt, M.tryCatch_apply, pure, M.pure, s1]
  · simp [hfuel4, s3, s2, s1]

end AddCall
