import Proofs.DTScript
import Proofs.IotaCall
import Proofs.ITGen

/-!
# A whole script: `let b = iota(5); total(b);` (examples/iota_total.js)

Run as the engine runs a script (ScriptEvaluation, its two call requests answered by the driver), it
evaluates to 10 = 0 + 1 + 2 + 3 + 4: `iota(5)` builds a new array (its writes go through
`Array.prototype`'s chain, assumed to have no index property below 5), `b` is bound to it, and
`total(b)` sums it. GlobalDeclarationInstantiation is as for examples/double_total.js
(`Proofs/DTScript.lean`), with `iota` in place of `double`.
-/

open ES ES.Conv SumProof SumForProof TotalProof
open Std (HashMap)
open DTScript (createMutableBinding_global initializeBinding_global identValue_global_decl
  resolveBinding_global_decl call_req gb2 gb2_b gb2_mem_b gb2_contains gb2_get gb2_mem isArray_of_arrayObj ne_bt l5
  callOf)

namespace ITScript

theorem varScoped : topLevelVarScoped ITGen.script_stmts = #[.func ITGen.total_func, .func ITGen.iota_func] := by
  rfl
theorem lexScoped : topLevelLexicallyScoped ITGen.script_stmts = #[.binding .let (.ident "b")] := by
  have hv : (VarKind.let == VarKind.var) = false := by decide
  simp [topLevelLexicallyScoped, stmtLexScoped, ITGen.script_stmts, hv]
theorem annexB : annexBFunctions ITGen.script_stmts #[JSStr.ofString "b"] = #[] := by rfl
theorem names_b : (LexScoped.binding .let (.ident "b")).names = #[JSStr.ofString "b"] := by rfl

theorem ne_ti : (JSStr.ofString "total" = JSStr.ofString "iota") = False := by simp; decide
theorem ne_it : (JSStr.ofString "iota" = JSStr.ofString "total") = False := by simp; decide

theorem simple_total : Inst.SimpleFn ITGen.total_func "total" := ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem simple_iota : Inst.SimpleFn ITGen.iota_func "iota" := ⟨rfl, rfl, rfl, rfl, rfl⟩

section
variable (t : State) (ge : EnvId) (g : ObjId) (gb : HashMap JSStr Binding) (gtv : Value) (ctx : Ctx) (fp : ObjId)

/-- After `let b`'s binding is created (uninitialized) in the global record. -/
def stL : State := t.setEnv ge (.global g (gb.insert "b" { deletable := false }) gtv)
/-- After `total`'s function object is created and bound on the global object. -/
def stT : State :=
  let u := Inst.instStateFn ITGen.total_func "total" (stL t ge g gb gtv) ge ctx.script fp
  let p : Property := .data (.obj (stL t ge g gb gtv).heap.size) true true false
  (u.setProp g (.str "total") p).setProp g (.str "total") p
/-- After `iota`'s, the state GlobalDeclarationInstantiation ends in. -/
def stI : State :=
  let u := Inst.instStateFn ITGen.iota_func "iota" (stT t ge g gb gtv ctx fp) ge ctx.script fp
  let p : Property := .data (.obj (stT t ge g gb gtv ctx fp).heap.size) true true false
  (u.setProp g (.str "iota") p).setProp g (.str "iota") p

theorem stT_heap_size : (stT t ge g gb gtv ctx fp).heap.size = t.heap.size + 2 := by
  simp [stT, stL, Inst.instStateFn_size]
theorem stI_heap_size : (stI t ge g gb gtv ctx fp).heap.size = t.heap.size + 4 := by
  simp [stI, Inst.instStateFn_size, stT_heap_size]
theorem stI_envs : (stI t ge g gb gtv ctx fp).envs = (stL t ge g gb gtv).envs := by
  simp [stI, stT, Inst.instStateFn_envs]
theorem stI_fuel : (stI t ge g gb gtv ctx fp).fuel = t.fuel := by
  simp [stI, stT, stL, Inst.instStateFn_fuel]
theorem stI_realms : (stI t ge g gb gtv ctx fp).realms = t.realms := by
  simp [stI, stT, stL, Inst.instStateFn_realms]
theorem stI_curRealm : (stI t ge g gb gtv ctx fp).curRealm = t.curRealm := by
  simp [stI, stT, stL, State.curRealm, Inst.instStateFn_realms, Inst.instStateFn_realm]
theorem stT_curRealm : (stT t ge g gb gtv ctx fp).curRealm = t.curRealm := by
  simp [stT, stL, State.curRealm, Inst.instStateFn_realms, Inst.instStateFn_realm]

end

theorem gdi (t : State) (ge : EnvId) (g : ObjId) (ctx : Ctx) (gb : HashMap JSStr Binding) (gtv : Value)
    (fp : ObjId) (hstrict : ctx.strict = false) (hge : ge < t.envs.size)
    (hE : t.envEntry ge = .global g gb gtv) (hgbb : gb.contains "b" = false) (hgbt : gb.contains "total" = false)
    (hgbd : gb.contains "iota" = false)
    (hgs : g < t.heap.size) (hk : (t.objEntry g).kind = .ordinary) (hx : (t.objEntry g).extensible = true)
    (hpb : (t.objEntry g).props.get? (.str "b") = none) (hpt : (t.objEntry g).props.get? (.str "total") = none)
    (hpd : (t.objEntry g).props.get? (.str "iota") = none)
    (hfp : t.curRealm.intrinsics["%Function.prototype%"]? = some fp) :
    globalDeclarationInstantiation ITGen.script_stmts ge g ctx t =
      .ok (AddScript.gdiCtx ctx) (stI t ge g gb gtv (AddScript.gdiCtx ctx) fp) := by
  have hk' : (t.objEntry g).kind.isPlain = true := by rw [hk]; rfl
  have hnt : ITGen.total_func.name = some (JSStr.ofString "total") := rfl
  have hnd : ITGen.iota_func.name = some (JSStr.ofString "iota") := rfl
  let c := AddScript.gdiCtx ctx
  -- `b`
  have hcm := createMutableBinding_global ge "b" false t g gb gtv hge hE
  -- `total`
  let tL := stL t ge g gb gtv
  have hiT := Inst.instantiate_fn ITGen.total_func "total" simple_total tL ge c fp (by simp [tL, stL]; exact hfp)
  let uT := Inst.instStateFn ITGen.total_func "total" tL ge c.script fp
  have hgL : g < tL.heap.size := by simp [tL, stL]; exact hgs
  have huT : uT.objEntry g = t.objEntry g := by
    simp only [uT]; rw [Inst.instStateFn_entry_lt _ _ _ _ _ _ _ hgL]; simp [tL, stL]
  have hcgT := AddScript.createGlobalFunctionBinding_new uT g "total" (.obj tL.heap.size)
    (by simp only [uT]; rw [Inst.instStateFn_size]; exact Nat.lt_succ_of_lt (Nat.lt_succ_of_lt hgL))
    (by rw [huT]; exact hk) (by rw [huT]; exact hx)
    (by rw [huT]; exact hpt)
  -- `iota`
  let tT := stT t ge g gb gtv c fp
  have hiD := Inst.instantiate_fn ITGen.iota_func "iota" simple_iota tT ge c fp
    (by rw [stT_curRealm]; exact hfp)
  let uD := Inst.instStateFn ITGen.iota_func "iota" tT ge c.script fp
  have hgT : g < tT.heap.size := by simp only [tT]; rw [stT_heap_size]; exact Nat.lt_succ_of_lt (Nat.lt_succ_of_lt hgs)
  have hTg : tT.objEntry g = ((t.objEntry g).withProps (·.insert (.str "total")
      (.data (.obj tL.heap.size) true true false))).withProps (·.insert (.str "total")
      (.data (.obj tL.heap.size) true true false)) := by
    have hgu : g < uT.heap.size := by
      simp only [uT]; rw [Inst.instStateFn_size]; exact Nat.lt_succ_of_lt (Nat.lt_succ_of_lt hgL)
    simp only [tT, stT]
    rw [State.setProp_entry_self _ _ _ _ (by simpa using hgu), State.setProp_entry_self _ _ _ _ hgu, huT]
  have huD : uD.objEntry g = tT.objEntry g := by simp only [uD]; rw [Inst.instStateFn_entry_lt _ _ _ _ _ _ _ hgT]
  have hne : PropKey.str (JSStr.ofString "total") ≠ PropKey.str (JSStr.ofString "iota") := by
    intro h; injection h with h; revert h; decide
  have hcgD := AddScript.createGlobalFunctionBinding_new uD g "iota" (.obj tT.heap.size)
    (by simp only [uD]; rw [Inst.instStateFn_size]; exact Nat.lt_succ_of_lt (Nat.lt_succ_of_lt hgT))
    (by rw [huD, hTg, Obj.withProps_kind, Obj.withProps_kind]; exact hk)
    (by rw [huD, hTg, Obj.withProps_extensible, Obj.withProps_extensible]; exact hx)
    (by rw [huD, hTg, Obj.withProps_props, Obj.withProps_props, PropMap.get?_insert_ne _ _ _ _ hne,
        PropMap.get?_insert_ne _ _ _ _ hne]
        exact hpd)
  have hctx : ({ ctx with strict := false, annexB := funcIds #[] } : Ctx) = c := by
    cases ctx; simp_all [c, AddScript.gdiCtx]
  have hcm' : createMutableBinding ge "b" false t = .ok () tL := hcm
  have hcgT' : createGlobalFunctionBinding g "total" (.obj tL.heap.size) false
      (Inst.instStateFn ITGen.total_func "total" tL ge c.script fp) = .ok () tT := hcgT
  have hcgD' : createGlobalFunctionBinding g "iota" (.obj tT.heap.size) false
      (Inst.instStateFn ITGen.iota_func "iota" tT ge c.script fp) = .ok () (stI t ge g gb gtv c fp) :=
    hcgD
  have hk1 : (VarKind.let == VarKind.const) = false := by decide
  have hk2 : (VarKind.let == VarKind.using) = false := by decide
  have hk3 : (VarKind.let == VarKind.awaitUsing) = false := by decide
  simp only [globalDeclarationInstantiation, varScoped, lexScoped, hstrict]
  simp [names_b, annexB, globalDeclRecHas, readEnv_entry _ _ _ hge, hE, hgbb, hgbt, hgbd, hasRestrictedGlobalProperty,
    canDeclareGlobalFunction, Obj'.getOwnProperty_entry _ _ _ hgs hk', Obj'.isExtensible_entry _ _ hgs hk', hx, hpb,
    hpt, hpd, hnt, hnd, VarScoped.names, M.bind_eq, M.bind_apply, M.bindRes_ok, ne_ti, ne_it, LexScoped.isConstant, pure, M.pure, funcNameKey, hctx, hcm', hk1, hk2, hk3, hiT, hcgT', hiD, hcgD']
  exact ⟨rfl, rfl⟩

/-- What GlobalDeclarationInstantiation leaves: `b` declared (uninitialized) in the global record,
`total` (object `t.heap.size`) and `iota` (object `t.heap.size + 2`) bound on the global object. -/
theorem stI_facts (t : State) (ge : EnvId) (g : ObjId) (gb : HashMap JSStr Binding) (gtv : Value) (c : Ctx)
    (fp : ObjId) (hge : ge < t.envs.size) (hgs : g < t.heap.size) :
    let u := stI t ge g gb gtv c fp
    u.envEntry ge = .global g (gb.insert "b" { deletable := false }) gtv ∧ u.envs.size = t.envs.size ∧
    (∀ e, e ≠ ge → u.envEntry e = t.envEntry e) ∧
    (u.objEntry g).kind = (t.objEntry g).kind ∧
    (u.objEntry g).props.get? (.str "total") = some (.data (.obj t.heap.size) true true false) ∧
    (u.objEntry g).props.get? (.str "iota") = some (.data (.obj (t.heap.size + 2)) true true false) ∧
    (u.objEntry t.heap.size).kind = .func (Inst.fnData ITGen.total_func (stL t ge g gb gtv) ge c.script) ∧
    (u.objEntry (t.heap.size + 2)).kind =
      .func (Inst.fnData ITGen.iota_func (stT t ge g gb gtv c fp) ge c.script) ∧
    u.heap.size = t.heap.size + 4 ∧ u.fuel = t.fuel ∧ u.realms = t.realms ∧
    (u.objEntry g).proto = (t.objEntry g).proto ∧
    (∀ j, j < 10 ^ 10 → (u.objEntry g).props.get? (PropKey.ofNat j) = (t.objEntry g).props.get? (PropKey.ofNat j)) ∧
    (∀ x, x < t.heap.size → x ≠ g → u.objEntry x = t.objEntry x) := by
  intro u
  have hLs : (stL t ge g gb gtv).heap.size = t.heap.size := by simp [stL]
  have hTs : (stT t ge g gb gtv c fp).heap.size = t.heap.size + 2 := stT_heap_size _ _ _ _ _ _ _
  obtain ⟨tL, htL⟩ : ∃ x, stL t ge g gb gtv = x := ⟨_, rfl⟩
  obtain ⟨tT, htT⟩ : ∃ x, stT t ge g gb gtv c fp = x := ⟨_, rfl⟩
  rw [htL] at hLs; rw [htT] at hTs
  have hu : u = ((Inst.instStateFn ITGen.iota_func "iota" tT ge c.script fp).setProp g (.str "iota")
      (.data (.obj tT.heap.size) true true false)).setProp g (.str "iota") (.data (.obj tT.heap.size) true true false) := by
    simp only [u, stI, htT]
  have hT : tT = ((Inst.instStateFn ITGen.total_func "total" tL ge c.script fp).setProp g (.str "total")
      (.data (.obj tL.heap.size) true true false)).setProp g (.str "total") (.data (.obj tL.heap.size) true true false) := by
    rw [← htT]; simp only [stT, htL]
  have hLe : tL.envEntry ge = .global g (gb.insert "b" { deletable := false }) gtv := by
    rw [← htL]; exact State.setEnv_envEntry_self _ _ _ hge
  have hLo : ∀ o, tL.objEntry o = t.objEntry o := by intro o; rw [← htL]; simp [stL]
  -- environments
  have hTenvs : tT.envs = tL.envs := by rw [hT]; simp [Inst.instStateFn_envs]
  have huenvs : u.envs = tL.envs := by rw [hu]; simp [Inst.instStateFn_envs, hTenvs]
  have hLenvs : tL.envs.size = t.envs.size := by rw [← htL]; simp [stL]
  -- the global object
  have hgL : g < tL.heap.size := by rw [hLs]; exact hgs
  have hgUT : g < (Inst.instStateFn ITGen.total_func "total" tL ge c.script fp).heap.size := by
    rw [Inst.instStateFn_size]; exact Nat.lt_succ_of_lt (Nat.lt_succ_of_lt hgL)
  have hgT : g < tT.heap.size := by rw [hTs]; exact Nat.lt_succ_of_lt (Nat.lt_succ_of_lt hgs)
  have hgUD : g < (Inst.instStateFn ITGen.iota_func "iota" tT ge c.script fp).heap.size := by
    rw [Inst.instStateFn_size]; exact Nat.lt_succ_of_lt (Nat.lt_succ_of_lt hgT)
  have hTg : tT.objEntry g = ((t.objEntry g).withProps (·.insert (.str "total")
      (.data (.obj tL.heap.size) true true false))).withProps (·.insert (.str "total")
      (.data (.obj tL.heap.size) true true false)) := by
    rw [hT, State.setProp_entry_self _ _ _ _ (by simpa using hgUT), State.setProp_entry_self _ _ _ _ hgUT,
      Inst.instStateFn_entry_lt _ _ _ _ _ _ _ hgL, hLo]
  have hug : u.objEntry g = ((tT.objEntry g).withProps (·.insert (.str "iota")
      (.data (.obj tT.heap.size) true true false))).withProps (·.insert (.str "iota")
      (.data (.obj tT.heap.size) true true false)) := by
    rw [hu, State.setProp_entry_self _ _ _ _ (by simpa using hgUD), State.setProp_entry_self _ _ _ _ hgUD,
      Inst.instStateFn_entry_lt _ _ _ _ _ _ _ hgT]
  have hne : PropKey.str (JSStr.ofString "iota") ≠ PropKey.str (JSStr.ofString "total") := by
    intro h; injection h with h; revert h; decide
  -- the function objects
  have hfT : t.heap.size < tT.heap.size := by rw [hTs]; exact Nat.lt_succ_of_lt (Nat.lt_succ_self _)
  have hgfT : g ≠ t.heap.size := Nat.ne_of_lt hgs
  have hgfD : g ≠ t.heap.size + 2 := Nat.ne_of_lt (Nat.lt_succ_of_lt (Nat.lt_succ_of_lt hgs))
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [State.envEntry, huenvs]; exact hLe
  · rw [huenvs, hLenvs]
  · intro e he
    simp only [State.envEntry, huenvs]; rw [← htL]; simp only [stL]
    exact State.setEnv_envEntry_ne _ _ _ _ (Ne.symm he)
  · rw [hug, Obj.withProps_kind, Obj.withProps_kind, hTg, Obj.withProps_kind, Obj.withProps_kind]
  · rw [hug, Obj.withProps_props, Obj.withProps_props, PropMap.get?_insert_ne _ _ _ _ hne,
      PropMap.get?_insert_ne _ _ _ _ hne, hTg, Obj.withProps_props, Obj.withProps_props, hLs]
    simp
  · rw [hug, Obj.withProps_props, Obj.withProps_props, hTs]; simp
  · rw [hu, State.setProp_entry_ne _ _ _ _ _ hgfT, State.setProp_entry_ne _ _ _ _ _ hgfT,
      Inst.instStateFn_entry_lt _ _ _ _ _ _ _ hfT, hT, State.setProp_entry_ne _ _ _ _ _ hgfT,
      State.setProp_entry_ne _ _ _ _ _ hgfT, ← hLs, Inst.instStateFn_func, htL]
  · rw [hu, State.setProp_entry_ne _ _ _ _ _ hgfD, State.setProp_entry_ne _ _ _ _ _ hgfD, ← hTs,
      Inst.instStateFn_func, htT]
  · simp only [u]; exact stI_heap_size _ _ _ _ _ _ _
  · simp only [u]; exact stI_fuel _ _ _ _ _ _ _
  · simp only [u]; exact stI_realms _ _ _ _ _ _ _
  · rw [hug, Obj.withProps_proto, Obj.withProps_proto, hTg, Obj.withProps_proto, Obj.withProps_proto]
  · intro j hj
    have hi := name_ne_index "iota" (by decide) j hj
    have ht := name_ne_index "total" (by decide) j hj
    rw [hug, Obj.withProps_props, Obj.withProps_props, PropMap.get?_insert_ne _ _ _ _ hi,
      PropMap.get?_insert_ne _ _ _ _ hi, hTg, Obj.withProps_props, Obj.withProps_props,
      PropMap.get?_insert_ne _ _ _ _ ht, PropMap.get?_insert_ne _ _ _ _ ht]
  · intro x hx hxg
    have hxL : x < tL.heap.size := by rw [hLs]; exact hx
    have hxT : x < tT.heap.size := by rw [hTs]; exact Nat.lt_of_lt_of_le hx (Nat.le_add_right _ _)
    rw [hu, State.setProp_entry_ne _ _ _ _ _ (Ne.symm hxg), State.setProp_entry_ne _ _ _ _ _ (Ne.symm hxg),
      Inst.instStateFn_entry_lt _ _ _ _ _ _ _ hxT, hT, State.setProp_entry_ne _ _ _ _ _ (Ne.symm hxg),
      State.setProp_entry_ne _ _ _ _ _ (Ne.symm hxg), Inst.instStateFn_entry_lt _ _ _ _ _ _ _ hxL, hLo]

theorem stT_realm (t : State) (ge : EnvId) (g : ObjId) (gb : HashMap JSStr Binding) (gtv : Value) (c : Ctx)
    (fp : ObjId) : (stT t ge g gb gtv c fp).realm = t.realm := by
  simp [stT, stL, Inst.instStateFn_realm]
theorem total_same : ITGen.total_func = TotalGen.total_func := rfl
theorem isIota_it : IotaCall.IsIota ITGen.iota_func := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## The statements -/

theorem ne_bi : (JSStr.ofString "b" = JSStr.ofString "iota") = False := by simp; decide
theorem l5_eq : l5 = ofSmallInt 5 := by decide

/-- `resolveBinding` of a name bound on the global object (not in the declarative part). -/
theorem resolveBinding_global_obj (env : EnvId) (n : JSStr) (strict : Bool) (s : State) (g : ObjId)
    (b : HashMap JSStr Binding) (tv : Value) (p : Property) (h : env < s.envs.size)
    (hE : s.envEntry env = .global g b tv) (hb : b.contains n = false) (hbm : (n ∈ b) = False)
    (hgs : g < s.heap.size) (hk : (s.objEntry g).kind.isPlain = true) (hp : (s.objEntry g).props.get? (.str n) = some p)
    (hf : s.fuel ≠ 0) :
    resolveBinding env n strict s = .ok (.env (some env) n strict) s := by
  obtain ⟨k, hk1⟩ : ∃ k, s.fuel = k + 1 := ⟨s.fuel - 1, by omega⟩
  rw [resolveBinding_loop, hk1]
  simp [M.loop, resolveBody, M.bind_eq, M.bind_apply, hasBinding, readEnv_entry _ _ _ h, hE, hb, hbm,
    Obj'.hasProperty_entry_own _ _ _ hgs hk, hp, pure, M.pure]

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

/-- The script's statements: the declarations do nothing, `let b = iota(5)` asks for its call; when it
returns and `b` is initialized, `total(b)` asks for its call, and when that returns `v` the statements
complete normally with `v`. -/
theorem body_req (n : Nat) (c : Ctx) (u : State) (r3 : Req) (K3 : Outcome → State → Res Compl)
    (hann : c.annexB = funcIds #[]) (hf : 5 ≤ u.fuel) (h3 : letIota c u = .req r3 u K3) :
    ∃ K, ITGen.script n c u = .req r3 u K ∧
      ∀ v w w' r4 (K4 : Outcome → State → Res Compl), K3 (.normal v) w = .ok (.normal none) w' →
        callOf "total" c w' = .req r4 w' K4 → (∀ v t, K4 (.normal v) t = .ok (.normal (some v)) t) →
        ∃ K', K (.normal v) w = .req r4 w' K' ∧ ∀ v t, K' (.normal v) t = .ok (.normal (some v)) t := by
  obtain ⟨k, hk⟩ : ∃ k, u.fuel = k + 5 := ⟨u.fuel - 5, by omega⟩
  have hann0 : ∀ i, (funcIds #[]).contains i = false := by simp [funcIds]
  refine ⟨?K, ?h, ?_⟩
  case h =>
    conv =>
      lhs
      rw [script_def]
      simp [Sem.stmts, M.repeatFrom, hk, M.loop, Sem.funDecl, hann, hann0, h3, M.bind_eq, M.bind_apply,
        M.bindRes_ok, M.bindRes_req, pure, M.pure]
  intro v w w' r4 K4 hK3 h4 hK4
  refine ⟨?K', ?h', ?_⟩
  case h' =>
    conv =>
      lhs
      simp [hK3, M.loopRes_inl, M.loop, h4, M.bind_eq, M.bind_apply, M.bindRes_ok, M.bindRes_req, M.loopRes_req,
        pure, M.pure]
  intro v t
  simp [hK4, M.loopRes_inl, M.loopRes_inr, M.bindRes_ok, M.pure, Compl.updateEmpty]

theorem psum10 : psum (fun j => j) 5 = 10 := by decide

/-! ## The whole script -/

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
  -- ScriptEvaluation's first steps: the script record and its context
  let ge := s.curRealm.globalEnv
  let g := s.curRealm.globalObj
  let t : State := { s with scripts := s.scripts.push { prog := ITGen.program, realm := s.realm, path := "" }, script := s.scripts.size }
  let ctx0 : Ctx := { lex := ge, var := ge, strict := false, realm := s.realm, script := s.scripts.size }
  have htr : t.curRealm = s.curRealm := rfl
  have hge' : ge < t.envs.size := hge
  have hE' : t.envEntry ge = .global g gb gtv := hE
  have hgs' : g < t.heap.size := hgs
  have htf : t.fuel = s.fuel := rfl
  have hto : ∀ x, t.objEntry x = s.objEntry x := fun _ => rfl
  -- GlobalDeclarationInstantiation
  have hgdi := gdi t ge g ctx0 gb gtv fp rfl hge' hE' hgbb hgbt hgbi hgs' hk hx hpb hpt hpi (by rw [htr]; exact hfp)
  let c := AddScript.gdiCtx ctx0
  obtain ⟨hE1, hz1, -, hgk1, hpt1, hpi1, hfTk, hfIk, hsz1, hfu1, hrl1, hgp1, hgj1, ho1⟩ :=
    stI_facts t ge g gb gtv c fp hge' hgs'
  obtain ⟨u, hu⟩ : ∃ u, stI t ge g gb gtv c fp = u := ⟨_, rfl⟩
  rw [hu] at hgdi hE1 hz1 hgk1 hpt1 hpi1 hfTk hfIk hsz1 hfu1 hrl1 hgp1 hgj1 ho1
  let fT := t.heap.size
  let fI := t.heap.size + 2
  obtain ⟨dT, hdT⟩ : ∃ d, Inst.fnData ITGen.total_func (stL t ge g gb gtv) ge c.script = d := ⟨_, rfl⟩
  obtain ⟨dI, hdI⟩ : ∃ d, Inst.fnData ITGen.iota_func (stT t ge g gb gtv c fp) ge c.script = d := ⟨_, rfl⟩
  rw [hdT] at hfTk; rw [hdI] at hfIk
  have hir : dI.realm = s.realm := by rw [← hdI, Inst.fnData_realm, stT_realm]
  have htrl : dT.realm = s.realm := by rw [← hdT, Inst.fnData_realm]; simp [stL]; rfl
  have hcodeI : IotaCall.IsIota dI.code := by rw [← hdI, Inst.fnData_code]; exact isIota_it
  have hcodeT : dT.code = TotalGen.total_func := by rw [← hdT, Inst.fnData_code]; exact total_same
  have hclsI : dI.isClassCtor = false := by rw [← hdI, Inst.fnData_isClassCtor]
  have hclsT : dT.isClassCtor = false := by rw [← hdT, Inst.fnData_isClassCtor]
  have hmI : dI.thisMode = .global := by rw [← hdI, Inst.fnData_thisMode]
  have hmT : dT.thisMode = .global := by rw [← hdT, Inst.fnData_thisMode]
  have hgeu : ge < u.envs.size := by rw [hz1]; exact hge'
  have hgu : g < u.heap.size := by rw [hsz1]; exact Nat.lt_of_lt_of_le hgs' (Nat.le_add_right _ _)
  have hfTu : fT < u.heap.size := by show t.heap.size < u.heap.size; rw [hsz1]; omega
  have hfIu : fI < u.heap.size := by show t.heap.size + 2 < u.heap.size; rw [hsz1]; omega
  have hku : (u.objEntry g).kind = .ordinary := by rw [hgk1]; exact hk
  let gbL := gb.insert "b" { deletable := false }
  have hLb : (JSStr.ofString "b" ∈ gbL) = True := by simp [gbL]
  have hLi : gbL.contains "iota" = false := by simp [gbL, Std.HashMap.contains_insert, hgbi, ne_bi]
  have hLi' : gbL[JSStr.ofString "iota"]? = none := by
    have : gb[JSStr.ofString "iota"]? = none := Std.HashMap.getElem?_eq_none (fun hm => by
      rw [Std.HashMap.mem_iff_contains, hgbi] at hm; exact Bool.false_ne_true hm)
    simp [gbL, Std.HashMap.getElem?_insert, ne_bi, this]
  have hLim : (JSStr.ofString "iota" ∈ gbL) = False := by simp [Std.HashMap.mem_iff_contains, hLi]
  -- `let b = iota(5)` asks for its call
  obtain ⟨K3, h3, hK3⟩ := let_call_req c u ge g fI gbL gtv dI rfl rfl hgeu hE1 hLb hLi hLi' hLim hgu hku hpi1 hfIu
    hfIk (by rw [hfu1, htf]; omega)
  obtain ⟨K, hreq, hK⟩ := body_req 999956 c u _ K3 rfl (by rw [hfu1, htf]; omega) h3
  have hscript : evalStmts evalDepth (AddScript.gdiCtx ctx0) ITGen.script_stmts u = ITGen.script 999956 c u := by
    rw [ITGen.script_eq]; rfl
  -- the call of `iota`, answered by the driver
  obtain ⟨u', hu'⟩ : ∃ x, ({ u with fuel := u.fuel - 1 } : State) = x := ⟨_, rfl⟩
  have hr' : u'.realms = s.realms := by rw [← hu']; exact hrl1
  have hgeI : (u'.realms[dI.realm]!).globalEnv = ge := by rw [hr', hir]; rfl
  have hz' : u'.envs = u.envs := by rw [← hu']
  have hou : ∀ x, u'.objEntry x = u.objEntry x := fun x => by rw [← hu']; rfl
  have hPI : ∀ j < 5, AbsentChain u' 2 (u'.realms[dI.realm]!).arrayProto (PropKey.ofNat j) := by
    intro j hj
    have hap : (u'.realms[dI.realm]!).arrayProto = s.curRealm.arrayProto := by rw [hr', hir]; rfl
    rw [hap]
    refine absentChain_mono_key s u' _ (fun x hx => ?_) ?_ 2 _ (hP j hj)
    · rw [hou x]
      by_cases hxg : x = g
      · subst hxg; exact ⟨by rw [hgk1]; rfl, by rw [hgp1]; rfl, by rw [hgj1 j (by omega)]; rfl⟩
      · rw [ho1 x hx hxg]; exact ⟨rfl, rfl, rfl⟩
    · rw [← hu']; show s.heap.size ≤ u.heap.size; rw [hsz1]; exact Nat.le_add_right _ _
  obtain ⟨s3, hcallI, -, -, hA3, hz3, he3, hhs3, ho3, hr3, hfu3⟩ := IotaCall.iota_call fI dI u' 5 g gbL gtv
    hcodeI hclsI hmI (by rw [hgeI, hz']; exact hgeu) (by rw [hgeI]; simp only [State.envEntry, hz']; exact hE1)
    (by decide) hPI (by rw [← hu']; simp only; rw [hfu1, htf]; omega)
  let A := u.heap.size
  have hAu : u'.heap.size = A := by rw [← hu']
  rw [hAu] at hcallI hA3 hhs3
  have himplI : callImpl eng (.obj fI) .undefined #[.num l5] u = .ok (.obj A) s3 := by
    rw [l5_eq, callImpl_func eng fI dI _ _ u hfIu hfIk (by rw [hfu1, htf]; omega), hu']; exact hcallI
  -- `b` is initialized, in the state `iota` left
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
    intro x hx; rw [← hw, State.setEnv_objEntry, ho3 x (by rw [hAu]; exact hx), hou]
  have hhw : w.heap.size = A + 1 := by rw [← hw, State.setEnv_heap_size, hhs3]
  have hfw : w.fuel + 6 = s.fuel - 1 := by
    rw [← hw, State.setEnv_fuel]; rw [← hu'] at hfu3; simp only at hfu3; rw [hfu1, htf] at hfu3; omega
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
  obtain ⟨K', hK1, hK'⟩ := hK _ s3 w _ K4 hK3' h4 hK4
  -- the call of `total`, answered by the driver
  obtain ⟨w', hw'⟩ : ∃ x, ({ w with fuel := w.fuel - 1 } : State) = x := ⟨_, rfl⟩
  have hgeT : (w'.realms[dT.realm]!).globalEnv = ge := by rw [← hw']; show (w.realms[dT.realm]!).globalEnv = ge; rw [hrw, htrl]; rfl
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
  -- the script, with the driver
  have hbody : ITGen.program.body = ITGen.script_stmts := rfl
  have hstr : ITGen.program.strict = false := rfl
  refine ⟨s4, ?_⟩
  simp only [runM, callDepth, scriptEvaluation, M.bind_eq, M.bind_apply, M.readS_apply, M.bindRes_ok, M.modify_apply,
    hbody, hstr]
  rw [hgdi]
  simp only [M.bindRes_ok, M.bind_apply, hscript, hreq, M.bindRes_req]
  rw [drive_call_ok eng 3999 _ _ _ _ _ cs _ _ himplI]
  simp only [hK1, M.bindRes_req]
  rw [drive_call_ok eng 3999 _ _ _ _ _ cs _ _ himplT]
  simp only [hK', M.bindRes_ok, Option.getD_some, psum10]
  simp only [pure, M.pure, drive_ok]
  rfl

end ITScript
