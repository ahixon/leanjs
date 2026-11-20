import Proofs.MoreCalls
import Proofs.Instantiate
import Proofs.DTGen

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

namespace DTScript

/-! ## The global record's declarative part -/

theorem createMutableBinding_global (env : EnvId) (n : JSStr) (del : Bool) (s : State) (g : ObjId)
    (b : HashMap JSStr Binding) (tv : Value) (h : env < s.envs.size) (hE : s.envEntry env = .global g b tv) :
    createMutableBinding env n del s = .ok () (s.setEnv env (.global g (b.insert n { deletable := del }) tv)) := by
  simp only [createMutableBinding, M.bind_eq, M.bind_apply, readEnv_entry env id s h, M.bindRes_ok, id, hE]
  rw [modifyEnv_eq_setEnv s env _ h, hE]; rfl

theorem initializeBinding_global (env : EnvId) (n : JSStr) (v : Value) (s : State) (g : ObjId)
    (b : HashMap JSStr Binding) (tv : Value) (h : env < s.envs.size) (hE : s.envEntry env = .global g b tv)
    (hb : b.contains n = true) :
    initializeBinding env n v s =
      .ok () (s.setEnv env (.global g (b.modify n fun bd => { bd with value := some v }) tv)) := by
  simp only [initializeBinding, M.bind_eq, M.bind_apply, readEnv_entry env id s h, M.bindRes_ok, id, hE, hb,
    ↓reduceIte]
  rw [modifyEnv_eq_setEnv s env _ h, hE]; rfl

/-! ## GlobalDeclarationInstantiation -/

theorem varScoped : topLevelVarScoped DTGen.script_stmts = #[.func DTGen.total_func, .func DTGen.double_func] := by
  rfl
theorem lexScoped : topLevelLexicallyScoped DTGen.script_stmts = #[.binding .let (.ident "b")] := by
  have hv : (VarKind.let == VarKind.var) = false := by decide
  simp [topLevelLexicallyScoped, stmtLexScoped, DTGen.script_stmts, hv]
theorem annexB : annexBFunctions DTGen.script_stmts #[JSStr.ofString "b"] = #[] := by rfl
theorem names_b : (LexScoped.binding .let (.ident "b")).names = #[JSStr.ofString "b"] := by rfl

theorem ne_td : (JSStr.ofString "total" = JSStr.ofString "double") = False := by simp; decide
theorem ne_dt : (JSStr.ofString "double" = JSStr.ofString "total") = False := by simp; decide

theorem simple_total : Inst.SimpleFn DTGen.total_func "total" := ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem simple_double : Inst.SimpleFn DTGen.double_func "double" := ⟨rfl, rfl, rfl, rfl, rfl⟩

section
variable (t : State) (ge : EnvId) (g : ObjId) (gb : HashMap JSStr Binding) (gtv : Value) (ctx : Ctx) (fp : ObjId)

/-- After `let b`'s binding is created (uninitialized) in the global record. -/
def stL : State := t.setEnv ge (.global g (gb.insert "b" { deletable := false }) gtv)
/-- After `total`'s function object is created and bound on the global object. -/
def stT : State :=
  let u := Inst.instStateFn DTGen.total_func "total" (stL t ge g gb gtv) ge ctx.script fp
  let p : Property := .data (.obj (stL t ge g gb gtv).heap.size) true true false
  (u.setProp g (.str "total") p).setProp g (.str "total") p
/-- After `double`'s, the state GlobalDeclarationInstantiation ends in. -/
def stD : State :=
  let u := Inst.instStateFn DTGen.double_func "double" (stT t ge g gb gtv ctx fp) ge ctx.script fp
  let p : Property := .data (.obj (stT t ge g gb gtv ctx fp).heap.size) true true false
  (u.setProp g (.str "double") p).setProp g (.str "double") p

theorem stT_heap_size : (stT t ge g gb gtv ctx fp).heap.size = t.heap.size + 2 := by
  simp [stT, stL, Inst.instStateFn_size]
theorem stD_heap_size : (stD t ge g gb gtv ctx fp).heap.size = t.heap.size + 4 := by
  simp [stD, Inst.instStateFn_size, stT_heap_size]
theorem stD_envs : (stD t ge g gb gtv ctx fp).envs = (stL t ge g gb gtv).envs := by
  simp [stD, stT, Inst.instStateFn_envs]
theorem stD_fuel : (stD t ge g gb gtv ctx fp).fuel = t.fuel := by
  simp [stD, stT, stL, Inst.instStateFn_fuel]
theorem stD_realms : (stD t ge g gb gtv ctx fp).realms = t.realms := by
  simp [stD, stT, stL, Inst.instStateFn_realms]
theorem stD_curRealm : (stD t ge g gb gtv ctx fp).curRealm = t.curRealm := by
  simp [stD, stT, stL, State.curRealm, Inst.instStateFn_realms, Inst.instStateFn_realm]
theorem stT_curRealm : (stT t ge g gb gtv ctx fp).curRealm = t.curRealm := by
  simp [stT, stL, State.curRealm, Inst.instStateFn_realms, Inst.instStateFn_realm]

end

theorem gdi (t : State) (ge : EnvId) (g : ObjId) (ctx : Ctx) (gb : HashMap JSStr Binding) (gtv : Value)
    (fp : ObjId) (hstrict : ctx.strict = false) (hge : ge < t.envs.size)
    (hE : t.envEntry ge = .global g gb gtv) (hgbb : gb.contains "b" = false) (hgbt : gb.contains "total" = false)
    (hgbd : gb.contains "double" = false)
    (hgs : g < t.heap.size) (hk : (t.objEntry g).kind = .ordinary) (hx : (t.objEntry g).extensible = true)
    (hpb : (t.objEntry g).props.get? (.str "b") = none) (hpt : (t.objEntry g).props.get? (.str "total") = none)
    (hpd : (t.objEntry g).props.get? (.str "double") = none)
    (hfp : t.curRealm.intrinsics["%Function.prototype%"]? = some fp) :
    globalDeclarationInstantiation DTGen.script_stmts ge g ctx t =
      .ok (AddScript.gdiCtx ctx) (stD t ge g gb gtv (AddScript.gdiCtx ctx) fp) := by
  have hk' : (t.objEntry g).kind.isPlain = true := by rw [hk]; rfl
  have hnt : DTGen.total_func.name = some (JSStr.ofString "total") := rfl
  have hnd : DTGen.double_func.name = some (JSStr.ofString "double") := rfl
  let c := AddScript.gdiCtx ctx
  -- `b`
  have hcm := createMutableBinding_global ge "b" false t g gb gtv hge hE
  -- `total`
  let tL := stL t ge g gb gtv
  have hiT := Inst.instantiate_fn DTGen.total_func "total" simple_total tL ge c fp (by simp [tL, stL]; exact hfp)
  let uT := Inst.instStateFn DTGen.total_func "total" tL ge c.script fp
  have hgL : g < tL.heap.size := by simp [tL, stL]; exact hgs
  have huT : uT.objEntry g = t.objEntry g := by
    simp only [uT]; rw [Inst.instStateFn_entry_lt _ _ _ _ _ _ _ hgL]; simp [tL, stL]
  have hcgT := AddScript.createGlobalFunctionBinding_new uT g "total" (.obj tL.heap.size)
    (by simp only [uT]; rw [Inst.instStateFn_size]; exact Nat.lt_succ_of_lt (Nat.lt_succ_of_lt hgL))
    (by rw [huT]; exact hk) (by rw [huT]; exact hx)
    (by rw [huT]; exact hpt)
  -- `double`
  let tT := stT t ge g gb gtv c fp
  have hiD := Inst.instantiate_fn DTGen.double_func "double" simple_double tT ge c fp
    (by rw [stT_curRealm]; exact hfp)
  let uD := Inst.instStateFn DTGen.double_func "double" tT ge c.script fp
  have hgT : g < tT.heap.size := by simp only [tT]; rw [stT_heap_size]; exact Nat.lt_succ_of_lt (Nat.lt_succ_of_lt hgs)
  have hTg : tT.objEntry g = ((t.objEntry g).withProps (·.insert (.str "total")
      (.data (.obj tL.heap.size) true true false))).withProps (·.insert (.str "total")
      (.data (.obj tL.heap.size) true true false)) := by
    have hgu : g < uT.heap.size := by
      simp only [uT]; rw [Inst.instStateFn_size]; exact Nat.lt_succ_of_lt (Nat.lt_succ_of_lt hgL)
    simp only [tT, stT]
    rw [State.setProp_entry_self _ _ _ _ (by simpa using hgu), State.setProp_entry_self _ _ _ _ hgu, huT]
  have huD : uD.objEntry g = tT.objEntry g := by simp only [uD]; rw [Inst.instStateFn_entry_lt _ _ _ _ _ _ _ hgT]
  have hne : PropKey.str (JSStr.ofString "total") ≠ PropKey.str (JSStr.ofString "double") := by
    intro h; injection h with h; revert h; decide
  have hcgD := AddScript.createGlobalFunctionBinding_new uD g "double" (.obj tT.heap.size)
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
      (Inst.instStateFn DTGen.total_func "total" tL ge c.script fp) = .ok () tT := hcgT
  have hcgD' : createGlobalFunctionBinding g "double" (.obj tT.heap.size) false
      (Inst.instStateFn DTGen.double_func "double" tT ge c.script fp) = .ok () (stD t ge g gb gtv c fp) :=
    hcgD
  have hk1 : (VarKind.let == VarKind.const) = false := by decide
  have hk2 : (VarKind.let == VarKind.using) = false := by decide
  have hk3 : (VarKind.let == VarKind.awaitUsing) = false := by decide
  simp only [globalDeclarationInstantiation, varScoped, lexScoped, hstrict]
  simp [names_b, annexB, globalDeclRecHas, readEnv_entry _ _ _ hge, hE, hgbb, hgbt, hgbd, hasRestrictedGlobalProperty,
    canDeclareGlobalFunction, Obj'.getOwnProperty_entry _ _ _ hgs hk', Obj'.isExtensible_entry _ _ hgs hk', hx, hpb,
    hpt, hpd, hnt, hnd, VarScoped.names, M.bind_eq, M.bind_apply, M.bindRes_ok, ne_td, ne_dt, LexScoped.isConstant, pure, M.pure, funcNameKey, hctx, hcm', hk1, hk2, hk3, hiT, hcgT', hiD, hcgD']
  exact ⟨rfl, rfl⟩

/-! ## The statements -/

/-- An identifier bound (and initialized) in the global record's declarative part. -/
theorem identValue_global_decl (env : EnvId) (n : JSStr) (strict : Bool) (s : State) (g : ObjId)
    (b : HashMap JSStr Binding) (tv : Value) (bd : Binding) (v : Value) (h : env < s.envs.size)
    (hE : s.envEntry env = .global g b tv) (hb : b[n]? = some bd) (hbm : (n ∈ b) = True) (hv : bd.value = some v)
    (hf : s.fuel ≠ 0) : identValue env n strict s = .ok v s := by
  obtain ⟨k, hk1⟩ : ∃ k, s.fuel = k + 1 := ⟨s.fuel - 1, by omega⟩
  have hbn : ∀ hm : n ∈ b, b[n]'hm = bd := fun hm => by
    have := Std.HashMap.getElem?_eq_some_getElem (m := b) hm
    rw [hb] at this; exact (Option.some.inj this).symm
  rw [identValue_loop, hk1]
  cases bd with | mk val mu st de =>
  simp only at hv; subst hv
  simp [hbn, M.loop, identBody, M.bind_eq, M.bind_apply, readEnv_entry _ _ _ h, hE, pure, M.pure, resolveBinding, hasBinding,
    hbm, getRefValue, getBindingValue, hb, hk1, M.repeatFrom]

/-- The statement `nm(b)`, with `nm` a function bound on the global object and `b` (in the global
record's declarative part) the object `A`: asks the driver to call the function with `this` undefined;
when that returns `v`, the statement completes normally with `v`. -/
theorem call_req (c : Ctx) (w : State) (ge g fo A : Nat) (nm : JSStr) (gb : HashMap JSStr Binding) (gtv : Value)
    (d : FuncData) (bd : Binding) (hlex : c.lex = ge) (hstr : c.strict = false)
    (hge : ge < w.envs.size) (hE : w.envEntry ge = .global g gb gtv) (hgb : gb.contains nm = false)
    (hgb' : gb[nm]? = none) (hgbm : (nm ∈ gb) = False) (hbb : gb[JSStr.ofString "b"]? = some bd)
    (hbm : (JSStr.ofString "b" ∈ gb) = True) (hbv : bd.value = some (.obj A))
    (hgs : g < w.heap.size) (hk : (w.objEntry g).kind = .ordinary)
    (hp : (w.objEntry g).props.get? (.str nm) = some (.data (.obj fo) true true false))
    (hfs : fo < w.heap.size) (hfk : (w.objEntry fo).kind = .func d) (hf : 2 ≤ w.fuel) :
    ∃ K, Sem.exprStmt (Sem.call (Sem.identRef nm) (Sem.args #[Sem.ArgD.expr (Sem.ident "b")]) false
        (CalleeDesc.ident nm)) c w = .req (.call (.obj fo) .undefined #[.obj A]) w K ∧
      ∀ v t, K (.normal v) t = .ok (.normal (some v)) t := by
  obtain ⟨k, hk2⟩ : ∃ k, w.fuel = k + 2 := ⟨w.fuel - 2, by omega⟩
  have hk' : (w.objEntry g).kind.isPlain = true := by rw [hk]; rfl
  have hid := identValue_global_decl ge "b" false w g gb gtv bd (.obj A) hge hE hbb hbm hbv (by omega)
  refine ⟨?K, ?h, ?_⟩
  case h =>
    conv =>
      lhs
      simp [Sem.exprStmt, Sem.call, Sem.identRef, hlex, hstr, resolveBinding, hasBinding, readEnv_entry _ _ _ hge,
        hE, hgb, Obj'.hasProperty_entry_own _ _ _ hgs hk', hp, getRefValue, getBindingValue, hgb', getProp,
        Obj'.get_entry_data _ _ _ _ hgs hk', refThisValue, Sem.args, Sem.ident, hid, M.repeatFrom, hk2, M.loop,
        isCallable, readObj_entry' _ _ _ hfs, hfk, ES.call, pure, M.pure, Sem.inner, hgbm, hbb, hbm, hbv,
        M.bind_eq, M.bind_apply, M.bindRes_ok]
  intro v t
  simp [M.pure, pure]

/-- The literals 3, 4, 5 as the generated code writes them. -/
abbrev l3 : F64 := F64.fin false 6755399441055744 (-51)
abbrev l4 : F64 := F64.fin false 4503599627370496 (-50)
abbrev l5 : F64 := F64.fin false 5629499534213120 (-50)

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

/-- `resolveBinding` of a name in the global record's declarative part. -/
theorem resolveBinding_global_decl (env : EnvId) (n : JSStr) (strict : Bool) (s : State) (g : ObjId)
    (b : HashMap JSStr Binding) (tv : Value) (h : env < s.envs.size) (hE : s.envEntry env = .global g b tv)
    (hbm : (n ∈ b) = True) (hf : s.fuel ≠ 0) :
    resolveBinding env n strict s = .ok (.env (some env) n strict) s := by
  obtain ⟨k, hk1⟩ : ∃ k, s.fuel = k + 1 := ⟨s.fuel - 1, by omega⟩
  rw [resolveBinding_loop, hk1]
  simp [M.loop, resolveBody, M.bind_eq, M.bind_apply, hasBinding, readEnv_entry _ _ _ h, hE, hbm, pure, M.pure]

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
abbrev callOf (nm : JSStr) : Sem.CStmt :=
  Sem.exprStmt (Sem.call (Sem.identRef nm) (Sem.args #[Sem.ArgD.expr (Sem.ident "b")]) false (CalleeDesc.ident nm))

theorem script_def (n : Nat) : DTGen.script n = Sem.stmts #[Sem.funDecl DTGen.total_func,
    Sem.funDecl DTGen.double_func, Sem.varDecl #[Sem.declLex VarKind.let "b" (some arr3)], callOf "double",
    callOf "total"] := rfl

/-- The script's statements: the function declarations do nothing (they were instantiated), `let b`
runs, and `double(b)` asks for its call; when it returns, `total(b)` asks for its call, and when that
returns `v` the statements complete normally with `v`. -/
theorem body_req (n : Nat) (c : Ctx) (u u2 : State) (r4 : Req) (K4 : Outcome → State → Res Compl)
    (hann : c.annexB = funcIds #[]) (hf : 6 ≤ u.fuel)
    (h3 : Sem.varDecl #[Sem.declLex VarKind.let "b" (some arr3)] c u = .ok (.normal none) u2)
    (h4 : callOf "double" c u2 = .req r4 u2 K4) (hK4 : ∀ v t, K4 (.normal v) t = .ok (.normal (some v)) t) :
    ∃ K, DTGen.script n c u = .req r4 u2 K ∧
      ∀ w r5 (K5 : Outcome → State → Res Compl), callOf "total" c w = .req r5 w K5 →
        (∀ v t, K5 (.normal v) t = .ok (.normal (some v)) t) →
        ∃ K', K (.normal .undefined) w = .req r5 w K' ∧ ∀ v t, K' (.normal v) t = .ok (.normal (some v)) t := by
  obtain ⟨k, hk⟩ : ∃ k, u.fuel = k + 6 := ⟨u.fuel - 6, by omega⟩
  have hann0 : ∀ i, (funcIds #[]).contains i = false := by simp [funcIds]
  refine ⟨?K, ?h, ?_⟩
  case h =>
    conv =>
      lhs
      rw [script_def]
      simp [Sem.stmts, M.repeatFrom, hk, M.loop, Sem.funDecl, hann, hann0, h3, h4, M.bind_eq, M.bind_apply,
        M.bindRes_ok, M.bindRes_req, pure, M.pure]
  intro w r5 K5 h5 hK5
  refine ⟨?K', ?h', ?_⟩
  case h' =>
    conv =>
      lhs
      simp [hK4, M.loopRes_inl, M.loop, h5, M.bind_eq, M.bind_apply, M.bindRes_ok, M.bindRes_req, M.loopRes_req,
        pure, M.pure]
  intro v t
  simp [hK5, M.loopRes_inl, M.loopRes_inr, M.loop, M.bind_eq, M.bind_apply, M.bindRes_ok, pure, M.pure,
    Compl.updateEmpty]

/-! ## The states along the way -/

theorem ne_bd : (JSStr.ofString "b" = JSStr.ofString "double") = False := by simp; decide
theorem ne_bt : (JSStr.ofString "b" = JSStr.ofString "total") = False := by simp; decide

/-- The global record's declarative part once `b` holds `A`. -/
def gb2 (gb : HashMap JSStr Binding) (A : ObjId) : HashMap JSStr Binding :=
  (gb.insert "b" { deletable := false }).modify "b" fun bd => { bd with value := some (.obj A) }

section
variable (gb : HashMap JSStr Binding) (A : ObjId)
theorem gb2_b : (gb2 gb A)[JSStr.ofString "b"]? = some { value := some (.obj A), deletable := false } := by
  simp [gb2, Std.HashMap.getElem?_modify]
theorem gb2_mem_b : (JSStr.ofString "b" ∈ gb2 gb A) = True := by simp [gb2]
theorem gb2_contains (n : JSStr) (hn : (JSStr.ofString "b" = n) = False) (h : gb.contains n = false) :
    (gb2 gb A).contains n = false := by
  simp [gb2, Std.HashMap.contains_insert, h, hn]
theorem gb2_get (n : JSStr) (hn : (JSStr.ofString "b" = n) = False) (h : gb.contains n = false) :
    (gb2 gb A)[n]? = none := by
  have : gb[n]? = none := Std.HashMap.getElem?_eq_none (fun hm => by
    rw [Std.HashMap.mem_iff_contains, h] at hm; exact Bool.false_ne_true hm)
  simp [gb2, Std.HashMap.getElem?_modify, Std.HashMap.getElem?_insert, hn, this]
theorem gb2_mem (n : JSStr) (hn : (JSStr.ofString "b" = n) = False) (h : gb.contains n = false) :
    (n ∈ gb2 gb A) = False := by
  simp [Std.HashMap.mem_iff_contains, gb2_contains gb A n hn h]
end

theorem isArray_of_arrayObj (A : ObjId) (len : Nat) (xs : Nat → Nat) (t : State)
    (hA : ArrayObj A len (fun j => num (xs j)) t) : IsArray A len xs t := by
  obtain ⟨a1, a2, -, a4, a5, -⟩ := hA
  exact ⟨a1, a2, ⟨true, false, false, by rw [← kLength_eq]; exact a4⟩,
    fun j hj => ⟨true, true, true, by rw [key_eq]; exact a5 j hj⟩⟩

theorem psum24 : psum (fun j => 2 * xs3 j) 3 = 24 := by decide

/-- What GlobalDeclarationInstantiation leaves: `b` declared (uninitialized) in the global record,
`total` (object `t.heap.size`) and `double` (object `t.heap.size + 2`) bound on the global object. -/
theorem stD_facts (t : State) (ge : EnvId) (g : ObjId) (gb : HashMap JSStr Binding) (gtv : Value) (c : Ctx)
    (fp : ObjId) (hge : ge < t.envs.size) (hgs : g < t.heap.size) :
    let u := stD t ge g gb gtv c fp
    u.envEntry ge = .global g (gb.insert "b" { deletable := false }) gtv ∧ u.envs.size = t.envs.size ∧
    (∀ e, e ≠ ge → u.envEntry e = t.envEntry e) ∧
    (u.objEntry g).kind = (t.objEntry g).kind ∧
    (u.objEntry g).props.get? (.str "total") = some (.data (.obj t.heap.size) true true false) ∧
    (u.objEntry g).props.get? (.str "double") = some (.data (.obj (t.heap.size + 2)) true true false) ∧
    (u.objEntry t.heap.size).kind = .func (Inst.fnData DTGen.total_func (stL t ge g gb gtv) ge c.script) ∧
    (u.objEntry (t.heap.size + 2)).kind =
      .func (Inst.fnData DTGen.double_func (stT t ge g gb gtv c fp) ge c.script) ∧
    u.heap.size = t.heap.size + 4 ∧ u.fuel = t.fuel ∧ u.realms = t.realms := by
  intro u
  have hLs : (stL t ge g gb gtv).heap.size = t.heap.size := by simp [stL]
  have hTs : (stT t ge g gb gtv c fp).heap.size = t.heap.size + 2 := stT_heap_size _ _ _ _ _ _ _
  obtain ⟨tL, htL⟩ : ∃ x, stL t ge g gb gtv = x := ⟨_, rfl⟩
  obtain ⟨tT, htT⟩ : ∃ x, stT t ge g gb gtv c fp = x := ⟨_, rfl⟩
  rw [htL] at hLs; rw [htT] at hTs
  have hu : u = ((Inst.instStateFn DTGen.double_func "double" tT ge c.script fp).setProp g (.str "double")
      (.data (.obj tT.heap.size) true true false)).setProp g (.str "double") (.data (.obj tT.heap.size) true true false) := by
    simp only [u, stD, htT]
  have hT : tT = ((Inst.instStateFn DTGen.total_func "total" tL ge c.script fp).setProp g (.str "total")
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
  have hgUT : g < (Inst.instStateFn DTGen.total_func "total" tL ge c.script fp).heap.size := by
    rw [Inst.instStateFn_size]; exact Nat.lt_succ_of_lt (Nat.lt_succ_of_lt hgL)
  have hgT : g < tT.heap.size := by rw [hTs]; exact Nat.lt_succ_of_lt (Nat.lt_succ_of_lt hgs)
  have hgUD : g < (Inst.instStateFn DTGen.double_func "double" tT ge c.script fp).heap.size := by
    rw [Inst.instStateFn_size]; exact Nat.lt_succ_of_lt (Nat.lt_succ_of_lt hgT)
  have hTg : tT.objEntry g = ((t.objEntry g).withProps (·.insert (.str "total")
      (.data (.obj tL.heap.size) true true false))).withProps (·.insert (.str "total")
      (.data (.obj tL.heap.size) true true false)) := by
    rw [hT, State.setProp_entry_self _ _ _ _ (by simpa using hgUT), State.setProp_entry_self _ _ _ _ hgUT,
      Inst.instStateFn_entry_lt _ _ _ _ _ _ _ hgL, hLo]
  have hug : u.objEntry g = ((tT.objEntry g).withProps (·.insert (.str "double")
      (.data (.obj tT.heap.size) true true false))).withProps (·.insert (.str "double")
      (.data (.obj tT.heap.size) true true false)) := by
    rw [hu, State.setProp_entry_self _ _ _ _ (by simpa using hgUD), State.setProp_entry_self _ _ _ _ hgUD,
      Inst.instStateFn_entry_lt _ _ _ _ _ _ _ hgT]
  have hne : PropKey.str (JSStr.ofString "double") ≠ PropKey.str (JSStr.ofString "total") := by
    intro h; injection h with h; revert h; decide
  -- the function objects
  have hfT : t.heap.size < tT.heap.size := by rw [hTs]; exact Nat.lt_succ_of_lt (Nat.lt_succ_self _)
  have hgfT : g ≠ t.heap.size := Nat.ne_of_lt hgs
  have hgfD : g ≠ t.heap.size + 2 := Nat.ne_of_lt (Nat.lt_succ_of_lt (Nat.lt_succ_of_lt hgs))
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
  · simp only [u]; exact stD_heap_size _ _ _ _ _ _ _
  · simp only [u]; exact stD_fuel _ _ _ _ _ _ _
  · simp only [u]; exact stD_realms _ _ _ _ _ _ _

theorem stT_realm (t : State) (ge : EnvId) (g : ObjId) (gb : HashMap JSStr Binding) (gtv : Value) (c : Ctx)
    (fp : ObjId) : (stT t ge g gb gtv c fp).realm = t.realm := by
  simp [stT, stL, Inst.instStateFn_realm]
theorem total_same : DTGen.total_func = TotalGen.total_func := rfl
theorem isDouble_dt : MoreCalls.IsDouble DTGen.double_func := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## The whole script -/

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
  -- ScriptEvaluation's first steps: the script record and its context
  let ge := s.curRealm.globalEnv
  let g := s.curRealm.globalObj
  let t : State := { s with scripts := s.scripts.push { prog := DTGen.program, realm := s.realm, path := "" }, script := s.scripts.size }
  let ctx0 : Ctx := { lex := ge, var := ge, strict := false, realm := s.realm, script := s.scripts.size }
  have htr : t.curRealm = s.curRealm := rfl
  have hge' : ge < t.envs.size := hge
  have hE' : t.envEntry ge = .global g gb gtv := hE
  have hgs' : g < t.heap.size := hgs
  have hsz : t.heap.size = s.heap.size := rfl
  have htf : t.fuel = s.fuel := rfl
  -- GlobalDeclarationInstantiation
  have hgdi := gdi t ge g ctx0 gb gtv fp rfl hge' hE' hgbb hgbt hgbd hgs' hk hx hpb hpt hpd (by rw [htr]; exact hfp)
  let c := AddScript.gdiCtx ctx0
  obtain ⟨hE1, hz1, -, hgk1, hpt1, hpd1, hfTk, hfDk, hsz1, hfu1, hrl1⟩ := stD_facts t ge g gb gtv c fp hge' hgs'
  obtain ⟨u, hu⟩ : ∃ u, stD t ge g gb gtv c fp = u := ⟨_, rfl⟩
  rw [hu] at hgdi hE1 hz1 hgk1 hpt1 hpd1 hfTk hfDk hsz1 hfu1 hrl1
  let fT := t.heap.size
  let fD := t.heap.size + 2
  obtain ⟨dT, hdT⟩ : ∃ d, Inst.fnData DTGen.total_func (stL t ge g gb gtv) ge c.script = d := ⟨_, rfl⟩
  obtain ⟨dD, hdD⟩ : ∃ d, Inst.fnData DTGen.double_func (stT t ge g gb gtv c fp) ge c.script = d := ⟨_, rfl⟩
  rw [hdT] at hfTk; rw [hdD] at hfDk
  have hdr : dD.realm = s.realm := by rw [← hdD, Inst.fnData_realm, stT_realm]
  have htrl : dT.realm = s.realm := by rw [← hdT, Inst.fnData_realm]; simp [stL]; rfl
  have hcodeD : MoreCalls.IsDouble dD.code := by rw [← hdD, Inst.fnData_code]; exact isDouble_dt
  have hcodeT : dT.code = TotalGen.total_func := by rw [← hdT, Inst.fnData_code]; exact total_same
  have hclsD : dD.isClassCtor = false := by rw [← hdD, Inst.fnData_isClassCtor]
  have hclsT : dT.isClassCtor = false := by rw [← hdT, Inst.fnData_isClassCtor]
  have hmD : dD.thisMode = .global := by rw [← hdD, Inst.fnData_thisMode]
  have hmT : dT.thisMode = .global := by rw [← hdT, Inst.fnData_thisMode]
  have hgeu : ge < u.envs.size := by rw [hz1]; exact hge'
  have hgu : g < u.heap.size := by rw [hsz1]; exact Nat.lt_of_lt_of_le hgs' (Nat.le_add_right _ _)
  have hfTu : fT < u.heap.size := by show t.heap.size < u.heap.size; rw [hsz1]; omega
  have hfDu : fD < u.heap.size := by show t.heap.size + 2 < u.heap.size; rw [hsz1]; omega
  -- `let b = [3, 4, 5]`
  obtain ⟨u2, h3, hE2, hA2, hz2, hsz2, ho2, hfu2, -, hrl2⟩ := let_b c u ge g (gb.insert "b" { deletable := false }) gtv
    rfl rfl hgeu hE1 (by simp) (by rw [hfu1, htf]; omega)
  let A := u.heap.size
  have hE2' : u2.envEntry ge = .global g (gb2 gb A) gtv := hE2
  have hge2 : ge < u2.envs.size := by rw [hz2]; exact hgeu
  have hgA : g ≠ A := Nat.ne_of_lt hgu
  have hfTA : fT ≠ A := Nat.ne_of_lt hfTu
  have hk2 : (u2.objEntry g).kind = .ordinary := by rw [ho2 g hgu, hgk1]; exact hk
  have hpd2 : (u2.objEntry g).props.get? (.str "double") = some (.data (.obj fD) true true false) := by
    rw [ho2 g hgu]; exact hpd1
  have hpt2 : (u2.objEntry g).props.get? (.str "total") = some (.data (.obj fT) true true false) := by
    rw [ho2 g hgu]; exact hpt1
  have hfD2 : fD < u2.heap.size := by rw [hsz2]; exact Nat.lt_succ_of_lt hfDu
  have hfT2 : fT < u2.heap.size := by rw [hsz2]; exact Nat.lt_succ_of_lt hfTu
  have hfDk2 : (u2.objEntry fD).kind = .func dD := by rw [ho2 fD hfDu]; exact hfDk
  have hfTk2 : (u2.objEntry fT).kind = .func dT := by rw [ho2 fT hfTu]; exact hfTk
  have hgu2 : g < u2.heap.size := by rw [hsz2]; exact Nat.lt_succ_of_lt hgu
  have hfuel2 : u2.fuel = s.fuel := by rw [hfu2, hfu1, htf]
  -- `double(b)` asks for its call
  obtain ⟨K4, h4, hK4⟩ := call_req c u2 ge g fD A "double" (gb2 gb A) gtv dD _ rfl rfl hge2 hE2'
    (gb2_contains gb A _ ne_bd hgbd) (gb2_get gb A _ ne_bd hgbd) (gb2_mem gb A _ ne_bd hgbd) (gb2_b gb A)
    (gb2_mem_b gb A) rfl hgu2 hk2 hpd2 hfD2 hfDk2 (by omega)
  obtain ⟨K, hreq, hK⟩ := body_req 999956 c u u2 _ K4 rfl (by rw [hfu1, htf]; omega) h3 h4 hK4
  have hscript : evalStmts evalDepth (AddScript.gdiCtx ctx0) DTGen.script_stmts u = DTGen.script 999956 c u := by
    rw [DTGen.script_eq]; rfl
  -- the call of `double`, answered by the driver
  obtain ⟨u2', hu2'⟩ : ∃ x, ({ u2 with fuel := u2.fuel - 1 } : State) = x := ⟨_, rfl⟩
  have hr2' : u2'.realms = s.realms := by rw [← hu2']; exact hrl2.trans hrl1
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
  obtain ⟨K', hK1, hK'⟩ := hK s3 _ K5 h5 hK5
  -- the call of `total`, answered by the driver
  obtain ⟨s3', hs3'⟩ : ∃ x, ({ s3 with fuel := s3.fuel - 1 } : State) = x := ⟨_, rfl⟩
  have hr3' : s3'.realms = s.realms := by rw [← hs3']; exact hr3.trans hr2'
  have hgeT : (s3'.realms[dT.realm]!).globalEnv = ge := by rw [hr3', htrl]; rfl
  have hz3' : s3'.envs = s3.envs := by rw [← hs3']
  obtain ⟨s4, hcallT, -, -⟩ := TotalCall.total_call fT dT s3' A 3 (fun j => 2 * xs3 j) g (gb2 gb A) gtv hcodeT hclsT hmT
    (by rw [hgeT, hz3']; exact hge3) (by rw [hgeT]; simp only [State.envEntry, hz3']; exact hE3)
    (by decide) (by intro j hj; simp only [xs3]; omega)
    (isArray_of_arrayObj A 3 _ s3' (MoreCalls.arrayObj_of_heap A 3 _ s3 s3' (by rw [← hs3']) hA3))
    (by rw [← hs3']; simp only; omega)
  have himplT : callImpl eng (.obj fT) .undefined #[.obj A] s3 = .ok (num (psum (fun j => 2 * xs3 j) 3)) s4 := by
    rw [callImpl_func eng fT dT _ _ s3 (by rw [hhs3]; exact hfT2) (by rw [hobj fT hfTA]; exact hfTk2) (by omega), hs3']
    exact hcallT
  -- the script, with the driver
  have hbody : DTGen.program.body = DTGen.script_stmts := rfl
  have hstr : DTGen.program.strict = false := rfl
  refine ⟨s4, ?_⟩
  simp only [runM, callDepth, scriptEvaluation, M.bind_eq, M.bind_apply, M.readS_apply, M.bindRes_ok, M.modify_apply,
    hbody, hstr]
  rw [hgdi]
  simp only [M.bindRes_ok, M.bind_apply, hscript, hreq, M.bindRes_req]
  rw [drive_call_ok eng 3999 _ _ _ _ _ cs _ _ himplD]
  simp only [hK1, M.bindRes_req]
  rw [drive_call_ok eng 3999 _ _ _ _ _ cs _ _ himplT]
  simp only [hK', M.bindRes_ok, Option.getD_some, psum24]
  simp only [pure, M.pure, drive_ok]
  rfl

end DTScript
