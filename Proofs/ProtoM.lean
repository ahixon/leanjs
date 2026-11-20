import Proofs.Nested
import Proofs.PRGen

/-!
# Prototype methods: `o.inc()` found on `o`'s prototype (examples/proto.js)

```js
function inc() { this.n = this.n + 1; return this.n; }
let p = { inc: inc };
let o = { __proto__: p, n: 0 };
o.inc();
o.inc();
```
evaluates to 2: `o`'s prototype is `p` (the object literal's `__proto__`, [[SetPrototypeOf]] on the new object),
and `o.inc` is found on it ([[Get]] through the chain); `this` is `o`, whose own `n` the method updates.
-/

open ES ES.Conv SumProof

namespace ProtoM

/-- An object's prototype replaced, as a named state update. -/
def State.setProto (s : State) (o : ObjId) (v : Value) : State :=
  { s with heap := s.heap.modify o fun ob => { ob with proto := v } }

section
variable (s : State) (o : ObjId) (v : Value)
@[simp] theorem setProto_heap_size : (State.setProto s o v).heap.size = s.heap.size := by simp [State.setProto]
@[simp] theorem setProto_envs : (State.setProto s o v).envs = s.envs := by simp [State.setProto]
@[simp] theorem setProto_fuel : (State.setProto s o v).fuel = s.fuel := by simp [State.setProto]
@[simp] theorem setProto_realms : (State.setProto s o v).realms = s.realms := by simp [State.setProto]
@[simp] theorem setProto_realm : (State.setProto s o v).realm = s.realm := by simp [State.setProto]
@[simp] theorem setProto_curRealm : (State.setProto s o v).curRealm = s.curRealm := by
  simp [State.setProto, State.curRealm]
theorem setProto_entry_self (h : o < s.heap.size) :
    (State.setProto s o v).objEntry o = { s.objEntry o with proto := v } := by
  simp [State.setProto, State.objEntry, Array.getElem_modify, h]
theorem setProto_entry_ne (i : ObjId) (hne : o ≠ i) : (State.setProto s o v).objEntry i = s.objEntry i := by
  simp [State.setProto, State.objEntry, Array.getElem?_modify, hne]
end

/-- **[[SetPrototypeOf]]** of a fresh ordinary object `O` to `P`, whose chain is `P` → `OP` → null (none of
them `O`): succeeds, and only `O`'s prototype changes. -/
theorem setPrototypeOf_fresh (t : State) (O P OP : ObjId) (hO : O < t.heap.size) (hOk : (t.objEntry O).kind = .ordinary)
    (hOx : (t.objEntry O).extensible = true) (hOi : (t.objEntry O).immutableProto = false)
    (hOp : (t.objEntry O).proto = .obj OP) (hPO : P ≠ O) (hPOP : P ≠ OP) (hP : P < t.heap.size)
    (hPk : (t.objEntry P).kind = .ordinary) (hPp : (t.objEntry P).proto = .obj OP) (hOPO : OP ≠ O)
    (hOP : OP < t.heap.size) (hOPk : (t.objEntry OP).kind = .ordinary) (hOPp : (t.objEntry OP).proto = .null)
    (hf : 3 ≤ t.fuel) :
    Obj'.setPrototypeOf O (.obj P) t = .ok true (State.setProto t O (.obj P)) := by
  obtain ⟨k, hk⟩ : ∃ k, t.fuel = k + 3 := ⟨t.fuel - 3, by omega⟩
  have hd : maxDepth = 19999 + 1 := by decide
  have hsv : sameValue (.obj P) (.obj OP) = false := by simp [sameValue, hPOP]
  unfold Obj'.setPrototypeOf
  rw [hd, ES.setPrototypeOf]
  simp [objKind, M.bind_eq, M.bind_apply, readObj_entry' _ _ _ hO, hOk, hOx, hOi, hOp, hsv, M.repeatFrom, hk, M.loop,
    readObj_entry' _ _ _ hP, hPk, hPp, objProto, hPO, hOPO, readObj_entry' _ _ _ hOP, hOPk, hOPp, modifyObj, pure, M.pure,
    State.setProto, State.withHeap_eq]

/-! ## The two object literals -/

abbrev zero0 : F64 := F64.fin false 0 (-1074)
abbrev objP : Sem.CExpr := Sem.object #[Sem.PropD.init (Sem.KeyD.name (PropName.ident "inc")) (fun _ => Sem.ident "inc")]
abbrev objO : Sem.CExpr := Sem.object #[Sem.PropD.protoSet (Sem.ident "p"),
  Sem.PropD.init (Sem.KeyD.name (PropName.ident "n")) (fun _ => Sem.lit (Lit.num zero0))]

/-- After `{ inc: inc }`: the new object (`u.heap.size`) with `inc`. -/
def pState (u : State) (fI : ObjId) : State :=
  (u.allocObj { proto := .obj u.curRealm.objectProto }).setProp u.heap.size (.str "inc") (.data (.obj fI) true true true)

/-- After `{ __proto__: p, n: 0 }`: the new object (`u.heap.size`) with prototype `P` and `n = 0`. -/
def oState (u : State) (P : ObjId) : State :=
  (State.setProto (u.allocObj { proto := .obj u.curRealm.objectProto }) u.heap.size (.obj P)).setProp u.heap.size
    (.str "n") (.data (num 0) true true true)

/-- **`let p = { inc: inc }`**, `p` declared in the global record, `inc` on the global object. -/
theorem let_p (c : Ctx) (u : State) (ge g fI : Nat) (gb : Std.HashMap JSStr Binding) (gtv : Value)
    (hlex : c.lex = ge) (hstr : c.strict = false) (hge : ge < u.envs.size) (hE : u.envEntry ge = .global g gb gtv)
    (hbm : (JSStr.ofString "p" ∈ gb) = True) (hgi : gb.contains "inc" = false)
    (hgim : (JSStr.ofString "inc" ∈ gb) = False) (hgi' : gb[JSStr.ofString "inc"]? = none)
    (hgs : g < u.heap.size) (hk : (u.objEntry g).kind = .ordinary)
    (hp : (u.objEntry g).props.get? (.str "inc") = some (.data (.obj fI) true true false)) (hf : 2 ≤ u.fuel) :
    Sem.varDecl #[Sem.declLex VarKind.let "p" (some objP)] c u =
      .ok (.normal none) ((pState u fI).setEnv ge (.global g (gb.modify "p" fun bd =>
        { bd with value := some (.obj u.heap.size) }) gtv)) := by
  have hk' : (u.objEntry g).kind.isPlain = true := by rw [hk]; rfl
  have hr := Global.resolveBinding_global_decl ge "p" false u g gb gtv hge hE hbm (by omega)
  obtain ⟨t1, ht1⟩ : ∃ x, u.allocObj { proto := .obj u.curRealm.objectProto } = x := ⟨_, rfl⟩
  have hO1 : u.heap.size < t1.heap.size := by rw [← ht1]; simp [State.allocObj]
  have hE1 : t1.objEntry u.heap.size = { proto := .obj u.curRealm.objectProto } := by
    rw [← ht1]; exact State.allocObj_entry_new _ _
  have hgO : g ≠ u.heap.size := Nat.ne_of_lt hgs
  have hog1 : t1.objEntry g = u.objEntry g := by rw [← ht1, State.allocObj_entry_lt _ _ _ hgs]
  have hz1 : t1.heap.size = u.heap.size + 1 := by rw [← ht1]; simp [State.allocObj]
  have hf1 : t1.fuel = u.fuel := by rw [← ht1]; simp [State.allocObj]
  have he1 : t1.envs = u.envs := by rw [← ht1]; simp [State.allocObj]
  have hinc : identValue ge "inc" false t1 = .ok (.obj fI) t1 :=
    Global.identValue_global_obj ge "inc" false t1 g gb gtv _ _ _ _ (by rw [he1]; exact hge)
      (by simp only [State.envEntry, he1]; exact hE) hgi hgim hgi' (by rw [hz1]; exact Nat.lt_succ_of_lt hgs)
      (by rw [hog1]; exact hk') (by rw [hog1]; exact hp) (by rw [hf1]; exact hf)
  have hc1 := Method.cdp_ordinary u.heap.size (.str "inc") (.obj fI) t1 hO1 (by simp [hE1]) (by simp [hE1]) (by simp [hE1])
  obtain ⟨t2, ht2⟩ : ∃ x, t1.setProp u.heap.size (.str "inc") (.data (.obj fI) true true true) = x := ⟨_, rfl⟩
  rw [ht2] at hc1
  have he2 : t2.envs = u.envs := by rw [← ht2, State.setProp_envs, he1]
  have hin := Global.initializeBinding_global ge "p" (.obj u.heap.size) t2 g gb gtv (by rw [he2]; exact hge)
    (by simp only [State.envEntry, he2]; exact hE) (Std.HashMap.mem_iff_contains.mp (of_eq_true hbm))
  have hst : pState u fI = t2 := by rw [← ht2, ← ht1]; rfl
  rw [hst]
  have hlu : (VarKind.let == VarKind.using) = false := by decide
  have hla : (VarKind.let == VarKind.awaitUsing) = false := by decide
  have hik : Sem.propKey (Sem.KeyD.name (PropName.ident "inc")) = fun _ => pure (PropKey.str "inc") := rfl
  simp [Sem.varDecl, M.forArr_def, M.foldArr_toArray, M.foldList_cons, M.foldList_nil, Sem.declLex, Sem.inner, hlex,
    hstr, hr, Sem.object, newObject_eq, ht1, hik, Sem.ident, hinc, hc1, initializeRefBinding, hin, hlu, hla, pure,
    M.pure, M.bind_eq, M.bind_apply, M.bindRes_ok]

/-- **`let o = { __proto__: p, n: 0 }`**, `p` (a `let` of the global record) the ordinary object `P`, whose chain is
`P` → `Object.prototype` (`OP`) → null: a new object with prototype `P` and own `n = 0`, bound to `o`. -/
theorem let_o (c : Ctx) (u : State) (ge g P : Nat) (gb : Std.HashMap JSStr Binding) (gtv : Value) (bdP : Binding)
    (hlex : c.lex = ge) (hstr : c.strict = false) (hge : ge < u.envs.size) (hE : u.envEntry ge = .global g gb gtv)
    (hom : (JSStr.ofString "o" ∈ gb) = True) (hbP : gb[JSStr.ofString "p"]? = some bdP)
    (hpm : (JSStr.ofString "p" ∈ gb) = True) (hvP : bdP.value = some (.obj P))
    (hP : P < u.heap.size) (hPk : (u.objEntry P).kind = .ordinary)
    (hPp : (u.objEntry P).proto = .obj u.curRealm.objectProto) (hPOP : P ≠ u.curRealm.objectProto)
    (hOP : u.curRealm.objectProto < u.heap.size) (hOPk : (u.objEntry u.curRealm.objectProto).kind = .ordinary)
    (hOPp : (u.objEntry u.curRealm.objectProto).proto = .null) (hf : 4 ≤ u.fuel) :
    Sem.varDecl #[Sem.declLex VarKind.let "o" (some objO)] c u =
      .ok (.normal none) ((oState u P).setEnv ge (.global g (gb.modify "o" fun bd =>
        { bd with value := some (.obj u.heap.size) }) gtv)) := by
  have hr := Global.resolveBinding_global_decl ge "o" false u g gb gtv hge hE hom (by omega)
  obtain ⟨t1, ht1⟩ : ∃ x, u.allocObj { proto := .obj u.curRealm.objectProto } = x := ⟨_, rfl⟩
  have hO1 : u.heap.size < t1.heap.size := by rw [← ht1]; simp [State.allocObj]
  have hE1 : t1.objEntry u.heap.size = { proto := .obj u.curRealm.objectProto } := by
    rw [← ht1]; exact State.allocObj_entry_new _ _
  have hlt1 : ∀ x, x < u.heap.size → t1.objEntry x = u.objEntry x := fun x hx => by
    rw [← ht1, State.allocObj_entry_lt _ _ _ hx]
  have he1 : t1.envs = u.envs := by rw [← ht1]; simp [State.allocObj]
  have hf1 : t1.fuel = u.fuel := by rw [← ht1]; simp [State.allocObj]
  have hz1 : t1.heap.size = u.heap.size + 1 := by rw [← ht1]; simp [State.allocObj]
  have hpv : identValue ge "p" false t1 = .ok (.obj P) t1 :=
    Global.identValue_global_decl ge "p" false t1 g gb gtv bdP (.obj P) (by rw [he1]; exact hge)
      (by simp only [State.envEntry, he1]; exact hE) hbP hpm hvP (by omega)
  have hsp := setPrototypeOf_fresh t1 u.heap.size P u.curRealm.objectProto hO1 (by simp [hE1]) (by simp [hE1])
    (by simp [hE1]) (by simp [hE1]) (Nat.ne_of_lt hP) hPOP (by rw [hz1]; exact Nat.lt_succ_of_lt hP)
    (by rw [hlt1 P hP]; exact hPk) (by rw [hlt1 P hP]; exact hPp) (Nat.ne_of_lt hOP)
    (by rw [hz1]; exact Nat.lt_succ_of_lt hOP) (by rw [hlt1 _ hOP]; exact hOPk) (by rw [hlt1 _ hOP]; exact hOPp)
    (by rw [hf1]; omega)
  obtain ⟨t2, ht2⟩ : ∃ x, State.setProto t1 u.heap.size (.obj P) = x := ⟨_, rfl⟩
  rw [ht2] at hsp
  have hO2 : u.heap.size < t2.heap.size := by rw [← ht2, setProto_heap_size]; exact hO1
  have hE2 : t2.objEntry u.heap.size = { proto := .obj P } := by rw [← ht2, setProto_entry_self _ _ _ hO1, hE1]
  have hc1 := Method.cdp_ordinary u.heap.size (.str "n") (num 0) t2 hO2 (by simp [hE2]) (by simp [hE2]) (by simp [hE2])
  obtain ⟨t3, ht3⟩ : ∃ x, t2.setProp u.heap.size (.str "n") (.data (num 0) true true true) = x := ⟨_, rfl⟩
  rw [ht3] at hc1
  have he3 : t3.envs = u.envs := by rw [← ht3, State.setProp_envs, ← ht2, setProto_envs, he1]
  have hin := Global.initializeBinding_global ge "o" (.obj u.heap.size) t3 g gb gtv (by rw [he3]; exact hge)
    (by simp only [State.envEntry, he3]; exact hE) (Std.HashMap.mem_iff_contains.mp (of_eq_true hom))
  have hst : oState u P = t3 := by rw [← ht3, ← ht2, ← ht1]; rfl
  rw [hst]
  have hlu : (VarKind.let == VarKind.using) = false := by decide
  have hla : (VarKind.let == VarKind.awaitUsing) = false := by decide
  have hnk : Sem.propKey (Sem.KeyD.name (PropName.ident "n")) = fun _ => pure (PropKey.str "n") := rfl
  simp [Sem.varDecl, M.forArr_def, M.foldArr_toArray, M.foldList_cons, M.foldList_nil, Sem.declLex, Sem.inner, hlex,
    hstr, hr, Sem.object, newObject_eq, ht1, hnk, Sem.ident, hpv, hsp, Sem.lit, litValue, zero_eq, hc1,
    initializeRefBinding, hin, hlu, hla, pure, M.pure, M.bind_eq, M.bind_apply, M.bindRes_ok]

/-! ## Calling a method found on the prototype -/

/-- **A method call `e.m()`** whose callee [[Get]] finds the function `fo` (anywhere on `O`'s chain). -/
theorem method_call_get_req (c : Ctx) (w : State) (e : Sem.CExpr) (O fo : ObjId) (m : JSStr) (d : FuncData)
    (desc : CalleeDesc) (he : e c w = .ok (.obj O) w) (hstr : c.strict = false)
    (hget : Obj'.get O (.str m) (.obj O) w = .ok (.obj fo) w)
    (hfs : fo < w.heap.size) (hfk : (w.objEntry fo).kind = .func d) :
    ∃ K, Sem.call (Sem.memberRef e (.name m) false) (Sem.args #[]) false desc c w =
        .req (.call (.obj fo) (.obj O) #[]) w K ∧ ∀ v t, K (.normal v) t = .ok v t := by
  have hg := getRefValue_prop O m false w
  rw [hget] at hg
  refine ⟨?K, ?h, ?_⟩
  case h =>
    conv =>
      lhs
      simp [Sem.call, Sem.memberRef, he, hstr, Value.isNullish, hg, refThisValue, Sem.args, isCallable,
        readObj_entry' _ _ _ hfs, hfk, ES.call, pure, M.pure, M.bind_eq, M.bind_apply, M.bindRes_ok]
  intro v t
  simp [M.pure, pure]

/-- `O.inc`, `O` an ordinary object without own `inc` whose prototype `P` (ordinary) has `inc = fo`. -/
theorem get_inc_proto (w : State) (O P fo : ObjId) (wr en cf : Bool) (hO : O < w.heap.size)
    (hOk : (w.objEntry O).kind = .ordinary) (hOi : (w.objEntry O).props.get? (.str "inc") = none)
    (hOp : (w.objEntry O).proto = .obj P) (hP : P < w.heap.size) (hPk : (w.objEntry P).kind = .ordinary)
    (hPi : (w.objEntry P).props.get? (.str "inc") = some (.data (.obj fo) wr en cf)) :
    Obj'.get O (.str "inc") (.obj O) w = .ok (.obj fo) w := by
  have hc : PlainChain w 2 O (.str "inc") := by
    refine ⟨hO, by rw [hOk]; rfl, fun _ => ?_⟩
    rw [hOp]
    exact ⟨hP, by rw [hPk]; rfl, fun h => by rw [hPi] at h; cases h⟩
  have hl : ordLookup w 2 O (.str "inc") = some (.data (.obj fo) wr en cf) := by
    simp [ordLookup, hOi, hOp, hPi]
  rw [Obj'.get_chain w _ _ 2 O hc (by omega) (by rw [hl]; rfl), hl]; rfl

/-! ## The states along the way -/

theorem ne_n_inc : PropKey.str (JSStr.ofString "n") ≠ PropKey.str (JSStr.ofString "inc") := Method.ne_n_inc

theorem pState_facts (u : State) (fI : ObjId) :
    (pState u fI).heap.size = u.heap.size + 1 ∧ (∀ x, x < u.heap.size → (pState u fI).objEntry x = u.objEntry x) ∧
    ((pState u fI).objEntry u.heap.size).kind = .ordinary ∧
    ((pState u fI).objEntry u.heap.size).proto = .obj u.curRealm.objectProto ∧
    ((pState u fI).objEntry u.heap.size).props.get? (.str "inc") = some (.data (.obj fI) true true true) ∧
    (pState u fI).envs = u.envs ∧ (pState u fI).fuel = u.fuel ∧ (pState u fI).realms = u.realms ∧
    (pState u fI).realm = u.realm := by
  have hlt : u.heap.size < (u.allocObj { proto := .obj u.curRealm.objectProto }).heap.size := by simp [State.allocObj]
  refine ⟨by simp [pState, State.allocObj, State.setProp], fun x hx => ?_, ?_, ?_, ?_, by simp [pState, State.allocObj],
    by simp [pState, State.allocObj], by simp [pState, State.allocObj], by simp [pState, State.allocObj]⟩
  · simp only [pState]
    rw [State.setProp_entry_ne _ _ _ _ _ (Nat.ne_of_gt hx), State.allocObj_entry_lt _ _ _ hx]
  all_goals simp only [pState]; rw [State.setProp_entry_self _ _ _ _ hlt, State.allocObj_entry_new]; simp

theorem oState_facts (u : State) (P : ObjId) :
    (oState u P).heap.size = u.heap.size + 1 ∧ (∀ x, x < u.heap.size → (oState u P).objEntry x = u.objEntry x) ∧
    ((oState u P).objEntry u.heap.size).kind = .ordinary ∧ ((oState u P).objEntry u.heap.size).proto = .obj P ∧
    ((oState u P).objEntry u.heap.size).props.get? (.str "n") = some (.data (num 0) true true true) ∧
    ((oState u P).objEntry u.heap.size).props.get? (.str "inc") = none ∧
    (oState u P).envs = u.envs ∧ (oState u P).fuel = u.fuel ∧ (oState u P).realms = u.realms := by
  have hlt : u.heap.size < (u.allocObj { proto := .obj u.curRealm.objectProto }).heap.size := by simp [State.allocObj]
  have hlt2 : u.heap.size < (State.setProto (u.allocObj { proto := .obj u.curRealm.objectProto }) u.heap.size
      (.obj P)).heap.size := by simpa using hlt
  refine ⟨by simp [oState, State.allocObj, State.setProp], fun x hx => ?_, ?_, ?_, ?_, ?_,
    by simp [oState, State.allocObj], by simp [oState, State.allocObj], by simp [oState, State.allocObj]⟩
  · simp only [oState]
    rw [State.setProp_entry_ne _ _ _ _ _ (Nat.ne_of_gt hx), setProto_entry_ne _ _ _ _ (Nat.ne_of_gt hx),
      State.allocObj_entry_lt _ _ _ hx]
  all_goals simp only [oState]; rw [State.setProp_entry_self _ _ _ _ hlt2, setProto_entry_self _ _ _ hlt,
    State.allocObj_entry_new]
  all_goals simp [PropMap.get?_insert_ne _ _ _ _ ne_n_inc]

/-! ## The whole script -/

open Script

abbrev callInc : Sem.CStmt := Method.callInc

theorem script_def (n : Nat) : PRGen.script n = Sem.stmts #[Sem.funDecl PRGen.inc_func,
    Sem.varDecl #[Sem.declLex VarKind.let "p" (some objP)], Sem.varDecl #[Sem.declLex VarKind.let "o" (some objO)],
    callInc, callInc] := rfl
theorem lexScoped : topLevelLexicallyScoped PRGen.script_stmts =
    #[.binding .let (.ident "p"), .binding .let (.ident "o")] := by
  have hv : (VarKind.let == VarKind.var) = false := by decide
  simp [topLevelLexicallyScoped, stmtLexScoped, PRGen.script_stmts, hv]
theorem simple_inc : Inst.SimpleFn PRGen.inc_func "inc" := ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem inc_same : PRGen.inc_func = MEGen.inc_func := rfl
theorem ne_pi : (JSStr.ofString "p" = JSStr.ofString "inc") = False := by simp; decide
theorem ne_oi : (JSStr.ofString "o" = JSStr.ofString "inc") = False := by simp; decide
theorem ne_po : (JSStr.ofString "p" = JSStr.ofString "o") = False := by simp; decide
theorem ne_op : (JSStr.ofString "o" = JSStr.ofString "p") = False := by simp; decide

def fs : List (Func × JSStr) := [(PRGen.inc_func, "inc")]

theorem varS : topLevelVarScoped PRGen.program.body = (fs.map fun p => VarScoped.func p.1).toArray := rfl
theorem lexS : topLevelLexicallyScoped PRGen.program.body =
    ((["p", "o"] : List JSStr).map fun x => LexScoped.binding .let (.ident x)).toArray := by
  rw [show PRGen.program.body = PRGen.script_stmts from rfl, lexScoped]; rfl
theorem annS : annexBFunctions PRGen.program.body (["p", "o"] : List JSStr).toArray = #[] := rfl
theorem simpleS : ∀ p ∈ fs, Inst.SimpleFn p.1 p.2 := by
  intro p hp; simp only [fs, List.mem_cons, List.mem_nil_iff, or_false] at hp; rcases hp with rfl; exact simple_inc
theorem nodupS : (fs.map Prod.snd).Nodup := by decide

/-- **The whole program** (examples/proto.js), run as the engine runs a script: evaluates to 2. Started from a
realm whose global object is an ordinary extensible object without `p`, `o` or `inc`, and whose
`Object.prototype` is an ordinary object (not the global object) with prototype null. -/
theorem pm_script (eng : Engine) (s : State) (cs : Conts) (gb : Std.HashMap JSStr Binding) (gtv : Value)
    (fp : ObjId) (hge : s.curRealm.globalEnv < s.envs.size)
    (hE : s.envEntry s.curRealm.globalEnv = .global s.curRealm.globalObj gb gtv)
    (hgbp : gb.contains "p" = false) (hgbo : gb.contains "o" = false) (hgbi : gb.contains "inc" = false)
    (hgs : s.curRealm.globalObj < s.heap.size) (hk : (s.objEntry s.curRealm.globalObj).kind = .ordinary)
    (hx : (s.objEntry s.curRealm.globalObj).extensible = true)
    (hpp : (s.objEntry s.curRealm.globalObj).props.get? (.str "p") = none)
    (hpo : (s.objEntry s.curRealm.globalObj).props.get? (.str "o") = none)
    (hpi : (s.objEntry s.curRealm.globalObj).props.get? (.str "inc") = none)
    (hfp : s.curRealm.intrinsics["%Function.prototype%"]? = some fp)
    (hOP : s.curRealm.objectProto < s.heap.size) (hOPg : s.curRealm.objectProto ≠ s.curRealm.globalObj)
    (hOPk : (s.objEntry s.curRealm.objectProto).kind = .ordinary)
    (hOPp : (s.objEntry s.curRealm.objectProto).proto = .null) (hf : 30 ≤ s.fuel) :
    ∃ s', (runM eng (scriptEvaluation PRGen.program) s cs).1 = .ok (num 2) s' := by
  let ge := s.curRealm.globalEnv
  let g := s.curRealm.globalObj
  let OP := s.curRealm.objectProto
  let c := scriptCtx s false
  -- the declarations
  obtain ⟨t0, ht0⟩ : ∃ x, (scriptStart s PRGen.program).setEnv ge (.global g (insertLets gb ["p", "o"]) gtv) = x :=
    ⟨_, rfl⟩
  have ho0 : ∀ x, t0.objEntry x = s.objEntry x := by intro x; rw [← ht0, State.setEnv_objEntry]; rfl
  have hz0 : t0.heap.size = s.heap.size := by rw [← ht0, State.setEnv_heap_size]; rfl
  have hge0 : ge < t0.envs.size := by rw [← ht0, State.setEnv_envs_size]; exact hge
  have hgood : GoodG g fp t0 := ⟨by rw [hz0]; exact hgs, by rw [ho0]; exact hk, by rw [ho0]; exact hx,
    by rw [← ht0, State.setEnv_curRealm]; exact hfp⟩
  obtain ⟨⟨-, hku, -, -⟩, heu, hfuu, hru, hrlu, hszu, hou, -, -, hnames, hfuns⟩ :=
    instAll_facts ge g s.scripts.size fp fs t0 hgood (by decide)
  obtain ⟨u, hu⟩ : ∃ x, instAll ge g s.scripts.size fp fs t0 = x := ⟨_, rfl⟩
  rw [hu] at hku heu hfuu hru hrlu hszu hou hnames hfuns
  have hfu0 : t0.fuel = s.fuel := by rw [← ht0, State.setEnv_fuel]; rfl
  have hrl0 : t0.realm = s.realm := by rw [← ht0, State.setEnv_realm]; rfl
  have hr0 : t0.realms = s.realms := by rw [← ht0, State.setEnv_realms]; rfl
  have hcr : u.curRealm = s.curRealm := by simp only [State.curRealm, hru, hrlu, hr0, hrl0]
  let fI := s.heap.size
  obtain ⟨dI, hfIk, hcI, -, hmI, hclsI, -, -⟩ := hfuns 0 (by decide)
  rw [hz0] at hfIk hszu hnames hou
  simp only [fs, List.length_cons, List.length_nil] at hszu
  simp only [Nat.mul_zero, Nat.add_zero] at hfIk
  have hpI : (u.objEntry g).props.get? (.str "inc") = some (.data (.obj fI) true true false) := hnames 0 (by decide)
  have hOPu : u.objEntry OP = s.objEntry OP := by rw [hou OP hOP hOPg, ho0]
  let gbL := (gb.insert "p" { deletable := false }).insert "o" { deletable := false }
  have hE1 : u.envEntry ge = .global g gbL gtv := by
    have h1 : u.envEntry ge = t0.envEntry ge := by simp only [State.envEntry, heu]
    rw [h1, ← ht0, State.setEnv_envEntry_self _ _ _ (show ge < (scriptStart s PRGen.program).envs.size from hge)]
    simp [insertLets, gbL]
  have hgeu : ge < u.envs.size := by rw [heu]; exact hge0
  have hgu : g < u.heap.size := by rw [hszu]; exact Nat.lt_of_lt_of_le hgs (Nat.le_add_right _ _)
  have hfIu : fI < u.heap.size := by show s.heap.size < u.heap.size; rw [hszu]; omega
  have hOPlt : OP < u.heap.size := by rw [hszu]; exact Nat.lt_of_lt_of_le hOP (Nat.le_add_right _ _)
  have hgbI' : gb[JSStr.ofString "inc"]? = none := Std.HashMap.getElem?_eq_none (fun hm => by
    rw [Std.HashMap.mem_iff_contains, hgbi] at hm; exact Bool.false_ne_true hm)
  have hLi : gbL.contains "inc" = false := by simp [gbL, Std.HashMap.contains_insert, hgbi, ne_pi, ne_oi]
  have hLi' : gbL[JSStr.ofString "inc"]? = none := by simp [gbL, Std.HashMap.getElem?_insert, ne_pi, ne_oi, hgbI']
  have hLim : (JSStr.ofString "inc" ∈ gbL) = False := by simp [Std.HashMap.mem_iff_contains, hLi]
  -- `let p = { inc: inc }`
  have h3 := let_p c u ge g fI gbL gtv rfl rfl hgeu hE1 (by simp [gbL]) hLi hLim hLi' hgu hku hpI
    (by rw [hfuu, hfu0]; omega)
  let P := u.heap.size
  let gbP := gbL.modify "p" fun bd => { bd with value := some (.obj P) }
  obtain ⟨u2, hu2⟩ : ∃ x, (pState u fI).setEnv ge (.global g gbP gtv) = x := ⟨_, rfl⟩
  rw [hu2] at h3
  obtain ⟨hzP, hoP, hkP, hpP, hiP, heP, hfP, hrP, hrlP⟩ := pState_facts u fI
  have ho2 : ∀ x, u2.objEntry x = (pState u fI).objEntry x := by intro x; rw [← hu2, State.setEnv_objEntry]
  have hz2 : u2.heap.size = P + 1 := by rw [← hu2, State.setEnv_heap_size, hzP]
  have hge2 : ge < u2.envs.size := by rw [← hu2, State.setEnv_envs_size, heP]; exact hgeu
  have hE2 : u2.envEntry ge = .global g gbP gtv := by
    rw [← hu2]; exact State.setEnv_envEntry_self _ _ _ (by rw [heP]; exact hgeu)
  have hf2 : u2.fuel = s.fuel := by rw [← hu2, State.setEnv_fuel, hfP, hfuu, hfu0]
  have hcr2 : u2.curRealm = s.curRealm := by
    rw [← hu2, State.setEnv_curRealm]; simp only [State.curRealm, hrP, hrlP]; exact hcr
  -- `let o = { __proto__: p, n: 0 }`
  have hPOP : P ≠ OP := Nat.ne_of_gt hOPlt
  have h4 := let_o c u2 ge g P gbP gtv { value := some (.obj P), deletable := false } rfl rfl hge2 hE2
    (by simp [gbP, gbL]) (by simp [gbP, gbL, Std.HashMap.getElem?_modify, Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert, Std.HashMap.getElem_modify, ne_po, ne_op])
    (by simp [gbP, gbL]) rfl (by rw [hz2]; exact Nat.lt_succ_self _) (by rw [ho2]; exact hkP)
    (by rw [ho2, hpP, hcr, hcr2]) (by rw [hcr2]; exact hPOP) (by rw [hcr2, hz2]; exact Nat.lt_succ_of_lt hOPlt)
    (by rw [hcr2, ho2, hoP OP hOPlt, hOPu]; exact hOPk) (by rw [hcr2, ho2, hoP OP hOPlt, hOPu]; exact hOPp)
    (by omega)
  let O := u2.heap.size
  let gbO := gbP.modify "o" fun bd => { bd with value := some (.obj O) }
  obtain ⟨u3, hu3⟩ : ∃ x, (oState u2 P).setEnv ge (.global g gbO gtv) = x := ⟨_, rfl⟩
  rw [hu3] at h4
  obtain ⟨hzO, hoO, hkO, hpO, hnO, hiO, heO, hfO, -⟩ := oState_facts u2 P
  have ho3 : ∀ x, u3.objEntry x = (oState u2 P).objEntry x := by intro x; rw [← hu3, State.setEnv_objEntry]
  have hz3 : u3.heap.size = O + 1 := by rw [← hu3, State.setEnv_heap_size, hzO]
  have hge3 : ge < u3.envs.size := by rw [← hu3, State.setEnv_envs_size, heO]; exact hge2
  have hE3 : u3.envEntry ge = .global g gbO gtv := by
    rw [← hu3]; exact State.setEnv_envEntry_self _ _ _ (by rw [heO]; exact hge2)
  have hf3 : u3.fuel = s.fuel := by rw [← hu3, State.setEnv_fuel, hfO, hf2]
  have hOv : O = P + 1 := hz2
  have hPv : P = u.heap.size := rfl
  have hO3 : O < u3.heap.size := by rw [hz3]; exact Nat.lt_succ_self _
  have hP3 : P < u3.heap.size := by rw [hz3]; omega
  have hfI3 : fI < u3.heap.size := by rw [hz3]; omega
  have hPu3 : u3.objEntry P = (pState u fI).objEntry P := by rw [ho3, hoO P (by omega), ho2]
  have hfIu3 : u3.objEntry fI = u.objEntry fI := by
    rw [ho3, hoO fI (by omega), ho2, hoP fI hfIu]
  have hOb : gbO[JSStr.ofString "o"]? = some { value := some (.obj O), deletable := false } := by
    simp [gbO, gbP, gbL, Std.HashMap.getElem?_modify, Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert,
      Std.HashMap.getElem_modify, ne_po, ne_op]
  have hOm : (JSStr.ofString "o" ∈ gbO) = True := by simp [gbO, gbP, gbL]
  have hcodeI : dI.code = MEGen.inc_func := hcI.trans inc_same
  have hPO : P ≠ O := by omega
  have hfIO : fI ≠ O := by omega
  -- the first `o.inc()`: found on `p`; `this = o`, `n` from 0 to 1
  have hro3 := Global.identValue_global_decl ge "o" false u3 g gbO gtv _ (.obj O) hge3 hE3 hOb hOm rfl (by omega)
  have hget3 := get_inc_proto u3 O P fI true true true hO3 (by rw [ho3]; exact hkO) (by rw [ho3]; exact hiO)
    (by rw [ho3]; exact hpO) hP3 (by rw [hPu3]; exact hkP) (by rw [hPu3]; exact hiP)
  obtain ⟨K5, h5, hK5⟩ := method_call_get_req (Sem.inner c) u3 (Sem.ident "o") O fI "inc" dI (.prop "inc")
    hro3 rfl hget3 hfI3 (by rw [hfIu3]; exact hfIk)
  obtain ⟨K6, h6, hK6⟩ := Stmts.exprStmt_req _ c u3 _ K5 h5 hK5
  obtain ⟨u3', hu3'⟩ : ∃ x, ({ u3 with fuel := u3.fuel - 1 } : State) = x := ⟨_, rfl⟩
  have hou3 : ∀ x, u3'.objEntry x = u3.objEntry x := fun x => by rw [← hu3']; rfl
  obtain ⟨s4, hc1, -, hz4, he4, hh4, ho4, -, hf4⟩ := Method.inc_call fI dI u3' O 0 hcodeI hclsI hmI
    (by rw [← hu3']; exact hO3) (by rw [hou3, ho3]; exact hkO) (by rw [hou3, ho3]; exact hnO) (by decide)
    (by rw [← hu3']; simp only; omega)
  have himpl1 : callImpl eng (.obj fI) (.obj O) #[] u3 = .ok (num 1) s4 := by
    rw [callImpl_func eng fI dI _ _ u3 hfI3 (by rw [hfIu3]; exact hfIk) (by omega), hu3']; exact hc1
  -- the state after it
  have hO4 : ∀ x, x ≠ O → s4.objEntry x = u3.objEntry x := by
    intro x hx; rw [ho4 x]; simp only [Method.bump]; rw [State.setProp_entry_ne _ _ _ _ _ (Ne.symm hx), hou3]
  have hO4e : s4.objEntry O = (u3.objEntry O).withProps
      (·.insert (.str "n") (.data (num ((0 : Nat) + 1 : Int)) true true true)) := by
    rw [ho4 O]; simp only [Method.bump]; rw [State.setProp_entry_self _ _ _ _ (by rw [← hu3']; exact hO3), hou3]
  have hz4' : s4.heap.size = u3.heap.size := by rw [hh4, ← hu3']
  have hf4' : s4.fuel = s.fuel - 1 := by rw [hf4, ← hu3']; simp only; rw [hf3]
  have hge4 : ge < s4.envs.size := Nat.lt_of_lt_of_le (by rw [← hu3']; exact hge3) hz4
  have hE4 : s4.envEntry ge = .global g gbO gtv := by rw [he4 ge (by rw [← hu3']; exact hge3)]; rw [← hu3']; exact hE3
  -- the second `o.inc()`: `n` from 1 to 2
  have hro4 := Global.identValue_global_decl ge "o" false s4 g gbO gtv _ (.obj O) hge4 hE4 hOb hOm rfl (by omega)
  have hget4 := get_inc_proto s4 O P fI true true true (by rw [hz4']; exact hO3)
    (by rw [hO4e, Obj.withProps_kind, ho3]; exact hkO)
    (by rw [hO4e, Obj.withProps_props, PropMap.get?_insert_ne _ _ _ _ ne_n_inc, ho3]; exact hiO)
    (by rw [hO4e, Obj.withProps_proto, ho3]; exact hpO) (by rw [hz4']; exact hP3)
    (by rw [hO4 P hPO, hPu3]; exact hkP) (by rw [hO4 P hPO, hPu3]; exact hiP)
  obtain ⟨K7, h7, hK7⟩ := method_call_get_req (Sem.inner c) s4 (Sem.ident "o") O fI "inc" dI (.prop "inc")
    hro4 rfl hget4 (by rw [hz4']; exact hfI3) (by rw [hO4 fI hfIO, hfIu3]; exact hfIk)
  obtain ⟨K8, h8, hK8⟩ := Stmts.exprStmt_req _ c s4 _ K7 h7 hK7
  obtain ⟨s4', hs4'⟩ : ∃ x, ({ s4 with fuel := s4.fuel - 1 } : State) = x := ⟨_, rfl⟩
  have hos4 : ∀ x, s4'.objEntry x = s4.objEntry x := fun x => by rw [← hs4']; rfl
  obtain ⟨s5, hc2, -⟩ := Method.inc_call fI dI s4' O 1 hcodeI hclsI hmI
    (by rw [← hs4', hz4']; exact hO3) (by rw [hos4, hO4e, Obj.withProps_kind, ho3]; exact hkO)
    (by rw [hos4, hO4e, Obj.withProps_props]; simp) (by decide) (by rw [← hs4']; simp only; omega)
  have himpl2 : callImpl eng (.obj fI) (.obj O) #[] s4 = .ok (num 2) s5 := by
    rw [callImpl_func eng fI dI _ _ s4 (by rw [hz4']; exact hfI3) (by rw [hO4 fI hfIO, hfIu3]; exact hfIk) (by omega),
      hs4']
    exact hc2
  -- the script
  have hgbl : ∀ x ∈ (["p", "o"] : List JSStr), gb.contains x = false := by
    intro x hx; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl
    · exact hgbp
    · exact hgbo
  have hpl : ∀ x ∈ (["p", "o"] : List JSStr), (s.objEntry s.curRealm.globalObj).props.get? (.str x) = none := by
    intro x hx; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl
    · exact hpp
    · exact hpo
  refine ⟨s5, script_value eng s cs PRGen.program fs ["p", "o"] gb gtv fp _ s5 rfl varS lexS annS simpleS nodupS hge hE
    (by intro p hp; simp only [fs, List.mem_cons, List.mem_nil_iff, or_false] at hp; rcases hp with rfl; exact hgbi)
    hgbl hgs hk hx
    (by intro p hp; simp only [fs, List.mem_cons, List.mem_nil_iff, or_false] at hp; rcases hp with rfl; exact hpi)
    hpl hfp ?_⟩
  have hu0 : scriptState s PRGen.program fs ["p", "o"] gb gtv fp = u := by rw [← hu, ← ht0]; rfl
  have hscript : evalStmts evalDepth (scriptCtx s false) PRGen.program.body u = PRGen.script 999962 c u := by
    rw [PRGen.script_eq]; rfl
  have h6' : callInc c u3 = .req (.call (.obj fI) (.obj O) #[]) u3 K6 := h6
  have h8' : callInc c s4 = .req (.call (.obj fI) (.obj O) #[]) s4 K8 := h8
  rw [hu0, hscript, script_def]
  refine _root_.Runs.script_runs eng _ _ _ (_root_.Runs.stmts_run eng c _ u _ s5 ?_ (by simp; rw [hfuu, hfu0]; omega))
  show _root_.Runs.StmtsRun eng c [Sem.funDecl PRGen.inc_func, Sem.varDecl #[Sem.declLex VarKind.let "p" (some objP)],
    Sem.varDecl #[Sem.declLex VarKind.let "o" (some objO)], callInc, callInc] u none (some (num 2)) s5
  refine .cons _ _ u u s5 none none _ (_root_.Runs.runs_funDecl eng _ c u rfl) ?_
  refine .cons _ _ u u2 s5 none none _ (by rw [h3]; exact _root_.Runs.runsTo_ok eng _ _) ?_
  refine .cons _ _ u2 u3 s5 none none _ (by rw [h4]; exact _root_.Runs.runsTo_ok eng _ _) ?_
  refine .cons _ _ u3 s4 s5 (some (num 1)) none _ ?_ ?_
  · rw [h6']; exact _root_.Runs.runsTo_req1 eng _ _ _ u3 K6 _ s4 _ s4 himpl1 (hK6 _ s4)
  refine .cons _ _ s4 s5 s5 (some (num 2)) _ _ ?_ (.nil _ _)
  rw [h8']; exact _root_.Runs.runsTo_req1 eng _ _ _ s4 K8 _ s5 _ s5 himpl2 (hK8 _ s5)

end ProtoM
