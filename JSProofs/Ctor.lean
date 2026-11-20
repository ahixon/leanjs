import JSProofs.Construct
import JSProofs.ProtoM
import JSProofs.CTGen

/-!
# Constructors: `new Counter()` and a method on `Counter.prototype` (examples/ctor.js)

```js
function inc() { this.n = this.n + 1; return this.n; }
function Counter() { this.n = 0; }
Counter.prototype.inc = inc;
let c = new Counter();
c.inc();
c.inc();
```
`new Counter()` creates an object whose prototype is `Counter.prototype` (`Construct.constructECMA_ord`) and
gives it `n = 0` (`ctr_construct`); `c.inc` is found on the prototype; the script evaluates to 2.
-/

open ES ES.Conv SumProof

namespace Ctor

/-! ## `Counter`'s body: `this.n = 0` -/

theorem ctr_spec (nn : Nat) (ctx : Ctx) (L F O : Nat) (hlex : ctx.lex = L) (hstr : ctx.strict = false)
    (s0 : State) (b bF : Std.HashMap JSStr Binding) (o : Option EnvId) (fo : ObjId) (nt : Value)
    (hL : L < s0.envs.size) (hF : F < s0.envs.size) (hLE : s0.envEntry L = .decl b (some F))
    (hFE : s0.envEntry F = .func bF o .initialized (.obj O) fo nt) (s1 : State)
    (hput : putRefValue (.prop (.obj O) (.str "n") false none) (num 0) s0 = .ok () s1) (hf : 4 ≤ s0.fuel) :
    ∃ c, CTGen.Counter nn ctx s0 = .ok (.normal c) s1 := by
  have hth := Method.resolveThis_decl L F s0 b bF o (.obj O) fo nt hL hF hLE hFE (by omega)
  obtain ⟨j, hj⟩ : ∃ j, s0.fuel = j + 3 := ⟨s0.fuel - 3, by omega⟩
  simp only [CTGen.Counter, Sem.stmts, M.repeatFrom, hj, M.loop]
  rw [zero_eq]
  simp [M.bind_eq, M.bind_apply, Sem.exprStmt, Sem.assign, Sem.memberRef, Sem.inner, Sem.this, hlex, hstr, hth,
    Value.isNullish, Sem.lit, litValue, hput, pure, M.pure, Compl.updateEmpty]

/-! ## The [[Construct]] of `Counter` -/

theorem ctr_fdi (f : ObjId) (d : FuncData) (env : EnvId) (s : State) (tv nt : Value)
    (hcode : d.code = CTGen.Counter_func) (henv : env < s.envs.size)
    (hE : s.envEntry env = .func ∅ (some d.env) .initialized tv f nt) (hf : s.fuel ≠ 0) :
    ∃ ctx s', functionDeclarationInstantiation 999999 f d env #[] s = .ok ctx s' ∧
      ctx.lex = s.envs.size ∧ ctx.strict = false ∧ ctx.isGen = false ∧
      s.envs.size < s'.envs.size ∧ s'.envEntry s.envs.size = .decl ∅ (some env) ∧
      (∀ e, e < s.envs.size → s'.envEntry e = s.envEntry e) ∧
      s'.heap = s.heap ∧ s'.fuel = s.fuel ∧ s'.realms = s.realms := by
  have hr : Array.range 0 = [].toArray := by decide
  have hbody : CTGen.Counter_func.body = .stmts CTGen.Counter_stmts := rfl
  have hparams : CTGen.Counter_func.params = #[] := rfl
  have hstr : CTGen.Counter_func.strict = false := rfl
  have hasync : CTGen.Counter_func.isAsync = false := rfl
  have hgen : CTGen.Counter_func.isGenerator = false := rfl
  have hkind : CTGen.Counter_func.kind = .normal := rfl
  have hfdi : CTGen.Counter_func.info.fdi = { paramNames := #[], hasDuplicates := false, varNames := #[], hasFunctions := false, functionNames := #[], hasLexical := false, lexNames := #[], argumentsNeeded := false, hasAnnexB := false, usesDispose := false } := rfl
  have hphe : CTGen.Counter_func.info.paramsHaveExpressions = false := rfl
  refine ⟨?c, ?t, ?h, ?_⟩
  case h =>
    conv =>
      lhs
      simp only [functionDeclarationInstantiation, hcode, hbody, hparams, hstr, hfdi, hasync, hgen, hkind, hphe]
      simp [hr, newDeclEnv, pure, M.pure, -allocEnv_apply, allocEnv_eq]
  refine ⟨rfl, rfl, rfl, by simp, by simp, fun e he => ?_, by simp [State.pushEnv], by simp, by simp [State.pushEnv]⟩
  simp [State.pushEnv_entry_lt, he]

/-- The heap after `new Counter()`: a fresh object with prototype `P` and `n = 0`. -/
def newState (s : State) (P : ObjId) : State :=
  (s.allocObj { proto := .obj P }).setProp s.heap.size (.str "n") (.data (num 0) true true true)

/-- **`new Counter()`** (`Counter` the function `f`, `Counter.prototype` the object `P`, whose prototype `OP`
ends the chain; neither has `n`): gives the fresh object `s.heap.size`, with prototype `P` and `n = 0`. -/
theorem ctr_construct (f : ObjId) (d : FuncData) (s : State) (P OP : ObjId) (wr en cf : Bool)
    (hcode : d.code = CTGen.Counter_func) (hmode : d.thisMode = .global) (hdef : d.isDefaultCtor = false)
    (hder : d.derived = false) (hfields : d.fields = #[]) (hpriv : d.privMethods = #[])
    (hf : f < s.heap.size) (hfk : (s.objEntry f).kind = .func d)
    (hp : (s.objEntry f).props.get? (.str kPrototype) = some (.data (.obj P) wr en cf))
    (hP : P < s.heap.size) (hPk : (s.objEntry P).kind = .ordinary) (hPn : (s.objEntry P).props.get? (.str "n") = none)
    (hPp : (s.objEntry P).proto = .obj OP) (hOP : OP < s.heap.size) (hOPk : (s.objEntry OP).kind = .ordinary)
    (hOPn : (s.objEntry OP).props.get? (.str "n") = none) (hOPp : (s.objEntry OP).proto = .null)
    (hfu : 6 ≤ s.fuel) :
    ∃ s', constructECMA f d #[] (.obj f) s = .ok (.obj s.heap.size) s' ∧ s'.realm = s.realm ∧
      s.envs.size ≤ s'.envs.size ∧ (∀ e, e < s.envs.size → s'.envEntry e = s.envEntry e) ∧
      s'.heap = (newState s P).heap ∧ s'.realms = s.realms ∧ s'.fuel = s.fuel := by
  let O := s.heap.size
  obtain ⟨s', h1, h2, -, t', ⟨q1, q2, q3, q4, q5⟩, hh, hen, hfe, hrs⟩ := Construct.constructECMA_ord
    (Q := fun t => s.envs.size ≤ t.envs.size ∧ (∀ e, e < s.envs.size → t.envEntry e = s.envEntry e) ∧
      t.heap = (newState s P).heap ∧ t.realms = s.realms ∧ t.fuel = s.fuel)
    f d s #[] .undefined P wr en cf hdef hder hmode hfields hpriv hf hfk hp rfl
    (fun t hlt hEt hold hheap hfu' hrl _ => by
      have hoN : ∀ x, t.objEntry x = (s.allocObj { proto := .obj P }).objEntry x := by
        intro x; simp [State.objEntry, hheap]
      have hOt : O < t.heap.size := by rw [hheap]; simp [O]
      have hPt : t.objEntry P = s.objEntry P := by rw [hoN, State.allocObj_entry_lt _ _ _ hP]
      have hOPt : t.objEntry OP = s.objEntry OP := by rw [hoN, State.allocObj_entry_lt _ _ _ hOP]
      have hOe : t.objEntry O = { proto := .obj P } := by rw [hoN]; exact State.allocObj_entry_new _ _
      have hc : PlainChain t 3 O (.str "n") := by
        refine ⟨hOt, by rw [hOe]; rfl, fun _ => ?_⟩
        rw [hOe]
        refine ⟨by rw [hheap, State.allocObj_size]; exact Nat.lt_succ_of_lt hP, by rw [hPt, hPk]; rfl, fun _ => ?_⟩
        rw [hPt, hPp]
        exact ⟨by rw [hheap, State.allocObj_size]; exact Nat.lt_succ_of_lt hOP, by rw [hOPt, hOPk]; rfl, fun _ => by rw [hOPt, hOPp]; trivial⟩
      have hl : ordLookup t 3 O (.str "n") = none := by
        simp [ordLookup, hOe, hPt, hPn, hPp, hOPt, hOPn, hOPp]
      obtain ⟨ctx, t1, hfdi, hlex, hstr, hgen, hlt1, hL1, hfe1, hh1, hfu1, hr1⟩ :=
        ctr_fdi f d s.envs.size t (.obj O) (.obj f) hcode hlt hEt (by omega)
      have hput1 : putRefValue (.prop (.obj O) (.str "n") false none) (num 0) t1 =
          .ok () (t1.setProp O (.str "n") (.data (num 0) true true true)) := by
        have := putRefValue_prop O "n" false (num 0) t1 3 (by rw [hh1]; exact hOt)
          (by simp only [State.objEntry, hh1] at hOe ⊢; rw [hOe]; rfl)
          (by simp only [State.objEntry, hh1] at hOe ⊢; rw [hOe]; simp)
          (by simp only [State.objEntry, hh1] at hOe ⊢; rw [hOe])
          (by simp only [PlainChain, ordLookup, State.objEntry, hh1] at hc ⊢; exact hc) (by omega)
          (by simp only [ordLookup, State.objEntry, hh1] at hl ⊢; rw [hl]; rfl)
        exact this
      obtain ⟨cv, hbody⟩ := ctr_spec 999973 ctx t.envs.size s.envs.size O hlex hstr t1 ∅ ∅ (some d.env) f (.obj f)
        hlt1 (Nat.lt_trans hlt hlt1) hL1 (by rw [hfe1 _ hlt]; exact hEt) _ hput1 (by omega)
      refine ⟨t1.setProp O (.str "n") (.data (num 0) true true true), ?_,
        by simp only [State.setProp_envs]; exact Nat.le_of_lt (Nat.lt_trans hlt hlt1),
        fun e he => by simp only [State.envEntry, State.setProp_envs]; rw [← State.envEntry, hfe1 e (Nat.lt_trans he hlt)]; exact hold e he,
        by simp [State.setProp, newState, hh1, hheap]; rfl, by simp [hr1, hrl], by simp [hfu1, hfu']⟩
      have hbd : d.code.body = .stmts CTGen.Counter_stmts := by rw [hcode]; rfl
      have hdisp : d.code.info.fdi.usesDispose = false := by rw [hcode]; rfl
      have hbody' : evalStmts (999973 + 26) ctx CTGen.Counter_stmts t1 = .ok (.normal cv) (t1.setProp O (.str "n") (.data (num 0) true true true)) := by
        rw [← congrFun (CTGen.Counter_eq 999973) ctx]; exact hbody
      simp only [evalDepth, evalFunctionBody, M.bind_eq, M.bind_apply, hfdi, M.bindRes_ok, hbd, hdisp, withDisposeScope]
      simp [hbody', pure, M.pure])
  exact ⟨s', h1, h2, by rw [hen]; exact q1, fun e he => by simp only [State.envEntry, hen]; exact q2 e he,
    hh.trans q3, hrs.trans q4, hfe.trans q5⟩

/-! ## The function objects' `prototype` -/

theorem ne_pa : PropKey.str kPrototype ≠ PropKey.str "arguments" := by simp [kPrototype]; decide
theorem ne_pc : PropKey.str kPrototype ≠ PropKey.str "caller" := by simp [kPrototype]; decide

/-- A declared function's `prototype`: its own property points to the next object, an ordinary object whose
prototype is `Object.prototype` and whose only property is `constructor`. -/
theorem bindFn_proto (ge g sc fp : Nat) (fn : Func) (nm : JSStr) (t : State) (hg : g < t.heap.size) :
    let u := Script.bindFn ge g sc fp fn nm t
    (u.objEntry t.heap.size).props.get? (.str kPrototype) = some (.data (.obj (t.heap.size + 1)) true false false) ∧
    (u.objEntry (t.heap.size + 1)).kind = .ordinary ∧ (u.objEntry (t.heap.size + 1)).extensible = true ∧
    (u.objEntry (t.heap.size + 1)).proto = .obj t.curRealm.objectProto ∧
    (∀ k, k ≠ .str kConstructor → (u.objEntry (t.heap.size + 1)).props.get? k = none) := by
  intro u
  have hg0 : g ≠ t.heap.size := Nat.ne_of_lt hg
  have hg1 : g ≠ t.heap.size + 1 := Nat.ne_of_lt (Nat.lt_succ_of_lt hg)
  have hne : t.heap.size ≠ t.heap.size + 1 := Nat.ne_of_lt (Nat.lt_succ_self _)
  have hu : ∀ x, x ≠ g → u.objEntry x = (Inst.instStateFn fn nm t ge sc fp).objEntry x := by
    intro x hx; simp only [u, Script.bindFn]; rw [State.setProp_entry_ne _ _ _ _ _ (Ne.symm hx), State.setProp_entry_ne _ _ _ _ _ (Ne.symm hx)]
  have hlt0 : t.heap.size < (t.allocObj { proto := .obj fp, kind := .func (Inst.fnData fn t ge sc) }).heap.size := by simp
  rw [hu _ (Ne.symm hg0), hu _ (Ne.symm hg1)]
  simp only [Inst.instStateFn]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [State.setProp_entry_self _ _ _ _ (by simp only [State.setProp_size, State.allocObj_size]; exact Nat.lt_succ_of_lt (Nat.lt_succ_self _)), Obj.withProps_props, PropMap.get?_insert_ne _ _ _ _ (Ne.symm ne_pc),
      State.setProp_entry_self _ _ _ _ (by simp only [State.setProp_size, State.allocObj_size]; exact Nat.lt_succ_of_lt (Nat.lt_succ_self _)), Obj.withProps_props, PropMap.get?_insert_ne _ _ _ _ (Ne.symm ne_pa),
      State.setProp_entry_self _ _ _ _ (by simp only [State.setProp_size, State.allocObj_size]; exact Nat.lt_succ_of_lt (Nat.lt_succ_self _)), Obj.withProps_props, PropMap.get?_insert_self]
  all_goals
    rw [State.setProp_entry_ne _ _ _ _ _ hne, State.setProp_entry_ne _ _ _ _ _ hne, State.setProp_entry_ne _ _ _ _ _ hne,
      State.setProp_entry_self _ _ _ _ (by simp)]
    have hz : t.heap.size + 1 = (((t.allocObj { proto := .obj fp, kind := .func (Inst.fnData fn t ge sc) }).setProp t.heap.size
      (.str kLength) (.data (numV fn.info.expectedArgs) false false true)).setProp t.heap.size (.str kName)
      (.data (.str nm) false false true)).heap.size := by simp
    rw [hz, State.allocObj_entry_new]
  · rfl
  · rfl
  · rfl
  · intro k hk; simp [PropMap.get?_insert_ne _ _ _ _ (Ne.symm hk)]

/-! ## `Counter.prototype.inc = inc` and `new Counter()` -/

abbrev setProtoInc : Sem.CStmt := Sem.exprStmt (Sem.assign (Sem.memberRef (Sem.getValue (Sem.memberRef
  (Sem.ident "Counter") (Sem.Key.name "prototype") false)) (Sem.Key.name "inc") false) (Sem.ident "inc"))

/-- **`Counter.prototype.inc = inc`** (`Counter` and `inc` global functions `fC`, `fI`; `Counter.prototype` the
object `P`, which, like its prototype `OP`, has no `inc`): `P` gets an own `inc`. -/
theorem set_proto_inc (c : Ctx) (u : State) (ge g fI fC P OP : Nat) (gb : Std.HashMap JSStr Binding) (gtv : Value)
    (dC : FuncData) (hlex : c.lex = ge) (hstr : c.strict = false) (hge : ge < u.envs.size)
    (hE : u.envEntry ge = .global g gb gtv)
    (hgC : gb.contains "Counter" = false) (hgCm : (JSStr.ofString "Counter" ∈ gb) = False)
    (hgC' : gb[JSStr.ofString "Counter"]? = none)
    (hgi : gb.contains "inc" = false) (hgim : (JSStr.ofString "inc" ∈ gb) = False)
    (hgi' : gb[JSStr.ofString "inc"]? = none) (hgs : g < u.heap.size) (hk : (u.objEntry g).kind = .ordinary)
    (hpC : (u.objEntry g).props.get? (.str "Counter") = some (.data (.obj fC) true true false))
    (hpI : (u.objEntry g).props.get? (.str "inc") = some (.data (.obj fI) true true false))
    (hfC : fC < u.heap.size) (hfCk : (u.objEntry fC).kind = .func dC)
    (hpp : (u.objEntry fC).props.get? (.str "prototype") = some (.data (.obj P) true false false))
    (hP : P < u.heap.size) (hPk : (u.objEntry P).kind = .ordinary) (hPx : (u.objEntry P).extensible = true)
    (hPi : (u.objEntry P).props.get? (.str "inc") = none) (hPp : (u.objEntry P).proto = .obj OP)
    (hOP : OP < u.heap.size) (hOPk : (u.objEntry OP).kind = .ordinary)
    (hOPi : (u.objEntry OP).props.get? (.str "inc") = none) (hOPp : (u.objEntry OP).proto = .null)
    (hf : 2 ≤ u.fuel) :
    setProtoInc c u = .ok (.normal (some (.obj fI))) (u.setProp P (.str "inc") (.data (.obj fI) true true true)) := by
  have hk' : (u.objEntry g).kind.isPlain = true := by rw [hk]; rfl
  have hil : (Sem.inner c).lex = ge := hlex
  have his : (Sem.inner c).strict = false := hstr
  have hC := Global.identValue_global_obj ge "Counter" false u g gb gtv _ _ _ _ hge hE hgC hgCm hgC' hgs hk' hpC hf
  have hI := Global.identValue_global_obj ge "inc" false u g gb gtv _ _ _ _ hge hE hgi hgim hgi' hgs hk' hpI hf
  have hgetP : getRefValue (.prop (.obj fC) (.str "prototype") false none) u = .ok (.obj P) u := by
    rw [getRefValue_prop, Obj'.get_entry_data fC _ _ u hfC (by rw [hfCk]; rfl) (by rw [hpp]; rfl), hpp]; rfl
  have hc : PlainChain u 2 P (.str "inc") := by
    refine ⟨hP, by rw [hPk]; rfl, fun _ => ?_⟩
    rw [hPp]
    exact ⟨hOP, by rw [hOPk]; rfl, fun _ => by rw [hOPp]; trivial⟩
  have hl : ordLookup u 2 P (.str "inc") = none := by simp [ordLookup, hPi, hPp, hOPi, hOPp]
  have hput := putRefValue_prop P "inc" false (.obj fI) u 2 hP (by rw [hPk]; rfl) hPi hPx hc (by omega)
    (by rw [hl]; rfl)
  simp [setProtoInc, Sem.exprStmt, Sem.assign, Sem.memberRef, Sem.getValue, Sem.ident, hil, his, hC, hgetP, hI,
    hput, M.bind_eq, M.bind_apply, pure, M.pure]

/-- **`new Counter()`**: asks the driver to construct `fC` (new.target `fC` itself); its result is the value. -/
theorem new_req (c : Ctx) (u : State) (ge g fC : Nat) (gb : Std.HashMap JSStr Binding) (gtv : Value)
    (dC : FuncData) (hlex : c.lex = ge) (hstr : c.strict = false) (hge : ge < u.envs.size)
    (hE : u.envEntry ge = .global g gb gtv)
    (hgC : gb.contains "Counter" = false) (hgCm : (JSStr.ofString "Counter" ∈ gb) = False)
    (hgC' : gb[JSStr.ofString "Counter"]? = none) (hgs : g < u.heap.size) (hk : (u.objEntry g).kind = .ordinary)
    (hpC : (u.objEntry g).props.get? (.str "Counter") = some (.data (.obj fC) true true false))
    (hfC : fC < u.heap.size) (hfCk : (u.objEntry fC).kind = .func dC) (hkind : dC.code.kind = .normal)
    (hasync : dC.code.isAsync = false) (hgen : dC.code.isGenerator = false) (hf : 2 ≤ u.fuel) :
    ∃ K0, Sem.new (Sem.ident "Counter") (Sem.args #[]) c u = .req (.construct (.obj fC) #[] (.obj fC)) u K0 ∧
      ∀ v t, K0 (.normal v) t = .ok v t := by
  have hk' : (u.objEntry g).kind.isPlain = true := by rw [hk]; rfl
  have hC := Global.identValue_global_obj ge "Counter" c.strict u g gb gtv _ _ _ _ hge hE hgC hgCm hgC' hgs hk' hpC hf
  refine ⟨?K, ?h, ?_⟩
  case h =>
    conv =>
      lhs
      simp [Sem.new, Sem.ident, hlex, hC, Sem.args, M.foldArr, isConstructor, objKind, readObj_entry' _ _ _ hfC, hfCk,
        hkind, hasync, hgen, construct, M.bind_eq, M.bind_apply, pure, M.pure]
  intro v t; rfl

/-! ## The whole script -/

open Script

abbrev letC : Sem.CStmt := Sem.varDecl #[Sem.declLex VarKind.let "c" (some (Sem.new (Sem.ident "Counter") (Sem.args #[])))]
abbrev callC : Sem.CStmt := Sem.exprStmt (Sem.call (Sem.memberRef (Sem.ident "c") (Sem.Key.name "inc") false)
  (Sem.args #[]) false (CalleeDesc.prop "inc"))

theorem script_def (n : Nat) : CTGen.script n = Sem.stmts #[Sem.funDecl CTGen.inc_func, Sem.funDecl CTGen.Counter_func,
    setProtoInc, letC, callC, callC] := rfl
theorem lexScoped : topLevelLexicallyScoped CTGen.script_stmts = #[.binding .let (.ident "c")] := by
  have hv : (VarKind.let == VarKind.var) = false := by decide
  simp [topLevelLexicallyScoped, stmtLexScoped, CTGen.script_stmts, hv]
theorem inc_same : CTGen.inc_func = MEGen.inc_func := rfl
theorem ne_ci : (JSStr.ofString "c" = JSStr.ofString "inc") = False := by simp; decide
theorem ne_cC : (JSStr.ofString "c" = JSStr.ofString "Counter") = False := by simp; decide
theorem ne_n_ctor : PropKey.str (JSStr.ofString "n") ≠ PropKey.str kConstructor := by simp [kConstructor]; decide
theorem ne_inc_ctor : PropKey.str (JSStr.ofString "inc") ≠ PropKey.str kConstructor := by simp [kConstructor]; decide
theorem ne_inc_n : PropKey.str (JSStr.ofString "inc") ≠ PropKey.str (JSStr.ofString "n") := by simp; decide

def fs : List (Func × JSStr) := [(CTGen.inc_func, "inc"), (CTGen.Counter_func, "Counter")]

theorem varS : topLevelVarScoped CTGen.program.body = (fs.map fun p => VarScoped.func p.1).toArray := rfl
theorem lexS : topLevelLexicallyScoped CTGen.program.body =
    ((["c"] : List JSStr).map fun x => LexScoped.binding .let (.ident x)).toArray := by
  rw [show CTGen.program.body = CTGen.script_stmts from rfl, lexScoped]; rfl
theorem annS : annexBFunctions CTGen.program.body (["c"] : List JSStr).toArray = #[] := rfl
theorem simpleS : ∀ p ∈ fs, Inst.SimpleFn p.1 p.2 := by
  intro p hp; simp only [fs, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl
  · exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem nodupS : (fs.map Prod.snd).Nodup := by decide

/-- **The whole program** (examples/ctor.js), run as the engine runs a script: evaluates to 2. Started from a
realm whose global object is an ordinary extensible object without `c`, `inc` or `Counter`, and whose
`Object.prototype` is an ordinary object (not the global object) with prototype null and no `n` or `inc`. -/
theorem ct_script (eng : Engine) (s : State) (cs : Conts) (gb : Std.HashMap JSStr Binding) (gtv : Value)
    (fp : ObjId) (hge : s.curRealm.globalEnv < s.envs.size)
    (hE : s.envEntry s.curRealm.globalEnv = .global s.curRealm.globalObj gb gtv)
    (hgbc : gb.contains "c" = false) (hgbi : gb.contains "inc" = false) (hgbC : gb.contains "Counter" = false)
    (hgs : s.curRealm.globalObj < s.heap.size) (hk : (s.objEntry s.curRealm.globalObj).kind = .ordinary)
    (hx : (s.objEntry s.curRealm.globalObj).extensible = true)
    (hpc : (s.objEntry s.curRealm.globalObj).props.get? (.str "c") = none)
    (hpi : (s.objEntry s.curRealm.globalObj).props.get? (.str "inc") = none)
    (hpC : (s.objEntry s.curRealm.globalObj).props.get? (.str "Counter") = none)
    (hfp : s.curRealm.intrinsics["%Function.prototype%"]? = some fp)
    (hOP : s.curRealm.objectProto < s.heap.size) (hOPg : s.curRealm.objectProto ≠ s.curRealm.globalObj)
    (hOPk : (s.objEntry s.curRealm.objectProto).kind = .ordinary)
    (hOPp : (s.objEntry s.curRealm.objectProto).proto = .null)
    (hOPn : (s.objEntry s.curRealm.objectProto).props.get? (.str "n") = none)
    (hOPi : (s.objEntry s.curRealm.objectProto).props.get? (.str "inc") = none) (hf : 40 ≤ s.fuel) :
    ∃ s', (runM eng (scriptEvaluation CTGen.program) s cs).1 = .ok (num 2) s' := by
  let ge := s.curRealm.globalEnv
  let g := s.curRealm.globalObj
  let OP := s.curRealm.objectProto
  let c := scriptCtx s false
  -- the declarations
  obtain ⟨t0, ht0⟩ : ∃ x, (scriptStart s CTGen.program).setEnv ge (.global g (insertLets gb ["c"]) gtv) = x :=
    ⟨_, rfl⟩
  have ho0 : ∀ x, t0.objEntry x = s.objEntry x := by intro x; rw [← ht0, State.setEnv_objEntry]; rfl
  have hz0 : t0.heap.size = s.heap.size := by rw [← ht0, State.setEnv_heap_size]; rfl
  have hge0 : ge < t0.envs.size := by rw [← ht0, State.setEnv_envs_size]; exact hge
  have hgood : GoodG g fp t0 := ⟨by rw [hz0]; exact hgs, by rw [ho0]; exact hk, by rw [ho0]; exact hx,
    by rw [← ht0, State.setEnv_curRealm]; exact hfp⟩
  obtain ⟨⟨-, hku, -, -⟩, heu, hfuu, hru, hrlu, hszu, hou, -, -, hnames, hfuns⟩ :=
    instAll_facts ge g s.scripts.size fp fs t0 hgood (by decide)
  -- `Counter`'s object and its `prototype`, from the last declaration
  obtain ⟨hg1, -, -, -, ho1, -, hz1, -, -, hr1, hrl1⟩ := bindFn_good ge g s.scripts.size fp CTGen.inc_func "inc" t0 hgood
  obtain ⟨t1, ht1⟩ : ∃ x, bindFn ge g s.scripts.size fp CTGen.inc_func "inc" t0 = x := ⟨_, rfl⟩
  rw [ht1] at hg1 ho1 hz1 hr1 hrl1
  obtain ⟨-, -, -, -, -, hCk, -, -, -, -, -⟩ := bindFn_good ge g s.scripts.size fp CTGen.Counter_func "Counter" t1 hg1
  obtain ⟨hpp, hPk, hPx, hPp, hPprops⟩ := bindFn_proto ge g s.scripts.size fp CTGen.Counter_func "Counter" t1 hg1.1
  obtain ⟨u, hu⟩ : ∃ x, instAll ge g s.scripts.size fp fs t0 = x := ⟨_, rfl⟩
  have hu' : bindFn ge g s.scripts.size fp CTGen.Counter_func "Counter" t1 = u := by rw [← hu, ← ht1]; rfl
  rw [hu'] at hCk hpp hPk hPx hPp hPprops
  rw [hu] at hku heu hfuu hru hrlu hszu hou hnames hfuns
  have hfu0 : t0.fuel = s.fuel := by rw [← ht0, State.setEnv_fuel]; rfl
  have hrl0 : t0.realm = s.realm := by rw [← ht0, State.setEnv_realm]; rfl
  have hr0 : t0.realms = s.realms := by rw [← ht0, State.setEnv_realms]; rfl
  have hcr : u.curRealm = s.curRealm := by simp only [State.curRealm, hru, hrlu, hr0, hrl0]
  have hcr1 : t1.curRealm = s.curRealm := by simp only [State.curRealm, hr1, hrl1, hr0, hrl0]
  let fI := s.heap.size
  let fC := s.heap.size + 2
  let P := s.heap.size + 3
  have hfC : t1.heap.size = fC := by rw [hz1, hz0]
  rw [hfC] at hCk hpp hPk hPx hPp hPprops
  rw [hcr1] at hPp
  let dC := Inst.fnData CTGen.Counter_func t1 ge s.scripts.size
  obtain ⟨dI, hfIk, hcI, -, hmI, hclsI, -, -⟩ := hfuns 0 (by decide)
  rw [hz0] at hfIk hszu hnames hou
  simp only [fs, List.length_cons, List.length_nil] at hszu
  simp only [Nat.mul_zero, Nat.add_zero] at hfIk
  have hpI : (u.objEntry g).props.get? (.str "inc") = some (.data (.obj fI) true true false) := hnames 0 (by decide)
  have hpCu : (u.objEntry g).props.get? (.str "Counter") = some (.data (.obj fC) true true false) := hnames 1 (by decide)
  have hOPu : u.objEntry OP = s.objEntry OP := by rw [hou OP hOP hOPg, ho0]
  let gbL := gb.insert "c" { deletable := false }
  have hE1 : u.envEntry ge = .global g gbL gtv := by
    have h1 : u.envEntry ge = t0.envEntry ge := by simp only [State.envEntry, heu]
    rw [h1, ← ht0, State.setEnv_envEntry_self _ _ _ (show ge < (scriptStart s CTGen.program).envs.size from hge)]
    simp [insertLets, gbL]
  have hgeu : ge < u.envs.size := by rw [heu]; exact hge0
  have hgu : g < u.heap.size := by rw [hszu]; exact Nat.lt_of_lt_of_le hgs (Nat.le_add_right _ _)
  have hfIu : fI < u.heap.size := by show s.heap.size < u.heap.size; rw [hszu]; omega
  have hfCu : fC < u.heap.size := by show s.heap.size + 2 < u.heap.size; rw [hszu]; omega
  have hPu : P < u.heap.size := by show s.heap.size + 3 < u.heap.size; rw [hszu]; omega
  have hOPlt : OP < u.heap.size := by rw [hszu]; exact Nat.lt_of_lt_of_le hOP (Nat.le_add_right _ _)
  have hPOP : P ≠ OP := Ne.symm (Nat.ne_of_lt (Nat.lt_of_lt_of_le hOP (Nat.le_add_right _ 3)))
  have hgP : g ≠ P := Nat.ne_of_lt (Nat.lt_of_lt_of_le hgs (Nat.le_add_right _ 3))
  have hfCP : fC ≠ P := by show s.heap.size + 2 ≠ s.heap.size + 3; omega
  have hfIP : fI ≠ P := by show s.heap.size ≠ s.heap.size + 3; omega
  have hgbI' : gb[JSStr.ofString "inc"]? = none := Std.HashMap.getElem?_eq_none (fun hm => by
    rw [Std.HashMap.mem_iff_contains, hgbi] at hm; exact Bool.false_ne_true hm)
  have hgbC' : gb[JSStr.ofString "Counter"]? = none := Std.HashMap.getElem?_eq_none (fun hm => by
    rw [Std.HashMap.mem_iff_contains, hgbC] at hm; exact Bool.false_ne_true hm)
  have hLi : gbL.contains "inc" = false := by simp [gbL, Std.HashMap.contains_insert, hgbi, ne_ci]
  have hLi' : gbL[JSStr.ofString "inc"]? = none := by simp [gbL, Std.HashMap.getElem?_insert, ne_ci, hgbI']
  have hLim : (JSStr.ofString "inc" ∈ gbL) = False := by simp [Std.HashMap.mem_iff_contains, hLi]
  have hLC : gbL.contains "Counter" = false := by simp [gbL, Std.HashMap.contains_insert, hgbC, ne_cC]
  have hLC' : gbL[JSStr.ofString "Counter"]? = none := by simp [gbL, Std.HashMap.getElem?_insert, ne_cC, hgbC']
  have hLCm : (JSStr.ofString "Counter" ∈ gbL) = False := by simp [Std.HashMap.mem_iff_contains, hLC]
  -- `Counter.prototype.inc = inc`
  have hpp' : (u.objEntry fC).props.get? (.str "prototype") = some (.data (.obj P) true false false) := hpp
  have h3 := set_proto_inc c u ge g fI fC P OP gbL gtv dC rfl rfl hgeu hE1 hLC hLCm hLC' hLi hLim hLi' hgu hku hpCu hpI
    hfCu hCk hpp' hPu hPk hPx (hPprops _ ne_inc_ctor) hPp hOPlt (by rw [hOPu]; exact hOPk) (by rw [hOPu]; exact hOPi)
    (by rw [hOPu]; exact hOPp) (by rw [hfuu, hfu0]; omega)
  obtain ⟨u2, hu2⟩ : ∃ x, u.setProp P (.str "inc") (.data (.obj fI) true true true) = x := ⟨_, rfl⟩
  rw [hu2] at h3
  have ho2 : ∀ x, x ≠ P → u2.objEntry x = u.objEntry x := fun x hx => by rw [← hu2, State.setProp_entry_ne _ _ _ _ _ (Ne.symm hx)]
  have hP2 : u2.objEntry P = (u.objEntry P).withProps (·.insert (.str "inc") (.data (.obj fI) true true true)) := by
    rw [← hu2, State.setProp_entry_self _ _ _ _ hPu]
  have hz2 : u2.heap.size = u.heap.size := by rw [← hu2, State.setProp_size]
  have he2 : u2.envs = u.envs := by rw [← hu2, State.setProp_envs]
  have hf2 : u2.fuel = s.fuel := by rw [← hu2, State.setProp_fuel, hfuu, hfu0]
  have hge2 : ge < u2.envs.size := by rw [he2]; exact hgeu
  have hE2 : u2.envEntry ge = .global g gbL gtv := by simp only [State.envEntry, he2]; exact hE1
  -- `let c = new Counter()`
  obtain ⟨K0, h40, hK0⟩ := new_req (Sem.inner c) u2 ge g fC gbL gtv dC rfl rfl hge2 hE2 hLC hLCm hLC'
    (by rw [hz2]; exact hgu) (by rw [ho2 g hgP]; exact hku)
    (by rw [ho2 g hgP]; exact hpCu) (by rw [hz2]; exact hfCu) (by rw [ho2 fC hfCP]; exact hCk)
    rfl rfl rfl (by omega)
  obtain ⟨K4, h4, hK4⟩ := Stmts.let_req "c" _ c u2 ge g gbL gtv _ K0 rfl rfl hge2 hE2 (by simp [gbL]) (by omega) h40 hK0
  obtain ⟨u2', hu2'⟩ : ∃ x, ({ u2 with fuel := u2.fuel - 1 } : State) = x := ⟨_, rfl⟩
  have hou2 : ∀ x, u2'.objEntry x = u2.objEntry x := fun x => by rw [← hu2']; rfl
  have hz2' : u2'.heap.size = u.heap.size := by rw [← hu2', ← hz2]
  obtain ⟨s3, hc3, -, hz3, he3, hh3, hr3, hf3⟩ := ctr_construct fC dC u2' P OP true false false rfl rfl rfl rfl rfl rfl
    (by rw [hz2']; exact hfCu) (by rw [hou2, ho2 fC hfCP]; exact hCk) (by rw [hou2, ho2 fC hfCP]; exact hpp)
    (by rw [hz2']; exact hPu) (by rw [hou2, hP2, Obj.withProps_kind]; exact hPk)
    (by rw [hou2, hP2, Obj.withProps_props, PropMap.get?_insert_ne _ _ _ _ ne_inc_n]; exact hPprops _ ne_n_ctor)
    (by rw [hou2, hP2]; exact hPp) (by rw [hz2']; exact hOPlt)
    (by rw [hou2, ho2 OP (Ne.symm hPOP), hOPu]; exact hOPk) (by rw [hou2, ho2 OP (Ne.symm hPOP), hOPu]; exact hOPn)
    (by rw [hou2, ho2 OP (Ne.symm hPOP), hOPu]; exact hOPp) (by rw [← hu2']; simp only; omega)
  let O := u.heap.size
  have hOO : u2'.heap.size = O := hz2'
  rw [hOO] at hc3
  have himplC : constructImpl eng (.obj fC) #[] (.obj fC) u2 = .ok (.obj O) s3 := by
    rw [Construct.constructImpl_func eng fC dC _ _ u2 (by rw [hz2]; exact hfCu) (by rw [ho2 fC hfCP]; exact hCk) (by omega),
      hu2']
    exact hc3
  have hge3 : ge < s3.envs.size := Nat.lt_of_lt_of_le (by rw [← hu2']; exact hge2) hz3
  have hE3' : s3.envEntry ge = .global g gbL gtv := by rw [he3 ge (by rw [← hu2']; exact hge2)]; rw [← hu2']; exact hE2
  let gbC := gbL.modify "c" fun bd => { bd with value := some (.obj O) }
  obtain ⟨u3, hu3⟩ : ∃ x, s3.setEnv ge (.global g gbC gtv) = x := ⟨_, rfl⟩
  have hK4' := hK4 (.obj O) s3 gbL hge3 hE3' (by simp [gbL])
  rw [hu3] at hK4'
  have ho3 : ∀ x, u3.objEntry x = (newState u2' P).objEntry x := by
    intro x; rw [← hu3, State.setEnv_objEntry]; simp only [State.objEntry, hh3]
  have hz3' : u3.heap.size = O + 1 := by
    rw [← hu3, State.setEnv_heap_size, hh3]; simp [newState, hOO]
  have hge3' : ge < u3.envs.size := by rw [← hu3, State.setEnv_envs_size]; exact hge3
  have hE3 : u3.envEntry ge = .global g gbC gtv := by rw [← hu3]; exact State.setEnv_envEntry_self _ _ _ hge3
  have hf3' : u3.fuel = s.fuel - 1 := by rw [← hu3, State.setEnv_fuel, hf3, ← hu2']; simp only; rw [hf2]
  have hOe : u3.objEntry O = ({ proto := .obj P } : Obj).withProps (·.insert (.str "n") (.data (num 0) true true true)) := by
    rw [ho3, ← hOO]; simp only [newState]; rw [State.setProp_entry_self _ _ _ _ (by simp), State.allocObj_entry_new]
  have hO3 : O < u3.heap.size := by rw [hz3']; exact Nat.lt_succ_self _
  have hkO : (u3.objEntry O).kind = .ordinary := by rw [hOe]; rfl
  have hiO : (u3.objEntry O).props.get? (.str "inc") = none := by
    rw [hOe, Obj.withProps_props, PropMap.get?_insert_ne _ _ _ _ ProtoM.ne_n_inc]; simp
  have hpO : (u3.objEntry O).proto = .obj P := by rw [hOe]; rfl
  have hnO : (u3.objEntry O).props.get? (.str "n") = some (.data (num ((0 : Nat) : Int)) true true true) := by
    rw [hOe, Obj.withProps_props]; simp
  have hlt3 : ∀ x, x < u.heap.size → u3.objEntry x = u2.objEntry x := by
    intro x hx
    have hne : u2'.heap.size ≠ x := by rw [hz2']; exact Nat.ne_of_gt hx
    rw [ho3]; simp only [newState]
    rw [State.setProp_entry_ne _ _ _ _ _ hne, State.allocObj_entry_lt _ _ _ (by rw [hz2']; exact hx), hou2]
  have hPO : P ≠ O := Nat.ne_of_lt hPu
  have hfIO : fI ≠ O := Nat.ne_of_lt hfIu
  have hP3 : P < u3.heap.size := by rw [hz3']; exact Nat.lt_succ_of_lt hPu
  have hfI3 : fI < u3.heap.size := by rw [hz3']; exact Nat.lt_succ_of_lt hfIu
  have hPu3 : u3.objEntry P = (u.objEntry P).withProps (·.insert (.str "inc") (.data (.obj fI) true true true)) := by
    rw [hlt3 P hPu, hP2]
  have hkP : (u3.objEntry P).kind = .ordinary := by rw [hPu3, Obj.withProps_kind]; exact hPk
  have hiP : (u3.objEntry P).props.get? (.str "inc") = some (.data (.obj fI) true true true) := by
    rw [hPu3, Obj.withProps_props]; simp
  have hfIu3 : u3.objEntry fI = u.objEntry fI := by rw [hlt3 fI hfIu, ho2 fI hfIP]
  have hOb : gbC[JSStr.ofString "c"]? = some { value := some (.obj O), deletable := false } := by
    simp [gbC, gbL, Std.HashMap.getElem?_modify, Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert,
      Std.HashMap.getElem_modify]
  have hOm : (JSStr.ofString "c" ∈ gbC) = True := by simp [gbC, gbL]
  have hcodeI : dI.code = MEGen.inc_func := hcI.trans inc_same
  -- the first `c.inc()`: found on `Counter.prototype`; `this = c`, `n` from 0 to 1
  have hro3 := Global.identValue_global_decl ge "c" false u3 g gbC gtv _ (.obj O) hge3' hE3 hOb hOm rfl (by omega)
  have hget3 := ProtoM.get_inc_proto u3 O P fI true true true hO3 hkO hiO hpO hP3 hkP hiP
  obtain ⟨K5, h5, hK5⟩ := ProtoM.method_call_get_req (Sem.inner c) u3 (Sem.ident "c") O fI "inc" dI (.prop "inc")
    hro3 rfl hget3 hfI3 (by rw [hfIu3]; exact hfIk)
  obtain ⟨K6, h6, hK6⟩ := Stmts.exprStmt_req _ c u3 _ K5 h5 hK5
  obtain ⟨u3', hu3'⟩ : ∃ x, ({ u3 with fuel := u3.fuel - 1 } : State) = x := ⟨_, rfl⟩
  have hou3 : ∀ x, u3'.objEntry x = u3.objEntry x := fun x => by rw [← hu3']; rfl
  obtain ⟨s4, hc1, -, hz4, he4, hh4, ho4, -, hf4⟩ := Method.inc_call fI dI u3' O 0 hcodeI hclsI hmI
    (by rw [← hu3']; exact hO3) (by rw [hou3]; exact hkO) (by rw [hou3]; exact hnO) (by decide)
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
  have hge4 : ge < s4.envs.size := Nat.lt_of_lt_of_le (by rw [← hu3']; exact hge3') hz4
  have hE4 : s4.envEntry ge = .global g gbC gtv := by rw [he4 ge (by rw [← hu3']; exact hge3')]; rw [← hu3']; exact hE3
  have hf4' : s4.fuel = s.fuel - 2 := by rw [hf4, ← hu3']; simp only; rw [hf3']; omega
  -- the second `c.inc()`: `n` from 1 to 2
  have hro4 := Global.identValue_global_decl ge "c" false s4 g gbC gtv _ (.obj O) hge4 hE4 hOb hOm rfl (by omega)
  have hget4 := ProtoM.get_inc_proto s4 O P fI true true true (by rw [hz4']; exact hO3)
    (by rw [hO4e, Obj.withProps_kind]; exact hkO)
    (by rw [hO4e, Obj.withProps_props, PropMap.get?_insert_ne _ _ _ _ ProtoM.ne_n_inc]; exact hiO)
    (by rw [hO4e, Obj.withProps_proto]; exact hpO) (by rw [hz4']; exact hP3)
    (by rw [hO4 P hPO]; exact hkP) (by rw [hO4 P hPO]; exact hiP)
  obtain ⟨K7, h7, hK7⟩ := ProtoM.method_call_get_req (Sem.inner c) s4 (Sem.ident "c") O fI "inc" dI (.prop "inc")
    hro4 rfl hget4 (by rw [hz4']; exact hfI3) (by rw [hO4 fI hfIO, hfIu3]; exact hfIk)
  obtain ⟨K8, h8, hK8⟩ := Stmts.exprStmt_req _ c s4 _ K7 h7 hK7
  obtain ⟨s4', hs4'⟩ : ∃ x, ({ s4 with fuel := s4.fuel - 1 } : State) = x := ⟨_, rfl⟩
  have hos4 : ∀ x, s4'.objEntry x = s4.objEntry x := fun x => by rw [← hs4']; rfl
  obtain ⟨s5, hc2, -⟩ := Method.inc_call fI dI s4' O 1 hcodeI hclsI hmI
    (by rw [← hs4', hz4']; exact hO3) (by rw [hos4, hO4e, Obj.withProps_kind]; exact hkO)
    (by rw [hos4, hO4e, Obj.withProps_props]; simp) (by decide) (by rw [← hs4']; simp only; omega)
  have himpl2 : callImpl eng (.obj fI) (.obj O) #[] s4 = .ok (num 2) s5 := by
    rw [callImpl_func eng fI dI _ _ s4 (by rw [hz4']; exact hfI3) (by rw [hO4 fI hfIO, hfIu3]; exact hfIk) (by omega),
      hs4']
    exact hc2
  -- the script
  have hgbl : ∀ x ∈ (["c"] : List JSStr), gb.contains x = false := by
    intro x hx; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx; rcases hx with rfl; exact hgbc
  have hpl : ∀ x ∈ (["c"] : List JSStr), (s.objEntry s.curRealm.globalObj).props.get? (.str x) = none := by
    intro x hx; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx; rcases hx with rfl; exact hpc
  have hgbf : ∀ p ∈ fs, gb.contains p.2 = false := by
    intro p hp; simp only [fs, List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl
    · exact hgbi
    · exact hgbC
  have hpf : ∀ p ∈ fs, (s.objEntry s.curRealm.globalObj).props.get? (.str p.2) = none := by
    intro p hp; simp only [fs, List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl
    · exact hpi
    · exact hpC
  refine ⟨s5, script_value eng s cs CTGen.program fs ["c"] gb gtv fp _ s5 rfl varS lexS annS simpleS nodupS hge hE
    hgbf hgbl hgs hk hx hpf hpl hfp ?_⟩
  have hu0 : scriptState s CTGen.program fs ["c"] gb gtv fp = u := by rw [← hu, ← ht0]; rfl
  have hscript : evalStmts evalDepth (scriptCtx s false) CTGen.program.body u = CTGen.script 999962 c u := by
    rw [CTGen.script_eq]; rfl
  have h4' : letC c u2 = .req (.construct (.obj fC) #[] (.obj fC)) u2 K4 := h4
  have h6' : callC c u3 = .req (.call (.obj fI) (.obj O) #[]) u3 K6 := h6
  have h8' : callC c s4 = .req (.call (.obj fI) (.obj O) #[]) s4 K8 := h8
  rw [hu0, hscript, script_def]
  refine _root_.Runs.script_runs eng _ _ _ (_root_.Runs.stmts_run eng c _ u _ s5 ?_ (by simp; rw [hfuu, hfu0]; omega))
  show _root_.Runs.StmtsRun eng c [Sem.funDecl CTGen.inc_func, Sem.funDecl CTGen.Counter_func, setProtoInc, letC,
    callC, callC] u none (some (num 2)) s5
  refine .cons _ _ u u s5 none none _ (_root_.Runs.runs_funDecl eng _ c u rfl) ?_
  refine .cons _ _ u u s5 none none _ (_root_.Runs.runs_funDecl eng _ c u rfl) ?_
  refine .cons _ _ u u2 s5 (some (.obj fI)) none _ (by rw [h3]; exact _root_.Runs.runsTo_ok eng _ _) ?_
  refine .cons _ _ u2 u3 s5 none _ _ ?_ ?_
  · rw [h4']; exact Construct.runsTo_construct eng _ _ _ u2 K4 _ s3 _ u3 himplC (by rw [hK4']; exact _root_.Runs.runsTo_ok eng _ _)
  refine .cons _ _ u3 s4 s5 (some (num 1)) _ _ ?_ ?_
  · rw [h6']; exact _root_.Runs.runsTo_req1 eng _ _ _ u3 K6 _ s4 _ s4 himpl1 (hK6 _ s4)
  refine .cons _ _ s4 s5 s5 (some (num 2)) _ _ ?_ (.nil _ _)
  rw [h8']; exact _root_.Runs.runsTo_req1 eng _ _ _ s4 K8 _ s5 _ s5 himpl2 (hK8 _ s5)

end Ctor
