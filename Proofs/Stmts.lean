import Proofs.Global

/-!
# Statements that ask the driver for one call

* `args_pure`: argument lists whose expressions evaluate without effects;
* `call_expr_req`: a call `f(e₁, …, eₙ)` of a function bound on the global object asks the driver to
  call it (with `this` undefined); the call expression's value is what the call returns;
* `exprStmt_req`, `let_req`: an expression statement, or a global `let x = e`, whose expression asks for
  one call; when it returns, the statement completes normally (with the value), or `x` is initialized.
-/

open ES ES.Conv
open Std (HashMap)
open Global (resolveBinding_global_decl resolveBinding_global_obj initializeBinding_global)

namespace Stmts

theorem foldList_args (w : State) (f : Array Value → Sem.ArgD → M (Array Value)) :
    ∀ (l : List (Sem.CExpr × Value)) (acc : Array Value),
      (∀ p ∈ l, ∀ acc', f acc' (Sem.ArgD.expr p.1) w = .ok (acc'.push p.2) w) →
      M.foldList (l.map fun p => Sem.ArgD.expr p.1) acc f w = .ok (acc ++ (l.map Prod.snd).toArray) w := by
  intro l
  induction l with
  | nil => intro acc _; simp
  | cons p l ih =>
    intro acc hl
    simp only [List.map_cons, M.foldList_cons, hl p (List.mem_cons_self ..), M.bindRes_ok]
    rw [ih _ (fun q hq => hl q (List.mem_cons_of_mem _ hq))]
    simp

theorem args_pure (c : Ctx) (w : State) (ps : List (Sem.CExpr × Value)) (hev : ∀ p ∈ ps, p.1 c w = .ok p.2 w) :
    Sem.args (ps.map fun p => Sem.ArgD.expr p.1).toArray c w = .ok (ps.map Prod.snd).toArray w := by
  simp only [Sem.args, M.foldArr_toArray]
  rw [foldList_args w _ ps #[] (fun p hp acc' => by simp [hev p hp, M.bind_eq, M.bind_apply, pure, M.pure])]
  simp

/-- **A call `nm(e₁, …, eₙ)`** of the function `fo` bound (as a writable, enumerable data property) on
the global object, the arguments evaluating without effects to `v₁, …, vₙ`: asks the driver to call
`fo` with `this` undefined; when it returns `v`, the call expression's value is `v`. -/
theorem call_expr_req (c : Ctx) (w : State) (ge g fo : Nat) (nm : JSStr) (gb : HashMap JSStr Binding) (gtv : Value)
    (d : FuncData) (ps : List (Sem.CExpr × Value)) (hev : ∀ p ∈ ps, p.1 c w = .ok p.2 w)
    (hlex : c.lex = ge) (hstr : c.strict = false)
    (hge : ge < w.envs.size) (hE : w.envEntry ge = .global g gb gtv) (hgb : gb.contains nm = false)
    (hgb' : gb[nm]? = none) (hgbm : (nm ∈ gb) = False)
    (hgs : g < w.heap.size) (hk : (w.objEntry g).kind = .ordinary)
    (hp : (w.objEntry g).props.get? (.str nm) = some (.data (.obj fo) true true false))
    (hfs : fo < w.heap.size) (hfk : (w.objEntry fo).kind = .func d) (hf : w.fuel ≠ 0) :
    ∃ K, Sem.call (Sem.identRef nm) (Sem.args (ps.map fun p => Sem.ArgD.expr p.1).toArray) false
        (CalleeDesc.ident nm) c w = .req (.call (.obj fo) .undefined (ps.map Prod.snd).toArray) w K ∧
      ∀ v t, K (.normal v) t = .ok v t := by
  have hk' : (w.objEntry g).kind.isPlain = true := by rw [hk]; rfl
  have hr := resolveBinding_global_obj ge nm false w g gb gtv _ hge hE hgb hgbm hgs hk' hp hf
  have ha := args_pure c w ps hev
  refine ⟨?K, ?h, ?_⟩
  case h =>
    conv =>
      lhs
      simp [Sem.call, Sem.identRef, hlex, hstr, hr, getRefValue, getBindingValue, readEnv_entry _ _ _ hge, hE, hgb',
        Obj'.hasProperty_entry_own _ _ _ hgs hk', hp, getProp, Obj'.get_entry_data _ _ _ _ hgs hk', refThisValue, ha,
        isCallable, readObj_entry' _ _ _ hfs, hfk, ES.call, pure, M.pure, hgbm, M.bind_eq, M.bind_apply,
        M.bindRes_ok]
  intro v t
  simp [M.pure, pure]

/-- An expression statement whose expression asks for one call: so does the statement, which then
completes normally with the call's value. -/
theorem exprStmt_req (e : Sem.CExpr) (c : Ctx) (w : State) (r : Req) (K0 : Outcome → State → Res Value)
    (h : e (Sem.inner c) w = .req r w K0) (hK0 : ∀ v t, K0 (.normal v) t = .ok v t) :
    ∃ K, Sem.exprStmt e c w = .req r w K ∧ ∀ v t, K (.normal v) t = .ok (.normal (some v)) t := by
  refine ⟨?K, ?h, ?_⟩
  case h => conv => lhs; simp only [Sem.exprStmt, M.bind_eq, M.bind_apply, h, M.bindRes_req]
  intro v t
  simp [hK0, M.bindRes_ok, pure, M.pure]

/-- A global `let x = e` (`x` declared, uninitialized, in the global record) whose initializer asks for one
call: so does the declaration; when the call returns `v` (in a state where the global record is still
there), `x` is initialized to `v`. -/
theorem let_req (x : JSStr) (e : Sem.CExpr) (c : Ctx) (u : State) (ge g : Nat) (gb : HashMap JSStr Binding)
    (gtv : Value) (r : Req) (K0 : Outcome → State → Res Value) (hlex : c.lex = ge) (hstr : c.strict = false)
    (hge : ge < u.envs.size) (hE : u.envEntry ge = .global g gb gtv) (hbm : (x ∈ gb) = True) (hf : u.fuel ≠ 0)
    (h : e (Sem.inner c) u = .req r u K0) (hK0 : ∀ v t, K0 (.normal v) t = .ok v t) :
    ∃ K, Sem.varDecl #[Sem.declLex VarKind.let x (some e)] c u = .req r u K ∧
      ∀ v w gbw, ge < w.envs.size → w.envEntry ge = .global g gbw gtv → gbw.contains x = true →
        K (.normal v) w = .ok (.normal none) (w.setEnv ge (.global g (gbw.modify x fun bd =>
          { bd with value := some v }) gtv)) := by
  have hil : (Sem.inner c).lex = ge := hlex
  have his : (Sem.inner c).strict = false := hstr
  have hr := resolveBinding_global_decl ge x false u g gb gtv hge hE hbm hf
  have hlu : (VarKind.let == VarKind.using) = false := by decide
  have hla : (VarKind.let == VarKind.awaitUsing) = false := by decide
  refine ⟨?K, ?h, ?_⟩
  case h =>
    conv =>
      lhs
      simp only [Sem.varDecl, M.bind_eq, M.bind_apply, M.forArr_def, M.foldArr_toArray, M.foldList_cons,
        Sem.declLex, hil, his, hr, M.bindRes_ok, h, M.bindRes_req]
  intro v w gbw hgew hEw hbw
  simp [hK0, initializeRefBinding, initializeBinding_global ge x v w g gbw gtv hgew hEw hbw, hlu, hla, pure, M.pure,
    M.bind_eq, M.bind_apply, M.bindRes_ok, M.foldList_nil]

end Stmts
