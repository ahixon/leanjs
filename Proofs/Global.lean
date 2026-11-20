import Proofs.MoreCalls
import Proofs.Instantiate

/-!
# The global environment record's declarative part, and statements over it

Generic pieces for scripts: `let` bindings in the global record (create, initialize, resolve, read),
a statement `f(b)` asking the driver to call a function bound on the global object (`call_req`), and the
global record once `b` holds an object (`gb2`).
-/

open ES ES.Conv SumProof SumForProof TotalProof
open Std (HashMap)

namespace Global

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

/-- `resolveBinding` of a name in the global record's declarative part. -/
theorem resolveBinding_global_decl (env : EnvId) (n : JSStr) (strict : Bool) (s : State) (g : ObjId)
    (b : HashMap JSStr Binding) (tv : Value) (h : env < s.envs.size) (hE : s.envEntry env = .global g b tv)
    (hbm : (n ∈ b) = True) (hf : s.fuel ≠ 0) :
    resolveBinding env n strict s = .ok (.env (some env) n strict) s := by
  obtain ⟨k, hk1⟩ : ∃ k, s.fuel = k + 1 := ⟨s.fuel - 1, by omega⟩
  rw [resolveBinding_loop, hk1]
  simp [M.loop, resolveBody, M.bind_eq, M.bind_apply, hasBinding, readEnv_entry _ _ _ h, hE, hbm, pure, M.pure]


abbrev callOf (nm : JSStr) : Sem.CStmt :=
  Sem.exprStmt (Sem.call (Sem.identRef nm) (Sem.args #[Sem.ArgD.expr (Sem.ident "b")]) false (CalleeDesc.ident nm))

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

/-- An identifier bound on the global object (as a data property), not in the declarative part. -/
theorem identValue_global_obj (env : EnvId) (n : JSStr) (strict : Bool) (s : State) (g : ObjId)
    (b : HashMap JSStr Binding) (tv : Value) (v : Value) (w e c : Bool) (h : env < s.envs.size)
    (hE : s.envEntry env = .global g b tv) (hb : b.contains n = false) (hbm : (n ∈ b) = False)
    (hb' : b[n]? = none) (hgs : g < s.heap.size) (hk : (s.objEntry g).kind.isPlain = true)
    (hp : (s.objEntry g).props.get? (.str n) = some (.data v w e c)) (hf : 2 ≤ s.fuel) :
    identValue env n strict s = .ok v s := by
  obtain ⟨k, hk1⟩ : ∃ k, s.fuel = k + 2 := ⟨s.fuel - 2, by omega⟩
  have hr := resolveBinding_global_obj env n strict s g b tv _ h hE hb hbm hgs hk hp (by omega)
  rw [identValue_loop, hk1]
  simp [M.loop, identBody, M.bind_eq, M.bind_apply, readEnv_entry _ _ _ h, hE, hr, getRefValue, getBindingValue, hb',
    Obj'.hasProperty_entry_own _ _ _ hgs hk, hp, getProp, Obj'.get_entry_data _ _ _ _ hgs hk, ownDataValue,
    isOwnData, pure, M.pure]

end Global
