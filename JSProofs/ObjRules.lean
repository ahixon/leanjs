import JSProofs.SemRules
import JSProofs.Proto

/-!
# Rules for objects, assignments and calls (zippy docs/react-proofs.md)

Property reads through a chain of plain objects (`wp_getMember`, from `Proto.lean`'s `ordLookup`), writes of an own
writable data property (`wp_assignMember`: React's `update.hasEagerState = true`), assignments to variables of
declarative and function records (`wp_assignIdent`: a closure's module-level `executionContext = …`), `&&`/`||`,
`var`, expression statements, and calls of a variable's function (`wp_callIdent`), which hand the callee to its own
spec through `wp_call`.
-/

open ES ES.M HostRuns
open Std (HashMap)

namespace Logic

/-! ## State-level facts -/

/-- [[Set]] of an own writable data property of a plain object (receiver itself): the value replaced. -/
theorem putRefValue_own (o : ObjId) (k : JSStr) (strict : Bool) (v : Value) (s : State) (h : o < s.heap.size)
    (hk : (s.objEntry o).kind.isPlain = true) {v0 : Value} {e c : Bool}
    (hp : (s.objEntry o).props.get? (.str k) = some (.data v0 true e c)) :
    putRefValue (.prop (.obj o) (.str k) strict none) v s = .ok () (s.setProp o (.str k) (.data v true e c)) := by
  have hset : Obj'.set o (.str k) v (.obj o) s = .ok true (s.setProp o (.str k) (.data v true e c)) := by
    unfold Obj'.set
    rw [show maxDepth = 19997 + 3 from rfl, set_entry_own 19997 o _ v s h hk (by simp [hp]),
      ordinaryDefineOwnProperty_entry o _ _ s h, hp]
    simp [validateAndApply, PropDesc.isGeneric, PropDesc.isAccessor, PropDesc.isData, Property.configurable,
      Property.enumerable, State.setProp]
  simp [putRefValue, toPropertyKey, M.bind_eq, M.bind_apply, hset, Pure.pure, M.pure]

/-- SetMutableBinding of an initialized mutable binding of a declarative or function record. -/
theorem setMutableBinding_declLike (e : EnvId) (n : JSStr) (v : Value) (strict : Bool) (s : State)
    (he : e < s.envs.size) {bm : HashMap JSStr Binding} {o : Option EnvId}
    (hd : Scope.declLike? (s.envEntry e) = some (bm, o)) {bd : Binding} (hb : bm[n]? = some bd)
    (hv : bd.value.isSome = true) (hm : bd.mutable = true) :
    setMutableBinding e n v strict s =
      .ok () (s.setEnv e ((s.envEntry e).withBindings (·.modify n fun bd => { bd with value := some v }))) := by
  have hn : bd.value.isNone = false := by cases h : bd.value <;> simp_all
  simp only [setMutableBinding, M.bind_eq, M.bind_apply, readEnv_entry e _ s he, M.bindRes_ok, id]
  cases hen : s.envEntry e <;> rw [hen] at hd <;> simp [Scope.declLike?] at hd <;> obtain ⟨rfl, rfl⟩ := hd <;>
    simp only [declSetMutable, HashMap.get?_eq_getElem?, hb, hn, hm, Bool.false_eq_true, ↓reduceIte] <;>
    rw [modifyEnv_eq_setEnv _ e _ he, hen]

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ}

/-! ## Property reads and writes -/

/-- `o.k` reads a data property found through a chain of plain objects. -/
def GetsTo (s : State) (base : Value) (k : JSStr) (P : Value → Prop) : Prop :=
  ∃ o n, base = .obj o ∧ PlainChain s n o (.str k) ∧ n ≤ 9999 ∧ noAccessor (ordLookup s n o (.str k)) = true ∧
    P (ownDataValue (ordLookup s n o (.str k)))

/-- **`obj.k`** (a data property, own or inherited). -/
theorem wp_getMember {n : Nat} {h : σ} {obj : Sem.CExpr} {k : JSStr} {ctx : Ctx} {s : State}
    {Q : Value → State → σ → Prop}
    (hw : WP eng answer n h (obj ctx) s fun bv w h1 => GetsTo w bv k fun v => Q v w h1) :
    WP eng answer n h (Sem.getValue (Sem.memberRef obj (.name k) false) ctx) s Q := by
  rw [wp_iff_wpr]
  simp only [Sem.getValue, Sem.memberRef, M.bind_eq, M.bind_apply]
  apply wpr_bind
  apply wpr_bind
  refine wp_mono hw fun bv w h1 ⟨o, m, hb, hc, hm, hna, q⟩ => ?_
  subst hb
  simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  refine wp_of_eq (a := Ref.prop (.obj o) (.str k) ctx.strict none) rfl ?_
  exact wp_of_eq (by rw [getRefValue_prop]; exact Obj'.get_chain w _ _ m o hc hm hna) q

/-- `o.k = v` replaces an own writable data property of a plain object. -/
def PutsTo (s : State) (base : Value) (k : JSStr) (v : Value) (P : State → Prop) : Prop :=
  ∃ o v0 e c, base = .obj o ∧ o < s.heap.size ∧ (s.objEntry o).kind.isPlain = true ∧
    (s.objEntry o).props.get? (.str k) = some (.data v0 true e c) ∧ P (s.setProp o (.str k) (.data v true e c))

/-- **`obj.k = rhs`** of an own writable data property: the object, the value, then the write. -/
theorem wp_assignMember {n : Nat} {h : σ} {obj rhs : Sem.CExpr} {k : JSStr} {ctx : Ctx} {s : State}
    {Q : Value → State → σ → Prop}
    (hw : WP eng answer n h (obj ctx) s fun bv w1 h1 =>
      WP eng answer n h1 (rhs ctx) w1 fun v w2 h2 => PutsTo w2 bv k v fun w3 => Q v w3 h2) :
    WP eng answer n h (Sem.assign (Sem.memberRef obj (.name k) false) rhs ctx) s Q := by
  rw [wp_iff_wpr]
  simp only [Sem.assign, Sem.memberRef, M.bind_eq, M.bind_apply]
  apply wpr_bind
  apply wpr_bind
  refine wp_mono hw fun bv w1 h1 hr => ?_
  simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  refine wp_of_eq (a := Ref.prop bv (.str k) ctx.strict none) rfl ?_
  apply wp_bind
  refine wp_mono hr fun v w2 h2 ⟨o, v0, e, c, hb, hlt, hk, hp, q⟩ => ?_
  subst hb
  apply wp_bind
  exact wp_of_eq (putRefValue_own o k ctx.strict v w2 hlt hk hp) (wp_pure q)

/-! ## Variables -/

/-- Record `e` (resolved before the right-hand side ran) has an initialized mutable binding of `x`: setting it. -/
def SetsVar (s : State) (e : EnvId) (x : JSStr) (v : Value) (P : State → Prop) : Prop :=
  ∃ bm o bd, e < s.envs.size ∧ Scope.declLike? (s.envEntry e) = some (bm, o) ∧ bm[x]? = some bd ∧
    bd.value.isSome = true ∧ bd.mutable = true ∧
    P (s.setEnv e ((s.envEntry e).withBindings (·.modify x fun bd => { bd with value := some v })))

/-- **`x = rhs`** of a variable `Scope.resolve` finds in record `e`. -/
theorem wp_assignIdent {n : Nat} {h : σ} {x : JSStr} {rhs : Sem.CExpr} {ctx : Ctx} {s : State}
    {Q : Value → State → σ → Prop}
    (k : Nat) {e : EnvId} (hr : Scope.resolve s k ctx.lex x = some e) (hk : k ≤ s.fuel)
    (hw : WP eng answer n h (rhs ctx) s fun v w h1 => SetsVar w e x v fun w' => Q v w' h1) :
    WP eng answer n h (Sem.assign (Sem.identRef x) rhs ctx) s Q := by
  rw [wp_iff_wpr]
  simp only [Sem.assign, Sem.identRef, M.bind_eq, M.bind_apply,
    Scope.resolveBinding_of_resolve s k ctx.lex x ctx.strict e hr hk, M.bindRes_ok]
  apply wpr_bind
  refine wp_mono hw fun v w h1 ⟨bm, o, bd, he, hd, hb, hv, hm, q⟩ => ?_
  apply wp_bind
  refine wp_of_eq (by
    show setMutableBinding e x v ctx.strict w = _
    exact setMutableBinding_declLike e x v ctx.strict w he hd hb hv hm) ?_
  exact wp_pure q

/-! ## Logical operators -/

theorem wp_and {n : Nat} {h : σ} {l r : Sem.CExpr} {ctx : Ctx} {s : State} {Q : Value → State → σ → Prop}
    (hw : WP eng answer n h (l ctx) s fun lv w h1 =>
      if toBoolean lv then WP eng answer n h1 (r ctx) w Q else Q lv w h1) :
    WP eng answer n h (Sem.logical .and l r ctx) s Q := by
  rw [wp_iff_wpr]
  simp only [Sem.logical, M.bind_eq, M.bind_apply]
  apply wpr_bind
  refine wp_mono hw fun lv w h1 q => ?_
  cases hb : toBoolean lv <;> simp only [hb, Bool.not_false, Bool.not_true, ↓reduceIte] at q ⊢
  · exact wp_pure q
  · exact q

theorem wp_or {n : Nat} {h : σ} {l r : Sem.CExpr} {ctx : Ctx} {s : State} {Q : Value → State → σ → Prop}
    (hw : WP eng answer n h (l ctx) s fun lv w h1 =>
      if toBoolean lv then Q lv w h1 else WP eng answer n h1 (r ctx) w Q) :
    WP eng answer n h (Sem.logical .or l r ctx) s Q := by
  rw [wp_iff_wpr]
  simp only [Sem.logical, M.bind_eq, M.bind_apply]
  apply wpr_bind
  refine wp_mono hw fun lv w h1 q => ?_
  cases hb : toBoolean lv <;> simp only [hb, ↓reduceIte] at q ⊢
  · exact q
  · exact wp_pure q

theorem wp_sne {n : Nat} {h : σ} {a b : Value} {s : State} {Q : Value → State → σ → Prop}
    (hq : Q (.bool !(isStrictlyEqual a b)) s h) : WP eng answer n h (Sem.binaryOp .sne a b) s Q :=
  wp_of_eq rfl hq

/-! ## Statements -/

theorem wp_exprStmt {n : Nat} {h : σ} {e : Sem.CExpr} {ctx : Ctx} {s : State} {Q : Compl → State → σ → Prop}
    (hw : WP eng answer n h (e (Sem.inner ctx)) s fun v w h1 => Q (.normal (some v)) w h1) :
    WP eng answer n h (Sem.exprStmt e ctx) s Q := by
  rw [wp_iff_wpr]
  simp only [Sem.exprStmt, M.bind_eq, M.bind_apply]
  exact wpr_bind (wp_mono hw fun _ _ _ q => wp_of_eq rfl q)

/-- **`var x = rhs`** where `Scope.resolve` finds `x` in record `e` (the function's own, for its `var`s). -/
theorem wp_declVar {n : Nat} {h : σ} {x : JSStr} {rhs : Sem.CExpr} {ctx : Ctx} {s : State}
    {Q : Unit → State → σ → Prop}
    (k : Nat) {e : EnvId} (hr : Scope.resolve s k ctx.lex x = some e) (hk : k ≤ s.fuel)
    (hw : WP eng answer n h (rhs ctx) s fun v w h1 => SetsVar w e x v fun w' => Q () w' h1) :
    WP eng answer n h (Sem.declVar x rhs ctx) s Q := by
  rw [wp_iff_wpr]
  simp only [Sem.declVar, M.bind_eq, M.bind_apply,
    Scope.resolveBinding_of_resolve s k ctx.lex x ctx.strict e hr hk, M.bindRes_ok]
  apply wpr_bind
  refine wp_mono hw fun v w h1 ⟨bm, o, bd, he, hd, hb, hv, hm, q⟩ => ?_
  refine wp_of_eq (by
    show setMutableBinding e x v ctx.strict w = _
    exact setMutableBinding_declLike e x v ctx.strict w he hd hb hv hm) q

/-- A list of declarations, one after the other. -/
def DeclsWP (eng : Engine) (answer : HostAnswer σ) (n : Nat) (ctx : Ctx) :
    List Sem.CDecl → σ → State → (State → σ → Prop) → Prop
  | [], h, s, Q => Q s h
  | d :: ds, h, s, Q => WP eng answer n h (d ctx) s fun _ w h1 => DeclsWP eng answer n ctx ds h1 w Q

theorem wp_foldDecls {n : Nat} (ctx : Ctx) {Q : State → σ → Prop} :
    ∀ (ds : List Sem.CDecl) (h : σ) (s : State), DeclsWP eng answer n ctx ds h s Q →
      WP eng answer n h (foldList ds () fun _ d => d ctx) s fun _ w h1 => Q w h1 := by
  intro ds
  induction ds with
  | nil => intro h s hw; exact wp_of_eq rfl hw
  | cons d ds ih =>
    intro h s hw
    rw [wp_iff_wpr, foldList_cons]
    exact wpr_bind (wp_mono hw fun _ w h1 q => ih h1 w q)

/-- **`var d₁, d₂, …`**: the declarations in order; a normal, empty completion. -/
theorem wp_varDecl {n : Nat} {h : σ} {ds : Array Sem.CDecl} {ctx : Ctx} {s : State}
    {Q : Compl → State → σ → Prop}
    (hw : DeclsWP eng answer n (Sem.inner ctx) ds.toList h s fun w h1 => Q (.normal none) w h1) :
    WP eng answer n h (Sem.varDecl ds ctx) s Q := by
  rw [wp_iff_wpr]
  simp only [Sem.varDecl, M.bind_eq, M.bind_apply, forArr_def, foldArr_eq]
  exact wpr_bind (wp_mono (wp_foldDecls (Sem.inner ctx) ds.toList h s hw) fun _ w h1 q => wp_pure q)

end

end Logic
