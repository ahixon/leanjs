import JSProofs.Calls2

/-!
# More rules: `!`, object literals, `try/finally`, comma expressions, compound assignment, `++`
(zippy docs/react-proofs.md)

What React's `dispatchSetStateInternal` and its callees use beyond `Calls2.lean`: `!0`/`!1` (minified booleans),
`var update = {lane: lane, …}` (a fresh object, its properties defined in order), `try { … } finally { }` on its
normal path, `(a, b)`, `fiber.lanes |= lane` and `x |= y`, `i++`.
-/

open ES ES.M HostRuns
open Std (HashMap)

namespace Logic

/-! ## Objects of a body's states, unconditionally -/

theorem allocObj_objEntry (s : State) (ob : Obj) (i : ObjId) :
    (s.allocObj ob).objEntry i = if i = s.heap.size then ob else s.objEntry i := by
  split
  · next h => subst h; exact State.allocObj_entry_new s ob
  · next h =>
    by_cases hl : i < s.heap.size
    · exact State.allocObj_entry_lt s i ob hl
    · have hge : s.heap.size ≤ i := Nat.le_of_not_lt hl
      have hgt : (s.allocObj ob).heap.size ≤ i := by
        rw [State.allocObj_size]; exact Nat.lt_of_le_of_ne hge (fun h' => h h'.symm)
      simp [State.objEntry, Array.getElem?_eq_none hgt, Array.getElem?_eq_none hge]

theorem setProp_objEntry (s : State) (o : ObjId) (k : PropKey) (p : Property) (i : ObjId) :
    (s.setProp o k p).objEntry i =
      if o = i ∧ i < s.heap.size then (s.objEntry i).withProps (·.insert k p) else s.objEntry i := by
  split
  · next h => obtain ⟨rfl, hl⟩ := h; exact State.setProp_entry_self s o k p hl
  · next h =>
    by_cases he : o = i
    · subst he
      have hl : ¬ o < s.heap.size := fun hl => h ⟨rfl, hl⟩
      have hge : s.heap.size ≤ o := Nat.le_of_not_lt hl
      have hge' : (s.setProp o k p).heap.size ≤ o := by simpa using hge
      simp [State.objEntry, Array.getElem?_eq_none hge', Array.getElem?_eq_none hge]
    · exact State.setProp_entry_ne s o i k p he

@[simp] theorem allocObj_envEntry (s : State) (ob : Obj) (e : EnvId) : (s.allocObj ob).envEntry e = s.envEntry e := by
  simp [State.envEntry]
@[simp] theorem setProp_envEntry (s : State) (o : ObjId) (k : PropKey) (p : Property) (e : EnvId) :
    (s.setProp o k p).envEntry e = s.envEntry e := by
  simp [State.envEntry]
@[simp] theorem allocObj_curRealm' (s : State) (ob : Obj) : (s.allocObj ob).curRealm = s.curRealm := by
  simp

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ}

/-! ## `!` -/

theorem wp_not {n : Nat} {h : σ} {e : Sem.CExpr} {ctx : Ctx} {s : State} {Q : Value → State → σ → Prop}
    (hw : WP eng answer n h (e ctx) s fun v w h1 => Q (.bool !(toBoolean v)) w h1) :
    WP eng answer n h (Sem.unary .not e ctx) s Q := by
  rw [wp_iff_wpr]
  simp only [Sem.unary, M.bind_eq, M.bind_apply]
  exact wpr_bind (wp_mono hw fun v w h1 q => wp_of_eq rfl q)

/-! ## Object literals -/

/-- The rest of an object literal's properties, defined on the fresh object `o` (static names only; each name not
yet defined on `o`). -/
def ObjWP (eng : Engine) (answer : HostAnswer σ) (n : Nat) (ctx : Ctx) (o : ObjId) :
    List Sem.PropD → σ → State → (Value → State → σ → Prop) → Prop
  | [], h, s, Q => Q (.obj o) s h
  | .init (.name pn) value :: ps, h, s, Q =>
    match staticPropKey pn with
    | some k => WP eng answer n h (value k ctx) s fun v w h1 =>
        o < w.heap.size ∧ (w.objEntry o).kind.isPlain = true ∧ (w.objEntry o).extensible = true ∧
        (w.objEntry o).props.get? k = none ∧
        ObjWP eng answer n ctx o ps h1 (w.setProp o k (.data v true true true)) Q
    | none => False
  | _ :: _, _, _, _ => False

/-- CreateDataPropertyOrThrow of an absent key of a plain extensible object: defined. -/
theorem createDataPropertyOrThrow_new (o : ObjId) (k : PropKey) (v : Value) (s : State) (h : o < s.heap.size)
    (hk : (s.objEntry o).kind.isPlain = true) (hx : (s.objEntry o).extensible = true)
    (hn : (s.objEntry o).props.get? k = none) :
    createDataPropertyOrThrow o k v s = .ok () (s.setProp o k (.data v true true true)) := by
  simp only [createDataPropertyOrThrow, createDataProperty, Obj'.defineOwnProperty, M.bind_eq, M.bind_apply]
  rw [show maxDepth = 19999 + 1 from rfl, defineOwnProperty_entry 19999 o k _ s h hk,
    ordinaryDefineOwnProperty_entry o k _ s h, hn]
  simp [validateAndApply, hx, PropDesc.data, PropDesc.isAccessor, State.setProp, Pure.pure, M.pure]

/-- One property of an object literal (`Sem.object`'s loop body). -/
def objStep (ctx : Ctx) (o : ObjId) (pd : Sem.PropD) : M Unit :=
  match pd with
  | .protoSet value => do
    let v ← value ctx
    match v with
    | .obj _ | .null => let _ ← Obj'.setPrototypeOf o v
    | _ => Pure.pure ()
  | .init key value => do
    let k ← Sem.propKey key ctx
    let v ← value k ctx
    createDataPropertyOrThrow o k v
  | .shorthand nm => do
    let v ← getRefValue (← resolveBinding ctx.lex nm ctx.strict)
    createDataPropertyOrThrow o (.str nm) v
  | .spread e => do
    let v ← e ctx
    copyDataProperties o v #[]
  | .method key f => do
    let k ← Sem.propKey key ctx
    defineMethodOn ctx o k f true

theorem object_eq (props : Array Sem.PropD) (ctx : Ctx) :
    Sem.object props ctx = (do
      let o ← newObject
      M.forArr props fun pd => objStep ctx o pd
      Pure.pure (Value.obj o)) := rfl

theorem wp_objProps {n : Nat} (ctx : Ctx) (o : ObjId) {Q : Unit → State → σ → Prop}
    {R : Value → State → σ → Prop} (hQ : ∀ w h, R (.obj o) w h → Q () w h) :
    ∀ (ps : List Sem.PropD) (h : σ) (s : State), ObjWP eng answer n ctx o ps h s R →
      WP eng answer n h (M.foldList ps () fun _ pd => objStep ctx o pd) s Q := by
  intro ps
  induction ps with
  | nil => intro h s hw; exact wp_of_eq rfl (hQ s h hw)
  | cons pd ps ih =>
    intro h s hw
    cases pd with
    | init key value =>
      cases key with
      | name pn =>
        simp only [ObjWP] at hw
        cases hsk : staticPropKey pn with
        | none => rw [hsk] at hw; exact hw.elim
        | some k =>
          rw [hsk] at hw
          rw [wp_iff_wpr, M.foldList_cons]
          apply wpr_bind
          have hpk : Sem.propKey (.name pn) ctx s = .ok k s := by simp [Sem.propKey, hsk, Pure.pure, M.pure]
          rw [← wp_iff_wpr]
          simp only [objStep]
          apply wp_bind
          refine wp_of_eq hpk ?_
          apply wp_bind
          refine wp_mono hw fun v w h1 ⟨hlt, hk, hx, hn, q⟩ => ?_
          exact wp_of_eq (createDataPropertyOrThrow_new o k v w hlt hk hx hn) (ih h1 _ q)
      | computed e => exact hw.elim
    | _ => exact hw.elim

/-- **An object literal** with static names: a fresh ordinary object (prototype `%Object.prototype%`), its
properties defined in order. -/
theorem wp_object {n : Nat} {h : σ} {props : Array Sem.PropD} {ctx : Ctx} {s : State}
    {Q : Value → State → σ → Prop}
    (hw : ObjWP eng answer n ctx s.heap.size props.toList h
      (s.allocObj { proto := .obj s.curRealm.objectProto }) Q) :
    WP eng answer n h (Sem.object props ctx) s Q := by
  rw [wp_iff_wpr, object_eq]
  simp only [M.bind_eq, M.bind_apply, newObject, alloc]
  have ha : s.withHeap (·.push { proto := .obj s.curRealm.objectProto }) =
      s.allocObj { proto := .obj s.curRealm.objectProto } := rfl
  rw [ha, M.bindRes_ok]
  apply wpr_bind
  rw [← wp_iff_wpr, forArr_def, foldArr_eq]
  exact wp_mono (wp_objProps ctx s.heap.size (Q := fun _ w h1 => Q (.obj s.heap.size) w h1) (fun _ _ q => q) _ h _ hw)
    fun _ w h1 q => wp_of_eq rfl q

/-! ## `try { … } finally { … }` and `try { … } catch …` on the normal path -/

theorem wpr_attempt {α : Type} {n : Nat} {h : σ} {x : M α} {s : State} {Q : Except Value α → State → σ → Prop}
    (hw : WP eng answer n h x s fun a w h1 => Q (.ok a) w h1) : WPR eng answer n h (M.attempt x s) Q := by
  obtain ⟨b, w, h', k, hr, q⟩ := hw
  exact ⟨.ok b, w, h', k, hr_attempt eng answer x s hr, q⟩

/-- **A `try` statement whose block completes** (any handler is not run): with a `finally`, the finally block, whose
normal completion keeps the block's; without, the block's. Empty values become `undefined`. -/
theorem wp_tryS {n : Nat} {h : σ} {blk : Sem.CStmt} {hd : Option Sem.CatchD} {fin : Option Sem.CStmt} {ctx : Ctx}
    {s : State} {Q : Compl → State → σ → Prop}
    (hw : WP eng answer n h (blk (Sem.inner ctx)) s fun r w h1 => match fin with
      | none => Q (r.updateEmpty (some .undefined)) w h1
      | some f => WP eng answer n h1 (f (Sem.inner ctx)) w fun fr w2 h2 => match fr with
        | .normal _ => Q (r.updateEmpty (some .undefined)) w2 h2
        | fr => Q (fr.updateEmpty (some .undefined)) w2 h2) :
    WP eng answer n h (Sem.tryS blk hd fin ctx) s Q := by
  rw [wp_iff_wpr]
  simp only [Sem.tryS, M.bind_eq, M.bind_apply]
  apply wpr_bind
  refine wpr_attempt (wp_mono hw fun r w h1 q => ?_)
  cases hd <;> cases fin with
  | none => exact wp_of_eq rfl q
  | some f =>
    apply wp_bind
    refine wp_of_eq rfl ?_
    apply wp_bind
    refine wp_mono q fun fr w2 h2 q' => ?_
    cases fr <;> exact wp_of_eq rfl q'

/-! ## `(a, b, …)` -/

def SeqWP (eng : Engine) (answer : HostAnswer σ) (n : Nat) (ctx : Ctx) :
    List Sem.CExpr → Value → σ → State → (Value → State → σ → Prop) → Prop
  | [], v, h, s, Q => Q v s h
  | e :: es, _, h, s, Q => WP eng answer n h (e ctx) s fun v w h1 => SeqWP eng answer n ctx es v h1 w Q

theorem wp_foldSeq {n : Nat} (ctx : Ctx) {Q : Value → State → σ → Prop} :
    ∀ (es : List Sem.CExpr) (v : Value) (h : σ) (s : State), SeqWP eng answer n ctx es v h s Q →
      WP eng answer n h (M.foldList es v fun _ e => e ctx) s Q := by
  intro es
  induction es with
  | nil => intro v h s hw; exact wp_of_eq rfl hw
  | cons e es ih =>
    intro v h s hw
    rw [wp_iff_wpr, M.foldList_cons]
    exact wpr_bind (wp_mono hw fun v' w h1 q => ih v' h1 w q)

/-- **A comma expression**: each in turn, the last one's value. -/
theorem wp_seqExpr {n : Nat} {h : σ} {es : Array Sem.CExpr} {ctx : Ctx} {s : State} {Q : Value → State → σ → Prop}
    (hw : SeqWP eng answer n ctx es.toList .undefined h s Q) : WP eng answer n h (Sem.seq es ctx) s Q := by
  show WP eng answer n h (M.foldArr es .undefined _) s Q
  rw [M.foldArr_eq]
  exact wp_foldSeq ctx _ _ h s hw

/-! ## Compound assignment and `++` on numbers -/

theorem applyBinaryOp_num (op : BinOp) (a b : F64) (s : State) (hop : isNumOp op = true) :
    applyBinaryOp op (.num a) (.num b) s = .ok (.num (numberBinOp op a b)) s := by
  cases op <;> simp [isNumOp] at hop <;> rfl

theorem toNumeric_num (a : F64) (s : State) : toNumeric (.num a) s = .ok (.num a) s := rfl

/-- `x op= rhs` of a variable holding a Number, a numeric operator: read, the right-hand side, then the write to
the same record. -/
theorem wp_assignOpIdentC {n : Nat} {h : σ} {op : BinOp} {x : JSStr} {rhs : Sem.CExpr} {ctx : Ctx} {s : State}
    {Q : Value → State → σ → Prop} (hk : depth ≤ s.fuel) (hop : isNumOp op = true)
    (hw : match Scope.resolve s depth ctx.lex x, Scope.lookup s depth ctx.lex x with
      | some e, some (.num a) => WP eng answer n h (rhs ctx) s fun rv w h1 => match rv with
        | .num b => SetsC w e x (.num (numberBinOp op a b)) fun w' => Q (.num (numberBinOp op a b)) w' h1
        | _ => False
      | _, _ => False) :
    WP eng answer n h (Sem.assignOp op (Sem.identRef x) rhs ctx) s Q := by
  cases hr : Scope.resolve s depth ctx.lex x with
  | none => rw [hr] at hw; exact hw.elim
  | some e =>
    cases hl : Scope.lookup s depth ctx.lex x with
    | none => rw [hr, hl] at hw; exact hw.elim
    | some v =>
      rw [hr, hl] at hw
      cases v with
      | num a =>
        simp only at hw
        obtain ⟨bm, o, bd, he, hd, hb, hv⟩ := resolve_lookup s x (.num a) depth ctx.lex e hr hl
        have h1 : Sem.identRef x ctx s = .ok (.env (some e) x ctx.strict) s :=
          Scope.resolveBinding_of_resolve s depth ctx.lex x ctx.strict e hr hk
        have h2 := Scope.getRefValue_env s e x ctx.strict he bm o hd bd (.num a) hb hv
        rw [wp_iff_wpr]
        simp only [Sem.assignOp, M.bind_eq, M.bind_apply, h1, M.bindRes_ok, getRefValueOnce, h2, FDI.pure_app]
        apply wpr_bind
        refine wp_mono hw fun rv w h' q => ?_
        cases rv with
        | num b =>
          obtain ⟨bm', o', bd', he', hd', hb', hv', hm', q'⟩ := setsC_setsVar q
          rw [wp_iff_wpr]
          simp only [M.bind_apply, applyBinaryOp_num op a b w hop, M.bindRes_ok]
          apply wpr_bind
          refine wp_of_eq (by
            show setMutableBinding e x _ ctx.strict w = _
            exact setMutableBinding_declLike e x _ ctx.strict w he' hd' hb' hv' hm') ?_
          exact wp_of_eq rfl q'
        | _ => exact q.elim
      | _ => exact hw.elim

/-- **`x++`** of a variable holding a Number: the old value; the variable incremented. -/
theorem wp_postIncIdentC {n : Nat} {h : σ} {x : JSStr} {ctx : Ctx} {s : State} {Q : Value → State → σ → Prop}
    (hk : depth ≤ s.fuel)
    (hw : match Scope.resolve s depth ctx.lex x, Scope.lookup s depth ctx.lex x with
      | some e, some (.num a) => SetsC s e x (.num (Conv.addF a F64.one)) fun w' => Q (.num a) w' h
      | _, _ => False) :
    WP eng answer n h (Sem.update true false (Sem.identRef x) ctx) s Q := by
  cases hr : Scope.resolve s depth ctx.lex x with
  | none => rw [hr] at hw; exact hw.elim
  | some e =>
    cases hl : Scope.lookup s depth ctx.lex x with
    | none => rw [hr, hl] at hw; exact hw.elim
    | some v =>
      rw [hr, hl] at hw
      cases v with
      | num a =>
        simp only at hw
        obtain ⟨bm, o, bd, he, hd, hb, hv⟩ := resolve_lookup s x (.num a) depth ctx.lex e hr hl
        obtain ⟨bm', o', bd', he', hd', hb', hv', hm', q⟩ := setsC_setsVar hw
        have h1 : Sem.identRef x ctx s = .ok (.env (some e) x ctx.strict) s :=
          Scope.resolveBinding_of_resolve s depth ctx.lex x ctx.strict e hr hk
        have h2 := Scope.getRefValue_env s e x ctx.strict he bm o hd bd (.num a) hb hv
        have h3 := setMutableBinding_declLike e x (.num (Conv.addF a F64.one)) ctx.strict s he' hd' hb' hv' hm'
        apply wp_of_eq _ q
        simp only [Sem.update, M.bind_eq, M.bind_apply, h1, M.bindRes_ok, getRefValueOnce, h2, FDI.pure_app,
          toNumeric_num, putRefValue, ite_true, if_true]
        rw [h3]
        rfl
      | _ => exact hw.elim

/-- **A block without lexical declarations**: its statements. -/
theorem wp_block {n : Nat} {h : σ} {decls : Array LexScoped} {body : Array Sem.CStmt} {ctx : Ctx} {s : State}
    {Q : Compl → State → σ → Prop} (hd : decls.isEmpty = true)
    (hw : WP eng answer n h (Sem.stmts body (Sem.inner ctx)) s Q) :
    WP eng answer n h (Sem.block decls body ctx) s Q := by
  simp only [Sem.block, hd, ↓reduceIte]
  exact hw

end

/-- A callee's final state with the caller's realm and script back: records and objects as in `w`. -/
@[js_simp] theorem restore_envEntry (w s : State) (e : EnvId) : (w.restore s).envEntry e = w.envEntry e := rfl
@[js_simp] theorem restore_objEntry (w s : State) (o : ObjId) : (w.restore s).objEntry o = w.objEntry o := rfl
@[js_simp] theorem restore_envs (w s : State) : (w.restore s).envs = w.envs := rfl
@[js_simp] theorem restore_heap (w s : State) : (w.restore s).heap = w.heap := rfl
@[js_simp] theorem restore_fuel (w s : State) : (w.restore s).fuel = w.fuel := rfl

attribute [js_simp] ObjWP SeqWP allocObj_objEntry setProp_objEntry allocObj_envEntry setProp_envEntry
  State.allocObj_size State.allocObj_fuel State.allocObj_envs staticPropKey PropMap.get?_insert
  PropMap.get?_empty Obj.withProps_kind Obj.withProps_props Obj.withProps_extensible Kind.isPlain_ordinary
  toNumeric_num State.setProp_fuel State.setProp_envs

/-- `js_step` with object literals, `!`, `try`, comma expressions, `op=` and `++` on variables. -/
macro_rules
  | `(tactic| js_step) => `(tactic| first
      | apply wp_not
      | apply wp_block (by rfl)
      | apply wp_object
      | apply wp_tryS
      | apply wp_seqExpr
      | apply wp_assignOpIdentC (by simp [depth]; omega) (by decide)
      | apply wp_postIncIdentC (by simp [depth]; omega))

end Logic
