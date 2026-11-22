import Lean
import JSProofs.JsAttr
import JSProofs.Body

/-!
# Computational rules and the `js` tactic (zippy docs/react-proofs.md)

Each rule's premise evaluates what the step reads (`Scope.lookup`, `Scope.resolve`, `ordLookup`, a record's or an
object's entry) as a function of the state, and `simp` computes it: on a body's states (`bodyState`, record and
object updates), lookups reduce to hypotheses about the caller's state and to hash-map lookups of literal names,
decided by `decide`. `js` applies the rule for the computation's head symbol and normalizes, so a function's proof
follows its code without hand-written lookup facts.
-/

open ES ES.M HostRuns
open Std (HashMap)

namespace Logic

open Lean Meta Simp in
/-- `JSStr.ofString "a" == JSStr.ofString "b"` for two string literals: decided (the kernel checks the `rfl`). -/
simproc jsstrBeq (@BEq.beq JSStr _ (JSStr.ofString _) (JSStr.ofString _)) := fun e => do
  let_expr BEq.beq _ _ x y := e | return .continue
  let_expr JSStr.ofString a := x | return .continue
  let_expr JSStr.ofString b := y | return .continue
  let .lit (.strVal a) := a | return .continue
  let .lit (.strVal b) := b | return .continue
  let r := toExpr (a == b)
  return .done { expr := r, proof? := some (← mkExpectedTypeHint (← mkEqRefl r) (← mkEq e r)) }


/-- The scope-chain depth the rules look through (a module's code: the function's record, its enclosing
functions' records, the module's). -/
abbrev depth : Nat := 8

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ}

/-- **An identifier**, its value computed by `Scope.lookup`. -/
theorem wp_identC {n : Nat} {h : σ} {x : JSStr} {ctx : Ctx} {s : State} {Q : Value → State → σ → Prop}
    (hk : depth ≤ s.fuel)
    (hq : match Scope.lookup s depth ctx.lex x with | some v => Q v s h | none => False) :
    WP eng answer n h (Sem.ident x ctx) s Q := by
  cases hl : Scope.lookup s depth ctx.lex x with
  | none => rw [hl] at hq; exact hq.elim
  | some v => rw [hl] at hq; exact wp_ident depth hl hk hq

/-- `o.k` of a plain object whose own property `k` is a data property. -/
def GetsC (s : State) (base : Value) (k : JSStr) (P : Value → Prop) : Prop :=
  match base with
  | .obj o => o < s.heap.size ∧ (s.objEntry o).kind.isPlain = true ∧
    match (s.objEntry o).props.get? (.str k) with
    | some (.data v _ _ _) => P v
    | _ => False
  | _ => False

theorem getsC_getsTo {s : State} {base : Value} {k : JSStr} {P : Value → Prop} (h : GetsC s base k P) :
    GetsTo s base k P := by
  cases base with
  | obj o =>
    obtain ⟨hlt, hk, hp⟩ := h
    cases hg : (s.objEntry o).props.get? (.str k) with
    | none => rw [hg] at hp; exact hp.elim
    | some p =>
      rw [hg] at hp
      cases p with
      | accessor => exact hp.elim
      | data v w e c =>
        refine ⟨o, 1, rfl, plainChain_own s o _ hlt hk hg, by omega, by simp [ordLookup_own s o _ hg, noAccessor], ?_⟩
        rw [ordLookup_own s o _ hg]; exact hp
  | _ => exact h.elim

/-- **`obj.k`** of an own data property. -/
theorem wp_getMemberC {n : Nat} {h : σ} {obj : Sem.CExpr} {k : JSStr} {ctx : Ctx} {s : State}
    {Q : Value → State → σ → Prop}
    (hw : WP eng answer n h (obj ctx) s fun bv w h1 => GetsC w bv k fun v => Q v w h1) :
    WP eng answer n h (Sem.getValue (Sem.memberRef obj (.name k) false) ctx) s Q :=
  wp_getMember (wp_mono hw fun _ _ _ q => getsC_getsTo q)

/-- `x = v` of an initialized mutable binding in record `e`, computed. -/
def SetsC (s : State) (e : EnvId) (x : JSStr) (v : Value) (P : State → Prop) : Prop :=
  e < s.envs.size ∧
  match Scope.declLike? (s.envEntry e) with
  | some (bm, _) => match bm[x]? with
    | some bd => bd.value.isSome = true ∧ bd.mutable = true ∧
      P (s.setEnv e ((s.envEntry e).withBindings (·.modify x fun bd => { bd with value := some v })))
    | none => False
  | none => False

theorem setsC_setsVar {s : State} {e : EnvId} {x : JSStr} {v : Value} {P : State → Prop}
    (h : SetsC s e x v P) : SetsVar s e x v P := by
  obtain ⟨he, hm⟩ := h
  cases hd : Scope.declLike? (s.envEntry e) with
  | none => rw [hd] at hm; exact hm.elim
  | some p =>
    obtain ⟨bm, o⟩ := p
    rw [hd] at hm
    cases hb : bm[x]? with
    | none => simp only [hb] at hm
    | some bd =>
      simp only [hb] at hm
      exact ⟨bm, o, bd, he, hd, hb, hm.1, hm.2.1, hm.2.2⟩

/-- **`var x = rhs`**, `x`'s record found by `Scope.resolve`. -/
theorem wp_declVarC {n : Nat} {h : σ} {x : JSStr} {rhs : Sem.CExpr} {ctx : Ctx} {s : State}
    {Q : Unit → State → σ → Prop} (hk : depth ≤ s.fuel)
    (hw : match Scope.resolve s depth ctx.lex x with
      | some e => WP eng answer n h (rhs ctx) s fun v w h1 => SetsC w e x v fun w' => Q () w' h1
      | none => False) :
    WP eng answer n h (Sem.declVar x rhs ctx) s Q := by
  cases hr : Scope.resolve s depth ctx.lex x with
  | none => rw [hr] at hw; exact hw.elim
  | some e =>
    rw [hr] at hw
    exact wp_declVar depth hr hk (wp_mono hw fun _ _ _ q => setsC_setsVar q)

/-- **`x = rhs`** of a variable, its record found by `Scope.resolve`. -/
theorem wp_assignIdentC {n : Nat} {h : σ} {x : JSStr} {rhs : Sem.CExpr} {ctx : Ctx} {s : State}
    {Q : Value → State → σ → Prop} (hk : depth ≤ s.fuel)
    (hw : match Scope.resolve s depth ctx.lex x with
      | some e => WP eng answer n h (rhs ctx) s fun v w h1 => SetsC w e x v fun w' => Q v w' h1
      | none => False) :
    WP eng answer n h (Sem.assign (Sem.identRef x) rhs ctx) s Q := by
  cases hr : Scope.resolve s depth ctx.lex x with
  | none => rw [hr] at hw; exact hw.elim
  | some e =>
    rw [hr] at hw
    exact wp_assignIdent depth hr hk (wp_mono hw fun _ _ _ q => setsC_setsVar q)

/-- `o.k = v` of a plain object's own writable data property, computed. -/
def PutsC (s : State) (base : Value) (k : JSStr) (v : Value) (P : State → Prop) : Prop :=
  match base with
  | .obj o => o < s.heap.size ∧ (s.objEntry o).kind.isPlain = true ∧
    match (s.objEntry o).props.get? (.str k) with
    | some (.data _ true e c) => P (s.setProp o (.str k) (.data v true e c))
    | _ => False
  | _ => False

theorem putsC_putsTo {s : State} {base : Value} {k : JSStr} {v : Value} {P : State → Prop}
    (h : PutsC s base k v P) : PutsTo s base k v P := by
  cases base with
  | obj o =>
    obtain ⟨hlt, hk, hp⟩ := h
    cases hg : (s.objEntry o).props.get? (.str k) with
    | none => rw [hg] at hp; exact hp.elim
    | some p =>
      rw [hg] at hp
      cases p with
      | accessor => exact hp.elim
      | data v0 w e c =>
        cases w with
        | false => exact hp.elim
        | true => exact ⟨o, v0, e, c, rfl, hlt, hk, hg, hp⟩
  | _ => exact h.elim

/-- **`obj.k = rhs`** of an own writable data property. -/
theorem wp_assignMemberC {n : Nat} {h : σ} {obj rhs : Sem.CExpr} {k : JSStr} {ctx : Ctx} {s : State}
    {Q : Value → State → σ → Prop}
    (hw : WP eng answer n h (obj ctx) s fun bv w1 h1 =>
      WP eng answer n h1 (rhs ctx) w1 fun v w2 h2 => PutsC w2 bv k v fun w3 => Q v w3 h2) :
    WP eng answer n h (Sem.assign (Sem.memberRef obj (.name k) false) rhs ctx) s Q :=
  wp_assignMember (wp_mono hw fun _ _ _ q => wp_mono q fun _ _ _ q' => putsC_putsTo q')

/-- `if` on a value: the branch `toBoolean` picks. -/
theorem wp_ite {α : Type} {n : Nat} {h : σ} {c : Bool} {x y : M α} {s : State} {Q : α → State → σ → Prop}
    (hw : if c then WP eng answer n h x s Q else WP eng answer n h y s Q) :
    WP eng answer n h (if c then x else y) s Q := by
  cases c <;> simpa using hw

end

/-! ## The tactic -/

open Lean Meta Simp in
/-- `JSStr.ofString "a" = JSStr.ofString "b"` for two string literals: `True` or `False` (the kernel checks the
`decide`). -/
simproc jsstrEq ((JSStr.ofString _ : JSStr) = JSStr.ofString _) := fun e => do
  let_expr Eq _ x y := e | return .continue
  let_expr JSStr.ofString a := x | return .continue
  let_expr JSStr.ofString b := y | return .continue
  let .lit (.strVal a') := a | return .continue
  let .lit (.strVal b') := b | return .continue
  if a' == b' then
    return .done { expr := mkConst ``True, proof? := some (← mkEqTrue (← mkEqRefl x)) }
  else
    let hd ← mkDecide e
    let h ← mkEqRefl (mkConst ``false)
    let hne ← mkAppM ``of_decide_eq_false #[← mkExpectedTypeHint h (← mkEq hd (mkConst ``false))]
    return .done { expr := mkConst ``False, proof? := some (← mkEqFalse hne) }

/-! ## Literal arrays (a call's arguments, a function's parameter names) -/

@[simp] theorem lit_getElem?_zero {α : Type} (a : α) (l : List α) : (List.toArray (a :: l))[0]? = some a := by simp
@[simp] theorem lit_getElem?_succ {α : Type} (a : α) (l : List α) (i : Nat) :
    (List.toArray (a :: l))[i + 1]? = (List.toArray l)[i]? := by simp
@[simp] theorem lit_getElem!_zero {α : Type} [Inhabited α] (a : α) (l : List α) : (List.toArray (a :: l))[0]! = a := by
  simp
@[simp] theorem lit_getElem!_succ {α : Type} [Inhabited α] (a : α) (l : List α) (i : Nat) :
    (List.toArray (a :: l))[i + 1]! = (List.toArray l)[i]! := by
  simp [getElem!_def]

/-- The function's own record in `bodyState`, explicitly. -/
theorem bodyState_envEntry_self (s : State) (fo : ObjId) (d : FuncData) (t : Value) (args : Array Value) :
    (bodyState s fo d t args).envEntry s.envs.size = .func
      (FDI.fdiMap d.code.info.fdi.paramNames args d.code.info.fdi.varNames (FDI.lexDecls d))
      (some d.env) .initialized t fo .undefined := by
  have h : s.envs.size < (entryState s fo d t).envs.size := by simp [entryState]
  simp [bodyState, h]

/-! ## Numbers -/

/-- A numeric operator (not `+`, comparisons, `in`, `instanceof`) on two Numbers. -/
def isNumOp : BinOp → Bool
  | .sub | .mul | .div | .mod | .exp | .shl | .sar | .shr | .bitAnd | .bitOr | .bitXor => true
  | _ => false

theorem binaryOp_num (op : BinOp) (a b : F64) (s : State) (hop : isNumOp op = true) :
    Sem.binaryOp op (.num a) (.num b) s = .ok (.num (numberBinOp op a b)) s := by
  cases op <;> simp [isNumOp] at hop <;> rfl

open Lean Meta Simp in
/-- A closed `numberBinOp`/`isStrictlyEqual`/`toBoolean` term, reduced (the kernel checks the `rfl`). -/
simproc numEval (numberBinOp _ _ _) := fun e => do
  if e.hasFVar || e.hasMVar then return .continue
  let r ← withTransparency .all <| reduce e
  if r == e then return .continue
  return .done { expr := r, proof? := some (← mkExpectedTypeHint (← mkEqRefl r) (← mkEq e r)) }

open Lean Meta Simp in
simproc strictEqEval (isStrictlyEqual _ _) := fun e => do
  if e.hasFVar || e.hasMVar then return .continue
  let r ← withTransparency .all <| reduce e
  unless r.isConstOf ``Bool.true || r.isConstOf ``Bool.false do return .continue
  return .done { expr := r, proof? := some (← mkExpectedTypeHint (← mkEqRefl r) (← mkEq e r)) }


/-- A record of a body's state: the function's own one, or the caller's. -/
theorem bodyState_envEntry (s : State) (fo : ObjId) (d : FuncData) (t : Value) (args : Array Value) (e : EnvId) :
    (bodyState s fo d t args).envEntry e = if e = s.envs.size then .func
      (FDI.fdiMap d.code.info.fdi.paramNames args d.code.info.fdi.varNames (FDI.lexDecls d))
      (some d.env) .initialized t fo .undefined else s.envEntry e := by
  split
  · next h => subst h; exact bodyState_envEntry_self s fo d t args
  · next h =>
    by_cases hl : e < s.envs.size
    · exact bodyState_envEntry_lt s fo d t args e hl
    · have hge : s.envs.size ≤ e := Nat.le_of_not_lt hl
      have hgt : s.envs.size < e := Nat.lt_of_le_of_ne hge (fun h' => h h'.symm)
      have h1 : (bodyState s fo d t args).envs.size ≤ e := by rw [bodyState_envs_size]; exact hgt
      simp [State.envEntry, Array.getElem?_eq_none h1, Array.getElem?_eq_none hge]

/-- A record after an update: the updated one, or as it was. -/
theorem setEnv_envEntry (s : State) (e : EnvId) (ev : Env) (i : EnvId) :
    (s.setEnv e ev).envEntry i = if e = i ∧ i < s.envs.size then ev else s.envEntry i := by
  split
  · next h => obtain ⟨rfl, hl⟩ := h; exact State.setEnv_envEntry_self s e ev hl
  · next h =>
    by_cases he : e = i
    · subst he
      have hl : ¬ e < s.envs.size := fun hl => h ⟨rfl, hl⟩
      have hge : s.envs.size ≤ e := Nat.le_of_not_lt hl
      have hge' : (s.envs.modify e fun _ => ev).size ≤ e := by simpa using hge
      simp [State.envEntry, State.setEnv, Array.getElem?_eq_none hge', Array.getElem?_eq_none hge]
    · exact setEnv_envEntry_ne s e ev i he


/-! ## The simp set -/

attribute [js_simp] DeclsWP List.toList_toArray Scope.lookup_succ Scope.resolve Scope.lookup GetsC SetsC PutsC setEnv_envEntry Env.withBindings bodyState_envEntry FDI.fdiMap FDI.createParam FDI.bindParam FDI.createVar FDI.createLex List.range_succ List.range_zero List.nil_append List.cons_append List.foldl_cons List.foldl_nil List.foldl_append List.size_toArray List.length_cons List.length_nil Std.HashMap.getElem?_modify Std.HashMap.getElem?_insert Std.HashMap.getElem?_empty Std.HashMap.contains_eq_isSome_getElem? Option.isSome_some Option.isSome_none State.setEnv_envs_size State.setEnv_fuel setEnv_heap setEnv_objEntry bodyState_envs_size bodyState_fuel bodyState_objEntry bodyState_heap State.setProp_envs State.setProp_fuel State.setProp_size Option.map_some Option.map_none Bool.false_eq_true toBoolean litValue retVal Compl.updateEmpty Option.orElse HOrElse.hOrElse OrElse.orElse Bool.not_false Bool.not_true Bool.true_and Bool.false_and Bool.and_true Bool.or_false Bool.false_or Bool.true_or Bool.or_true Bool.and_false Nat.lt_add_one and_true true_and lit_getElem?_zero lit_getElem?_succ lit_getElem!_zero lit_getElem!_succ Option.getD_some List.contains_toArray List.contains_cons List.contains_nil
attribute [js_simp] jsstrBeq jsstrEq numEval strictEqEval PropKey.str.injEq

/-- `declLike?` by constructor, and through an `if` (so that a hypothesis about `declLike? (s.envEntry e)` applies,
instead of a `match` on an unknown record). -/
@[js_simp] theorem declLike_decl (b : HashMap JSStr Binding) (o : Option EnvId) :
    Scope.declLike? (.decl b o) = some (b, o) := rfl
@[js_simp] theorem declLike_func (b : HashMap JSStr Binding) (o : Option EnvId) (ts : ThisStatus) (tv : Value)
    (f : ObjId) (nt : Value) : Scope.declLike? (.func b o ts tv f nt) = some (b, o) := rfl
@[js_simp] theorem declLike_ite (c : Prop) [Decidable c] (a b : Env) :
    Scope.declLike? (if c then a else b) = if c then Scope.declLike? a else Scope.declLike? b := by
  split <;> rfl

/-- Normalizing a goal after a step: the generated denotations' bookkeeping, the states' reads, literal names,
and the given facts (the caller's state). -/
syntax "js_norm" ("[" Lean.Parser.Tactic.simpArg,* "]")? : tactic
macro_rules
  | `(tactic| js_norm) => `(tactic| js_norm [])
  | `(tactic| js_norm [$xs,*]) => `(tactic| simp only [js_simp, ↓reduceIte, ↓reduceDIte, $xs,*])

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ}

/-- A statement list's first statement (the rest stays folded, so normalization does not walk it). -/
theorem StmtsWP_cons {n : Nat} {ctx : Ctx} {c : Sem.CStmt} {cs : List Sem.CStmt} {v : Option Value} {h : σ}
    {s : State} {Q : Compl → State → σ → Prop} :
    StmtsWP eng answer n ctx (c :: cs) v h s Q = WP eng answer n h (c ctx) s fun r w h1 => match r with
      | .normal rv => StmtsWP eng answer n ctx cs (rv <|> v) h1 w Q
      | r => Q (r.updateEmpty v) w h1 := rfl

theorem StmtsWP_nil {n : Nat} {ctx : Ctx} {v : Option Value} {h : σ} {s : State} {Q : Compl → State → σ → Prop} :
    StmtsWP eng answer n ctx [] v h s Q = Q (.normal v) s h := rfl

end

/-- One step: the rule for the computation's head symbol. -/
syntax "js_step" : tactic
macro_rules
  | `(tactic| js_step) => `(tactic| first
      | apply wp_stmts (by simp [depth]; omega)
      | rw [StmtsWP_cons]
      | rw [StmtsWP_nil]
      | apply wp_varDecl
      | apply wp_declVarC (by simp [depth]; omega)
      | apply wp_assignIdentC (by simp [depth]; omega)
      | apply wp_assignMemberC
      | apply wp_getMemberC
      | apply wp_identC (by simp [depth]; omega)
      | apply wp_ret (by simp_all [FDI.fdiCtx, Sem.inner])
      | apply wp_exprStmt
      | apply wp_or
      | apply wp_and
      | apply wp_cond
      | apply wp_binary
      | apply wp_lit
      | apply wp_seq
      | apply wp_sne
      | apply wp_ite)

open Lean Elab Tactic in
/-- A case split on a condition whose outcome is unknown: only when the goal itself is an `if`. -/
elab "js_split" : tactic => do
  let t ← instantiateMVars (← getMainTarget)
  unless t.isAppOfArity ``ite 5 do throwError "js_split: the goal is not an if"
  let c ← Term.exprToSyntax (t.getArg! 1)
  evalTactic (← `(tactic| by_cases hjs : $c <;>
    (try simp only [Bool.not_eq_true, Bool.false_eq_true, Bool.true_eq_false] at hjs) <;>
    simp only [hjs, ↓reduceIte, Bool.not_eq_true]))

/-- Steps and normalization until neither applies. -/
syntax "js" ("[" Lean.Parser.Tactic.simpArg,* "]")? : tactic
macro_rules
  | `(tactic| js) => `(tactic| js [])
  | `(tactic| js [$xs,*]) => `(tactic| repeat' (first | js_step | js_norm [*, $xs,*] | js_split))

end Logic
