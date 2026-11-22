import JSProofs.Logic
import JSProofs.Scope

/-!
# The program logic's rules for the generated denotations (`ES.Sem`; zippy docs/react-proofs.md)

One backward rule per combinator `leanjs compile --defs` emits: a goal `WP … (Sem.X … ctx) s Q` becomes goals about
the parts, so a function body's proof follows its syntax. Identifiers are read by computing `Scope.lookup`/`resolve`
on the state's records.
-/

open ES ES.M HostRuns
open Std (HashMap)

namespace Logic

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ}

/-- **A loop iteration**: on to `next` (`inl`) or done (`inr`). -/
theorem wpr_loopRes {τ α : Type} {n : Nat} {h : σ} (next : τ → State → Res α) {r : Res (τ ⊕ α)}
    {Q : α → State → σ → Prop}
    (hw : WPR eng answer n h r fun x w h1 => match x with
      | .inl st => WPR eng answer n h1 (next st w) Q
      | .inr a => Q a w h1) :
    WPR eng answer n h (M.loopRes next r) Q := by
  rw [loopRes_eq_bindRes]
  apply wpr_bind
  obtain ⟨x, w, h1, k, hr, q⟩ := hw
  refine ⟨x, w, h1, k, hr, ?_⟩
  cases x with
  | inl st => exact q
  | inr a => exact wpr_ok q

/-! ## Expressions -/

theorem wp_lit {n : Nat} {h : σ} {l : Lit} {ctx : Ctx} {s : State} {Q : Value → State → σ → Prop}
    (hq : Q (litValue l) s h) : WP eng answer n h (Sem.lit l ctx) s Q := wp_of_eq rfl hq

/-- **An identifier** that `Scope.lookup` finds in the context's scope chain. -/
theorem wp_ident {n : Nat} {h : σ} {x : JSStr} {ctx : Ctx} {s : State} {Q : Value → State → σ → Prop}
    (k : Nat) {v : Value} (hl : Scope.lookup s k ctx.lex x = some v) (hk : k ≤ s.fuel) (hq : Q v s h) :
    WP eng answer n h (Sem.ident x ctx) s Q :=
  wp_of_eq (Scope.identValue_of_lookup s k ctx.lex x ctx.strict v hl hk) hq

theorem wp_binary {n : Nat} {h : σ} {op : BinOp} {l r : Sem.CExpr} {ctx : Ctx} {s : State}
    {Q : Value → State → σ → Prop}
    (hw : WP eng answer n h (l ctx) s fun lv w1 h1 =>
      WP eng answer n h1 (r ctx) w1 fun rv w2 h2 => WP eng answer n h2 (Sem.binaryOp op lv rv) w2 Q) :
    WP eng answer n h (Sem.binary op l r ctx) s Q := by
  show WP eng answer n h (l ctx >>= fun lv => r ctx >>= fun rv => Sem.binaryOp op lv rv) s Q
  exact wp_bind (wp_mono hw fun _ _ _ hr => wp_bind hr)

theorem wp_seq {n : Nat} {h : σ} {a b : Value} {s : State} {Q : Value → State → σ → Prop}
    (hq : Q (.bool (isStrictlyEqual a b)) s h) : WP eng answer n h (Sem.binaryOp .seq a b) s Q :=
  wp_of_eq rfl hq

theorem wp_cond {n : Nat} {h : σ} {t c a : Sem.CExpr} {ctx : Ctx} {s : State} {Q : Value → State → σ → Prop}
    (hw : WP eng answer n h (t ctx) s fun tv w h1 =>
      WP eng answer n h1 (if toBoolean tv then c ctx else a ctx) w Q) :
    WP eng answer n h (Sem.cond t c a ctx) s Q := by
  show WP eng answer n h (t ctx >>= fun tv => if toBoolean tv then c ctx else a ctx) s Q
  exact wp_bind hw

/-- `typeof` of a primitive. -/
theorem wp_typeOf_prim {n : Nat} {h : σ} {v : Value} {s : State} {Q : JSStr → State → σ → Prop}
    (hv : ∀ o, v ≠ .obj o) {t : JSStr} (ht : (match v with
      | .undefined => some "undefined" | .null => some "object" | .bool _ => some "boolean"
      | .num _ => some "number" | .str _ => some "string" | .sym _ => some "symbol" | .bigint _ => some "bigint"
      | .obj _ => none) = some t) (hq : Q t s h) :
    WP eng answer n h (typeOf v) s Q := by
  apply wp_of_eq _ hq
  cases v <;> simp_all [typeOf] <;> (try subst ht) <;> rfl

/-- **`typeof x`** of a variable that `Scope.resolve` finds, bound and initialized. -/
theorem wp_typeof_ident {n : Nat} {h : σ} {x : JSStr} {ctx : Ctx} {s : State} {Q : Value → State → σ → Prop}
    (k : Nat) {e : EnvId} (hr : Scope.resolve s k ctx.lex x = some e) (hk : k ≤ s.fuel) (he : e < s.envs.size)
    {bm : HashMap JSStr Binding} {o : Option EnvId} (hd : Scope.declLike? (s.envEntry e) = some (bm, o))
    {bd : Binding} {v : Value} (hb : bm[x]? = some bd) (hv : bd.value = some v)
    (hw : WP eng answer n h (typeOf v) s fun t w h1 => Q (.str t) w h1) :
    WP eng answer n h (Sem.typeofRef (Sem.identRef x) ctx) s Q := by
  have h1 : Sem.identRef x ctx s = .ok (.env (some e) x ctx.strict) s :=
    Scope.resolveBinding_of_resolve s k ctx.lex x ctx.strict e hr hk
  have h2 := Scope.getRefValue_env s e x ctx.strict he bm o hd bd v hb hv
  rw [wp_iff_wpr]
  simp only [Sem.typeofRef, M.bind_eq, M.bind_apply, h1, M.bindRes_ok, h2]
  exact wpr_bind (wp_mono hw fun t w h' q => wp_pure q)

/-! ## Statements -/

/-- **`return e`** outside async generators. -/
theorem wp_ret {n : Nat} {h : σ} {e : Sem.CExpr} {ctx : Ctx} {s : State} {Q : Compl → State → σ → Prop}
    (hag : (ctx.isAsync && ctx.isGen) = false)
    (hw : WP eng answer n h (e (Sem.inner ctx)) s fun v w h1 => Q (.ret v) w h1) :
    WP eng answer n h (Sem.ret (some e) ctx) s Q := by
  have hag' : ((Sem.inner ctx).isAsync && (Sem.inner ctx).isGen && true) = false := by
    simpa [Sem.inner] using hag
  rw [wp_iff_wpr]
  simp only [Sem.ret, M.bind_eq, M.bind_apply]
  apply wpr_bind
  refine wp_mono hw fun v w h1 q => ?_
  simp only [Option.isSome_some, hag', Bool.false_eq_true, ↓reduceIte]
  exact wp_of_eq rfl q

/-- What a statement list does from statement `cs` on, with the value so far `v`: each statement in turn while
they complete normally; another completion (`return`, `break`, …) ends the list. -/
def StmtsWP (eng : Engine) (answer : HostAnswer σ) (n : Nat) (ctx : Ctx) :
    List Sem.CStmt → Option Value → σ → State → (Compl → State → σ → Prop) → Prop
  | [], v, h, s, Q => Q (.normal v) s h
  | c :: cs, v, h, s, Q => WP eng answer n h (c ctx) s fun r w h1 => match r with
    | .normal rv => StmtsWP eng answer n ctx cs (rv <|> v) h1 w Q
    | r => Q (r.updateEmpty v) w h1

/-- `Sem.stmts`' loop body. -/
def stmtsBody (ss : Array Sem.CStmt) (ctx : Ctx) : Nat × Option Value → M ((Nat × Option Value) ⊕ Compl) :=
  fun (i, v) => do
    if h : i < ss.size then
      let r ← ss[i] ctx
      match r with
      | .normal rv => return .inl (i + 1, rv <|> v)
      | r => return .inr (r.updateEmpty v)
    else return .inr (.normal v)

theorem loop_stmts {n : Nat} (ss : Array Sem.CStmt) (ctx : Ctx) {Q : Compl → State → σ → Prop} :
    ∀ (j i b : Nat) (v : Option Value) (h : σ) (s : State), i + j = ss.size → j + 1 ≤ b →
      StmtsWP eng answer n ctx (ss.toList.drop i) v h s Q →
      WPR eng answer n h (M.loop (stmtsBody ss ctx) b (i, v) s) Q := by
  intro j
  induction j with
  | zero =>
    intro i b v h s hij hb hw
    obtain ⟨b, rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
    have hd : ss.toList.drop i = [] := by simp; omega
    rw [hd] at hw
    simp only [M.loop, stmtsBody, show ¬ i < ss.size by omega, ↓reduceDIte]
    exact wpr_loopRes _ (wpr_ok hw)
  | succ j ih =>
    intro i b v h s hij hb hw
    obtain ⟨b, rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
    have hi : i < ss.size := by omega
    have hd : ss.toList.drop i = ss[i] :: ss.toList.drop (i + 1) := by
      rw [List.drop_eq_getElem_cons (by simp; omega)]
      simp
    rw [hd] at hw
    simp only [M.loop, stmtsBody, hi, ↓reduceDIte]
    apply wpr_loopRes
    apply wpr_bind
    refine wp_mono hw fun r w h1 q => ?_
    cases r with
    | normal rv => exact wp_pure (ih (i + 1) b (rv <|> v) h1 w (by omega) (by omega) q)
    | brk l rv => exact wp_pure q
    | cont l rv => exact wp_pure q
    | ret rv => exact wp_pure q

/-- **A statement list**, the statements one by one (`StmtsWP`), with fuel for its iterations. -/
theorem wp_stmts {n : Nat} {h : σ} {ss : Array Sem.CStmt} {ctx : Ctx} {s : State} {Q : Compl → State → σ → Prop}
    (hf : ss.size + 1 ≤ s.fuel) (hw : StmtsWP eng answer n ctx ss.toList none h s Q) :
    WP eng answer n h (Sem.stmts ss ctx) s Q :=
  loop_stmts ss ctx ss.size 0 s.fuel none h s (by omega) hf (by simpa using hw)

end

end Logic
