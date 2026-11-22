import JSProofs.Loops3

/-!
# `switch` statements (zippy docs/react-proofs.md)

React's `computeExpirationTime`, `beginWork`, `completeWork`, the commit phase: `switch (x) { case …: … }` with no
lexical declarations in its block. The case tests are tried in order (`SelWP`); from the first case whose value is
strictly equal (or the `default`), the bodies run in order until one does not complete normally (`BodiesWP`).
First: the interpreter's array folds as list folds.
-/

open ES ES.M HostRuns
open Std (HashMap)

namespace Logic

/-- The loop of `M.foldArr` from index `i`, `k` elements left: the list fold of the rest. -/
theorem foldArr_loop {α β : Type} (xs : Array α) (f : β → α → M β) :
    ∀ (k i : Nat) (acc : β), i + k = xs.size → ∀ s,
      M.loop (fun (st : Nat × β) =>
          if h : st.1 < xs.size then
            fun s => M.bindRes (fun acc' s => .ok (.inl (st.1 + 1, acc')) s) (f st.2 xs[st.1] s)
          else M.pure (.inr st.2)) (k + 1) (i, acc) s =
        (xs.toList.drop i).foldlM f acc s := by
  intro k
  induction k with
  | zero =>
    intro i acc hik s
    have hi : ¬ i < xs.size := by omega
    have hd : xs.toList.drop i = [] := by simp; omega
    simp [M.loop, M.loopRes, hi, hd, M.pure]; rfl
  | succ k ih =>
    intro i acc hik s
    have hi : i < xs.size := by omega
    have hd : xs.toList.drop i = xs[i] :: xs.toList.drop (i + 1) := by
      rw [List.drop_eq_getElem_cons (by simpa using hi)]; simp
    rw [hd, List.foldlM_cons]
    simp only [M.loop, hi, ↓reduceDIte]
    show M.loopRes _ (M.bindRes _ (f acc xs[i] s)) = M.bindRes _ (f acc xs[i] s)
    generalize f acc xs[i] s = r
    induction r with
    | ok a w => simp only [M.bindRes, M.loopRes]; exact ih (i + 1) a (by omega) w
    | err e w => rfl
    | halt m w => rfl
    | req q w k' ihk => simp only [M.bindRes, M.loopRes]; congr 1; funext o w'; exact ihk o w'

/-- **`M.foldArr` is the list fold.** -/
theorem foldArr_eq {α β : Type} (xs : Array α) (init : β) (f : β → α → M β) :
    M.foldArr xs init f = xs.toList.foldlM f init := by
  funext s
  unfold M.foldArr
  simpa using foldArr_loop xs f xs.size 0 init (by omega) s

end Logic

namespace Logic

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ}

/-- The case tests from `i` on: the first whose value is strictly equal to `sv` (its index), or none. -/
def SelWP (eng : Engine) (answer : HostAnswer σ) (n : Nat) (sv : Value) (cctx : Ctx) :
    List Sem.CaseD → Nat → σ → State → (Option Nat → State → σ → Prop) → Prop
  | [], _, h, s, K => K none s h
  | c :: cs, i, h, s, K => match c.test with
    | none => SelWP eng answer n sv cctx cs (i + 1) h s K
    | some t => WP eng answer n h (t cctx) s fun cv w h1 =>
      if isStrictlyEqual sv cv then K (some i) w h1 else SelWP eng answer n sv cctx cs (i + 1) h1 w K

/-- The case bodies in order, while they complete normally. -/
def BodiesWP (eng : Engine) (answer : HostAnswer σ) (n : Nat) (cctx : Ctx) :
    List Sem.CaseD → Compl → σ → State → (Compl → State → σ → Prop) → Prop
  | [], acc, h, s, K => K acc s h
  | c :: cs, .normal v, h, s, K => WP eng answer n h (c.body cctx) s fun r w h1 =>
    BodiesWP eng answer n cctx cs (r.updateEmpty v) h1 w K
  | _ :: _, acc, h, s, K => K acc s h

/-- The selection fold, once a case is found: it stays found. -/
theorem selFold_found (cases : Array Sem.CaseD) (cctx : Ctx) (sv : Value) (i : Nat) :
    ∀ (l : List Nat) (s : State), List.foldlM (m := M) (fun (found : Option Nat) j => do
        if found.isSome then return found
        match cases[j]!.test with
        | some t =>
          let cv ← t cctx
          if isStrictlyEqual sv cv then return some j else return none
        | none => return none) (some i) l s = Res.ok (some i) s := by
  intro l
  induction l with
  | nil => intro s; rfl
  | cons j l ih => intro s; simp only [List.foldlM_cons, Option.isSome_some, ↓reduceIte]; exact ih s

/-- The body fold, once a body did not complete normally: the rest is skipped. -/
theorem bodyFold_stop (cases : Array Sem.CaseD) (cctx : Ctx) (acc : Compl) (hacc : ∀ v, acc ≠ .normal v) :
    ∀ (l : List Nat) (s : State), List.foldlM (m := M) (fun (acc : Compl) i => do
        match acc with
        | .normal v =>
          let r ← cases[i]!.body cctx
          Pure.pure (r.updateEmpty v)
        | acc => Pure.pure acc) acc l s = Res.ok acc s := by
  intro l
  induction l with
  | nil => intro s; rfl
  | cons j l ih =>
    intro s
    simp only [List.foldlM_cons]
    cases acc with
    | normal v => exact absurd rfl (hacc v)
    | _ => exact ih s

end

end Logic

namespace Logic

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ}

theorem drop_cons_getElem! {α : Type} [Inhabited α] (xs : Array α) (j : Nat) {c : α} {cs : List α}
    (hd : xs.toList.drop j = c :: cs) : xs[j]! = c ∧ xs.toList.drop (j + 1) = cs := by
  have hj : j < xs.size := by
    have := congrArg List.length hd; simp at this; omega
  have h1 : xs.toList.drop j = xs[j] :: xs.toList.drop (j + 1) := by
    rw [List.drop_eq_getElem_cons (by simpa using hj)]; simp
  rw [h1] at hd
  simp only [List.cons.injEq] at hd
  exact ⟨by simp [getElem!_pos, hj, hd.1], hd.2⟩

/-- **The selection fold** (over the case indices) as `SelWP`. -/
theorem selFold_wp {n : Nat} (cases : Array Sem.CaseD) (cctx : Ctx) (sv : Value) (f : Option Nat → Nat → M (Option Nat))
    (hfF : ∀ i j, f (some i) j = Pure.pure (some i))
    (hfN : ∀ j, f none j = match cases[j]!.test with
      | some t => (t cctx).bind fun cv => if isStrictlyEqual sv cv then Pure.pure (some j) else Pure.pure none
      | none => Pure.pure none) :
    ∀ (cs : List Sem.CaseD) (j : Nat), cases.toList.drop j = cs → ∀ (h : σ) (s : State) (K : Option Nat → State → σ → Prop),
      SelWP eng answer n sv cctx cs j h s K → WP eng answer n h (List.foldlM f none (List.range' j cs.length)) s K := by
  have found : ∀ (i : Nat) (l : List Nat) (s : State), List.foldlM f (some i) l s = Res.ok (some i) s := by
    intro i l; induction l with
    | nil => intro s; rfl
    | cons j l ih => intro s; simp only [List.foldlM_cons, hfF]; exact ih s
  intro cs
  induction cs with
  | nil => intro j _ h s K hw; exact wp_of_eq rfl hw
  | cons c cs ih =>
    intro j hd h s K hw
    obtain ⟨hc, hd'⟩ := drop_cons_getElem! cases j hd
    simp only [List.length_cons, List.range'_succ, List.foldlM_cons]
    apply wp_bind
    rw [hfN j, hc]
    cases ht : c.test with
    | none =>
      simp only [SelWP, ht] at hw
      exact wp_of_eq rfl (ih (j + 1) hd' h s K hw)
    | some t =>
      simp only [SelWP, ht] at hw
      apply wp_bind
      refine wp_mono hw fun cv w h1 q => ?_
      cases hs : isStrictlyEqual sv cv
      · simp only [hs, Bool.false_eq_true, ↓reduceIte] at q ⊢
        exact wp_of_eq rfl (ih (j + 1) hd' h1 w K q)
      · simp only [hs, ↓reduceIte] at q ⊢
        exact wp_of_eq rfl (wp_of_eq (found j _ w) q)

/-- **The body fold** (from the selected case on) as `BodiesWP`. -/
theorem bodyFold_wp {n : Nat} (cases : Array Sem.CaseD) (cctx : Ctx) (g : Compl → Nat → M Compl)
    (hgN : ∀ v i, g (.normal v) i = (cases[i]!.body cctx).bind fun r => Pure.pure (r.updateEmpty v))
    (hgS : ∀ acc i, (∀ v, acc ≠ .normal v) → g acc i = Pure.pure acc) :
    ∀ (cs : List Sem.CaseD) (j : Nat), cases.toList.drop j = cs → ∀ (acc : Compl) (h : σ) (s : State)
      (K : Compl → State → σ → Prop),
      BodiesWP eng answer n cctx cs acc h s K → WP eng answer n h (List.foldlM g acc (List.range' j cs.length)) s K := by
  have stop : ∀ (acc : Compl), (∀ v, acc ≠ .normal v) → ∀ (l : List Nat) (s : State),
      List.foldlM g acc l s = Res.ok acc s := by
    intro acc hacc l; induction l with
    | nil => intro s; rfl
    | cons j l ih => intro s; simp only [List.foldlM_cons, hgS acc j hacc]; exact ih s
  intro cs
  induction cs with
  | nil => intro j _ acc h s K hw; exact wp_of_eq rfl hw
  | cons c cs ih =>
    intro j hd acc h s K hw
    obtain ⟨hc, hd'⟩ := drop_cons_getElem! cases j hd
    simp only [List.length_cons, List.range'_succ, List.foldlM_cons]
    apply wp_bind
    cases acc with
    | normal v =>
      simp only [BodiesWP] at hw
      rw [hgN v j, hc]
      apply wp_bind
      refine wp_mono hw fun r w h1 q => ?_
      exact wp_of_eq rfl (ih (j + 1) hd' _ h1 w K q)
    | _ =>
      simp only [BodiesWP] at hw
      rw [hgS _ j (by simp)]
      exact wp_of_eq rfl (wp_of_eq (stop _ (by simp) _ s) hw)

end

end Logic

namespace Logic

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ}

/-- The case block's context: its own (empty) record. -/
def caseCtx (ctx : Ctx) (w : State) : Ctx := { Sem.inner ctx with lex := w.envs.size }

/-- **`switch (disc) { … }`** without lexical declarations: the discriminant, a record for the block, the case
tests in order (`SelWP`), then the bodies from the selected case (or the `default`) on (`BodiesWP`). -/
theorem wp_switchC {n : Nat} {h : σ} {disc : Sem.CExpr} {decls : Array LexScoped} {cases : Array Sem.CaseD}
    {ctx : Ctx} {s : State} {Q : Compl → State → σ → Prop} (hdec : decls = #[])
    (hw : WP eng answer n h (disc (Sem.inner ctx)) s fun sv w h1 =>
      SelWP eng answer n sv (caseCtx ctx w) cases.toList 0 h1 (w.pushEnv (.decl {} (some (Sem.inner ctx).lex)))
        fun st w2 h2 => match st <|> cases.findIdx? (fun c => c.test.isNone) with
        | none => Q (Sem.breakToNormal (Compl.normal (some .undefined))) w2 h2
        | some i => BodiesWP eng answer n (caseCtx ctx w) (cases.toList.drop i) (.normal none) h2 w2
            fun r w3 h3 => Q (Sem.breakToNormal (r.updateEmpty (some .undefined))) w3 h3) :
    WP eng answer n h (Sem.switch disc decls cases ctx) s Q := by
  subst hdec
  rw [wp_iff_wpr]
  simp only [Sem.switch, M.bind_eq, M.bind_apply]
  apply wpr_bind
  refine wp_mono hw fun sv w h1 q => ?_
  rw [wp_iff_wpr]
  simp only [M.bind_apply, newDeclEnv_eq, M.bindRes_ok]
  have hb : ∀ e (c : Ctx) (u : State), blockDeclarationInstantiation #[] e c u = Res.ok () u := fun _ _ _ => rfl
  have hu : (usingKinds #[]).fst = false := rfl
  simp only [hb, M.bindRes_ok, hu, withDisposeScope, Bool.not_false, ↓reduceIte]
  rw [← wp_iff_wpr]
  rw [foldArr_eq]
  apply wp_bind
  have hl : (Array.range cases.size).toList = List.range' 0 cases.toList.length := by
    simp [Array.toList_range, List.range_eq_range']
  rw [hl]
  refine wp_mono (selFold_wp (eng := eng) (answer := answer) (n := n) cases (caseCtx ctx w) sv _ ?hF ?hN
    cases.toList 0 (by simp) h1 _ _ q) ?post
  case hF => intro i j; rfl
  case hN => intro j; rfl
  case post =>
  intro st w2 h2 q2
  revert q2
  cases hst : (st <|> Array.findIdx? (fun c => c.test.isNone) cases) with
  | none => intro q2; exact wp_of_eq rfl q2
  | some i =>
    intro q2
    dsimp only
    rw [foldArr_eq]
    have hl2 : ((Array.range cases.size).extract i cases.size).toList = List.range' i (cases.toList.drop i).length := by
      apply List.ext_getElem
      · simp
      · intro k h1 h2; simp at h1 h2 ⊢
    rw [hl2]
    apply wp_bind
    refine wp_mono (bodyFold_wp (eng := eng) (answer := answer) (n := n) cases (caseCtx ctx w) _ ?gN ?gS
      (cases.toList.drop i) i rfl _ h2 w2 _ q2) ?post2
    case gN => intro v j; rfl
    case gS => intro acc j hacc; cases acc with
      | normal v => exact absurd rfl (hacc v)
      | _ => rfl
    case post2 => intro r w3 h3 q3; exact wp_of_eq rfl q3

end

end Logic
attribute [js_simp] Logic.SelWP Logic.BodiesWP Logic.caseCtx
attribute [js_simp] Nat.zero_add List.drop_succ_cons List.drop_zero

namespace Logic

theorem pushEnv_envEntry (s : State) (e : Env) (i : EnvId) :
    (s.pushEnv e).envEntry i = if i = s.envs.size then e else s.envEntry i := by
  split
  · subst_vars; exact State.pushEnv_entry_new s e
  · rename_i hi
    simp [State.pushEnv, State.envEntry, Array.getElem?_push, hi]

attribute [js_simp] pushEnv_envEntry State.pushEnv_size State.pushEnv_objEntry State.pushEnv_heap_size
  State.pushEnv_fuel

/-- A new record pushed: framed by any footprint. -/
theorem frame_pushEnv {fp : Footprint} {s u : State} (hF : Frame fp s u) (e : Env) : Frame fp s (u.pushEnv e) := by
  exact {
    envs_le := by simp; have := hF.envs_le; omega
    heap_le := by simpa [State.pushEnv] using hF.heap_le
    env_agree := fun i hi => by
      rw [State.pushEnv_entry_lt _ _ _ (Nat.lt_of_lt_of_le hi hF.envs_le)]; exact hF.env_agree i hi
    obj_agree := fun o ho => by simpa [State.pushEnv, State.objEntry] using hF.obj_agree o ho
    env_eq := fun i hi hn => by
      rw [State.pushEnv_entry_lt _ _ _ (Nat.lt_of_lt_of_le hi hF.envs_le)]; exact hF.env_eq i hi hn
    obj_eq := fun o ho hn => by simpa [State.pushEnv, State.objEntry] using hF.obj_eq o ho hn
    realms_eq := by simpa [State.pushEnv] using hF.realms_eq
    jobs_prefix := by simpa [State.pushEnv] using hF.jobs_prefix
    jobs_eq := fun hj => by simpa [State.pushEnv] using hF.jobs_eq hj }

end Logic

namespace Logic
/-! Record indices one or two past the caller's (a call's record, a block's inside it). -/
@[js_simp] theorem idx_lt_add_one (a : Nat) : a < a + 1 := Nat.lt_succ_self a
@[js_simp] theorem idx_lt_add_two (a : Nat) : a < a + 1 + 1 := by omega
@[js_simp] theorem idx_succ_lt_add_two (a : Nat) : a + 1 < a + 1 + 1 := by omega
@[js_simp] theorem idx_eq_add_one (a : Nat) : (a = a + 1) = False := by simp
@[js_simp] theorem idx_eq_add_two (a : Nat) : (a = a + 1 + 1) = False := by simp; omega
@[js_simp] theorem idx_add_one_eq_add_two (a : Nat) : (a + 1 = a + 1 + 1) = False := by simp
@[js_simp] theorem idx_add_one_eq (a : Nat) : (a + 1 = a) = False := by simp
end Logic

namespace Logic

theorem binaryOp_add_num (a b : F64) (s : State) :
    Sem.binaryOp .add (.num a) (.num b) s = .ok (.num (numberBinOp .add a b)) s := by
  simp only [Sem.binaryOp, applyBinaryOp, M.bind_eq, M.bind_apply, toPrim_num, M.bindRes_ok, toNumeric_num]
  rfl

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ}

/-- **`a + b`** of two Numbers. -/
theorem wp_addNum {n : Nat} {h : σ} {a b : F64} {s : State} {Q : Value → State → σ → Prop}
    (hq : Q (.num (numberBinOp .add a b)) s h) : WP eng answer n h (Sem.binaryOp .add (.num a) (.num b)) s Q :=
  wp_of_eq (binaryOp_add_num a b s) hq

end

end Logic

namespace Logic

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ}

/-- **`obj.k(args)`**: the object, its method (a data property, own or inherited), the arguments, then the call
with the object as `this`. -/
theorem wp_callMemberC {n : Nat} {h : σ} {obj : Sem.CExpr} {k : JSStr} {as : Array Sem.ArgD} {name : CalleeDesc}
    {ctx : Ctx} {s : State} {Q : Value → State → σ → Prop}
    (hw : WP eng answer (n + 1) h (obj ctx) s fun bv w h1 => GetsC w bv k fun fv =>
      ArgsWP eng answer (n + 1) ctx as.toList #[] h1 w fun args w2 h2 =>
        CallableC w2 fv ∧ WP eng answer n h2 (callImpl eng fv bv args) w2 Q) :
    WP eng answer (n + 1) h (Sem.call (Sem.memberRef obj (.name k) false) (Sem.args as) false name ctx) s Q := by
  rw [wp_iff_wpr]
  simp only [Sem.call, Sem.memberRef, M.bind_eq, M.bind_apply]
  apply wpr_bind
  apply wpr_bind
  refine wp_mono hw fun bv w h1 q => ?_
  obtain ⟨o, m, hb, hc, hm, hna, q'⟩ := getsC_getsTo q
  subst hb
  simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  refine wp_of_eq (a := Ref.prop (.obj o) (.str k) ctx.strict none) rfl ?_
  rw [wp_iff_wpr]
  simp only [M.bind_apply, getRefValue_prop, Obj'.get_chain w _ _ m o hc hm hna, M.bindRes_ok, refThisValue]
  show WPR eng answer (n + 1) h1 (M.bindRes _ (M.pure (Value.obj o) w)) Q
  simp only [M.pure, M.bindRes_ok]
  apply wpr_bind
  refine wp_mono (wp_args q') fun args w2 h2 ⟨hcl, hq⟩ => ?_
  rw [wp_iff_wpr]
  simp only [M.bind_apply, isCallable_of hcl, M.bindRes_ok, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [← wp_iff_wpr]
  exact wp_call hq

end

end Logic

namespace Logic

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ}

/-- **`l: body`**: the body (seeing the label if it is a loop, `switch` or labelled statement); a `break l` out of
it completes normally. -/
theorem wp_labeled {n : Nat} {h : σ} {l : JSStr} {b : Bool} {body : Sem.CStmt} {ctx : Ctx} {s : State}
    {Q : Compl → State → σ → Prop}
    (hw : WP eng answer n h (body { ctx with labels := if b then ctx.labels.push l else #[] }) s fun r w h1 =>
      Q (match r with
        | .brk (some l') v => if l' == l then .normal (some (v.getD .undefined)) else r
        | r => r) w h1) :
    WP eng answer n h (Sem.labeled l b body ctx) s Q := by
  rw [wp_iff_wpr]
  simp only [Sem.labeled, M.bind_eq, M.bind_apply]
  apply wpr_bind
  refine wp_mono hw fun r w h1 q => ?_
  cases r with
  | brk l' v =>
    cases l' with
    | none => exact wp_of_eq rfl q
    | some l' =>
      cases hl : (l' == l) <;> simp only [hl] at q ⊢ <;> exact wp_of_eq rfl q
  | _ => exact wp_of_eq rfl q

/-- **`break l`**. -/
theorem wp_brk {n : Nat} {h : σ} {l : Option JSStr} {ctx : Ctx} {s : State} {Q : Compl → State → σ → Prop}
    (hq : Q (.brk l none) s h) : WP eng answer n h (Sem.brk l ctx) s Q := wp_of_eq rfl hq

end

end Logic
