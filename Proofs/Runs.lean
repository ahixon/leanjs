import Proofs.Script

/-!
# Statement lists, statement by statement

`RunsTo eng r b w'`: `r`, with its requests answered by the driver, ends in `b` and state `w'` —
whatever continuation it is bound to (`M.bindRes k r` is driven as `k b w'` is). Statements then compose:
`stmts_run` takes one `RunsTo` fact per statement (`StmtsRun`) to the whole list's completion, and a
script's value is what its statements run to (`script_runs`).
-/

open ES

namespace Runs

theorem bindRes_assoc {α β γ : Type} (f : α → M β) (k : β → M γ) :
    ∀ r : Res α, M.bindRes k (M.bindRes f r) = M.bindRes (fun a s => M.bindRes k (f a s)) r := by
  intro r
  induction r with
  | ok a s => rfl
  | err e s => rfl
  | halt m s => rfl
  | req r s k' ih => simp only [M.bindRes]; congr 1; funext o s'; exact ih o s'

theorem loopRes_eq {σ α : Type} (next : σ → State → Res α) :
    ∀ r : Res (σ ⊕ α), M.loopRes next r =
      M.bindRes (fun x s => match x with | .inl st => next st s | .inr a => .ok a s) r := by
  intro r
  induction r with
  | ok x s => cases x <;> rfl
  | err e s => rfl
  | halt m s => rfl
  | req r s k ih => simp only [M.loopRes, M.bindRes]; congr 1; funext o s'; exact ih o s'

/-- `r`, its requests answered, ends in `b` and `w'`, under any continuation. -/
def RunsTo {β : Type} (eng : Engine) (r : Res β) (b : β) (w' : State) : Prop :=
  ∀ (α : Type) (k : β → M α) (v : α) (s' : State), Script.DrivesTo eng (k b w') v s' →
    Script.DrivesTo eng (M.bindRes k r) v s'

theorem runsTo_ok {β : Type} (eng : Engine) (b : β) (w : State) : RunsTo eng (.ok b w) b w :=
  fun _ _ _ _ h => h

theorem runsTo_bind {α β : Type} (eng : Engine) (r : Res α) (f : α → M β) (a : α) (b : β) (w1 w2 : State)
    (hr : RunsTo eng r a w1) (hf : RunsTo eng (f a w1) b w2) : RunsTo eng (M.bindRes f r) b w2 := by
  intro γ k v s' h
  rw [bindRes_assoc]
  exact hr γ _ v s' (hf γ k v s' h)

/-- A call request the engine answers with `x`, then the continuation. -/
theorem runsTo_call {β : Type} (eng : Engine) (f t : Value) (args : Array Value) (w : State)
    (K : Outcome → State → Res β) (x : Value) (w1 : State) (b : β) (w' : State)
    (h : callImpl eng f t args w = .ok x w1) (hk : RunsTo eng (K (.normal x) w1) b w') :
    RunsTo eng (.req (.call f t args) w K) b w' := by
  intro α k v s' hd
  show Script.DrivesTo eng (.req (.call f t args) w (fun o s => M.bindRes k (K o s))) v s'
  exact Script.drivesTo_call eng f t args w _ x w1 v s' h (hk α k v s' hd)

/-- A request for one call whose continuation finishes with `b`. -/
theorem runsTo_req1 {β : Type} (eng : Engine) (f t : Value) (args : Array Value) (w : State)
    (K : Outcome → State → Res β) (x : Value) (w1 : State) (b : β) (w2 : State)
    (h : callImpl eng f t args w = .ok x w1) (hk : K (.normal x) w1 = .ok b w2) :
    RunsTo eng (.req (.call f t args) w K) b w2 :=
  runsTo_call eng f t args w K x w1 b w2 h (by rw [hk]; exact runsTo_ok eng b w2)

/-- A statement list, run statement by statement: each completes normally; the list's value is the last
statement value (UpdateEmpty). -/
inductive StmtsRun (eng : Engine) (c : Ctx) : List Sem.CStmt → State → Option Value → Option Value → State → Prop
  | nil (w : State) (acc : Option Value) : StmtsRun eng c [] w acc acc w
  | cons (st : Sem.CStmt) (ss : List Sem.CStmt) (w w1 w' : State) (rv acc out : Option Value)
      (h : RunsTo eng (st c w) (.normal rv) w1) (rest : StmtsRun eng c ss w1 (rv <|> acc) out w') :
      StmtsRun eng c (st :: ss) w acc out w'

theorem loop_run (eng : Engine) (c : Ctx) (ss : Array Sem.CStmt)
    (body : Nat × Option Value → M ((Nat × Option Value) ⊕ Compl))
    (hstep : ∀ j acc w rv w1 (h : j < ss.size), RunsTo eng (ss[j] c w) (.normal rv) w1 →
      RunsTo eng (body (j, acc) w) (.inl (j + 1, rv <|> acc)) w1)
    (hend : ∀ j acc w, ss.size ≤ j → body (j, acc) w = .ok (.inr (.normal acc)) w) :
    ∀ (n j : Nat) (acc out : Option Value) (w w' : State), StmtsRun eng c (ss.toList.drop j) w acc out w' →
      ss.size - j + 1 ≤ n → RunsTo eng (M.loop body n (j, acc) w) (Compl.normal out) w' := by
  intro n
  induction n with
  | zero => intro j acc out w w' _ hn; omega
  | succ n ih =>
    intro j acc out w w' hr hn
    show RunsTo eng (M.loopRes (M.loop body n) (body (j, acc) w)) _ w'
    rw [loopRes_eq]
    by_cases hj : j < ss.size
    · rw [List.drop_eq_getElem_cons (by simpa using hj)] at hr
      cases hr with
      | cons _ _ _ w1 _ rv _ _ h rest =>
        refine runsTo_bind eng _ _ _ _ _ _ (hstep j acc w rv w1 hj (by simpa using h)) ?_
        exact ih (j + 1) _ out w1 w' rest (by omega)
    · rw [hend j acc w (by omega)]
      rw [List.drop_eq_nil_of_le (by simpa using Nat.le_of_not_lt hj)] at hr
      cases hr with
      | nil => exact runsTo_ok eng _ _

/-- **A statement list** whose statements run, one after the other, to normal completions: runs to the
list's completion, given one step of fuel per statement (and one more). -/
theorem stmts_run (eng : Engine) (c : Ctx) (ss : Array Sem.CStmt) (w : State) (out : Option Value) (w' : State)
    (h : StmtsRun eng c ss.toList w none out w') (hf : ss.size + 1 ≤ w.fuel) :
    RunsTo eng (Sem.stmts ss c w) (.normal out) w' := by
  simp only [Sem.stmts, M.repeatFrom]
  refine loop_run eng c ss _ (fun j acc w rv w1 hj hr => ?_) (fun j acc w hj => ?_) w.fuel 0 none out w w'
    (by simpa using h) (by omega)
  · simp only [hj, ↓reduceDIte, M.bind_eq, M.bind_apply]
    refine runsTo_bind eng _ _ _ _ _ _ hr ?_
    exact runsTo_ok eng _ _
  · simp [Nat.not_lt.mpr hj, pure, M.pure]

/-- A function declaration statement (its function instantiated by GlobalDeclarationInstantiation)
does nothing. -/
theorem runs_funDecl (eng : Engine) (f : Func) (c : Ctx) (w : State) (hann : c.annexB = funcIds #[]) :
    RunsTo eng (Sem.funDecl f c w) (.normal none) w := by
  have hann0 : (funcIds #[]).contains f.info.id = false := by simp [funcIds]
  simp only [Sem.funDecl, hann, hann0]
  exact runsTo_ok eng _ _

/-- **A script's value** from its statements run: as `Script.script_value`, with the body given as
statements that run to `.normal (some v)`. -/
theorem script_runs (eng : Engine) (body : Res Compl) (v : Value) (s' : State)
    (h : RunsTo eng body (.normal (some v)) s') : Script.DrivesTo eng (M.bindRes Script.complValue body) v s' :=
  h Value Script.complValue v s' (Script.drivesTo_ok eng v s')

end Runs
