import JSProofs.HostRuns
import JSProofs.FDI

/-!
# A program logic over the engine's runs (zippy docs/react-proofs.md)

`WP eng answer n h x s Q`: the computation `x`, run from state `s` with calls driven `n` levels deep and host
requests answered by `answer` from host state `h`, ends normally in a value and state satisfying `Q` (with the host
state then). Defined by `HR`, so a `WP` fact is a fact about what the embedder's loop computes (`hr_sound`).

The rules are backward: each reduces a goal about a composite computation to goals about its parts, so a proof
walks a function body statement by statement (`wp_bind`, `wp_call`, the `Sem` combinators' rules), and a callee's
spec, proved once, is used at every call site (`wp_call`).
-/

open ES HostRuns

namespace Logic

section
variable (eng : Engine) {σ : Type} (answer : HostAnswer σ)

/-- **Weakest precondition** (total, normal termination): `x` from `s` ends in `.ok b w` with host state `h'`, all
host requests answered, and `Q b w h'`. -/
def WP {α : Type} (n : Nat) (h : σ) (x : M α) (s : State) (Q : α → State → σ → Prop) : Prop :=
  ∃ b w h' k, HR eng answer n h (x s) b w h' k ∧ Q b w h'

/-- The same, for a computation's result already in hand (a `Res`). -/
def WPR {α : Type} (n : Nat) (h : σ) (r : Res α) (Q : α → State → σ → Prop) : Prop :=
  ∃ b w h' k, HR eng answer n h r b w h' k ∧ Q b w h'

variable {eng answer}

theorem wp_iff_wpr {α : Type} {n : Nat} {h : σ} {x : M α} {s : State} {Q : α → State → σ → Prop} :
    WP eng answer n h x s Q ↔ WPR eng answer n h (x s) Q := Iff.rfl

/-- Consequence. -/
theorem wp_mono {α : Type} {n : Nat} {h : σ} {x : M α} {s : State} {Q Q' : α → State → σ → Prop}
    (hw : WP eng answer n h x s Q) (hq : ∀ b w h', Q b w h' → Q' b w h') : WP eng answer n h x s Q' := by
  obtain ⟨b, w, h', k, hr, q⟩ := hw
  exact ⟨b, w, h', k, hr, hq b w h' q⟩

/-- A computation that returns at once. -/
theorem wpr_ok {α : Type} {n : Nat} {h : σ} {a : α} {w : State} {Q : α → State → σ → Prop} (hq : Q a w h) :
    WPR eng answer n h (.ok a w) Q := ⟨a, w, h, 0, .ok n h a w, hq⟩

theorem wp_of_eq {α : Type} {n : Nat} {h : σ} {x : M α} {s : State} {a : α} {w : State}
    {Q : α → State → σ → Prop} (he : x s = .ok a w) (hq : Q a w h) : WP eng answer n h x s Q := by
  rw [wp_iff_wpr, he]; exact wpr_ok hq

theorem wp_pure {α : Type} {n : Nat} {h : σ} {a : α} {s : State} {Q : α → State → σ → Prop} (hq : Q a s h) :
    WP eng answer n h (pure a) s Q := wp_of_eq rfl hq

/-- **Sequencing.** -/
theorem wpr_bind {α β : Type} {n : Nat} {h : σ} {r : Res α} {g : α → M β} {Q : β → State → σ → Prop}
    (hw : WPR eng answer n h r fun a w1 h1 => WP eng answer n h1 (g a) w1 Q) :
    WPR eng answer n h (M.bindRes g r) Q := by
  obtain ⟨a, w1, h1, k1, hr, b, w2, h2, k2, hg, q⟩ := hw
  exact ⟨b, w2, h2, k1 + k2, hr_bind eng answer g hr hg, q⟩

theorem wp_bind {α β : Type} {n : Nat} {h : σ} {x : M α} {g : α → M β} {s : State} {Q : β → State → σ → Prop}
    (hw : WP eng answer n h x s fun a w1 h1 => WP eng answer n h1 (g a) w1 Q) :
    WP eng answer n h (x >>= g) s Q := wpr_bind hw

/-- **A call**: the callee, driven one level down, then the caller's continuation with its value. -/
theorem wp_call {n : Nat} {h : σ} {f t : Value} {args : Array Value} {s : State} {Q : Value → State → σ → Prop}
    (hc : WP eng answer n h (callImpl eng f t args) s Q) : WP eng answer (n + 1) h (ES.call f t args) s Q := by
  obtain ⟨x, w1, h1, k1, hr, q⟩ := hc
  exact ⟨x, w1, h1, k1 + 0, .call n h f t args s _ x w1 h1 k1 x w1 h1 0 hr (.ok (n + 1) h1 x w1), q⟩

/-- **A host request** at this level, answered by the embedder. -/
theorem wpr_host {α : Type} {n : Nat} {h : σ} {nm : String} {t : Value} {a : Array Value} {s : State}
    {K : Outcome → State → Res α} {Q : α → State → σ → Prop}
    (hk : WPR eng answer n (answer h nm t a s).1 (K (answer h nm t a s).2.1 (answer h nm t a s).2.2) Q) :
    WPR eng answer n h (.req (.host nm t a) s K) Q := by
  obtain ⟨b, w, h', k, hr, q⟩ := hk
  exact ⟨b, w, h', k + 1, .host n h nm t a s K _ _ _ b w h' k rfl hr, q⟩

/-- A handler around a computation that ends normally. -/
theorem wpr_tryCatch {α : Type} {n : Nat} {h : σ} {r : Res α} {hd : Value → M α} {Q : α → State → σ → Prop}
    (hw : WPR eng answer n h r Q) : WPR eng answer n h (M.tryCatchRes hd r) Q := by
  obtain ⟨b, w, h', k, hr, q⟩ := hw
  exact ⟨b, w, h', k, hr_tryCatch eng answer hd hr, q⟩

/-- **A callee's realm**: the body in the function's realm and script, the caller's restored after. -/
theorem wp_inCallee {α : Type} {n : Nat} {h : σ} {realm script : Nat} {body : M α} {s : State}
    {Q : α → State → σ → Prop}
    (hb : WP eng answer n h body { s with realm, script }
      fun a w h' => Q a { w with realm := s.realm, script := s.script } h') :
    WP eng answer n h (inCallee realm script body) s Q := by
  obtain ⟨b, w, h', k, hr, q⟩ := hb
  exact ⟨b, _, h', k, hr_inCallee eng answer realm script body s hr, q⟩

/-! ## Calls of ECMAScript functions -/

/-- A callee's final state `w` with the caller's (`s`) realm and script back. -/
def _root_.ES.State.restore (w s : State) : State := { w with realm := s.realm, script := s.script }

/-- The function record a call of a non-arrow function runs its body in, `this` bound to `t`. -/
def boundEnv (fo : ObjId) (d : FuncData) (t : Value) : Env := .func {} (some d.env) .initialized t fo .undefined

/-- The state a strict function's body starts in: one step of fuel taken, the function's realm and script, its
record (`boundEnv`) pushed. -/
def entryState (s : State) (fo : ObjId) (d : FuncData) (t : Value) : State :=
  { s with fuel := s.fuel - 1, realm := d.realm, script := d.script, envs := s.envs.push (boundEnv fo d t) }

theorem modify_push_last {α : Type} (xs : Array α) (x y : α) :
    (xs.push x).modify xs.size (fun _ => y) = xs.push y := by
  apply Array.ext
  · simp
  · intro i h1 h2
    simp only [Array.getElem_modify, Array.getElem_push]
    by_cases hi : i = xs.size
    · subst hi; simp
    · have hlt : i < xs.size := by simp at h2; omega
      have hne : xs.size ≠ i := fun e => hi e.symm
      simp [hlt, hne]

/-- **The [[Call]] of a strict ECMAScript function** (not a class constructor, not async, not a generator), for
any `this` and arguments: its body (`evalFunctionBody`, which instantiates the declarations) from `entryState`; the
caller's realm and script restored after. -/
theorem wp_callImpl_strict {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t : Value} {args : Array Value}
    {s : State} {Q : Value → State → σ → Prop}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : s.fuel ≠ 0)
    (hcls : d.isClassCtor = false) (hmode : d.thisMode = .strict)
    (hasync : d.code.isAsync = false) (hgen : d.code.isGenerator = false)
    (hb : WP eng answer n h (evalFunctionBody evalDepth fo d s.envs.size args) (entryState s fo d t)
      fun v w h' => Q v (w.restore s) h') :
    WP eng answer n h (callImpl eng (.obj fo) t args) s Q := by
  -- (the call: one step of fuel, the function's kind, then [[Call]] in the callee's realm)
  have hfz : (s.fuel == 0) = false := by simp [hf]
  have hrd := readObj_entry fo (·.kind) { s with fuel := s.fuel - 1 } hlt
  have hk' : ({ s with fuel := s.fuel - 1 } : State).objEntry fo = s.objEntry fo := rfl
  rw [hk', hk] at hrd
  have hcall : callImpl eng (.obj fo) t args s = inCallee d.realm d.script (do
      let env ← newFunctionEnv fo d .undefined
      ordinaryCallBindThis d env t
      evalFunctionBody evalDepth fo d env args) { s with fuel := s.fuel - 1 } := by
    simp only [callImpl, M.bind_eq, M.bind_apply, M.tick, hfz, Bool.false_eq_true, ↓reduceIte, M.bindRes_ok,
      objKind, hrd, callECMA, hcls, hasync, hgen]
  rw [wp_iff_wpr, hcall, ← wp_iff_wpr]
  apply wp_inCallee
  -- (a new function record, `this` bound: the record `boundEnv`)
  have hl : (d.thisMode == .lexical) = false := by rw [hmode]; rfl
  have hs : (d.thisMode == .strict) = true := by rw [hmode]; rfl
  have hts : (ThisStatus.uninitialized == ThisStatus.initialized) = false := rfl
  have hbody : (do
      let env ← newFunctionEnv fo d .undefined
      ordinaryCallBindThis d env t
      evalFunctionBody evalDepth fo d env args : M Value)
        { s with fuel := s.fuel - 1, realm := d.realm, script := d.script } =
      evalFunctionBody evalDepth fo d s.envs.size args (entryState s fo d t) := by
    simp only [M.bind_eq, M.bind_apply, newFunctionEnv, hl, Bool.false_eq_true, ↓reduceIte, allocEnv,
      M.bindRes_ok, ordinaryCallBindThis, hs, bindThisValue, readEnv, modifyEnv, State.withEnvs, pure, M.pure,
      Array.size_push, Nat.lt_succ_self, ↓reduceDIte, Array.getElem_push_eq, id, hts, modify_push_last]
    rfl
  rw [wp_iff_wpr, hbody]
  exact hb

/-- A function body's completion as the call's value. -/
def retVal : Compl → Value
  | .ret v => v
  | _ => .undefined

theorem entryState_setEnv (s : State) (fo : ObjId) (d : FuncData) (t : Value) :
    (entryState s fo d t).setEnv s.envs.size (FDI.mkF (some d.env) .initialized t fo .undefined {}) =
      entryState s fo d t := by
  simp only [entryState, State.setEnv, boundEnv]
  congr 1
  exact modify_push_last s.envs _ _

/-- The state a simple strict function's statements start in: its record filled by instantiation. -/
def bodyState (s : State) (fo : ObjId) (d : FuncData) (t : Value) (args : Array Value) : State :=
  (entryState s fo d t).setEnv s.envs.size (FDI.mkF (some d.env) .initialized t fo .undefined
    (FDI.fdiMap d.code.info.fdi.paramNames args d.code.info.fdi.varNames (FDI.lexDecls d)))

/-- **The [[Call]] of a simple strict function** (`FDI.Simple`: simple parameters, no `arguments`, no nested
function declarations, no `using`), for any `this` and arguments: its statements in `FDI.fdiCtx` (everything in
its own record, the next one), from `bodyState`; its completion's value (`retVal`) is the call's, and the caller's
realm and script are restored. Every such function's call is this one theorem. -/
theorem wp_call_simple {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t : Value} {args : Array Value}
    {s : State} {Q : Value → State → σ → Prop} {body : Array Stmt}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : 2 ≤ s.fuel)
    (hcls : d.isClassCtor = false) (hmode : d.thisMode = .strict)
    (hasync : d.code.isAsync = false) (hgen : d.code.isGenerator = false) (hs : FDI.Simple d)
    (hbody : d.code.body = .stmts body) (hdisp : d.code.info.fdi.usesDispose = false)
    (hb : WP eng answer n h (evalStmts 999999 (FDI.fdiCtx fo d s.envs.size) body) (bodyState s fo d t args)
      fun c w h' => Q (retVal c) (w.restore s) h') :
    WP eng answer n h (callImpl eng (.obj fo) t args) s Q := by
  apply wp_callImpl_strict hlt hk (by omega) hcls hmode hasync hgen
  have hE : s.envs.size < (entryState s fo d t).envs.size := by simp [entryState]
  have hfd := FDI.fdi_strict (some d.env) .initialized t fo .undefined 999998 fo d s.envs.size args
    (entryState s fo d t) hs (by omega) hE (by simp [entryState]; omega)
  rw [entryState_setEnv] at hfd
  have hev : evalFunctionBody evalDepth fo d s.envs.size args (entryState s fo d t) =
      M.bindRes (fun r => M.pure (retVal r)) (evalStmts 999999 (FDI.fdiCtx fo d s.envs.size) body
        (bodyState s fo d t args)) := by
    rw [show evalDepth = 999999 + 1 from rfl]
    simp only [evalFunctionBody, M.bind_eq, M.bind_apply, hfd, M.bindRes_ok, hbody, hdisp, withDisposeScope,
      Bool.not_false, ↓reduceIte]
    rw [← bodyState]
    congr 1
    funext r
    cases r <;> rfl
  rw [wp_iff_wpr, hev]
  apply wpr_bind
  exact wp_mono hb fun c w h' q => wp_pure q

end

end Logic
