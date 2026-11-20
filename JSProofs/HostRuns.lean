import JSProofs.Nested

/-!
# Runs with host steps (Zippy's docs/lean-engine.md, "Proofs")

`HR eng answer n h r b w h' k`: `r`, driven with `n` levels of calls, ends in `.ok b w`, its host requests
answered by the embedder (`answer`) from host state `h` to `h'`, `k` of them. Host requests may come from any
depth: a callee's run with host steps is a step of its caller's (`HR.call`), which the driver implements by
pushing the caller's frame and passing the request up (`Conts.frames`). Soundness (`hr_sound`): the embedder's
loop (`driveHostAt`) gives that result. Every run without host requests lifts (`HR.drives`, `hr_of_runs`).
-/

open ES

namespace HostRuns

/-- The rest of a call once its callee's drive (one level down) returns: on to the continuation, or, at a host
request, the frame pushed and the request passed up (the driver's `finishCall`). -/
def finK {α : Type} (eng : Engine) (n : Nat) (K : Outcome → State → Res α) : Res Value × Conts → Res α × Conts
  | (.req (.host nm th a) s' kc, cs) => (.req (.host nm th a) s' (fun o s3 => .req (.resumeFrame o) s3 K), cs.push ⟨none, kc⟩)
  | (.ok v s', cs) => drive eng (n + 1) (K (.normal v) s') cs
  | (.err e s', cs) => drive eng (n + 1) (K (.throw e) s') cs
  | (.halt m s', cs) => (.halt m s', cs)
  | (.req _ s' _, cs) => (.halt "internal: a suspension escaped a function call" s', cs)

theorem drive_host {α : Type} (eng : Engine) (n : Nat) (nm : String) (t : Value) (a : Array Value) (s : State)
    (K : Outcome → State → Res α) (cs : Conts) :
    drive eng n (.req (.host nm t a) s K) cs = (.req (.host nm t a) s K, cs) := by
  cases n <;> simp [drive, driveWith]

theorem drive_call {α : Type} (eng : Engine) (n : Nat) (f t : Value) (args : Array Value) (s : State)
    (K : Outcome → State → Res α) (cs : Conts) :
    drive eng (n + 1) (.req (.call f t args) s K) cs = finK eng n K (drive eng n (callImpl eng f t args s) cs) := by
  simp only [drive, driveWith, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rcases drive eng n (callImpl eng f t args s) cs with ⟨r, cs'⟩
  rcases r with ⟨v, s'⟩ | ⟨e, s'⟩ | ⟨m, s'⟩ | ⟨q, s', kc⟩
  · rfl
  · rfl
  · rfl
  · cases q <;> rfl

theorem pop_push (cs : Conts) (fr : Frame) : { cs.push fr with frames := (cs.push fr).frames.pop } = cs := by
  cases cs; simp [Conts.push]

theorem drive_resumeFrame {α : Type} (eng : Engine) (n : Nat) (o : Outcome) (s : State) (K : Outcome → State → Res α)
    (cs : Conts) (kc : Outcome → State → Res Value) :
    drive eng (n + 1) (.req (.resumeFrame o) s K) (cs.push ⟨none, kc⟩) = finK eng n K (drive eng n (kc o s) cs) := by
  have hb : (cs.push ⟨none, kc⟩).frames.back? = some ⟨none, kc⟩ := by simp [Conts.push]
  simp only [drive, driveWith, hb, pop_push]
  rcases drive eng n (kc o s) cs with ⟨r, cs'⟩
  rcases r with ⟨v, s'⟩ | ⟨e, s'⟩ | ⟨m, s'⟩ | ⟨q, s', kc'⟩
  · rfl
  · rfl
  · rfl
  · cases q <;> rfl

/-! ## Runs with host steps -/

/-- `r`, driven with `n` levels of calls, runs to `.ok b w` with `k` host requests, answered by `answer` from host
state `h` to `h'`: without host requests (`drives`), a host request at this level (`host`), or a call whose callee
so runs one level down, then the continuation (`call`). -/
inductive HR (eng : Engine) {σ : Type} (answer : HostAnswer σ) : {α : Type} → Nat → σ → Res α → α → State → σ → Nat → Prop
  | drives {α : Type} (n : Nat) (h : σ) (r : Res α) (b : α) (w : State)
      (hd : ∀ cs, (drive eng n r cs).1 = .ok b w) : HR eng answer n h r b w h 0
  | host {α : Type} (n : Nat) (h : σ) (nm : String) (t : Value) (a : Array Value) (s : State)
      (K : Outcome → State → Res α) (h1 : σ) (o : Outcome) (s1 : State) (b : α) (w : State) (h2 : σ) (k : Nat)
      (ha : answer h nm t a s = (h1, o, s1)) (hk : HR eng answer n h1 (K o s1) b w h2 k) :
      HR eng answer n h (.req (.host nm t a) s K) b w h2 (k + 1)
  | call {α : Type} (n : Nat) (h : σ) (f t : Value) (args : Array Value) (s : State) (K : Outcome → State → Res α)
      (x : Value) (w1 : State) (h1 : σ) (k1 : Nat) (b : α) (w : State) (h2 : σ) (k2 : Nat)
      (hc : HR eng answer n h (callImpl eng f t args s) x w1 h1 k1)
      (hk : HR eng answer (n + 1) h1 (K (.normal x) w1) b w h2 k2) :
      HR eng answer (n + 1) h (.req (.call f t args) s K) b w h2 (k1 + k2)

section
variable (eng : Engine) {σ : Type} (answer : HostAnswer σ)

/-- The embedder's loop depends only on what driving gives. -/
theorem driveHostAt_congr {α : Type} (d f : Nat) (h : σ) (r r' : Res α) (cs cs' : Conts)
    (he : drive eng d r cs = drive eng d r' cs') :
    driveHostAt eng answer d (f + 1) h r cs = driveHostAt eng answer d (f + 1) h r' cs' := by
  simp only [driveHostAt, he]

/-- **A call whose callee runs with host steps**: if the caller's drive is the callee's (one level down) finished
by `finK`, and the callee's loop ends in `.ok x w1` within `j` host steps, then the caller's loop runs as the
continuation's from there. -/
theorem call_ctx {α : Type} (n : Nat) (K : Outcome → State → Res α) (x : Value) (w1 : State) (h1 : σ) (cs1 : Conts)
    (b : α) (w : State) (h2 : σ) (k2 : Nat)
    (hk : ∀ fuel, k2 + 1 ≤ fuel → ∀ cs, ∃ cs', driveHostAt eng answer (n + 1) fuel h1 (K (.normal x) w1) cs = (.ok b w, cs', h2)) :
    ∀ (j : Nat) (rc : Res Value) (T : Res α) (cs cs0 : Conts) (h : σ),
      drive eng (n + 1) T cs = finK eng n K (drive eng n rc cs0) →
      driveHostAt eng answer n (j + 1) h rc cs0 = (.ok x w1, cs1, h1) →
      ∀ fuel, j + k2 + 1 ≤ fuel → ∃ cs', driveHostAt eng answer (n + 1) fuel h T cs = (.ok b w, cs', h2) := by
  intro j
  induction j with
  | zero =>
    intro rc T cs cs0 h hT hrun fuel hf
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    rcases hd : drive eng n rc cs0 with ⟨r', cs0'⟩
    rw [hd] at hT
    simp only [driveHostAt, hd] at hrun
    rcases r' with ⟨v, s'⟩ | ⟨e, s'⟩ | ⟨m, s'⟩ | ⟨q, s', kc⟩
    · simp only [Prod.mk.injEq, Res.ok.injEq] at hrun
      obtain ⟨⟨rfl, rfl⟩, rfl, rfl⟩ := hrun
      rw [driveHostAt_congr eng answer _ f h T (K (.normal v) s') cs _ (by rw [hT]; rfl)]
      exact hk (f + 1) (by omega) _
    · simp at hrun
    · simp at hrun
    · cases q <;> simp [driveHostAt] at hrun
  | succ j ih =>
    intro rc T cs cs0 h hT hrun fuel hf
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    rcases hd : drive eng n rc cs0 with ⟨r', cs0'⟩
    rw [hd] at hT
    simp only [driveHostAt, hd] at hrun
    rcases r' with ⟨v, s'⟩ | ⟨e, s'⟩ | ⟨m, s'⟩ | ⟨q, s', kc⟩
    · simp only [Prod.mk.injEq, Res.ok.injEq] at hrun
      obtain ⟨⟨rfl, rfl⟩, rfl, rfl⟩ := hrun
      rw [driveHostAt_congr eng answer _ f h T (K (.normal v) s') cs _ (by rw [hT]; rfl)]
      exact hk (f + 1) (by omega) _
    · simp at hrun
    · simp at hrun
    · cases q with
      | host nm th a =>
        rcases hp : answer h nm th a s' with ⟨h', o, s1⟩
        simp only [hp] at hrun
        have hT' : drive eng (n + 1) T cs = (.req (.host nm th a) s' (fun o s3 => .req (.resumeFrame o) s3 K),
            cs0'.push ⟨none, kc⟩) := by rw [hT]; rfl
        simp only [driveHostAt, hT', hp]
        exact ih (kc o s1) (.req (.resumeFrame o) s1 K) (cs0'.push ⟨none, kc⟩) cs0' h'
          (drive_resumeFrame eng n o s1 K cs0' kc) hrun f (by omega)
      | _ => simp at hrun

/-- **Soundness**: the embedder's loop, with fuel for the host steps, gives what `HR` says. -/
theorem hr_sound {α : Type} {n : Nat} {h : σ} {r : Res α} {b : α} {w : State} {h' : σ} {k : Nat}
    (hr : HR eng answer n h r b w h' k) :
    ∀ fuel, k + 1 ≤ fuel → ∀ cs, ∃ cs', driveHostAt eng answer n fuel h r cs = (.ok b w, cs', h') := by
  induction hr with
  | drives n h r b w hd =>
    intro fuel hf cs
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    rcases hdc : drive eng n r cs with ⟨r', cs'⟩
    have := hd cs
    rw [hdc] at this
    simp only at this
    subst this
    exact ⟨cs', by simp only [driveHostAt, hdc]⟩
  | host n h nm t a s K h1 o s1 b w h2 k ha hk ih =>
    intro fuel hf cs
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    simp only [driveHostAt, drive_host, ha]
    exact ih f (by omega) cs
  | call n h f t args s K x w1 h1 k1 b w h2 k2 hc hk ihc ihk =>
    intro fuel hf cs
    obtain ⟨cs1, hrun⟩ := ihc (k1 + 1) (Nat.le_refl _) cs
    exact call_ctx eng answer n K x w1 h1 cs1 b w h2 k2 ihk k1 (callImpl eng f t args s) _ cs cs h
      (drive_call eng n f t args s K cs) hrun fuel (by omega)

/-- **The embedder's entry point** (`runMHost`, as `Session.runWith` runs a script): a computation that
`HR`-runs at the call depth limit, with fuel for its host steps, ends there. -/
theorem runMHost_of_hr {α : Type} (h : σ) (m : M α) (s : State) (cs : Conts) (b : α) (w : State) (h' : σ) (k : Nat)
    (hr : HR eng answer callDepth h (m s) b w h' k) (hf : k + 1 ≤ s.fuel) :
    ∃ cs', runMHost eng answer h m s cs = (.ok b w, cs', h') :=
  hr_sound eng answer hr s.fuel hf cs

/-- Every run without host requests lifts (the existing call proofs). -/
theorem hr_of_runs {α : Type} (n : Nat) (h : σ) (r : Res α) (b : α) (w : State) (hr : Nested.Runs eng n r b w) :
    HR eng answer n h r b w h 0 :=
  .drives n h r b w (Nested.drive_of_runs eng n r b w hr)

theorem hr_of_drivesTo {α : Type} (h : σ) (r : Res α) (b : α) (w : State) (hd : Script.DrivesTo eng r b w) :
    HR eng answer callDepth h r b w h 0 :=
  .drives callDepth h r b w hd

theorem hr_ok {α : Type} (n : Nat) (h : σ) (b : α) (w : State) : HR eng answer n h (.ok b w) b w h 0 :=
  .drives n h _ b w (fun cs => by rw [Nested.drive_succ_ok])

end

end HostRuns
