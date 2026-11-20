import Proofs.Loops

/-!
# Environment Records' operations as rewriting rules

Each operation on an environment, in terms of the record at that index (`s.envEntry env`), with
side conditions that mention only the state and the index, so `simp` can apply the rules to any
state and discharge the conditions by computing the record (after `State.setEnv`s).
-/

namespace ES

open Std (HashMap)

variable {α : Type}

/-- The record at an index (`default` when out of range). -/
def State.envEntry (s : State) (env : EnvId) : Env := (s.envs[env]?).getD default

/-- The state with environment `env` replaced. -/
def State.setEnv (s : State) (env : EnvId) (e : Env) : State := { s with envs := s.envs.modify env fun _ => e }

@[simp] theorem State.setEnv_envs_size (s : State) (env : EnvId) (e : Env) :
    (s.setEnv env e).envs.size = s.envs.size := by simp [State.setEnv]

@[simp] theorem State.setEnv_fuel (s : State) (env : EnvId) (e : Env) : (s.setEnv env e).fuel = s.fuel := by
  simp only [State.setEnv]

@[simp] theorem State.setEnv_get? (s : State) (env i : EnvId) (e : Env) :
    (s.setEnv env e).envs[i]? = if env = i then (s.envs[i]?).map (fun _ => e) else s.envs[i]? := by
  simp [State.setEnv, Array.getElem?_modify]

@[simp] theorem State.setEnv_envEntry_self (s : State) (env : EnvId) (e : Env) (h : env < s.envs.size) :
    (s.setEnv env e).envEntry env = e := by
  simp [State.envEntry, State.setEnv, Array.getElem_modify, h]

@[simp] theorem State.setEnv_setEnv (s : State) (env : EnvId) (e₁ e₂ : Env) :
    (s.setEnv env e₁).setEnv env e₂ = s.setEnv env e₂ := by
  simp only [State.setEnv]
  congr 1
  apply Array.ext
  · simp
  · intro i h1 h2
    simp only [Array.getElem_modify]
    split <;> rfl

theorem State.envEntry_of (s : State) (env : EnvId) (h : env < s.envs.size) : s.envEntry env = s.envs[env] := by
  simp [State.envEntry, Array.getElem?_eq_getElem h]

/-- Declarative and function records (the ones with their own bindings map, not object records). -/
def Env.isDeclLike : Env → Bool
  | .decl .. | .func .. => true
  | _ => false

/-- A record's bindings (declarative, function, module, and the global record's declarative part). -/
def Env.bindingsMap : Env → HashMap JSStr Binding
  | .decl b _ | .func b .. | .module b .. | .global _ b _ => b
  | .object .. => {}

@[simp] theorem Env.isDeclLike_func (b : HashMap JSStr Binding) (o : Option EnvId) (ts : ThisStatus)
    (tv : Value) (fo : ObjId) (nt : Value) : (Env.func b o ts tv fo nt).isDeclLike = true := by
  simp only [Env.isDeclLike]
@[simp] theorem Env.isDeclLike_decl (b : HashMap JSStr Binding) (o : Option EnvId) :
    (Env.decl b o).isDeclLike = true := by
  simp only [Env.isDeclLike]
@[simp] theorem Env.bindingsMap_func (b : HashMap JSStr Binding) (o : Option EnvId) (ts : ThisStatus)
    (tv : Value) (fo : ObjId) (nt : Value) : (Env.func b o ts tv fo nt).bindingsMap = b := by
  simp only [Env.bindingsMap]
@[simp] theorem Env.bindingsMap_decl (b : HashMap JSStr Binding) (o : Option EnvId) :
    (Env.decl b o).bindingsMap = b := by
  simp only [Env.bindingsMap]
@[simp] theorem Env.withBindings_func (b : HashMap JSStr Binding) (o : Option EnvId) (ts : ThisStatus)
    (tv : Value) (fo : ObjId) (nt : Value) (g : HashMap JSStr Binding → HashMap JSStr Binding) :
    (Env.func b o ts tv fo nt).withBindings g = .func (g b) o ts tv fo nt := by
  simp only [Env.withBindings]
@[simp] theorem Env.withBindings_decl (b : HashMap JSStr Binding) (o : Option EnvId)
    (g : HashMap JSStr Binding → HashMap JSStr Binding) : (Env.decl b o).withBindings g = .decl (g b) o := by
  simp only [Env.withBindings]
@[simp] theorem Env.outer_func (b : HashMap JSStr Binding) (o : Option EnvId) (ts : ThisStatus)
    (tv : Value) (fo : ObjId) (nt : Value) : (Env.func b o ts tv fo nt).outer = o := by
  simp only [Env.outer]
@[simp] theorem Env.outer_decl (b : HashMap JSStr Binding) (o : Option EnvId) : (Env.decl b o).outer = o := by
  simp only [Env.outer]

theorem readEnv_entry (id : EnvId) (f : Env → α) (s : State) (h : id < s.envs.size) :
    readEnv id f s = .ok (f (s.envEntry id)) s := by
  simp [readEnv, h, State.envEntry_of s id h]

/-- `modifyEnv` is setting the record to the modified one. -/
theorem modifyEnv_eq_setEnv (s : State) (env : EnvId) (g : Env → Env) (h : env < s.envs.size) :
    modifyEnv env g s = .ok () (s.setEnv env (g (s.envEntry env))) := by
  simp only [modifyEnv, State.withEnvs_eq, State.setEnv]
  congr 2
  apply Array.ext
  · simp
  · intro i h1 h2
    simp only [Array.getElem_modify]
    split
    · next heq => subst heq; simp [State.envEntry_of s env h]
    · rfl

/-- HasBinding(N) on a declarative or function record. -/
theorem hasBinding_declLike (env : EnvId) (n : JSStr) (s : State) (h : env < s.envs.size)
    (hk : (s.envEntry env).isDeclLike = true) :
    hasBinding env n s = .ok ((s.envEntry env).bindingsMap.contains n) s := by
  simp only [hasBinding, M.bind_eq, M.bind_apply, readEnv_entry env id s h, M.bindRes_ok, id]
  revert hk
  cases s.envEntry env <;> simp [Env.isDeclLike, Env.bindingsMap] <;> rfl

/-- CreateMutableBinding(N, D) on a declarative or function record. -/
theorem createMutableBinding_declLike (env : EnvId) (n : JSStr) (del : Bool) (s : State)
    (h : env < s.envs.size) (hk : (s.envEntry env).isDeclLike = true) :
    createMutableBinding env n del s =
      .ok () (s.setEnv env ((s.envEntry env).withBindings (·.insert n { deletable := del }))) := by
  simp only [createMutableBinding, M.bind_eq, M.bind_apply, readEnv_entry env id s h, M.bindRes_ok, id]
  revert hk
  cases he : s.envEntry env <;> simp only [Env.isDeclLike, reduceCtorEq, false_implies] <;>
    intro _ <;> rw [modifyEnv_eq_setEnv s env _ h, he]

/-- InitializeBinding(N, V) on a declarative or function record. -/
theorem initializeBinding_declLike (env : EnvId) (n : JSStr) (v : Value) (s : State)
    (h : env < s.envs.size) (hk : (s.envEntry env).isDeclLike = true) :
    initializeBinding env n v s =
      .ok () (s.setEnv env ((s.envEntry env).withBindings
        (·.modify n fun bd => { bd with value := some v }))) := by
  simp only [initializeBinding, M.bind_eq, M.bind_apply, readEnv_entry env id s h, M.bindRes_ok, id]
  revert hk
  cases he : s.envEntry env <;> simp only [Env.isDeclLike, reduceCtorEq, false_implies] <;>
    intro _ <;> rw [modifyEnv_eq_setEnv s env _ h, he]

/-- ResolveBinding when the name is bound in the first record. -/
theorem resolveBinding_here (env : EnvId) (n : JSStr) (strict : Bool) (s : State)
    (h : env < s.envs.size) (hk : (s.envEntry env).isDeclLike = true)
    (hb : (s.envEntry env).bindingsMap.contains n = true) (hf0 : s.fuel ≠ 0) :
    resolveBinding env n strict s = .ok (.env (some env) n strict) s := by
  obtain ⟨k, hf⟩ : ∃ k, s.fuel = k + 1 := ⟨s.fuel - 1, by omega⟩
  simp only [resolveBinding, M.repeatFrom, hf, M.loop]
  simp only [M.bind_eq, M.bind_apply, hasBinding_declLike env n s h hk, M.bindRes_ok, hb]
  rfl

/-- Binding an identifier parameter (no default) to a value: InitializeBinding in `e`. -/
theorem bindElement_ident (m : Nat) (ctx : Ctx) (x : JSStr) (e : EnvId) (v : Value) (s : State)
    (hm : 2 ≤ m) (h : e < s.envs.size) (hk : (s.envEntry e).isDeclLike = true)
    (hb : (s.envEntry e).bindingsMap.contains x = true) (hf : s.fuel ≠ 0) :
    bindElement m ctx (.ident x) none (.init (some e)) (M.pure v) s =
      .ok () (s.setEnv e ((s.envEntry e).withBindings (·.modify x fun bd => { bd with value := some v }))) := by
  obtain ⟨m, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  simp only [bindElement, targetRefOf, M.bind_eq, M.bind_apply,
    resolveBinding_here e x ctx.strict s h hk hb hf, M.bindRes_ok]
  simp only [putTarget, initializeRefBinding]
  exact initializeBinding_declLike e x v s h hk

/-- allocEnv: the new record is at the old size. -/
@[simp] theorem State.push_envEntry_new (s : State) (e : Env) :
    ({ s with envs := s.envs.push e } : State).envEntry s.envs.size = e := by
  simp [State.envEntry]

/-- Reading an identifier through an empty declarative record into the function record that
binds it (a function body's top-level lexical environment, then its parameters). -/
theorem identValue_decl_func (lex env : EnvId) (n : JSStr) (strict : Bool) (s : State) (v : Value)
    (b : HashMap JSStr Binding) (bd : Binding) (o : Option EnvId) (ts : ThisStatus) (tv : Value) (fo : ObjId)
    (nt : Value) (hl : lex < s.envs.size) (hL : s.envEntry lex = .decl ∅ (some env))
    (he : env < s.envs.size) (hE : s.envEntry env = .func b o ts tv fo nt)
    (hb : b[n]? = some bd) (hv : bd.value = some v) (hf : 2 ≤ s.fuel) :
    identValue lex n strict s = .ok v s := by
  obtain ⟨k, hk⟩ : ∃ k, s.fuel = k + 2 := ⟨s.fuel - 2, by omega⟩
  simp only [identValue, M.repeatFrom, hk, M.loop]
  simp [M.bind_eq, M.bind_apply, readEnv_entry _ _ s hl, readEnv_entry _ _ s he, hL, hE, hb, hv, M.loopRes,
    pure, M.pure, M.loop]

/-- Reading an identifier bound (and initialized) in the first record, a declarative one. -/
theorem identValue_decl_here (lex : EnvId) (n : JSStr) (strict : Bool) (s : State) (v : Value)
    (b : HashMap JSStr Binding) (o : Option EnvId) (bd : Binding) (hl : lex < s.envs.size)
    (hL : s.envEntry lex = .decl b o) (hb : b[n]? = some bd) (hv : bd.value = some v) (hf : s.fuel ≠ 0) :
    identValue lex n strict s = .ok v s := by
  obtain ⟨k, hk⟩ : ∃ k, s.fuel = k + 1 := ⟨s.fuel - 1, by omega⟩
  simp only [identValue, M.repeatFrom, hk, M.loop]
  simp [M.bind_eq, M.bind_apply, readEnv_entry _ _ s hl, hL, hb, hv, pure, M.pure]

/-- Reading an identifier through a declarative record that does not bind it into the function
record that does. -/
theorem identValue_decl_outer (lex env : EnvId) (n : JSStr) (strict : Bool) (s : State) (v : Value)
    (bL : HashMap JSStr Binding) (b : HashMap JSStr Binding) (bd : Binding) (o : Option EnvId) (ts : ThisStatus)
    (tv : Value) (fo : ObjId) (nt : Value) (hl : lex < s.envs.size) (hL : s.envEntry lex = .decl bL (some env))
    (hn : bL[n]? = none) (he : env < s.envs.size) (hE : s.envEntry env = .func b o ts tv fo nt)
    (hb : b[n]? = some bd) (hv : bd.value = some v) (hf : 2 ≤ s.fuel) :
    identValue lex n strict s = .ok v s := by
  obtain ⟨k, hk⟩ : ∃ k, s.fuel = k + 2 := ⟨s.fuel - 2, by omega⟩
  simp only [identValue, M.repeatFrom, hk, M.loop]
  simp [M.bind_eq, M.bind_apply, readEnv_entry _ _ s hl, readEnv_entry _ _ s he, hL, hE, hn, hb, hv,
    pure, M.pure, M.loop]

/-- SetMutableBinding of an initialized mutable binding of a declarative record. -/
theorem setMutableBinding_decl (env : EnvId) (n : JSStr) (v : Value) (strict : Bool) (s : State)
    (b : HashMap JSStr Binding) (o : Option EnvId) (bd : Binding) (h : env < s.envs.size)
    (hE : s.envEntry env = .decl b o) (hb : b[n]? = some bd) (hv : bd.value.isSome = true)
    (hm : bd.mutable = true) :
    setMutableBinding env n v strict s =
      .ok () (s.setEnv env (.decl (b.modify n fun bd => { bd with value := some v }) o)) := by
  cases hvv : bd.value with
  | none => simp [hvv] at hv
  | some w =>
    simp [setMutableBinding, M.bind_eq, M.bind_apply, readEnv_entry _ _ s h, hE, declSetMutable, hb, hvv, hm, -modifyEnv_apply,
      modifyEnv_eq_setEnv _ _ _ h]

/-! ## Allocating environments as a named update -/

/-- The state with environment `e` allocated (at index `s.envs.size`). -/
def State.pushEnv (s : State) (e : Env) : State := { s with envs := s.envs.push e }

theorem allocEnv_eq (e : Env) (s : State) : allocEnv e s = .ok s.envs.size (s.pushEnv e) := by
  simp only [allocEnv, State.pushEnv, State.withEnvs_eq]

theorem newDeclEnv_eq (o : Option EnvId) (s : State) :
    newDeclEnv o s = .ok s.envs.size (s.pushEnv (.decl {} o)) := by
  simp only [newDeclEnv, allocEnv_eq]

@[simp] theorem State.pushEnv_size (s : State) (e : Env) : (s.pushEnv e).envs.size = s.envs.size + 1 := by
  simp [State.pushEnv]
@[simp] theorem State.pushEnv_fuel (s : State) (e : Env) : (s.pushEnv e).fuel = s.fuel := by
  simp only [State.pushEnv]
@[simp] theorem State.pushEnv_entry_new (s : State) (e : Env) : (s.pushEnv e).envEntry s.envs.size = e := by
  simp [State.pushEnv, State.envEntry]
theorem State.pushEnv_entry_at (s : State) (e : Env) (i : EnvId) (h : i = s.envs.size) :
    (s.pushEnv e).envEntry i = e := by
  subst h; exact State.pushEnv_entry_new s e

theorem State.pushEnv_entry_lt (s : State) (e : Env) (i : EnvId) (h : i < s.envs.size) :
    (s.pushEnv e).envEntry i = s.envEntry i := by
  simp [State.pushEnv, State.envEntry, Array.getElem?_push, Nat.ne_of_lt h]

theorem State.setEnv_envEntry_ne (s : State) (env i : EnvId) (e : Env) (h : env ≠ i) :
    (s.setEnv env e).envEntry i = s.envEntry i := by
  simp [State.envEntry, State.setEnv, Array.getElem?_modify, h]

/-! ## Walking environment chains (one record per step of the lookup loop) -/

/-- One step of `identValue`'s walk. -/
def identBody (n : JSStr) (strict : Bool) : EnvId → M (EnvId ⊕ Value) := fun e => do
  let r ← readEnv e fun ev => match ev with
    | .decl b o | .func b o .. => match b.get? n with
      | some bd => Sum.inr (Sum.inl bd.value)
      | none => match o with
        | some o => Sum.inl o
        | none => Sum.inr (Sum.inr ())
    | _ => Sum.inr (Sum.inr ())
  match r with
  | .inl o => return .inl o
  | .inr (.inl (some v)) => return .inr v
  | .inr (.inl none) => tdzError n
  | .inr (.inr ()) => return .inr (← getRefValue (← resolveBinding e n strict))

theorem identValue_loop (env : EnvId) (n : JSStr) (strict : Bool) (s : State) :
    identValue env n strict s = M.loop (identBody n strict) s.fuel env s := rfl

/-- A declarative record without the name: the walk continues at its outer record. -/
theorem identBody_skip (k : Nat) (env o : EnvId) (n : JSStr) (strict : Bool) (s : State)
    (b : HashMap JSStr Binding) (h : env < s.envs.size) (hE : s.envEntry env = .decl b (some o))
    (hn : b[n]? = none) :
    M.loop (identBody n strict) (k + 1) env s = M.loop (identBody n strict) k o s := by
  simp [M.loop, identBody, M.bind_eq, M.bind_apply, readEnv_entry _ _ _ h, hE, hn, pure, M.pure]

/-- A declarative or function record with the (initialized) binding: the walk ends with its value. -/
theorem identBody_found (k : Nat) (env : EnvId) (n : JSStr) (strict : Bool) (s : State) (bd : Binding) (v : Value)
    (h : env < s.envs.size) (hk : (s.envEntry env).isDeclLike = true)
    (hb : (s.envEntry env).bindingsMap[n]? = some bd) (hv : bd.value = some v) :
    M.loop (identBody n strict) (k + 1) env s = .ok v s := by
  revert hk hb
  cases hE : s.envEntry env <;> simp [Env.isDeclLike, Env.bindingsMap] <;> intro hb <;>
    simp [M.loop, identBody, M.bind_eq, M.bind_apply, readEnv_entry _ _ _ h, hE, hb, hv, pure, M.pure]

/-- One step of `resolveBinding`'s walk. -/
def resolveBody (n : JSStr) (strict : Bool) : Option EnvId → M (Option EnvId ⊕ Ref) := fun e => do
  match e with
  | none => return .inr (.env none n strict)
  | some e =>
    if ← hasBinding e n then return .inr (.env (some e) n strict)
    return .inl (← readEnv e Env.outer)

theorem resolveBinding_loop (env : EnvId) (n : JSStr) (strict : Bool) (s : State) :
    resolveBinding env n strict s = M.loop (resolveBody n strict) s.fuel (some env) s := rfl

theorem resolveBody_skip (k : Nat) (env o : EnvId) (n : JSStr) (strict : Bool) (s : State)
    (b : HashMap JSStr Binding) (h : env < s.envs.size) (hE : s.envEntry env = .decl b (some o))
    (hn : b[n]? = none) :
    M.loop (resolveBody n strict) (k + 1) (some env) s = M.loop (resolveBody n strict) k (some o) s := by
  have hc : b.contains n = false := by simp [Std.HashMap.contains_eq_isSome_getElem?, hn]
  simp [M.loop, resolveBody, M.bind_eq, M.bind_apply, hasBinding_declLike _ _ _ h (by rw [hE]; rfl), hE, hc,
    readEnv_entry _ _ _ h, pure, M.pure, Env.bindingsMap]

theorem resolveBody_found (k : Nat) (env : EnvId) (n : JSStr) (strict : Bool) (s : State)
    (h : env < s.envs.size) (hk : (s.envEntry env).isDeclLike = true)
    (hb : (s.envEntry env).bindingsMap.contains n = true) :
    M.loop (resolveBody n strict) (k + 1) (some env) s = .ok (.env (some env) n strict) s := by
  simp [M.loop, resolveBody, M.bind_eq, M.bind_apply, hasBinding_declLike _ _ _ h hk, hb, pure, M.pure]

/-- Reading a name in the first record, or after skipping one or two declarative records without it. -/
theorem identValue_skip0 (env : EnvId) (n : JSStr) (strict : Bool) (s : State) (bd : Binding) (v : Value)
    (h : env < s.envs.size) (hk : (s.envEntry env).isDeclLike = true)
    (hb : (s.envEntry env).bindingsMap[n]? = some bd) (hv : bd.value = some v) (hf : s.fuel ≠ 0) :
    identValue env n strict s = .ok v s := by
  obtain ⟨k, hk1⟩ : ∃ k, s.fuel = k + 1 := ⟨s.fuel - 1, by omega⟩
  rw [identValue_loop, hk1, identBody_found k env n strict s bd v h hk hb hv]

theorem identValue_skip1 (e1 env : EnvId) (n : JSStr) (strict : Bool) (s : State) (b1 : HashMap JSStr Binding)
    (bd : Binding) (v : Value) (h1 : e1 < s.envs.size) (hE1 : s.envEntry e1 = .decl b1 (some env))
    (hn1 : b1[n]? = none) (h : env < s.envs.size) (hk : (s.envEntry env).isDeclLike = true)
    (hb : (s.envEntry env).bindingsMap[n]? = some bd) (hv : bd.value = some v) (hf : 2 ≤ s.fuel) :
    identValue e1 n strict s = .ok v s := by
  obtain ⟨k, hk1⟩ : ∃ k, s.fuel = k + 2 := ⟨s.fuel - 2, by omega⟩
  rw [identValue_loop, hk1, identBody_skip _ e1 env n strict s b1 h1 hE1 hn1,
    identBody_found k env n strict s bd v h hk hb hv]

theorem identValue_skip2 (e1 e2 env : EnvId) (n : JSStr) (strict : Bool) (s : State) (b1 b2 : HashMap JSStr Binding)
    (bd : Binding) (v : Value) (h1 : e1 < s.envs.size) (hE1 : s.envEntry e1 = .decl b1 (some e2))
    (hn1 : b1[n]? = none) (h2 : e2 < s.envs.size) (hE2 : s.envEntry e2 = .decl b2 (some env))
    (hn2 : b2[n]? = none) (h : env < s.envs.size) (hk : (s.envEntry env).isDeclLike = true)
    (hb : (s.envEntry env).bindingsMap[n]? = some bd) (hv : bd.value = some v) (hf : 3 ≤ s.fuel) :
    identValue e1 n strict s = .ok v s := by
  obtain ⟨k, hk1⟩ : ∃ k, s.fuel = k + 3 := ⟨s.fuel - 3, by omega⟩
  rw [identValue_loop, hk1, identBody_skip _ e1 e2 n strict s b1 h1 hE1 hn1, identBody_skip _ e2 env n strict s b2 h2 hE2 hn2,
    identBody_found k env n strict s bd v h hk hb hv]

theorem resolveBinding_skip1 (e1 env : EnvId) (n : JSStr) (strict : Bool) (s : State) (b1 : HashMap JSStr Binding)
    (h1 : e1 < s.envs.size) (hE1 : s.envEntry e1 = .decl b1 (some env)) (hn1 : b1[n]? = none)
    (h : env < s.envs.size) (hk : (s.envEntry env).isDeclLike = true)
    (hb : (s.envEntry env).bindingsMap.contains n = true) (hf : 2 ≤ s.fuel) :
    resolveBinding e1 n strict s = .ok (.env (some env) n strict) s := by
  obtain ⟨k, hk1⟩ : ∃ k, s.fuel = k + 2 := ⟨s.fuel - 2, by omega⟩
  rw [resolveBinding_loop, hk1, resolveBody_skip _ e1 env n strict s b1 h1 hE1 hn1, resolveBody_found k env n strict s h hk hb]

end ES
