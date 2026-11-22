import JSProofs.ObjRules

/-!
# What a function body starts from, and what record updates leave alone (zippy docs/react-proofs.md)

Facts every proof of a function body uses: `bodyState` changes only the environments (one record pushed, the
function's own), so objects and the caller's records read as before; a record update (`setEnv`) changes only that
record. With these as `simp` lemmas, lookups in a body's states reduce to facts about the caller's state.
-/

open ES ES.M HostRuns
open Std (HashMap)

namespace Logic

section
variable (s : State) (fo : ObjId) (d : FuncData) (t : Value) (args : Array Value)

@[simp] theorem bodyState_envs_size : (bodyState s fo d t args).envs.size = s.envs.size + 1 := by
  simp [bodyState, entryState]

@[simp] theorem bodyState_fuel : (bodyState s fo d t args).fuel = s.fuel - 1 := by
  simp [bodyState, entryState]

@[simp] theorem bodyState_heap : (bodyState s fo d t args).heap = s.heap := by
  simp [bodyState, entryState, State.setEnv]

@[simp] theorem bodyState_objEntry (o : ObjId) : (bodyState s fo d t args).objEntry o = s.objEntry o := by
  simp [State.objEntry]

/-- The caller's records are as they were. -/
theorem bodyState_envEntry_lt (e : EnvId) (he : e < s.envs.size) :
    (bodyState s fo d t args).envEntry e = s.envEntry e := by
  have hne : s.envs.size ≠ e := Nat.ne_of_gt he
  simp [bodyState, entryState, State.envEntry, State.setEnv, Array.getElem?_modify, hne, Array.getElem?_push,
    Ne.symm hne]

/-- The function's own record: the instantiated bindings, the function's environment outside. -/
theorem bodyState_self : Scope.declLike? ((bodyState s fo d t args).envEntry s.envs.size) =
    some (FDI.fdiMap d.code.info.fdi.paramNames args d.code.info.fdi.varNames (FDI.lexDecls d), some d.env) := by
  have h : s.envs.size < (entryState s fo d t).envs.size := by simp [entryState]
  simp [bodyState, h, Scope.declLike?]

end

section
variable (s : State) (e : EnvId) (ev : Env)

@[simp] theorem setEnv_heap : (s.setEnv e ev).heap = s.heap := by simp [State.setEnv]
@[simp] theorem setEnv_objEntry (o : ObjId) : (s.setEnv e ev).objEntry o = s.objEntry o := by
  simp [State.objEntry]

theorem setEnv_envEntry_ne (i : EnvId) (h : e ≠ i) : (s.setEnv e ev).envEntry i = s.envEntry i := by
  simp [State.envEntry, h]

@[simp] theorem declLike_withBindings_func (b : HashMap JSStr Binding) (o : Option EnvId) (ts : ThisStatus)
    (tv : Value) (f : ObjId) (nt : Value) (g : HashMap JSStr Binding → HashMap JSStr Binding) :
    Scope.declLike? ((Env.func b o ts tv f nt).withBindings g) = some (g b, o) := rfl

/-- After updating a declarative or function record's bindings, it is still one, with the updated bindings. -/
theorem declLike_withBindings {ev : Env} {bm : HashMap JSStr Binding} {o : Option EnvId}
    (h : Scope.declLike? ev = some (bm, o)) (g : HashMap JSStr Binding → HashMap JSStr Binding) :
    Scope.declLike? (ev.withBindings g) = some (g bm, o) := by
  cases ev <;> simp [Scope.declLike?] at h <;> obtain ⟨rfl, rfl⟩ := h <;> rfl

end

/-- A chain of plain objects that finds `k` as `o`'s own property: one object. -/
theorem plainChain_own (s : State) (o : ObjId) (k : PropKey) (h : o < s.heap.size)
    (hk : (s.objEntry o).kind.isPlain = true) {p : Property} (hp : (s.objEntry o).props.get? k = some p) :
    PlainChain s 1 o k := by
  simp [PlainChain, h, hk, hp]

theorem ordLookup_own (s : State) (o : ObjId) (k : PropKey) {p : Property}
    (hp : (s.objEntry o).props.get? k = some p) : ordLookup s 1 o k = some p := by
  simp [ordLookup, hp]

end Logic
