import JSProofs.Frame
import JSProofs.Rebase

/-!
# Facts the commit's passes hand each other (zippy docs/react-proofs.md)

A module binding's value and a writable property's value at a state: what one pass's post gives the next pass's
call (the effects status, the restored execution context, transition and priority).
-/

open ES Logic
open Std (HashMap)

namespace ReactFacts

/-- A mutable binding of the scope `g` holding `v`. -/
def BindIs (w : State) (g : EnvId) (x : JSStr) (v : Value) : Prop :=
  ∃ bm o bd, Scope.declLike? (w.envEntry g) = some (bm, o) ∧ bm[x]? = some bd ∧ bd.value = some v ∧ bd.mutable = true

/-- A writable data property of `o` holding `v`. -/
def PropIs (w : State) (o : ObjId) (k : JSStr) (v : Value) : Prop :=
  ∃ e c, (w.objEntry o).props.get? (.str k) = some (.data v true e c)

/-- What the before-mutation pass leaves for `flushMutationEffects`: `selectionInformation` an object `SI` beyond `hs`
(the heap at the commit's start) with `focusedElem` `E` and a `selectionRange`, `eventsEnabled` holding `ev`,
`_enabled` false. -/
def SelInfo (w : State) (g : EnvId) (E : ObjId) (ev : Value) (hs : Nat) : Prop :=
  (∃ SI, hs ≤ SI ∧ SI < w.heap.size ∧ (w.objEntry SI).kind.isPlain = true ∧
    (∃ a b c, (w.objEntry SI).props.get? (.str (JSStr.ofString "focusedElem")) = some (.data (.obj E) a b c)) ∧
    (∃ v a b c, (w.objEntry SI).props.get? (.str (JSStr.ofString "selectionRange")) = some (.data v a b c)) ∧
    BindIs w g (JSStr.ofString "selectionInformation") (.obj SI)) ∧
  BindIs w g (JSStr.ofString "eventsEnabled") ev ∧ BindIs w g (JSStr.ofString "_enabled") (.bool false)

section
open Logic

theorem BindIs.setProp {w : State} {g : EnvId} {x : JSStr} {v : Value} (h : BindIs w g x v) (o : ObjId) (k : PropKey)
    (p : Property) : BindIs (w.setProp o k p) g x v := by
  simpa only [BindIs, setProp_envEntry] using h

/-- A write to another scope. -/
theorem BindIs.setEnv_other {w : State} {g e : EnvId} {x : JSStr} {v : Value} (h : BindIs w g x v) (hne : e ≠ g)
    (ev : Env) : BindIs (w.setEnv e ev) g x v := by
  simpa only [BindIs, setEnv_envEntry_ne _ _ _ _ hne] using h

/-- A binding of the same scope other than `x` modified. -/
theorem BindIs.setEnv_modify {w : State} {g : EnvId} {x y : JSStr} {v : Value} {ev : Env}
    {f : Binding → Binding} (h : BindIs w g x v) (hg : g < w.envs.size) (hent : w.envEntry g = ev) (hne : y ≠ x) :
    BindIs (w.setEnv g (ev.withBindings (·.modify y f))) g x v := by
  obtain ⟨bm, o, bd, hd, hb, hv, hm⟩ := h
  refine ⟨bm.modify y f, o, bd, ?_, ?_, hv, hm⟩
  · rw [setEnv_envEntry_self _ _ _ hg, declLike_withBindings', ← hent, hd]; rfl
  · rw [Std.HashMap.getElem?_modify]; simp only [hb]; split <;> simp_all

theorem SelInfo.setProp {w : State} {g : EnvId} {E : ObjId} {ev : Value} {hs : Nat} (h : SelInfo w g E ev hs)
    {o : ObjId} (ho : o < hs) (k : PropKey) (p : Property) : SelInfo (w.setProp o k p) g E ev hs := by
  obtain ⟨⟨SI, h1, h2, h3, h4, h5, h6⟩, h7, h8⟩ := h
  have hne : o ≠ SI := Nat.ne_of_lt (Nat.lt_of_lt_of_le ho h1)
  refine ⟨⟨SI, h1, by simpa using h2, ?_, ?_, ?_, h6.setProp o k p⟩, h7.setProp o k p, h8.setProp o k p⟩ <;>
    simp only [setProp_objEntry, hne, false_and, ↓reduceIte] <;> assumption

theorem SelInfo.setEnv_other {w : State} {g e : EnvId} {E : ObjId} {ev : Value} {hs : Nat} (h : SelInfo w g E ev hs)
    (hne : e ≠ g) (en : Env) : SelInfo (w.setEnv e en) g E ev hs := by
  obtain ⟨⟨SI, h1, h2, h3, h4, h5, h6⟩, h7, h8⟩ := h
  exact ⟨⟨SI, h1, by simpa using h2, by simpa using h3, by simpa using h4, by simpa using h5, h6.setEnv_other hne en⟩,
    h7.setEnv_other hne en, h8.setEnv_other hne en⟩

/-- A binding of the same scope other than the three modified. -/
theorem SelInfo.setEnv_modify {w : State} {g : EnvId} {E : ObjId} {ev : Value} {hs : Nat} {y : JSStr} {en : Env}
    {f : Binding → Binding} (h : SelInfo w g E ev hs) (hg : g < w.envs.size) (hent : w.envEntry g = en)
    (hne : y ∉ [JSStr.ofString "selectionInformation", JSStr.ofString "eventsEnabled", JSStr.ofString "_enabled"]) :
    SelInfo (w.setEnv g (en.withBindings (·.modify y f))) g E ev hs := by
  obtain ⟨⟨SI, h1, h2, h3, h4, h5, h6⟩, h7, h8⟩ := h
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hne
  exact ⟨⟨SI, h1, by simpa using h2, by simpa using h3, by simpa using h4, by simpa using h5,
    h6.setEnv_modify hg hent hne.1⟩, h7.setEnv_modify hg hent hne.2.1, h8.setEnv_modify hg hent hne.2.2⟩

end

end ReactFacts
