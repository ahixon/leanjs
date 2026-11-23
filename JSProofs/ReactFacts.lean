import JSProofs.Frame

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

end ReactFacts
