import JSProofs.FactsCompose
import JSProofs.ReactUseFiber

/-! The render's callees composed in Lean (contract-style specs and `facts_compose`, replacing
`tools/gen_react_*.py`): `useFiber` with `createWorkInProgress`. -/

facts_form ReactCreateWIP.reuse_spec
facts_form ReactUseFiber.spec_c

namespace ReactUseFiber
open ES Logic

facts_compose useFiber_comp := spec_c
  | hCW => ReactCreateWIP.reuse_spec (X := X) same

end ReactUseFiber
