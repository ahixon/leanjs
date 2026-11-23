import JSProofs.ReactUpdateProps
import JSProofs.Rebase

/-!
# updateProperties' spec at a framed state (zippy docs/react-proofs.md)

`up_at`: `up_spec`'s conclusion at any state `w0` with an empty frame from the state its premises describe, the
shape callers' contracts quantify over.
-/

open ES ES.M HostRuns Logic
open Std (HashMap)

namespace ReactUpdateProps

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ}

theorem up_at {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t : Value} {s : State}
    {bG : HashMap JSStr Binding} {oG : Option EnvId} {bdC : Binding} {fC : ObjId} {dC : FuncData}
    {bdSP bdN bdS bdV : Binding} {fSP fN fS T : ObjId} {dSP dS : FuncData} {R1 R2 : State → σ → Prop}
    {fI : ObjId} {bdI : BuiltinData} {dom LP NP OP fH : ObjId} {bdH : BuiltinData} {f0 f1 : ObjId} {t0 t1 : JSStr}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d)
    (hcode : d.code = UPGen.updateProperties_func) (hcls : d.isClassCtor = false) (hmode : d.thisMode = .strict)
    (hG : d.env < s.envs.size) (hGe : Scope.declLike? (s.envEntry d.env) = some (bG, oG))
    (hGC : bG[JSStr.ofString "isCustomElement"]? = some bdC) (hGCv : bdC.value = some (.obj fC))
    (hCo : fC < s.heap.size) (hCk : (s.objEntry fC).kind = .func dC) (hCcode : dC.code = ICEGen.isCustomElement_func)
    (hCcls : dC.isClassCtor = false) (hCmode : dC.thisMode = .strict)
    (hI : ∀ w, Frame {} s w → StrGets w (JSStr.ofString "button") (JSStr.ofString "indexOf") fun v => v = .obj fI)
    (hIlt : fI < s.heap.size) (hIk : (s.objEntry fI).kind = .builtin bdI)
    (hIfn : eng.builtins[bdI.id]? = some ES.Builtins.Text.stringProtoIndexOf)
    (hLPlt : LP < s.heap.size) (hLPk : (s.objEntry LP).kind.isPlain = true)
    (hLPkeys : (s.objEntry LP).props.keys = #[.str (JSStr.ofString "onClick"), .str (JSStr.ofString "children")])
    (hLPon : (s.objEntry LP).props.get? (.str (JSStr.ofString "onClick")) = some (.data (.obj f0) true true true))
    (hLPch : (s.objEntry LP).props.get? (.str (JSStr.ofString "children")) = some (.data (.str t0) true true true))
    (hLPh : (s.objEntry LP).props.get? (.str (JSStr.ofString "hasOwnProperty")) = none)
    (hLPp : (s.objEntry LP).proto = .obj OP)
    (hNPlt : NP < s.heap.size) (hNPk : (s.objEntry NP).kind.isPlain = true)
    (hNPkeys : (s.objEntry NP).props.keys = #[.str (JSStr.ofString "onClick"), .str (JSStr.ofString "children")])
    (hNPon : (s.objEntry NP).props.get? (.str (JSStr.ofString "onClick")) = some (.data (.obj f1) true true true))
    (hNPch : (s.objEntry NP).props.get? (.str (JSStr.ofString "children")) = some (.data (.str t1) true true true))
    (hNPh : (s.objEntry NP).props.get? (.str (JSStr.ofString "hasOwnProperty")) = none)
    (hNPp : (s.objEntry NP).proto = .obj OP)
    (hOPlt : OP < s.heap.size) (hOPk : (s.objEntry OP).kind.isPlain = true)
    (hOPh : (s.objEntry OP).props.get? (.str (JSStr.ofString "hasOwnProperty")) = some (.data (.obj fH) true false true))
    (hHlt : fH < s.heap.size) (hHk : (s.objEntry fH).kind = .builtin bdH)
    (hHfn : eng.builtins[bdH.id]? = some objProtoHasOwnProperty)
    (hOPp : (s.objEntry OP).proto = .null) (hOPn : (s.objEntry OP).props.keys.size ≤ 100)
    (hOPne : ∀ k p, (s.objEntry OP).props.get? k = some p → p.enumerable = false)
    (hf01 : f1 ≠ f0) (ht01 : t1 ≠ t0)
    (hGSP : bG[JSStr.ofString "setProp"]? = some bdSP) (hGSPv : bdSP.value = some (.obj fSP))
    (hSPo : fSP < s.heap.size) (hSPk : (s.objEntry fSP).kind = .func dSP) (hSPcode : dSP.code = SetPropGen.setProp_func)
    (hSPcls : dSP.isClassCtor = false) (hSPmode : dSP.thisMode = .strict) (hSPenv : dSP.env = d.env)
    (hGN : bG[JSStr.ofString "noop$1"]? = some bdN) (hGNv : bdN.value = some (.obj fN))
    (hGS : bG[JSStr.ofString "setTextContent"]? = some bdS) (hGSv : bdS.value = some (.obj fS))
    (hSo : fS < s.heap.size) (hSk : (s.objEntry fS).kind = .func dS) (hScode : dS.code = STCGen.setTextContent_func)
    (hScls : dS.isClassCtor = false) (hSmode : dS.thisMode = .strict)
    (hGV : bG[JSStr.ofString "viewTransitionMutationContext"]? = some bdV) (hGVm : bdV.mutable = true)
    (hGVi : bdV.value.isSome = true)
    (hOC : ∀ w h1, Frame {} s w → SetsAcc eng answer (n + 1) h1 w (.obj dom) "onclick" (.obj fN)
      fun w' h' => R1 w' h' ∧ Frame {} w w' ∧ w.fuel ≤ w'.fuel + 1)
    (htext : t1.isEmpty = false)
    (hFC : ReactHostContainer.DomRead eng answer n s {} dom "firstChild" (.obj T))
    (hLC : ReactHostContainer.DomRead eng answer n s {} dom "lastChild" (.obj T))
    (hNT : ReactHostContainer.DomRead eng answer n s {} T "nodeType" (.num (F64.fin false 6755399441055744 (-51))))
    (hNV : ∀ w h1, Frame {} s w → SetsAcc eng answer n h1 w (.obj T) "nodeValue" (.str t1)
      fun w' h' => R2 w' h' ∧ Frame {} w w' ∧ w.fuel ≤ w'.fuel + 1)
    {u : State} (hw : Frame {} s u) (hfw : 2000 ≤ u.fuel) :
    WP eng answer (n + 3) h
      (callImpl eng (.obj fo) t #[.obj dom, .str (JSStr.ofString "button"), .obj LP, .obj NP]) u
      fun v w h' => v = .undefined ∧ (∃ w0 h0, R1 w0 h0) ∧ (∃ w0, R2 w0 h') ∧ u.fuel ≤ w.fuel + 2000 ∧
        Frame ⟨[(d.env, JSStr.ofString "viewTransitionMutationContext")], [], false⟩ u w ∧
        ∃ bm, Scope.declLike? (w.envEntry d.env) = some (bm, oG) ∧
          (∃ bd, bm[JSStr.ofString "viewTransitionMutationContext"]? = some bd ∧ bd.value = some (.bool true) ∧ bd.mutable = true) ∧
          ∀ x, x ≠ JSStr.ofString "viewTransitionMutationContext" → bm[x]? = bG[x]? :=
  by
  apply up_spec (s := u) (hf := hfw) (hI := fun w' hw' => hI w' (frame_empty_trans hw hw'))
    (hOC := fun w' h1 hw' => hOC w' h1 (frame_empty_trans hw hw'))
    (hNV := fun w' h1 hw' => hNV w' h1 (frame_empty_trans hw hw'))
    (hFC := fun w' h1 hw' => hFC w' h1 (frame_empty_trans hw hw'))
    (hLC := fun w' h1 hw' => hLC w' h1 (frame_empty_trans hw hw'))
    (hNT := fun w' h1 hw' => hNT w' h1 (frame_empty_trans hw hw'))
  all_goals rebase_tac hw

end

end ReactUpdateProps
