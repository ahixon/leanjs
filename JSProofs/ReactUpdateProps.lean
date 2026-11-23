import JSProofs.UPInfra
import JSProofs.UPBodies
import JSProofs.UPSwitch
import JSProofs.ReactIsCustom
import JSProofs.ReactSetProp
import JSProofs.BuiltinHasOwn

/-!
# updateProperties for the counter's button (zippy docs/react-proofs.md)

`updateProperties(dom, "button", lastProps, nextProps)` where both props objects have `onClick` (a function, a new
one each render) and `children` (the text, changed): the tag switch's `default` (not a custom element), the first
loop finds nothing removed, the second calls `setProp` for each changed prop: `dom.onclick = noop$1` and the text
node's `nodeValue`.
-/

open ES ES.M HostRuns Logic
open Std (HashMap)

namespace ReactUpdateProps

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ}

@[simp] theorem objEntry_withFuel (s : State) (f : Nat) (o : ObjId) : (s.withFuel f).objEntry o = s.objEntry o := rfl
@[simp] theorem heap_withFuel (s : State) (f : Nat) : (s.withFuel f).heap = s.heap := rfl
@[simp] theorem envs_withFuel (s : State) (f : Nat) : (s.withFuel f).envs = s.envs := rfl
@[simp] theorem fuel_withFuel (s : State) (f : Nat) : (s.withFuel f).fuel = f := rfl

theorem size_qsort' {α : Type} (as : Array α) (lt : α → α → Bool) : (as.qsort lt).size = as.size := by
  unfold Array.qsort
  split
  · rfl
  · simp

theorem orderedKeys_size (ks : Array PropKey) : (orderedKeys ks).size ≤ 3 * ks.size := by
  simp only [orderedKeys, Array.size_append, Array.size_map, size_qsort']
  refine Nat.le_trans (Nat.add_le_add (Nat.add_le_add Array.size_filterMap_le Array.size_filter_le)
    Array.size_filter_le) ?_
  omega

theorem two_keys : (orderedKeys #[PropKey.str (JSStr.ofString "onClick"), PropKey.str (JSStr.ofString "children")]).filter
    (fun k => match k with | .str _ => true | _ => false) =
    #[PropKey.str (JSStr.ofString "onClick"), PropKey.str (JSStr.ofString "children")] := by
  decide +kernel

theorem simple (d : FuncData) (hc : d.code = UPGen.updateProperties_func) : FDI.Simple d := by
  constructor <;> rw [hc] <;> try rfl
  simp [UPGen.updateProperties_func, Func.params, Func.info]

set_option maxRecDepth 40000 in
set_option maxHeartbeats 8000000 in
theorem up_spec {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t : Value} {s : State}
    {bG : HashMap JSStr Binding} {oG : Option EnvId} {bdC : Binding} {fC : ObjId} {dC : FuncData}
    {bdSP bdN bdS bdV : Binding} {fSP fN fS T : ObjId} {dSP dS : FuncData} {R1 R2 : State → σ → Prop}
    {fI : ObjId} {bdI : BuiltinData} {dom LP NP OP fH : ObjId} {bdH : BuiltinData} {f0 f1 : ObjId} {t0 t1 : JSStr}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : 2000 ≤ s.fuel)
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
      fun w' h' => R2 w' h' ∧ Frame {} w w' ∧ w.fuel ≤ w'.fuel + 1) :
    WP eng answer (n + 3) h
      (callImpl eng (.obj fo) t #[.obj dom, .str (JSStr.ofString "button"), .obj LP, .obj NP]) s
      fun v w h' => v = .undefined ∧ (∃ w0 h0, R1 w0 h0) ∧ (∃ w0, R2 w0 h') ∧ s.fuel ≤ w.fuel + 2000 ∧
        Frame ⟨[(d.env, JSStr.ofString "viewTransitionMutationContext")], [], false⟩ s w ∧
        ∃ bm, Scope.declLike? (w.envEntry d.env) = some (bm, oG) ∧
          (∃ bd, bm[JSStr.ofString "viewTransitionMutationContext"]? = some bd ∧ bd.value = some (.bool true) ∧ bd.mutable = true) ∧
          ∀ x, x ≠ JSStr.ofString "viewTransitionMutationContext" → bm[x]? = bG[x]? := by
  apply wp_callGen UPGen.updateProperties_eq (by decide) hlt hk (by omega) hcls hmode
    (by rw [hcode]; rfl) (by rw [hcode]; rfl) (simple d hcode) (by rw [hcode]; rfl) (by rw [hcode]; rfl)
  have hpn : d.code.info.fdi.paramNames = #[JSStr.ofString "domElement", JSStr.ofString "tag",
    JSStr.ofString "lastProps", JSStr.ofString "nextProps"] := by rw [hcode]; rfl
  have hv : d.code.info.fdi.varNames = #[JSStr.ofString "name", JSStr.ofString "type", JSStr.ofString "value",
    JSStr.ofString "defaultValue", JSStr.ofString "lastDefaultValue", JSStr.ofString "checked",
    JSStr.ofString "defaultChecked", JSStr.ofString "lastProp", JSStr.ofString "propKey$221",
    JSStr.ofString "propKey", JSStr.ofString "propKey$237", JSStr.ofString "propKey$242",
    JSStr.ofString "propKey$247", JSStr.ofString "propKey$252"] := by rw [hcode]; rfl
  have hl : FDI.lexDecls d = #[] := by simp [FDI.lexDecls, hcode, UPGen.updateProperties_func, Func.info]
  have ha : d.code.isAsync = false := by rw [hcode]; rfl
  have e1 : d.env ≠ s.envs.size := Nat.ne_of_lt hG
  have e2 : d.env ≠ s.envs.size + 1 := Nat.ne_of_lt (Nat.lt_succ_of_lt hG)
  have e3 : d.env < s.envs.size + 1 + 1 := Nat.lt_succ_of_lt (Nat.lt_succ_of_lt hG)
  have e4 : d.env < s.envs.size + 1 := Nat.lt_succ_of_lt hG
  clear hcode
  simp only [UPGen.updateProperties]
  iterate 2 (first | js_go | js_norm [hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner] | js_split)
  refine wp_switchC UPSwitch.lex ?_
  js_until [] [e1, e2, e3, e4, hGe, hGC, hGCv, hG, hCo, hCk, hCcls, hCmode, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  have hw0 : Frame {} s ((bodyState s fo d t #[.obj dom, .str (JSStr.ofString "button"), .obj LP, .obj NP]).pushEnv
      (Env.decl ∅ (some s.envs.size))) := by frame_go' [*]
  refine ⟨by js_norm [CallableC, e1, e2, e3, e4, hGe, hGC, hGCv, hG, hCo, hCk, hCcls, hCmode, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner], ?_⟩
  refine wp_mono (ReactIsCustom.ice_spec (by js_norm [e1, e2, e3, e4, hGe, hGC, hGCv, hG, hCo, hCk, hCcls, hCmode, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]) (by js_norm [e1, e2, e3, e4, hGe, hGC, hGCv, hG, hCo, hCk, hCcls, hCmode, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]) (by simp; omega) hCcode hCcls hCmode
    (fun w hw => hI w (frame_empty_trans hw0 hw)) (by js_norm [hIlt, e1, e2, e3, e4, hGe, hGC, hGCv, hG, hCo, hCk, hCcls, hCmode, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]) (by js_norm [hIk, hIlt, e1, e2, e3, e4, hGe, hGC, hGCv, hG, hCo, hCk, hCcls, hCmode, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]) hIfn
    (by decide +kernel)) ?_
  rintro v1 w1 h1 ⟨rfl, hF1, hfu1, rfl⟩
  have hlt0 : s.envs.size < ((bodyState s fo d t #[.obj dom, .str (JSStr.ofString "button"), .obj LP, .obj NP]).pushEnv (Env.decl ∅ (some s.envs.size))).envs.size := by simp; omega
  have hS1 : s.envs.size < w1.envs.size := Nat.lt_of_lt_of_le hlt0 hF1.envs_le
  have hE1 : w1.envEntry s.envs.size = ((bodyState s fo d t #[.obj dom, .str (JSStr.ofString "button"), .obj LP, .obj NP]).pushEnv (Env.decl ∅ (some s.envs.size))).envEntry s.envs.size := envEntry_frame0 hF1 hlt0
  have hd1 : Scope.declLike? (w1.envEntry d.env) = some (bG, oG) := by
    rw [envEntry_frame0 hF1 (by simp <;> omega)]; js_norm [e1, e2, e3, e4, hGe, hGC, hGCv, hG, hCo, hCk, hCcls, hCmode, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  have hfw1 : 1900 ≤ w1.fuel := by simp [bodyState, State.pushEnv, entryState] at hfu1; omega
  have hfr1 : s.fuel ≤ w1.fuel + 30 := by simp [bodyState, State.pushEnv, entryState] at hfu1; omega
  have hG1 : d.env < w1.envs.size := Nat.lt_of_lt_of_le (by simp <;> omega) hF1.envs_le
  js_until [] [hlt0, hS1, hE1, hd1, hG1, e1, e2, e3, e4, hGe, hGC, hGCv, hG, hCo, hCk, hCcls, hCmode, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  rw [show 999999 - 59 + 58 = 999996 + 2 from rfl]
  refine wp_forInStmt (by intro x ie hh; cases hh) ?_
  rw [show (999996 : Nat) = 999995 + 1 from rfl]
  simp only [evalForHead]
  rw [if_pos (show (VarKind.var == VarKind.var) = true from rfl)]
  refine (show ∀ c, evalExpr 999995 c (Expr.ident (JSStr.ofString "lastProps")) = Sem.ident (JSStr.ofString "lastProps") c
    from fun _ => rfl) _ ▸ ?_
  js_until [] [hfw1, hS1, hE1, hd1, hG1, e1, e2, e3, e4, hGe, hGC, hGCv, hG, hCo, hCk, hCcls, hCmode, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  refine ⟨LP, rfl, ?_⟩
  rw [← UPBodies.body1Stmt.eq_1]
  have hF01 : Frame {} s w1 := frame_empty_trans hw0 hF1
  have hLP1 : w1.objEntry LP = s.objEntry LP := objEntry_frame0 hF01 hLPlt
  have hLPlt1 : LP < w1.heap.size := Nat.lt_of_lt_of_le hLPlt hF01.heap_le
  refine forIn_enter (by omega) (by omega) ?_
  have hLPw : ∀ f, (w1.withFuel f).objEntry LP = s.objEntry LP := fun _ => hLP1
  refine wp_of_eq (ownPropertyKeys_plain LP _ hLPlt1 (by rw [hLPw]; exact hLPk)) ?_
  rw [hLPw, hLPkeys]
  generalize hks : Array.filter _ (orderedKeys _) = ks
  obtain rfl : ks = #[PropKey.str (JSStr.ofString "onClick"), PropKey.str (JSStr.ofString "children")] := by
    rw [← hks]; decide +kernel
  rw [show (999995 + 1 : Nat) = 999984 + 12 from rfl]
  have hOP1 : w1.objEntry OP = s.objEntry OP := objEntry_frame0 hF01 hOPlt
  have hOPlt1 : OP < w1.heap.size := Nat.lt_of_lt_of_le hOPlt hF01.heap_le
  have hNP1 : w1.objEntry NP = s.objEntry NP := objEntry_frame0 hF01 hNPlt
  have hNPlt1 : NP < w1.heap.size := Nat.lt_of_lt_of_le hNPlt hF01.heap_le
  have hH1 : w1.objEntry fH = s.objEntry fH := objEntry_frame0 hF01 hHlt
  have hHlt1 : fH < w1.heap.size := Nat.lt_of_lt_of_le hHlt hF01.heap_le
  have hSP1 : w1.objEntry fSP = s.objEntry fSP := objEntry_frame0 hF01 hSPo
  have hSPlt1 : fSP < w1.heap.size := Nat.lt_of_lt_of_le hSPo hF01.heap_le
  -- loop 1, key onClick
  refine forIn_key (k := JSStr.ofString "onClick") (by omega) (by simp only [fuel_withFuel]; omega) (by decide) rfl
    (by simp) ?_
  refine wp_of_eq (Obj'.getOwnProperty_entry LP _ _ (by simpa using hLPlt1) (by simp only [objEntry_withFuel, setEnv_objEntry, hLP1]; exact hLPk)) ?_
  simp only [objEntry_withFuel, setEnv_objEntry, hLP1, hLPon]
  refine ⟨_, rfl, rfl, ?_⟩
  refine wp_bindForVar (by show 8 ≤ _; simp only [fuel_withFuel]; omega) ?_
  js_norm [hOP1, hOPlt1, hNP1, hNPlt1, hH1, hHlt1, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLP1, hLPlt1, hLPk, hLPon, hLPch, hfw1, hS1, hE1, hd1, hG1, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  rw [UPBodies.body1_eval]
  simp only [UPBodies.body1Sem]
  iterate 5 (first | js_go | js_norm [hOP1, hOPlt1, hNP1, hNPlt1, hH1, hHlt1, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLP1, hLPlt1, hLPk, hLPon, hLPch, hfw1, hS1, hE1, hd1, hG1, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner] | js_split)
  refine wp_getStrKey ?_
  js_until [] [hOP1, hOPlt1, hNP1, hNPlt1, hH1, hHlt1, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLP1, hLPlt1, hLPk, hLPon, hLPch, hfw1, hS1, hE1, hd1, hG1, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  refine ⟨_, rfl, ?_⟩
  simp only [hLPon]
  iterate 3 (first | js_go | js_norm [hOP1, hOPlt1, hNP1, hNPlt1, hH1, hHlt1, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLP1, hLPlt1, hLPk, hLPon, hLPch, hfw1, hS1, hE1, hd1, hG1, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner] | js_split)
  refine wp_callMemberT ?_
  js_until [] [hOP1, hOPlt1, hNP1, hNPlt1, hH1, hHlt1, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLP1, hLPlt1, hLPk, hLPon, hLPch, hfw1, hS1, hE1, hd1, hG1, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  refine ⟨LP, 2, rfl, by js_norm [PlainChain, reduceCtorEq, hOP1, hOPlt1, hNP1, hNPlt1, hH1, hHlt1, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLP1, hLPlt1, hLPk, hLPon, hLPch, hfw1, hS1, hE1, hd1, hG1, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]; intro _ hh; exact hh.elim, by decide,
    by js_norm [ordLookup, noAccessor, hOP1, hOPlt1, hNP1, hNPlt1, hH1, hHlt1, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLP1, hLPlt1, hLPk, hLPon, hLPch, hfw1, hS1, hE1, hd1, hG1, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner], ?_⟩
  js_norm [ordLookup, ownDataValue, hOP1, hOPlt1, hNP1, hNPlt1, hH1, hHlt1, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLP1, hLPlt1, hLPk, hLPon, hLPch, hfw1, hS1, hE1, hd1, hG1, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  js_until [] [hOP1, hOPlt1, hNP1, hNPlt1, hH1, hHlt1, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLP1, hLPlt1, hLPk, hLPon, hLPch, hfw1, hS1, hE1, hd1, hG1, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  refine ⟨by js_norm [CallableC, hOP1, hOPlt1, hNP1, hNPlt1, hH1, hHlt1, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLP1, hLPlt1, hLPk, hLPon, hLPch, hfw1, hS1, hE1, hd1, hG1, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner], ?_⟩
  refine wp_mono (hasOwn_spec (by js_norm [hOP1, hOPlt1, hNP1, hNPlt1, hH1, hHlt1, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLP1, hLPlt1, hLPk, hLPon, hLPch, hfw1, hS1, hE1, hd1, hG1, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]) (by js_norm [hOP1, hOPlt1, hNP1, hNPlt1, hH1, hHlt1, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLP1, hLPlt1, hLPk, hLPon, hLPch, hfw1, hS1, hE1, hd1, hG1, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]) hHfn (by js_norm [hOP1, hOPlt1, hNP1, hNPlt1, hH1, hHlt1, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLP1, hLPlt1, hLPk, hLPon, hLPch, hfw1, hS1, hE1, hd1, hG1, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]; omega)
    (by js_norm [hOP1, hOPlt1, hNP1, hNPlt1, hH1, hHlt1, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLP1, hLPlt1, hLPk, hLPon, hLPch, hfw1, hS1, hE1, hd1, hG1, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]) (by js_norm [hOP1, hOPlt1, hNP1, hNPlt1, hH1, hHlt1, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLP1, hLPlt1, hLPk, hLPon, hLPch, hfw1, hS1, hE1, hd1, hG1, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner])) ?_
  rintro v2 w2 h2 ⟨rfl, -, -, rfl, rfl⟩
  iterate 5 (first | js_go | js_norm [hOP1, hOPlt1, hNP1, hNPlt1, hH1, hHlt1, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLP1, hLPlt1, hLPk, hLPon, hLPch, hfw1, hS1, hE1, hd1, hG1, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner] | js_split)
  refine wp_neNullObj' (by js_norm [hOP1, hOPlt1, hNP1, hNPlt1, hH1, hHlt1, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLP1, hLPlt1, hLPk, hLPon, hLPch, hfw1, hS1, hE1, hd1, hG1, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]; omega) ?_
  iterate 2 (first | js_go | js_norm [hOP1, hOPlt1, hNP1, hNPlt1, hH1, hHlt1, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLP1, hLPlt1, hLPk, hLPon, hLPch, hfw1, hS1, hE1, hd1, hG1, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner] | js_split)
  refine wp_callMemberT ?_
  js_until [] [hOP1, hOPlt1, hNP1, hNPlt1, hH1, hHlt1, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLP1, hLPlt1, hLPk, hLPon, hLPch, hfw1, hS1, hE1, hd1, hG1, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  refine ⟨NP, 2, rfl, by js_norm [PlainChain, reduceCtorEq, hOP1, hOPlt1, hNP1, hNPlt1, hH1, hHlt1, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLP1, hLPlt1, hLPk, hLPon, hLPch, hfw1, hS1, hE1, hd1, hG1, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]; intro _ hh; exact hh.elim, by decide,
    by js_norm [ordLookup, noAccessor, hOP1, hOPlt1, hNP1, hNPlt1, hH1, hHlt1, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLP1, hLPlt1, hLPk, hLPon, hLPch, hfw1, hS1, hE1, hd1, hG1, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner], ?_⟩
  js_norm [ordLookup, ownDataValue, hOP1, hOPlt1, hNP1, hNPlt1, hH1, hHlt1, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLP1, hLPlt1, hLPk, hLPon, hLPch, hfw1, hS1, hE1, hd1, hG1, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  js_until [] [hOP1, hOPlt1, hNP1, hNPlt1, hH1, hHlt1, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLP1, hLPlt1, hLPk, hLPon, hLPch, hfw1, hS1, hE1, hd1, hG1, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  refine ⟨by js_norm [CallableC, hOP1, hOPlt1, hNP1, hNPlt1, hH1, hHlt1, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLP1, hLPlt1, hLPk, hLPon, hLPch, hfw1, hS1, hE1, hd1, hG1, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner], ?_⟩
  refine wp_mono (hasOwn_spec (by js_norm [hOP1, hOPlt1, hNP1, hNPlt1, hH1, hHlt1, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLP1, hLPlt1, hLPk, hLPon, hLPch, hfw1, hS1, hE1, hd1, hG1, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]) (by js_norm [hOP1, hOPlt1, hNP1, hNPlt1, hH1, hHlt1, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLP1, hLPlt1, hLPk, hLPon, hLPch, hfw1, hS1, hE1, hd1, hG1, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]) hHfn (by js_norm [hOP1, hOPlt1, hNP1, hNPlt1, hH1, hHlt1, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLP1, hLPlt1, hLPk, hLPon, hLPch, hfw1, hS1, hE1, hd1, hG1, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]; omega)
    (by js_norm [hOP1, hOPlt1, hNP1, hNPlt1, hH1, hHlt1, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLP1, hLPlt1, hLPk, hLPon, hLPch, hfw1, hS1, hE1, hd1, hG1, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]) (by js_norm [hOP1, hOPlt1, hNP1, hNPlt1, hH1, hHlt1, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLP1, hLPlt1, hLPk, hLPon, hLPch, hfw1, hS1, hE1, hd1, hG1, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner])) ?_
  rintro v3 w3 h3 ⟨rfl, -, -, rfl, rfl⟩
  js_until [] [hOP1, hOPlt1, hNP1, hNPlt1, hH1, hHlt1, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLP1, hLPlt1, hLPk, hLPon, hLPch, hfw1, hS1, hE1, hd1, hG1, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  -- loop 1, key children
  refine forIn_key (k := JSStr.ofString "children") (by omega) (by simp only [fuel_withFuel]; omega) (by decide) rfl
    (by simp only [Std.HashSet.contains_insert, Std.HashSet.contains_empty, Bool.or_false]; decide) ?_
  refine wp_of_eq (Obj'.getOwnProperty_entry LP _ _ (by simpa using hLPlt1) (by simp only [objEntry_withFuel, setEnv_objEntry, hLP1]; exact hLPk)) ?_
  simp only [objEntry_withFuel, setEnv_objEntry, hLP1, hLPch]
  refine ⟨_, rfl, rfl, ?_⟩
  refine wp_bindForVar (by show 8 ≤ _; simp only [fuel_withFuel]; omega) ?_
  js_norm [hOP1, hOPlt1, hNP1, hNPlt1, hH1, hHlt1, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLP1, hLPlt1, hLPk, hLPon, hLPch, hfw1, hS1, hE1, hd1, hG1, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  rw [UPBodies.body1_eval]
  simp only [UPBodies.body1Sem]
  iterate 5 (first | js_go | js_norm [hOP1, hOPlt1, hNP1, hNPlt1, hH1, hHlt1, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLP1, hLPlt1, hLPk, hLPon, hLPch, hfw1, hS1, hE1, hd1, hG1, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner] | js_split)
  refine wp_getStrKey ?_
  js_until [] [hOP1, hOPlt1, hNP1, hNPlt1, hH1, hHlt1, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLP1, hLPlt1, hLPk, hLPon, hLPch, hfw1, hS1, hE1, hd1, hG1, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  refine ⟨_, rfl, ?_⟩
  simp only [hLPch]
  iterate 3 (first | js_go | js_norm [hOP1, hOPlt1, hNP1, hNPlt1, hH1, hHlt1, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLP1, hLPlt1, hLPk, hLPon, hLPch, hfw1, hS1, hE1, hd1, hG1, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner] | js_split)
  refine wp_callMemberT ?_
  js_until [] [hOP1, hOPlt1, hNP1, hNPlt1, hH1, hHlt1, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLP1, hLPlt1, hLPk, hLPon, hLPch, hfw1, hS1, hE1, hd1, hG1, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  refine ⟨LP, 2, rfl, by js_norm [PlainChain, reduceCtorEq, hOP1, hOPlt1, hNP1, hNPlt1, hH1, hHlt1, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLP1, hLPlt1, hLPk, hLPon, hLPch, hfw1, hS1, hE1, hd1, hG1, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]; intro _ hh; exact hh.elim, by decide,
    by js_norm [ordLookup, noAccessor, hOP1, hOPlt1, hNP1, hNPlt1, hH1, hHlt1, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLP1, hLPlt1, hLPk, hLPon, hLPch, hfw1, hS1, hE1, hd1, hG1, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner], ?_⟩
  js_norm [ordLookup, ownDataValue, hOP1, hOPlt1, hNP1, hNPlt1, hH1, hHlt1, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLP1, hLPlt1, hLPk, hLPon, hLPch, hfw1, hS1, hE1, hd1, hG1, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  js_until [] [hOP1, hOPlt1, hNP1, hNPlt1, hH1, hHlt1, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLP1, hLPlt1, hLPk, hLPon, hLPch, hfw1, hS1, hE1, hd1, hG1, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  refine ⟨by js_norm [CallableC, hOP1, hOPlt1, hNP1, hNPlt1, hH1, hHlt1, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLP1, hLPlt1, hLPk, hLPon, hLPch, hfw1, hS1, hE1, hd1, hG1, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner], ?_⟩
  refine wp_mono (hasOwn_spec (by js_norm [hOP1, hOPlt1, hNP1, hNPlt1, hH1, hHlt1, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLP1, hLPlt1, hLPk, hLPon, hLPch, hfw1, hS1, hE1, hd1, hG1, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]) (by js_norm [hOP1, hOPlt1, hNP1, hNPlt1, hH1, hHlt1, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLP1, hLPlt1, hLPk, hLPon, hLPch, hfw1, hS1, hE1, hd1, hG1, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]) hHfn (by js_norm [hOP1, hOPlt1, hNP1, hNPlt1, hH1, hHlt1, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLP1, hLPlt1, hLPk, hLPon, hLPch, hfw1, hS1, hE1, hd1, hG1, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]; omega)
    (by js_norm [hOP1, hOPlt1, hNP1, hNPlt1, hH1, hHlt1, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLP1, hLPlt1, hLPk, hLPon, hLPch, hfw1, hS1, hE1, hd1, hG1, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]) (by js_norm [hOP1, hOPlt1, hNP1, hNPlt1, hH1, hHlt1, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLP1, hLPlt1, hLPk, hLPon, hLPch, hfw1, hS1, hE1, hd1, hG1, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner])) ?_
  rintro v2 w2 h2 ⟨rfl, -, -, rfl, rfl⟩
  iterate 5 (first | js_go | js_norm [hOP1, hOPlt1, hNP1, hNPlt1, hH1, hHlt1, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLP1, hLPlt1, hLPk, hLPon, hLPch, hfw1, hS1, hE1, hd1, hG1, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner] | js_split)
  refine wp_neNullStr (by js_norm [hOP1, hOPlt1, hNP1, hNPlt1, hH1, hHlt1, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLP1, hLPlt1, hLPk, hLPon, hLPch, hfw1, hS1, hE1, hd1, hG1, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]; omega) ?_
  iterate 2 (first | js_go | js_norm [hOP1, hOPlt1, hNP1, hNPlt1, hH1, hHlt1, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLP1, hLPlt1, hLPk, hLPon, hLPch, hfw1, hS1, hE1, hd1, hG1, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner] | js_split)
  refine wp_callMemberT ?_
  js_until [] [hOP1, hOPlt1, hNP1, hNPlt1, hH1, hHlt1, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLP1, hLPlt1, hLPk, hLPon, hLPch, hfw1, hS1, hE1, hd1, hG1, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  refine ⟨NP, 2, rfl, by js_norm [PlainChain, reduceCtorEq, hOP1, hOPlt1, hNP1, hNPlt1, hH1, hHlt1, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLP1, hLPlt1, hLPk, hLPon, hLPch, hfw1, hS1, hE1, hd1, hG1, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]; intro _ hh; exact hh.elim, by decide,
    by js_norm [ordLookup, noAccessor, hOP1, hOPlt1, hNP1, hNPlt1, hH1, hHlt1, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLP1, hLPlt1, hLPk, hLPon, hLPch, hfw1, hS1, hE1, hd1, hG1, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner], ?_⟩
  js_norm [ordLookup, ownDataValue, hOP1, hOPlt1, hNP1, hNPlt1, hH1, hHlt1, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLP1, hLPlt1, hLPk, hLPon, hLPch, hfw1, hS1, hE1, hd1, hG1, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  js_until [] [hOP1, hOPlt1, hNP1, hNPlt1, hH1, hHlt1, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLP1, hLPlt1, hLPk, hLPon, hLPch, hfw1, hS1, hE1, hd1, hG1, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  refine ⟨by js_norm [CallableC, hOP1, hOPlt1, hNP1, hNPlt1, hH1, hHlt1, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLP1, hLPlt1, hLPk, hLPon, hLPch, hfw1, hS1, hE1, hd1, hG1, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner], ?_⟩
  refine wp_mono (hasOwn_spec (by js_norm [hOP1, hOPlt1, hNP1, hNPlt1, hH1, hHlt1, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLP1, hLPlt1, hLPk, hLPon, hLPch, hfw1, hS1, hE1, hd1, hG1, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]) (by js_norm [hOP1, hOPlt1, hNP1, hNPlt1, hH1, hHlt1, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLP1, hLPlt1, hLPk, hLPon, hLPch, hfw1, hS1, hE1, hd1, hG1, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]) hHfn (by js_norm [hOP1, hOPlt1, hNP1, hNPlt1, hH1, hHlt1, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLP1, hLPlt1, hLPk, hLPon, hLPch, hfw1, hS1, hE1, hd1, hG1, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]; omega)
    (by js_norm [hOP1, hOPlt1, hNP1, hNPlt1, hH1, hHlt1, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLP1, hLPlt1, hLPk, hLPon, hLPch, hfw1, hS1, hE1, hd1, hG1, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]) (by js_norm [hOP1, hOPlt1, hNP1, hNPlt1, hH1, hHlt1, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLP1, hLPlt1, hLPk, hLPon, hLPch, hfw1, hS1, hE1, hd1, hG1, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner])) ?_
  rintro v3 w3 h3 ⟨rfl, -, -, rfl, rfl⟩
  js_until [] [hOP1, hOPlt1, hNP1, hNPlt1, hH1, hHlt1, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLP1, hLPlt1, hLPk, hLPon, hLPch, hfw1, hS1, hE1, hd1, hG1, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  -- loop 1: Object.prototype
  refine forIn_proto (by omega) (by simp only [fuel_withFuel]; omega) (by simp) ?_
  refine wp_of_eq (by unfold Obj'.getPrototypeOf; rw [maxDepth_eq]
                      exact getPrototypeOf_plain _ LP _ (by simpa using hLPlt1)
                        (by simp only [objEntry_withFuel, setEnv_objEntry, hLP1]; exact hLPk)) ?_
  simp only [objEntry_withFuel, setEnv_objEntry, hLP1, hLPp]
  refine forIn_enter (by omega) (by simp only [fuel_withFuel]; omega) ?_
  refine wp_of_eq (ownPropertyKeys_plain OP _ (by simpa using hOPlt1)
    (by simp only [objEntry_withFuel, setEnv_objEntry, hOP1]; exact hOPk)) ?_
  simp only [objEntry_withFuel, setEnv_objEntry, hOP1]
  generalize hks : Array.filter _ (orderedKeys _) = ks
  have hksn : ks.size ≤ 300 := by
    rw [← hks]; exact Nat.le_trans Array.size_filter_le (Nat.le_trans (orderedKeys_size _) (by omega))
  refine forIn_hidden ks.size 0 _ _ _ (by omega) (by omega) (by simp only [fuel_withFuel]; omega)
    (by simpa using hOPlt1) (by simp only [objEntry_withFuel, setEnv_objEntry, hOP1]; exact hOPk)
    (fun j hj _ p hp => hOPne _ p (by simpa only [objEntry_withFuel, setEnv_objEntry, hOP1] using hp)) ?_
  intro vis'
  refine forIn_proto (by omega) (by simp only [fuel_withFuel]; omega) (Nat.le_refl _) ?_
  refine wp_of_eq (by unfold Obj'.getPrototypeOf; rw [maxDepth_eq]
                      exact getPrototypeOf_plain _ OP _ (by simpa using hOPlt1)
                        (by simp only [objEntry_withFuel, setEnv_objEntry, hOP1]; exact hOPk)) ?_
  simp only [objEntry_withFuel, setEnv_objEntry, hOP1, hOPp]
  refine forIn_end (by omega) (by simp only [fuel_withFuel]; omega) (by intro o hh; cases hh) ?_
  js_until [] [hOP1, hOPlt1, hNP1, hNPlt1, hH1, hHlt1, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLP1, hLPlt1, hLPk, hLPon, hLPch, hfw1, hS1, hE1, hd1, hG1, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  -- loop 2: for (lastProp in nextProps)
  have hse01 : isStrictlyEqual (.obj f1) (.obj f0) = false := by simp [isStrictlyEqual, sameValue, hf01]
  refine wp_forInStmt (by intro x ie hh; cases hh) ?_
  rw [show (999984 + 12 : Nat) = 999995 + 1 from rfl]
  simp only [evalForHead]
  refine (show ∀ c, evalExpr 999995 c (Expr.ident (JSStr.ofString "nextProps")) = Sem.ident (JSStr.ofString "nextProps") c
    from fun _ => rfl) _ ▸ ?_
  js_until [] [hSP1, hSPlt1, Ne.symm e1, hGSP, hGSPv, hSPo, hSPk, hse01, hOP1, hOPlt1, hNP1, hNPlt1, hH1, hHlt1, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLP1, hLPlt1, hLPk, hLPon, hLPch, hfw1, hS1, hE1, hd1, hG1, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  refine ⟨NP, rfl, ?_⟩
  rw [← UPBodies.body2Stmt.eq_1]
  refine forIn_enter (by omega) (by simp only [fuel_withFuel]; omega) ?_
  refine wp_of_eq (ownPropertyKeys_plain NP _ (by simpa using hNPlt1)
    (by simp only [objEntry_withFuel, setEnv_objEntry, hNP1]; exact hNPk)) ?_
  simp only [objEntry_withFuel, setEnv_objEntry, hNP1, hNPkeys]
  generalize hks2 : Array.filter _ (orderedKeys _) = ks2
  obtain rfl : ks2 = #[PropKey.str (JSStr.ofString "onClick"), PropKey.str (JSStr.ofString "children")] := by
    rw [← hks2]; decide +kernel
  rw [show (999995 + 1 : Nat) = 999984 + 12 from rfl]
  -- loop 2, key onClick
  refine forIn_key (k := JSStr.ofString "onClick") (by omega) (by simp only [fuel_withFuel]; omega) (by decide) rfl
    (by simp) ?_
  refine wp_of_eq (Obj'.getOwnProperty_entry NP _ _ (by simpa using hNPlt1) (by simp only [objEntry_withFuel, setEnv_objEntry, hNP1]; exact hNPk)) ?_
  simp only [objEntry_withFuel, setEnv_objEntry, hNP1, hNPon]
  refine ⟨_, rfl, rfl, ?_⟩
  refine wp_bindForPat (by show 8 ≤ _; simp only [fuel_withFuel]; omega) ?_
  js_norm [hSP1, hSPlt1, Ne.symm e1, hGSP, hGSPv, hSPo, hSPk, hse01, hOP1, hOPlt1, hNP1, hNPlt1, hH1, hHlt1, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLP1, hLPlt1, hLPk, hLPon, hLPch, hfw1, hS1, hE1, hd1, hG1, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  rw [UPBodies.body2_eval]
  simp only [UPBodies.body2Sem]
  iterate 5 (first | js_go | js_norm [hSP1, hSPlt1, Ne.symm e1, hGSP, hGSPv, hSPo, hSPk, hse01, hOP1, hOPlt1, hNP1, hNPlt1, hH1, hHlt1, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLP1, hLPlt1, hLPk, hLPon, hLPch, hfw1, hS1, hE1, hd1, hG1, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner] | js_split)
  refine wp_getStrKey ?_
  js_until [] [hSP1, hSPlt1, Ne.symm e1, hGSP, hGSPv, hSPo, hSPk, hse01, hOP1, hOPlt1, hNP1, hNPlt1, hH1, hHlt1, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLP1, hLPlt1, hLPk, hLPon, hLPch, hfw1, hS1, hE1, hd1, hG1, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  refine ⟨_, rfl, ?_⟩
  simp only [hNPon]
  iterate 2 (first | js_go | js_norm [hSP1, hSPlt1, Ne.symm e1, hGSP, hGSPv, hSPo, hSPk, hse01, hOP1, hOPlt1, hNP1, hNPlt1, hH1, hHlt1, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLP1, hLPlt1, hLPk, hLPon, hLPch, hfw1, hS1, hE1, hd1, hG1, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner] | js_split)
  refine wp_getStrKey ?_
  js_until [] [hSP1, hSPlt1, Ne.symm e1, hGSP, hGSPv, hSPo, hSPk, hse01, hOP1, hOPlt1, hNP1, hNPlt1, hH1, hHlt1, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLP1, hLPlt1, hLPk, hLPon, hLPch, hfw1, hS1, hE1, hd1, hG1, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  refine ⟨_, rfl, ?_⟩
  simp only [hLPon]
  iterate 4 (first | js_go | js_norm [hSP1, hSPlt1, Ne.symm e1, hGSP, hGSPv, hSPo, hSPk, hse01, hOP1, hOPlt1, hNP1, hNPlt1, hH1, hHlt1, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLP1, hLPlt1, hLPk, hLPon, hLPch, hfw1, hS1, hE1, hd1, hG1, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner] | js_split)
  refine wp_callMemberT ?_
  js_until [] [hSP1, hSPlt1, Ne.symm e1, hGSP, hGSPv, hSPo, hSPk, hse01, hOP1, hOPlt1, hNP1, hNPlt1, hH1, hHlt1, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLP1, hLPlt1, hLPk, hLPon, hLPch, hfw1, hS1, hE1, hd1, hG1, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  refine ⟨NP, 2, rfl, by js_norm [PlainChain, reduceCtorEq, hse01, hOP1, hOPlt1, hNP1, hNPlt1, hH1, hHlt1, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLP1, hLPlt1, hLPk, hLPon, hLPch, hfw1, hS1, hE1, hd1, hG1, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]; intro _ hh; exact hh.elim, by decide,
    by js_norm [ordLookup, noAccessor, hse01, hOP1, hOPlt1, hNP1, hNPlt1, hH1, hHlt1, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLP1, hLPlt1, hLPk, hLPon, hLPch, hfw1, hS1, hE1, hd1, hG1, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner], ?_⟩
  js_norm [ordLookup, ownDataValue, hse01, hOP1, hOPlt1, hNP1, hNPlt1, hH1, hHlt1, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLP1, hLPlt1, hLPk, hLPon, hLPch, hfw1, hS1, hE1, hd1, hG1, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  js_until [] [hSP1, hSPlt1, Ne.symm e1, hGSP, hGSPv, hSPo, hSPk, hse01, hOP1, hOPlt1, hNP1, hNPlt1, hH1, hHlt1, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLP1, hLPlt1, hLPk, hLPon, hLPch, hfw1, hS1, hE1, hd1, hG1, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  refine ⟨by js_norm [CallableC, hse01, hOP1, hOPlt1, hNP1, hNPlt1, hH1, hHlt1, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLP1, hLPlt1, hLPk, hLPon, hLPch, hfw1, hS1, hE1, hd1, hG1, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner], ?_⟩
  refine wp_mono (hasOwn_spec (by js_norm [hSP1, hSPlt1, Ne.symm e1, hGSP, hGSPv, hSPo, hSPk, hse01, hOP1, hOPlt1, hNP1, hNPlt1, hH1, hHlt1, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLP1, hLPlt1, hLPk, hLPon, hLPch, hfw1, hS1, hE1, hd1, hG1, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]) (by js_norm [hSP1, hSPlt1, Ne.symm e1, hGSP, hGSPv, hSPo, hSPk, hse01, hOP1, hOPlt1, hNP1, hNPlt1, hH1, hHlt1, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLP1, hLPlt1, hLPk, hLPon, hLPch, hfw1, hS1, hE1, hd1, hG1, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]) hHfn (by js_norm [hSP1, hSPlt1, Ne.symm e1, hGSP, hGSPv, hSPo, hSPk, hse01, hOP1, hOPlt1, hNP1, hNPlt1, hH1, hHlt1, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLP1, hLPlt1, hLPk, hLPon, hLPch, hfw1, hS1, hE1, hd1, hG1, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]; omega)
    (by js_norm [hSP1, hSPlt1, Ne.symm e1, hGSP, hGSPv, hSPo, hSPk, hse01, hOP1, hOPlt1, hNP1, hNPlt1, hH1, hHlt1, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLP1, hLPlt1, hLPk, hLPon, hLPch, hfw1, hS1, hE1, hd1, hG1, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]) (by js_norm [hSP1, hSPlt1, Ne.symm e1, hGSP, hGSPv, hSPo, hSPk, hse01, hOP1, hOPlt1, hNP1, hNPlt1, hH1, hHlt1, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLP1, hLPlt1, hLPk, hLPon, hLPch, hfw1, hS1, hE1, hd1, hG1, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner])) ?_
  rintro v2 w2 h2 ⟨rfl, -, -, rfl, rfl⟩
  iterate 9 (first | js_go | js_norm [hSP1, hSPlt1, Ne.symm e1, hGSP, hGSPv, hSPo, hSPk, hse01, hOP1, hOPlt1, hNP1, hNPlt1, hH1, hHlt1, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLP1, hLPlt1, hLPk, hLPon, hLPch, hfw1, hS1, hE1, hd1, hG1, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner] | js_split)
  iterate 4 (first | js_go | js_norm [hSP1, hSPlt1, Ne.symm e1, hGSP, hGSPv, hSPo, hSPk, hse01, hOP1, hOPlt1, hNP1, hNPlt1, hH1, hHlt1, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLP1, hLPlt1, hLPk, hLPon, hLPch, hfw1, hS1, hE1, hd1, hG1, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner] | js_split)
  refine wp_eqNullObj (by js_norm [hSP1, hSPlt1, Ne.symm e1, hGSP, hGSPv, hSPo, hSPk, hse01, hOP1, hOPlt1, hNP1, hNPlt1, hH1, hHlt1, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLP1, hLPlt1, hLPk, hLPon, hLPch, hfw1, hS1, hE1, hd1, hG1, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]; omega) ?_
  js_until [] [hSP1, hSPlt1, Ne.symm e1, hGSP, hGSPv, hSPo, hSPk, hse01, hOP1, hOPlt1, hNP1, hNPlt1, hH1, hHlt1, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLP1, hLPlt1, hLPk, hLPon, hLPch, hfw1, hS1, hE1, hd1, hG1, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  refine ⟨by js_norm [CallableC, hSP1, hSPlt1, Ne.symm e1, hGSP, hGSPv, hSPo, hSPk, hse01, hOP1, hOPlt1, hNP1, hNPlt1, hH1, hHlt1, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLP1, hLPlt1, hLPk, hLPon, hLPch, hfw1, hS1, hE1, hd1, hG1, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner], ?_⟩
  refine wp_mono (ReactSetProp.onClick_spec (bG := bG) (oG := oG) (R := R1) (by js_norm [hSP1, hSPlt1, Ne.symm e1, hGSP, hGSPv, hSPo, hSPk, hse01, hOP1, hOPlt1, hNP1, hNPlt1, hH1, hHlt1, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLP1, hLPlt1, hLPk, hLPon, hLPch, hfw1, hS1, hE1, hd1, hG1, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]) (by js_norm [hSP1, hSPlt1, Ne.symm e1, hGSP, hGSPv, hSPo, hSPk, hse01, hOP1, hOPlt1, hNP1, hNPlt1, hH1, hHlt1, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLP1, hLPlt1, hLPk, hLPon, hLPch, hfw1, hS1, hE1, hd1, hG1, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner])
    (by js_norm [hSP1, hSPlt1, Ne.symm e1, hGSP, hGSPv, hSPo, hSPk, hse01, hOP1, hOPlt1, hNP1, hNPlt1, hH1, hHlt1, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLP1, hLPlt1, hLPk, hLPon, hLPch, hfw1, hS1, hE1, hd1, hG1, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]; omega) hSPcode hSPcls hSPmode (by rw [hSPenv]; js_norm [hSP1, hSPlt1, Ne.symm e1, hGSP, hGSPv, hSPo, hSPk, hse01, hOP1, hOPlt1, hNP1, hNPlt1, hH1, hHlt1, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLP1, hLPlt1, hLPk, hLPon, hLPch, hfw1, hS1, hE1, hd1, hG1, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner])
    (by rw [hSPenv]; js_norm [hSP1, hSPlt1, Ne.symm e1, hGSP, hGSPv, hSPo, hSPk, hse01, hOP1, hOPlt1, hNP1, hNPlt1, hH1, hHlt1, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLP1, hLPlt1, hLPk, hLPon, hLPch, hfw1, hS1, hE1, hd1, hG1, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]) hGN hGNv
    (fun w h1 hw => hOC w h1 (frame_empty_trans (by frame_go' [*]) hw))) ?_
  rintro v4 w4 h4 ⟨rfl, hR1, hF4, hfu4⟩
  have hFs4 : Frame {} s w4 := frame_empty_trans (by frame_go' [*]) hF4
  have hLP4 : w4.objEntry LP = s.objEntry LP := objEntry_frame0 hFs4 hLPlt
  have hLPlt4 : LP < w4.heap.size := Nat.lt_of_lt_of_le hLPlt hFs4.heap_le
  have hNP4 : w4.objEntry NP = s.objEntry NP := objEntry_frame0 hFs4 hNPlt
  have hNPlt4 : NP < w4.heap.size := Nat.lt_of_lt_of_le hNPlt hFs4.heap_le
  have hOP4 : w4.objEntry OP = s.objEntry OP := objEntry_frame0 hFs4 hOPlt
  have hOPlt4 : OP < w4.heap.size := Nat.lt_of_lt_of_le hOPlt hFs4.heap_le
  have hH4 : w4.objEntry fH = s.objEntry fH := objEntry_frame0 hFs4 hHlt
  have hHlt4 : fH < w4.heap.size := Nat.lt_of_lt_of_le hHlt hFs4.heap_le
  have hSP4 : w4.objEntry fSP = s.objEntry fSP := objEntry_frame0 hFs4 hSPo
  have hSPlt4 : fSP < w4.heap.size := Nat.lt_of_lt_of_le hSPo hFs4.heap_le
  have hS4' : w4.objEntry fS = s.objEntry fS := objEntry_frame0 hFs4 hSo
  have hSlt4 : fS < w4.heap.size := Nat.lt_of_lt_of_le hSo hFs4.heap_le
  have hd4 : Scope.declLike? (w4.envEntry d.env) = some (bG, oG) := by rw [envEntry_frame0 hFs4 hG]; exact hGe
  have hG4 : d.env < w4.envs.size := Nat.lt_of_lt_of_le hG hFs4.envs_le
  have hE4 := envEntry_frame0 hF4 (e := s.envs.size) (by js_norm [hSP1, hSPlt1, Ne.symm e1, hGSP, hGSPv, hSPo, hSPk, hse01, hOP1, hOPlt1, hNP1, hNPlt1, hH1, hHlt1, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLP1, hLPlt1, hLPk, hLPon, hLPch, hfw1, hS1, hE1, hd1, hG1, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner])
  have hS4 : s.envs.size < w4.envs.size := Nat.lt_of_lt_of_le (by js_norm [hSP1, hSPlt1, Ne.symm e1, hGSP, hGSPv, hSPo, hSPk, hse01, hOP1, hOPlt1, hNP1, hNPlt1, hH1, hHlt1, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLP1, hLPlt1, hLPk, hLPon, hLPch, hfw1, hS1, hE1, hd1, hG1, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]) hF4.envs_le
  have hfw4 : 1500 ≤ w4.fuel := by simp only [fuel_withFuel, State.setEnv_fuel] at hfu4; omega
  have hfr4 : w1.fuel ≤ w4.fuel + 400 := by simp only [fuel_withFuel, State.setEnv_fuel] at hfu4; omega
  have hst01 : isStrictlyEqual (.str t1) (.str t0) = false := by simp [isStrictlyEqual, sameValue, ht01]
  clear hfu4 hF4
  -- loop 2, key children
  refine forIn_key (k := JSStr.ofString "children") (by omega) (by omega) (by decide) rfl
    (by simp only [Std.HashSet.contains_insert, Std.HashSet.contains_empty, Bool.or_false]; decide) ?_
  refine wp_of_eq (Obj'.getOwnProperty_entry NP _ _ (by simpa using hNPlt4) (by simp only [objEntry_withFuel, hNP4]; exact hNPk)) ?_
  simp only [objEntry_withFuel, hNP4, hNPch]
  refine ⟨_, rfl, rfl, ?_⟩
  refine wp_bindForPat (by show 8 ≤ _; simp only [fuel_withFuel]; omega) ?_
  js_norm [hst01, hS1, hE1, hfw1, hSP4, hSPlt4, hLP4, hLPlt4, hNP4, hNPlt4, hOP4, hOPlt4, hH4, hHlt4, hS4', hSlt4, hfw4, hS4, hE4, hd4, hG4, Ne.symm e1, hGSP, hGSPv, hGS, hGSv, hSPo, hSPk, hSo, hSk, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLPk, hLPon, hLPch, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  rw [UPBodies.body2_eval]
  simp only [UPBodies.body2Sem]
  iterate 5 (first | js_go | js_norm [hst01, hS1, hE1, hfw1, hSP4, hSPlt4, hLP4, hLPlt4, hNP4, hNPlt4, hOP4, hOPlt4, hH4, hHlt4, hS4', hSlt4, hfw4, hS4, hE4, hd4, hG4, Ne.symm e1, hGSP, hGSPv, hGS, hGSv, hSPo, hSPk, hSo, hSk, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLPk, hLPon, hLPch, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner] | js_split)
  refine wp_getStrKey ?_
  js_until [] [hst01, hS1, hE1, hfw1, hSP4, hSPlt4, hLP4, hLPlt4, hNP4, hNPlt4, hOP4, hOPlt4, hH4, hHlt4, hS4', hSlt4, hfw4, hS4, hE4, hd4, hG4, Ne.symm e1, hGSP, hGSPv, hGS, hGSv, hSPo, hSPk, hSo, hSk, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLPk, hLPon, hLPch, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  refine ⟨_, rfl, ?_⟩
  simp only [hNPch]
  iterate 2 (first | js_go | js_norm [hst01, hS1, hE1, hfw1, hSP4, hSPlt4, hLP4, hLPlt4, hNP4, hNPlt4, hOP4, hOPlt4, hH4, hHlt4, hS4', hSlt4, hfw4, hS4, hE4, hd4, hG4, Ne.symm e1, hGSP, hGSPv, hGS, hGSv, hSPo, hSPk, hSo, hSk, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLPk, hLPon, hLPch, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner] | js_split)
  refine wp_getStrKey ?_
  js_until [] [hst01, hS1, hE1, hfw1, hSP4, hSPlt4, hLP4, hLPlt4, hNP4, hNPlt4, hOP4, hOPlt4, hH4, hHlt4, hS4', hSlt4, hfw4, hS4, hE4, hd4, hG4, Ne.symm e1, hGSP, hGSPv, hGS, hGSv, hSPo, hSPk, hSo, hSk, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLPk, hLPon, hLPch, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  refine ⟨_, rfl, ?_⟩
  simp only [hLPch]
  iterate 4 (first | js_go | js_norm [hst01, hS1, hE1, hfw1, hSP4, hSPlt4, hLP4, hLPlt4, hNP4, hNPlt4, hOP4, hOPlt4, hH4, hHlt4, hS4', hSlt4, hfw4, hS4, hE4, hd4, hG4, Ne.symm e1, hGSP, hGSPv, hGS, hGSv, hSPo, hSPk, hSo, hSk, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLPk, hLPon, hLPch, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner] | js_split)
  refine wp_callMemberT ?_
  js_until [] [hst01, hS1, hE1, hfw1, hSP4, hSPlt4, hLP4, hLPlt4, hNP4, hNPlt4, hOP4, hOPlt4, hH4, hHlt4, hS4', hSlt4, hfw4, hS4, hE4, hd4, hG4, Ne.symm e1, hGSP, hGSPv, hGS, hGSv, hSPo, hSPk, hSo, hSk, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLPk, hLPon, hLPch, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  refine ⟨NP, 2, rfl, by js_norm [PlainChain, reduceCtorEq, hst01, hS1, hE1, hfw1, hSP4, hSPlt4, hLP4, hLPlt4, hNP4, hNPlt4, hOP4, hOPlt4, hH4, hHlt4, hS4', hSlt4, hfw4, hS4, hE4, hd4, hG4, Ne.symm e1, hGSP, hGSPv, hGS, hGSv, hSPo, hSPk, hSo, hSk, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLPk, hLPon, hLPch, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]; intro _ hh; exact hh.elim, by decide,
    by js_norm [ordLookup, noAccessor, hst01, hS1, hE1, hfw1, hSP4, hSPlt4, hLP4, hLPlt4, hNP4, hNPlt4, hOP4, hOPlt4, hH4, hHlt4, hS4', hSlt4, hfw4, hS4, hE4, hd4, hG4, Ne.symm e1, hGSP, hGSPv, hGS, hGSv, hSPo, hSPk, hSo, hSk, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLPk, hLPon, hLPch, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner], ?_⟩
  js_norm [ordLookup, ownDataValue, hst01, hS1, hE1, hfw1, hSP4, hSPlt4, hLP4, hLPlt4, hNP4, hNPlt4, hOP4, hOPlt4, hH4, hHlt4, hS4', hSlt4, hfw4, hS4, hE4, hd4, hG4, Ne.symm e1, hGSP, hGSPv, hGS, hGSv, hSPo, hSPk, hSo, hSk, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLPk, hLPon, hLPch, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  js_until [] [hst01, hS1, hE1, hfw1, hSP4, hSPlt4, hLP4, hLPlt4, hNP4, hNPlt4, hOP4, hOPlt4, hH4, hHlt4, hS4', hSlt4, hfw4, hS4, hE4, hd4, hG4, Ne.symm e1, hGSP, hGSPv, hGS, hGSv, hSPo, hSPk, hSo, hSk, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLPk, hLPon, hLPch, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  refine ⟨by js_norm [CallableC, hst01, hS1, hE1, hfw1, hSP4, hSPlt4, hLP4, hLPlt4, hNP4, hNPlt4, hOP4, hOPlt4, hH4, hHlt4, hS4', hSlt4, hfw4, hS4, hE4, hd4, hG4, Ne.symm e1, hGSP, hGSPv, hGS, hGSv, hSPo, hSPk, hSo, hSk, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLPk, hLPon, hLPch, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner], ?_⟩
  refine wp_mono (hasOwn_spec (by js_norm [hst01, hS1, hE1, hfw1, hSP4, hSPlt4, hLP4, hLPlt4, hNP4, hNPlt4, hOP4, hOPlt4, hH4, hHlt4, hS4', hSlt4, hfw4, hS4, hE4, hd4, hG4, Ne.symm e1, hGSP, hGSPv, hGS, hGSv, hSPo, hSPk, hSo, hSk, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLPk, hLPon, hLPch, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]) (by js_norm [hst01, hS1, hE1, hfw1, hSP4, hSPlt4, hLP4, hLPlt4, hNP4, hNPlt4, hOP4, hOPlt4, hH4, hHlt4, hS4', hSlt4, hfw4, hS4, hE4, hd4, hG4, Ne.symm e1, hGSP, hGSPv, hGS, hGSv, hSPo, hSPk, hSo, hSk, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLPk, hLPon, hLPch, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]) hHfn (by js_norm [hst01, hS1, hE1, hfw1, hSP4, hSPlt4, hLP4, hLPlt4, hNP4, hNPlt4, hOP4, hOPlt4, hH4, hHlt4, hS4', hSlt4, hfw4, hS4, hE4, hd4, hG4, Ne.symm e1, hGSP, hGSPv, hGS, hGSv, hSPo, hSPk, hSo, hSk, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLPk, hLPon, hLPch, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]; omega)
    (by js_norm [hst01, hS1, hE1, hfw1, hSP4, hSPlt4, hLP4, hLPlt4, hNP4, hNPlt4, hOP4, hOPlt4, hH4, hHlt4, hS4', hSlt4, hfw4, hS4, hE4, hd4, hG4, Ne.symm e1, hGSP, hGSPv, hGS, hGSv, hSPo, hSPk, hSo, hSk, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLPk, hLPon, hLPch, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]) (by js_norm [hst01, hS1, hE1, hfw1, hSP4, hSPlt4, hLP4, hLPlt4, hNP4, hNPlt4, hOP4, hOPlt4, hH4, hHlt4, hS4', hSlt4, hfw4, hS4, hE4, hd4, hG4, Ne.symm e1, hGSP, hGSPv, hGS, hGSv, hSPo, hSPk, hSo, hSk, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLPk, hLPon, hLPch, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner])) ?_
  rintro v5 w5 h5 ⟨rfl, -, -, rfl, rfl⟩
  iterate 9 (first | js_go | js_norm [hst01, hS1, hE1, hfw1, hSP4, hSPlt4, hLP4, hLPlt4, hNP4, hNPlt4, hOP4, hOPlt4, hH4, hHlt4, hS4', hSlt4, hfw4, hS4, hE4, hd4, hG4, Ne.symm e1, hGSP, hGSPv, hGS, hGSv, hSPo, hSPk, hSo, hSk, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLPk, hLPon, hLPch, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner] | js_split)
  iterate 4 (first | js_go | js_norm [hst01, hS1, hE1, hfw1, hSP4, hSPlt4, hLP4, hLPlt4, hNP4, hNPlt4, hOP4, hOPlt4, hH4, hHlt4, hS4', hSlt4, hfw4, hS4, hE4, hd4, hG4, Ne.symm e1, hGSP, hGSPv, hGS, hGSv, hSPo, hSPk, hSo, hSk, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLPk, hLPon, hLPch, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner] | js_split)
  refine wp_eqNullStr (by js_norm [hst01, hS1, hE1, hfw1, hSP4, hSPlt4, hLP4, hLPlt4, hNP4, hNPlt4, hOP4, hOPlt4, hH4, hHlt4, hS4', hSlt4, hfw4, hS4, hE4, hd4, hG4, Ne.symm e1, hGSP, hGSPv, hGS, hGSv, hSPo, hSPk, hSo, hSk, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLPk, hLPon, hLPch, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]; omega) ?_
  js_until [] [hst01, hS1, hE1, hfw1, hSP4, hSPlt4, hLP4, hLPlt4, hNP4, hNPlt4, hOP4, hOPlt4, hH4, hHlt4, hS4', hSlt4, hfw4, hS4, hE4, hd4, hG4, Ne.symm e1, hGSP, hGSPv, hGS, hGSv, hSPo, hSPk, hSo, hSk, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLPk, hLPon, hLPch, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  refine ⟨by js_norm [CallableC, hst01, hS1, hE1, hfw1, hSP4, hSPlt4, hLP4, hLPlt4, hNP4, hNPlt4, hOP4, hOPlt4, hH4, hHlt4, hS4', hSlt4, hfw4, hS4, hE4, hd4, hG4, Ne.symm e1, hGSP, hGSPv, hGS, hGSv, hSPo, hSPk, hSo, hSk, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLPk, hLPon, hLPch, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner], ?_⟩
  refine wp_mono (ReactSetProp.children_spec (bG := bG) (oG := oG) (R := R2) (by js_norm [hst01, hS1, hE1, hfw1, hSP4, hSPlt4, hLP4, hLPlt4, hNP4, hNPlt4, hOP4, hOPlt4, hH4, hHlt4, hS4', hSlt4, hfw4, hS4, hE4, hd4, hG4, Ne.symm e1, hGSP, hGSPv, hGS, hGSv, hSPo, hSPk, hSo, hSk, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLPk, hLPon, hLPch, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]) (by js_norm [hst01, hS1, hE1, hfw1, hSP4, hSPlt4, hLP4, hLPlt4, hNP4, hNPlt4, hOP4, hOPlt4, hH4, hHlt4, hS4', hSlt4, hfw4, hS4, hE4, hd4, hG4, Ne.symm e1, hGSP, hGSPv, hGS, hGSv, hSPo, hSPk, hSo, hSk, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLPk, hLPon, hLPch, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner])
    (by js_norm [hst01, hS1, hE1, hfw1, hSP4, hSPlt4, hLP4, hLPlt4, hNP4, hNPlt4, hOP4, hOPlt4, hH4, hHlt4, hS4', hSlt4, hfw4, hS4, hE4, hd4, hG4, Ne.symm e1, hGSP, hGSPv, hGS, hGSv, hSPo, hSPk, hSo, hSk, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLPk, hLPon, hLPch, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]; omega) hSPcode hSPcls hSPmode (by rw [hSPenv]; js_norm [hst01, hS1, hE1, hfw1, hSP4, hSPlt4, hLP4, hLPlt4, hNP4, hNPlt4, hOP4, hOPlt4, hH4, hHlt4, hS4', hSlt4, hfw4, hS4, hE4, hd4, hG4, Ne.symm e1, hGSP, hGSPv, hGS, hGSv, hSPo, hSPk, hSo, hSk, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLPk, hLPon, hLPch, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner])
    (by rw [hSPenv]; js_norm [hst01, hS1, hE1, hfw1, hSP4, hSPlt4, hLP4, hLPlt4, hNP4, hNPlt4, hOP4, hOPlt4, hH4, hHlt4, hS4', hSlt4, hfw4, hS4, hE4, hd4, hG4, Ne.symm e1, hGSP, hGSPv, hGS, hGSv, hSPo, hSPk, hSo, hSk, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLPk, hLPon, hLPch, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]) hGS hGSv hGV hGVm hGVi (by js_norm [hst01, hS1, hE1, hfw1, hSP4, hSPlt4, hLP4, hLPlt4, hNP4, hNPlt4, hOP4, hOPlt4, hH4, hHlt4, hS4', hSlt4, hfw4, hS4, hE4, hd4, hG4, Ne.symm e1, hGSP, hGSPv, hGS, hGSv, hSPo, hSPk, hSo, hSk, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLPk, hLPon, hLPch, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]) (by js_norm [hst01, hS1, hE1, hfw1, hSP4, hSPlt4, hLP4, hLPlt4, hNP4, hNPlt4, hOP4, hOPlt4, hH4, hHlt4, hS4', hSlt4, hfw4, hS4, hE4, hd4, hG4, Ne.symm e1, hGSP, hGSPv, hGS, hGSv, hSPo, hSPk, hSo, hSk, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLPk, hLPon, hLPch, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]) hScode hScls hSmode
    htext (fun w h1 hw => hFC w h1 (frame_empty_trans (by frame_go' [*]) hw))
    (fun w h1 hw => hLC w h1 (frame_empty_trans (by frame_go' [*]) hw))
    (fun w h1 hw => hNT w h1 (frame_empty_trans (by frame_go' [*]) hw))
    (fun w h1 hw => hNV w h1 (frame_empty_trans (by frame_go' [*]) hw))) ?_
  rintro v6 w6 h6 ⟨rfl, hR2, hfu6, hF6, bm6, hbm6, hVT6, hrest6⟩
  have hNP6 : w6.objEntry NP = s.objEntry NP := by
    rw [hF6.obj_eq NP (by js_norm [hst01, hS1, hE1, hfw1, hSP4, hSPlt4, hLP4, hLPlt4, hNP4, hNPlt4, hOP4, hOPlt4, hH4, hHlt4, hS4', hSlt4, hfw4, hS4, hE4, hd4, hG4, Ne.symm e1, hGSP, hGSPv, hGS, hGSv, hSPo, hSPk, hSo, hSk, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLPk, hLPon, hLPch, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]) (fun _ hh => by simp at hh)]; js_norm [hst01, hS1, hE1, hfw1, hSP4, hSPlt4, hLP4, hLPlt4, hNP4, hNPlt4, hOP4, hOPlt4, hH4, hHlt4, hS4', hSlt4, hfw4, hS4, hE4, hd4, hG4, Ne.symm e1, hGSP, hGSPv, hGS, hGSv, hSPo, hSPk, hSo, hSk, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLPk, hLPon, hLPch, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  have hNPlt6 : NP < w6.heap.size := Nat.lt_of_lt_of_le (by js_norm [hst01, hS1, hE1, hfw1, hSP4, hSPlt4, hLP4, hLPlt4, hNP4, hNPlt4, hOP4, hOPlt4, hH4, hHlt4, hS4', hSlt4, hfw4, hS4, hE4, hd4, hG4, Ne.symm e1, hGSP, hGSPv, hGS, hGSv, hSPo, hSPk, hSo, hSk, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLPk, hLPon, hLPch, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]) hF6.heap_le
  have hOP6 : w6.objEntry OP = s.objEntry OP := by
    rw [hF6.obj_eq OP (by js_norm [hst01, hS1, hE1, hfw1, hSP4, hSPlt4, hLP4, hLPlt4, hNP4, hNPlt4, hOP4, hOPlt4, hH4, hHlt4, hS4', hSlt4, hfw4, hS4, hE4, hd4, hG4, Ne.symm e1, hGSP, hGSPv, hGS, hGSv, hSPo, hSPk, hSo, hSk, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLPk, hLPon, hLPch, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]) (fun _ hh => by simp at hh)]; js_norm [hst01, hS1, hE1, hfw1, hSP4, hSPlt4, hLP4, hLPlt4, hNP4, hNPlt4, hOP4, hOPlt4, hH4, hHlt4, hS4', hSlt4, hfw4, hS4, hE4, hd4, hG4, Ne.symm e1, hGSP, hGSPv, hGS, hGSv, hSPo, hSPk, hSo, hSk, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLPk, hLPon, hLPch, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  have hOPlt6 : OP < w6.heap.size := Nat.lt_of_lt_of_le (by js_norm [hst01, hS1, hE1, hfw1, hSP4, hSPlt4, hLP4, hLPlt4, hNP4, hNPlt4, hOP4, hOPlt4, hH4, hHlt4, hS4', hSlt4, hfw4, hS4, hE4, hd4, hG4, Ne.symm e1, hGSP, hGSPv, hGS, hGSv, hSPo, hSPk, hSo, hSk, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLPk, hLPon, hLPch, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]) hF6.heap_le
  have hfw6 : 1400 ≤ w6.fuel := by simp only [fuel_withFuel, State.setEnv_fuel] at hfu6; omega
  have hfr6 : w4.fuel ≤ w6.fuel + 100 := by simp only [fuel_withFuel, State.setEnv_fuel] at hfu6; omega
  -- loop 2: Object.prototype
  refine forIn_proto (by omega) (by omega) (by simp) ?_
  refine wp_of_eq (by unfold Obj'.getPrototypeOf; rw [maxDepth_eq]
                      exact getPrototypeOf_plain _ NP _ (by simpa using hNPlt6)
                        (by simp only [objEntry_withFuel, hNP6]; exact hNPk)) ?_
  simp only [objEntry_withFuel, hNP6, hNPp]
  refine forIn_enter (by omega) (by simp only [fuel_withFuel]; omega) ?_
  refine wp_of_eq (ownPropertyKeys_plain OP _ (by simpa using hOPlt6)
    (by simp only [objEntry_withFuel, hOP6]; exact hOPk)) ?_
  simp only [objEntry_withFuel, hOP6, hks]
  refine forIn_hidden ks.size 0 _ _ _ (by omega) (by omega) (by simp only [fuel_withFuel]; omega)
    (by simpa using hOPlt6) (by simp only [objEntry_withFuel, hOP6]; exact hOPk)
    (fun j hj _ p hp => hOPne _ p (by simpa only [objEntry_withFuel, hOP6] using hp)) ?_
  intro vis'
  refine forIn_proto (by omega) (by simp only [fuel_withFuel]; omega) (Nat.le_refl _) ?_
  refine wp_of_eq (by unfold Obj'.getPrototypeOf; rw [maxDepth_eq]
                      exact getPrototypeOf_plain _ OP _ (by simpa using hOPlt6)
                        (by simp only [objEntry_withFuel, hOP6]; exact hOPk)) ?_
  simp only [objEntry_withFuel, hOP6, hOPp]
  refine forIn_end (by omega) (by simp only [fuel_withFuel]; omega) (by intro o hh; cases hh) ?_
  js_until [] [hst01, hS1, hE1, hfw1, hSP4, hSPlt4, hLP4, hLPlt4, hNP4, hNPlt4, hOP4, hOPlt4, hH4, hHlt4, hS4', hSlt4, hfw4, hS4, hE4, hd4, hG4, Ne.symm e1, hGSP, hGSPv, hGS, hGSv, hSPo, hSPk, hSo, hSk, hLPh, hLPp, hNPh, hNPp, hOPk, hOPh, hNPk, hNPon, hNPch, hHk, objEntry_withFuel, heap_withFuel, envs_withFuel, fuel_withFuel, hLPk, hLPon, hLPch, e1, e2, e3, e4, hGe, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  obtain ⟨w0, hr1⟩ := hR1
  rw [hSPenv] at hF6 hbm6
  refine ⟨⟨w0, _, hr1⟩, by omega, ?_, bm6, hbm6, hVT6, hrest6⟩
  have hFs6 := frame_trans (fp1 := {}) (s := s) (by frame_go' [*]) hF6
  refine frame_restore (frame_withFuel (frame_withFuel (frame_withFuel (frame_withFuel (frame_withFuel
    (frame_mono hFs6 (fun p hp => by simpa [Footprint.union] using hp) (fun p hp => by simp [Footprint.union] at hp)
      (fun _ => by simp [Footprint.union])) _) _) _) _) _) s
