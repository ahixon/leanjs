import JSProofs.ReactUseState
import JSProofs.ReactJsx
import JSProofs.CounterGen
import JSProofs.ReactNewProps

/-!
# The counter component's re-render after a click (zippy docs/react-proofs.md)

The component as Vite emits it:
`const [n, setN] = (0, import_react.useState)(0); return (0, import_jsx_runtime.jsx)("button", { onClick: () => setN(n + 1), children: `Count: ${n}` });`
`useState` (`ReactUseState.click_spec`: the click's update processed, `[state, dispatch]`), the destructuring
(`Destructure.bindPair_spec`, through the array iterator), the props object (the arrow function, the template
literal), and `jsx` (`ReactJsx.spec`): the button element whose `children` is `"Count: " + state`.
-/

open ES ES.M HostRuns Logic ReactReducer ReactUpdateReducer ReactUseState
open Std (HashMap)

namespace ReactCounter

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ}

/-- The `onClick` arrow function's code (`() => setN(n + 1)`), as `CounterGen` compiles it. -/
def onClickFunc : Func := (Func.mk none FuncKind.arrow false false #[] (FuncBody.expr (Expr.call (Expr.ident "setN") #[(Arg.expr (Expr.binary BinOp.add (Expr.ident "n") (Expr.lit (Lit.num (F64.fin false 4503599627370496 (-52))))))] false false)) { strict := true, span := { start := 212, stop := 229 : Span }, simpleParams := true, expectedArgs := 0, hasDirectEval := false, usesArguments := false, usesThis := false, paramsHaveExpressions := false, id := 1, fdi := { paramNames := #[], hasDuplicates := false, varNames := #[], hasFunctions := false, functionNames := #[], hasLexical := false, lexNames := #[], argumentsNeeded := false, hasAnnexB := false, usesDispose := false : FDIInfo } : FuncInfo })

/-- A frame from `s` carried on to a state `W` that agrees with `w` on everything `s` had. -/
theorem frame_of_agree {fp : Footprint} {s w W : State} (hF : Frame fp s w)
    (he : ∀ e, e < s.envs.size → W.envEntry e = w.envEntry e) (ho : ∀ o, o < s.heap.size → W.objEntry o = w.objEntry o)
    (hE : w.envs.size ≤ W.envs.size) (hH : w.heap.size ≤ W.heap.size) (hr : W.realms = w.realms) (hj : W.jobs = w.jobs) :
    Frame fp s W where
  envs_le := Nat.le_trans hF.envs_le hE
  heap_le := Nat.le_trans hF.heap_le hH
  env_agree e h := by rw [he e h]; exact hF.env_agree e h
  obj_agree o h := by rw [ho o h]; exact hF.obj_agree o h
  env_eq e h hn := by rw [he e h]; exact hF.env_eq e h hn
  obj_eq o h hn := by rw [ho o h]; exact hF.obj_eq o h hn
  realms_eq := by rw [hr]; exact hF.realms_eq
  jobs_prefix := by rw [hj]; exact hF.jobs_prefix
  jobs_eq h := by rw [hj]; exact hF.jobs_eq h

section ElemFacts
variable (s : State) (It A : ObjId) (i : Nat) (v : Value) (env : EnvId) (x : JSStr)

theorem elemState_old {o : ObjId} (ho : o < s.heap.size) (hoIt : o ≠ It) (hIt : It < s.heap.size) :
    (elemState s It A i v env x).objEntry o = s.objEntry o := by
  rw [elemState_objEntry]
  exact nextState_old { s with fuel := s.fuel - 1 } It A i v o ho hoIt hIt

theorem elemState_envEntry_ne {e : EnvId} (he : e ≠ env) :
    (elemState s It A i v env x).envEntry e = s.envEntry e := by
  simp only [elemState, State.withEnvs, State.envEntry, nextState_envs, Array.getElem?_modify, Ne.symm he]
  simp [Ne.symm he]

theorem elemState_realm : (elemState s It A i v env x).realm = s.realm := rfl

theorem elemState_realms : (elemState s It A i v env x).realms = s.realms := by
  simp [elemState, State.withEnvs, nextState, State.withHeap]

end ElemFacts

theorem push_old (s : State) (f : Nat) (ob : Obj) {o : ObjId} (ho : o < s.heap.size) :
    ({ s with fuel := f, heap := s.heap.push ob } : State).objEntry o = s.objEntry o := by
  simp [State.objEntry, Array.getElem?_push, Nat.ne_of_lt ho, ho]

theorem simpleK (d : FuncData) (hc : d.code = CounterGen.Counter_func) : FDI.Simple d := by
  constructor <;> rw [hc] <;> try rfl
  simp [CounterGen.Counter_func, Func.params, Func.info]

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- **`Counter()`** in the click's re-render. -/
theorem click_spec {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {s : State}
    {bG : HashMap JSStr Binding} {oG : Option EnvId} {fD : ObjId} {dD : FuncData} {fS RSI HD : ObjId} {dS : FuncData} {bR : HashMap JSStr Binding}
    {oR : Option EnvId} {fK IR IJ fJ AP fV fN AIP IP OP : ObjId} {dK dJ : FuncData} {tK vT : Value} {argsK : Array Value}
    {bA bJ : HashMap JSStr Binding} {oA oJ : Option EnvId} {bdIR bdIJ bdT : Binding} {bdV bdN : BuiltinData} {xE : F64}
    {irw ire irc ijw ije ijc pw pe pc nnw nne nnc : Bool} {bdRSI : Binding} {rw re rc uw ue' uc : Bool} {bdU bdB : Binding}
    {bdC bdW bdF bdUW bdUR bdRL bdCE bdSD bdDR bdIs : Binding} {bdIsb : BuiltinData}
    {fW fR fIs C1 C0 H0 Q U : ObjId} {dW dR : FuncData} {r ms bs vE a dv : Value}
    {aw ae ac me mc nw ne nc w1 e1 c1 w2 e2 c2 e3 c3 w4 e4 c4 : Bool}
    {qp qr ql qd ul ur ua ue uv un : Bool × Bool × Bool}
    (hS : fS < s.heap.size) (hSk : (s.objEntry fS).kind = .func dS) (hScode : dS.code = USGen.fn0_func)
    (hScls : dS.isClassCtor = false) (hSmode : dS.thisMode = .strict)
    -- (`react`'s module scope: `ReactSharedInternals`, whose `H` is the update dispatcher `HD`)
    (hSG : dS.env < s.envs.size) (hSGe : Scope.declLike? (s.envEntry dS.env) = some (bR, oR))
    (hRSI : bR[JSStr.ofString "ReactSharedInternals"]? = some bdRSI) (hRSIv : bdRSI.value = some (.obj RSI))
    (hI : RSI < s.heap.size) (hIk : (s.objEntry RSI).kind.isPlain = true)
    (hIH : (s.objEntry RSI).props.get? (.str "H") = some (.data (.obj HD) rw re rc))
    (hHD : HD < s.heap.size) (hHDk : (s.objEntry HD).kind.isPlain = true)
    (hHDu : (s.objEntry HD).props.get? (.str "useState") = some (.data (.obj fD) uw ue' uc))
    (hD : fD < s.heap.size) (hDk : (s.objEntry fD).kind = .func dD) (hDcode : dD.code = USDGen.fn1_func)
    (hDcls : dD.isClassCtor = false) (hDmode : dD.thisMode = .strict) (hDenv : dD.env = d.env)
    (hGU : bG[JSStr.ofString "updateReducer"]? = some bdU) (hGUv : bdU.value = some (.obj fo))
    (hGB : bG[JSStr.ofString "basicStateReducer"]? = some bdB) (hGBv : bdB.value = some r)
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : 200 ≤ s.fuel)
    (hcode : d.code = URGen.updateReducer_func) (hcls : d.isClassCtor = false) (hmode : d.thisMode = .strict)
    (hG : d.env < s.envs.size) (hGe : Scope.declLike? (s.envEntry d.env) = some (bG, oG))
    -- (`updateWorkInProgressHook`'s module variables)
    (hGC : bG[JSStr.ofString "currentHook"]? = some bdC) (hGCm : bdC.mutable = true) (hGCv : bdC.value = some .null)
    (hGW : bG[JSStr.ofString "workInProgressHook"]? = some bdW) (hGWm : bdW.mutable = true)
    (hGWv : bdW.value = some .null)
    (hGF : bG[JSStr.ofString "currentlyRenderingFiber"]? = some bdF) (hGFv : bdF.value = some (.obj C1))
    -- (the two callees, functions of the same module)
    (hGUW : bG[JSStr.ofString "updateWorkInProgressHook"]? = some bdUW) (hGUWv : bdUW.value = some (.obj fW))
    (hW : fW < s.heap.size) (hWk : (s.objEntry fW).kind = .func dW)
    (hWcode : dW.code = UWHGen.updateWorkInProgressHook_func) (hWcls : dW.isClassCtor = false)
    (hWmode : dW.thisMode = .strict) (hWenv : dW.env = d.env)
    (hGUR : bG[JSStr.ofString "updateReducerImpl"]? = some bdUR) (hGURv : bdUR.value = some (.obj fR))
    (hR : fR < s.heap.size) (hRk : (s.objEntry fR).kind = .func dR)
    (hRcode : dR.code = URIGen.updateReducerImpl_func) (hRcls : dR.isClassCtor = false)
    (hRmode : dR.thisMode = .strict) (hRenv : dR.env = d.env)
    -- (`updateReducerImpl`'s module variables)
    (hGRL : bG[JSStr.ofString "renderLanes"]? = some bdRL) (hGRLv : bdRL.value = some two)
    (hGCE : bG[JSStr.ofString "currentEntangledLane"]? = some bdCE) (hGCEv : bdCE.value = some zero)
    (hGSD : bG[JSStr.ofString "shouldDoubleInvokeUserFnsInHooksDEV"]? = some bdSD)
    (hGSDv : bdSD.value = some (.bool false))
    (hGDR : bG[JSStr.ofString "didReceiveUpdate"]? = some bdDR) (hGDRm : bdDR.mutable = true)
    (hGDRi : bdDR.value.isSome = true)
    (hGIs : bG[JSStr.ofString "objectIs"]? = some bdIs) (hGIsv : bdIs.value = some (.obj fIs))
    (hIs : fIs < s.heap.size) (hIsk : (s.objEntry fIs).kind = .builtin bdIsb)
    (hIstab : eng.builtins[bdIsb.id]? = some objectIs)
    -- (the work in progress `C1`, its current `C0`, the current first hook `H0`, its queue `Q`, the update `U`)
    (hC1 : C1 < s.heap.size) (hC1k : (s.objEntry C1).kind.isPlain = true)
    (hC1a : (s.objEntry C1).props.get? (.str "alternate") = some (.data (.obj C0) aw ae ac))
    (hC1m : (s.objEntry C1).props.get? (.str "memoizedState") = some (.data .null true me mc))
    (hC0 : C0 < s.heap.size) (hC0k : (s.objEntry C0).kind.isPlain = true)
    (hC0m : (s.objEntry C0).props.get? (.str "memoizedState") = some (.data (.obj H0) nw ne nc))
    (hH0 : H0 < s.heap.size) (hH0k : (s.objEntry H0).kind.isPlain = true)
    (hHm : (s.objEntry H0).props.get? (.str "memoizedState") = some (.data ms w1 e1 c1))
    (hHb : (s.objEntry H0).props.get? (.str "baseState") = some (.data bs w2 e2 c2))
    (hHbq : (s.objEntry H0).props.get? (.str "baseQueue") = some (.data .null true e3 c3))
    (hHq : (s.objEntry H0).props.get? (.str "queue") = some (.data (.obj Q) w4 e4 c4))
    (hQ : Q < s.heap.size) (hQk : (s.objEntry Q).kind.isPlain = true)
    (hQp : (s.objEntry Q).props.get? (.str "pending") = some (.data (.obj U) true qp.2.1 qp.2.2))
    (hQr : (s.objEntry Q).props.get? (.str "lastRenderedReducer") = some (.data r true qr.2.1 qr.2.2))
    (hQl : (s.objEntry Q).props.get? (.str "lastRenderedState") = some (.data ms true ql.2.1 ql.2.2))
    (hQd : (s.objEntry Q).props.get? (.str "dispatch") = some (.data dv qd.1 qd.2.1 qd.2.2))
    (hU : U < s.heap.size) (hUk : (s.objEntry U).kind.isPlain = true)
    (hUl : (s.objEntry U).props.get? (.str "lane") = some (.data two ul.1 ul.2.1 ul.2.2))
    (hUr : (s.objEntry U).props.get? (.str "revertLane") = some (.data zero ur.1 ur.2.1 ur.2.2))
    (hUa : (s.objEntry U).props.get? (.str "action") = some (.data a ua.1 ua.2.1 ua.2.2))
    (hUe : (s.objEntry U).props.get? (.str "hasEagerState") = some (.data (.bool true) ue.1 ue.2.1 ue.2.2))
    (hUv : (s.objEntry U).props.get? (.str "eagerState") = some (.data vE uv.1 uv.2.1 uv.2.2))
    (hUn : (s.objEntry U).props.get? (.str "next") = some (.data (.obj U) un.1 un.2.1 un.2.2))
    (hdiff : sameValue vE ms = false)
    (d1 : C1 ≠ C0) (d2 : C1 ≠ H0) (d3 : C1 ≠ Q) (d4 : C1 ≠ U) (d5 : C1 ≠ fIs) (d6 : C1 ≠ fR)
    (d7 : H0 ≠ Q) (d8 : H0 ≠ U) (d9 : Q ≠ U) (d10 : fIs ≠ H0) (d11 : fIs ≠ Q) (d12 : fIs ≠ U)
    -- (the component and its module scope: `import_react`, `import_jsx_runtime`)
    (hK : fK < s.heap.size) (hKk : (s.objEntry fK).kind = .func dK) (hKcode : dK.code = CounterGen.Counter_func)
    (hKcls : dK.isClassCtor = false) (hKmode : dK.thisMode = .strict)
    (hAG : dK.env < s.envs.size) (hAGe : Scope.declLike? (s.envEntry dK.env) = some (bA, oA))
    (hAR : bA[JSStr.ofString "import_react"]? = some bdIR) (hARv : bdIR.value = some (.obj IR))
    (hIR : IR < s.heap.size) (hIRk : (s.objEntry IR).kind.isPlain = true)
    (hIRu : (s.objEntry IR).props.get? (.str "useState") = some (.data (.obj fS) irw ire irc))
    (hAJ : bA[JSStr.ofString "import_jsx_runtime"]? = some bdIJ) (hAJv : bdIJ.value = some (.obj IJ))
    (hIJ : IJ < s.heap.size) (hIJk : (s.objEntry IJ).kind.isPlain = true)
    (hIJj : (s.objEntry IJ).props.get? (.str "jsx") = some (.data (.obj fJ) ijw ije ijc))
    -- (`jsxProd` and its module's `REACT_ELEMENT_TYPE`)
    (hJ : fJ < s.heap.size) (hJk : (s.objEntry fJ).kind = .func dJ) (hJcode : dJ.code = JSXGen.jsxProd_func)
    (hJcls : dJ.isClassCtor = false) (hJmode : dJ.thisMode = .strict)
    (hJG : dJ.env < s.envs.size) (hJGe : Scope.declLike? (s.envEntry dJ.env) = some (bJ, oJ))
    (hJT : bJ[JSStr.ofString "REACT_ELEMENT_TYPE"]? = some bdT) (hJTv : bdT.value = some vT)
    -- (the realm's built-ins the destructuring and the object literal use)
    (hAP : s.realms[dR.realm]!.arrayProto = AP)
    (hP : AP < s.heap.size) (hPk : (s.objEntry AP).kind.isReadPlain = true)
    (hPv : (s.objEntry AP).props.get? (.sym WK.iterator) = some (.data (.obj fV) pw pe pc))
    (hV : fV < s.heap.size) (hVk : (s.objEntry fV).kind = .builtin bdV)
    (hVfn : eng.builtins[bdV.id]? = some (ES.arrayProtoValues 1)) (hVr : bdV.realm = dK.realm)
    (hII : s.realms[dK.realm]!.intrinsics["%ArrayIteratorPrototype%"]? = some AIP)
    (hAIP : AIP < s.heap.size) (hAIPk : (s.objEntry AIP).kind.isReadPlain = true)
    (hAIPn : (s.objEntry AIP).props.get? (.str kNext) = some (.data (.obj fN) nnw nne nnc))
    (hN : fN < s.heap.size) (hNk : (s.objEntry fN).kind = .builtin bdN)
    (hNfn : eng.builtins[bdN.id]? = some ES.arrayIteratorNext) (hNr : bdN.realm = dK.realm)
    (hAIPp : (s.objEntry AIP).proto = .obj IP) (hAIPr : (s.objEntry AIP).props.get? (.str "return") = none)
    (hIP : IP < s.heap.size) (hIPk : (s.objEntry IP).kind.isReadPlain = true)
    (hIPr : (s.objEntry IP).props.get? (.str "return") = none) (hIPp : (s.objEntry IP).proto = .obj OP)
    (hOPe : s.realms[dK.realm]!.objectProto = OP)
    (hOP : OP < s.heap.size) (hOPk : (s.objEntry OP).kind.isPlain = true)
    (hOPr : (s.objEntry OP).props.get? (.str "return") = none) (hOPp : (s.objEntry OP).proto = .null)
    (hOPkey : (s.objEntry OP).props.get? (.str "key") = none)
    (hOPref : (s.objEntry OP).props.get? (.str "ref") = none)
    (hFP : (s.realms[dK.realm]!.intrinsics["%Function.prototype%"]?).isSome = true)
    -- (the new state is a Number)
    (hvE : vE = .num xE)
    -- (the realm's and the other modules' objects are not React's fiber, hook, or queue; the module scopes differ)
    (dAP : AP ≠ C1 ∧ AP ≠ H0 ∧ AP ≠ Q) (dfV : fV ≠ C1 ∧ fV ≠ H0 ∧ fV ≠ Q) (dAIP : AIP ≠ C1 ∧ AIP ≠ H0 ∧ AIP ≠ Q)
    (dfN : fN ≠ C1 ∧ fN ≠ H0 ∧ fN ≠ Q) (dIP : IP ≠ C1 ∧ IP ≠ H0 ∧ IP ≠ Q) (dOP : OP ≠ C1 ∧ OP ≠ H0 ∧ OP ≠ Q)
    (dIJ : IJ ≠ C1 ∧ IJ ≠ H0 ∧ IJ ≠ Q) (dfJ : fJ ≠ C1 ∧ fJ ≠ H0 ∧ fJ ≠ Q)
    (hKd : dK.env ≠ d.env) (hJd : dJ.env ≠ d.env) :
    WP eng answer (n + 5) h (callImpl eng (.obj fK) tK argsK) s fun v w h' =>
      ∃ E C F dF, v = .obj E ∧ E < w.heap.size ∧ C < w.heap.size ∧ F < w.heap.size ∧
      s.heap.size < w.heap.size ∧ s.envs.size < w.envs.size ∧ s.heap.size ≤ E ∧ s.heap.size ≤ C ∧
      Frame (fpU d.env C1 s.heap.size H0 Q) s w ∧ s.fuel ≤ w.fuel + 200 ∧ h' = h ∧
      -- (the element: a `button` whose props' `children` is the new count, `onClick` the arrow over the new state)
      (w.objEntry E).props.get? (.str "$$typeof") = some (.data vT true true true) ∧
      (w.objEntry E).props.get? (.str "type") = some (.data (.str (JSStr.ofString "button")) true true true) ∧
      (w.objEntry E).props.get? (.str "key") = some (.data .null true true true) ∧
      (w.objEntry E).props.get? (.str "ref") = some (.data .null true true true) ∧
      (w.objEntry E).props.get? (.str "props") = some (.data (.obj C) true true true) ∧
      (w.objEntry C).props.get? (.str "children") =
        some (.data (.str (JSStr.ofString "Count: " ++ numberToJSStr xE ++ JSStr.ofString "")) true true true) ∧
      (w.objEntry C).props.get? (.str "onClick") = some (.data (.obj F) true true true) ∧
      (w.objEntry E).kind = .ordinary ∧ (w.objEntry C).kind = .ordinary ∧ (w.objEntry C).proto = .obj OP ∧
      (w.objEntry C).props.get? (.str "ref") = none ∧
      (w.objEntry F).kind = .func dF ∧ dF.code = onClickFunc ∧ dF.env = s.envs.size ∧ dF.thisMode = .lexical ∧
      Scope.declLike? (w.envEntry s.envs.size) = some (((((∅ : HashMap JSStr Binding).insert (JSStr.ofString "n")
        { mutable := false, strict := true }).insert (JSStr.ofString "setN") { mutable := false, strict := true }).modify
        (JSStr.ofString "n") (fun bd => { bd with value := some vE })).modify (JSStr.ofString "setN")
        (fun bd => { bd with value := some dv }), some dK.env) ∧
      -- (`useState`'s writes: the module's variables, the work in progress's new first hook, the queue)
      Scope.declLike? (w.envEntry d.env) = some ((((bG.modify (JSStr.ofString "currentHook")
        (fun bd => { bd with value := some (.obj H0) })).modify (JSStr.ofString "workInProgressHook")
        (fun bd => { bd with value := some (.obj s.heap.size) })).modify (JSStr.ofString "didReceiveUpdate")
        (fun bd => { bd with value := some (.bool true) })), oG) ∧
      (w.objEntry C1).props.get? (.str "memoizedState") = some (.data (.obj s.heap.size) true me mc) ∧
      (w.objEntry s.heap.size).props.get? (.str "memoizedState") = some (.data vE true true true) ∧
      (w.objEntry s.heap.size).props.get? (.str "baseState") = some (.data vE true true true) ∧
      (w.objEntry s.heap.size).props.get? (.str "baseQueue") = some (.data .null true true true) ∧
      (w.objEntry s.heap.size).props.get? (.str "queue") = some (.data (.obj Q) true true true) ∧
      (w.objEntry s.heap.size).props.get? (.str "next") = some (.data .null true true true) ∧
      (w.objEntry H0).props.get? (.str "baseQueue") = some (.data (.obj U) true e3 c3) ∧
      (w.objEntry Q).props.get? (.str "pending") = some (.data .null true qp.2.1 qp.2.2) ∧
      (w.objEntry Q).props.get? (.str "lastRenderedReducer") = some (.data r true qr.2.1 qr.2.2) ∧
      (w.objEntry Q).props.get? (.str "lastRenderedState") = some (.data vE true ql.2.1 ql.2.2) ∧
      ReactNewProps.NewProps w C F OP (JSStr.ofString "Count: " ++ numberToJSStr xE ++ JSStr.ofString "") := by
  apply wp_callGen CounterGen.Counter_eq (by decide) hK hKk (by omega) hKcls hKmode
    (by rw [hKcode]; rfl) (by rw [hKcode]; rfl) (simpleK dK hKcode) (by rw [hKcode]; rfl) (by rw [hKcode]; rfl)
  have hpn : dK.code.info.fdi.paramNames = #[] := by rw [hKcode]; rfl
  have hv : dK.code.info.fdi.varNames = #[] := by rw [hKcode]; rfl
  have ha : dK.code.isAsync = false := by rw [hKcode]; rfl
  have hpn' : CounterGen.Counter_func.info.fdi.paramNames = #[] := rfl
  have hv' : CounterGen.Counter_func.info.fdi.varNames = #[] := rfl
  have ha' : CounterGen.Counter_func.isAsync = false := rfl
  have hl : FDI.lexDecls dK = #[LexScoped.binding .const (Pattern.arr #[some (PatElem.mk (Pattern.ident
      (JSStr.ofString "n")) none), some (PatElem.mk (Pattern.ident (JSStr.ofString "setN")) none)] none)] := by
    rw [FDI.lexDecls, hKcode]; first | rfl | simp [CounterGen.Counter_func, topLevelLexicallyScoped, stmtLexScoped, Func.info, Func.body, Array.foldl_toList]; decide
  have hnames : (LexScoped.binding .const (Pattern.arr #[some (PatElem.mk (Pattern.ident (JSStr.ofString "n")) none),
      some (PatElem.mk (Pattern.ident (JSStr.ofString "setN")) none)] none)).names =
      #[JSStr.ofString "n", JSStr.ofString "setN"] := rfl
  have hconst : (LexScoped.binding .const (Pattern.arr #[some (PatElem.mk (Pattern.ident (JSStr.ofString "n")) none),
      some (PatElem.mk (Pattern.ident (JSStr.ofString "setN")) none)] none)).isConstant = true := rfl
  have hneA : s.envs.size ≠ dK.env := Nat.ne_of_gt hAG
  have hAG1 : dK.env < s.envs.size + 1 := Nat.lt_succ_of_lt hAG
  simp only [CounterGen.Counter]
  js [hpn, hv, hpn', hv', ha', hl, hnames, hconst, ha, hAG, hAG1, hneA, Ne.symm hneA, hAGe, hAR, hARv, hIR, hIRk, hIRu, FDI.fdiCtx, Sem.inner]
  -- (`(0, import_react.useState)(0)`)
  refine wp_callValueC ?_
  js [hpn, hv, hpn', hv', ha', hl, hnames, hconst, ha, hAG, hAG1, hneA, Ne.symm hneA, hAGe, hAR, hARv, hIR, hIRk, hIRu, FDI.fdiCtx, Sem.inner]
  refine ⟨by js_norm [CallableC, hS, hSk], ?_⟩
  -- (`useState(0)`: the click's update processed; the array `[state, dispatch]` at `s.heap.size + 1`)
  refine wp_mono (ReactUseState.click_spec (bG := bG) (oG := oG) (bR := bR) (oR := oR) (x := .num (F64.fin false 0 (-1074)))
    (hS := hS) (hSk := hSk) (hScode := hScode) (hScls := hScls) (hSmode := hSmode)
    (hSG := by js_norm [hSG, Nat.lt_succ_of_lt hSG])
    (hSGe := by js_norm [hSGe, Nat.ne_of_gt hSG, Ne.symm (Nat.ne_of_gt hSG)]) (hRSI := hRSI) (hRSIv := hRSIv)
    (hI := hI) (hIk := hIk) (hIH := hIH) (hHD := hHD) (hHDk := hHDk) (hHDu := hHDu) (hD := hD) (hDk := hDk)
    (hDcode := hDcode) (hDcls := hDcls) (hDmode := hDmode) (hDenv := hDenv) (hGU := hGU) (hGUv := hGUv)
    (hGB := hGB) (hGBv := hGBv) (hlt := hlt) (hk := hk) (hf := by js_norm; omega) (hcode := hcode) (hcls := hcls)
    (hmode := hmode) (hG := by js_norm [hG, Nat.lt_succ_of_lt hG])
    (hGe := by js_norm [hGe, Nat.ne_of_gt hG, Ne.symm (Nat.ne_of_gt hG)]) (hGC := hGC) (hGCm := hGCm)
    (hGCv := hGCv) (hGW := hGW) (hGWm := hGWm) (hGWv := hGWv) (hGF := hGF) (hGFv := hGFv) (hGUW := hGUW)
    (hGUWv := hGUWv) (hW := hW) (hWk := hWk) (hWcode := hWcode) (hWcls := hWcls) (hWmode := hWmode)
    (hWenv := hWenv) (hGUR := hGUR) (hGURv := hGURv) (hR := hR) (hRk := hRk) (hRcode := hRcode) (hRcls := hRcls)
    (hRmode := hRmode) (hRenv := hRenv) (hGRL := hGRL) (hGRLv := hGRLv) (hGCE := hGCE) (hGCEv := hGCEv)
    (hGSD := hGSD) (hGSDv := hGSDv) (hGDR := hGDR) (hGDRm := hGDRm) (hGDRi := hGDRi) (hGIs := hGIs)
    (hGIsv := hGIsv) (hIs := hIs) (hIsk := hIsk) (hIstab := hIstab) (hC1 := hC1) (hC1k := hC1k) (hC1a := hC1a)
    (hC1m := hC1m) (hC0 := hC0) (hC0k := hC0k) (hC0m := hC0m) (hH0 := hH0) (hH0k := hH0k) (hHm := hHm)
    (hHb := hHb) (hHbq := hHbq) (hHq := hHq) (hQ := hQ) (hQk := hQk) (hQp := hQp) (hQr := hQr) (hQl := hQl)
    (hQd := hQd) (hU := hU) (hUk := hUk) (hUl := hUl) (hUr := hUr) (hUa := hUa) (hUe := hUe) (hUv := hUv)
    (hUn := hUn) (hdiff := hdiff) (d1 := d1) (d2 := d2) (d3 := d3) (d4 := d4) (d5 := d5) (d6 := d6) (d7 := d7)
    (d8 := d8) (d9 := d9) (d10 := d10) (d11 := d11) (d12 := d12)) ?post
  intro v w h1 ⟨hv1, hF1, hfu1, hh1, hA1, hp1, hsym1, hdl1, hm1, hkk1, hkm1, hkb1, hkbq1, hkq1, hkn1, hH0b1, hQp1, hQr1,
    hQl1, hr1⟩
  subst v h1
  have hbz : (bodyState s fK dK tK argsK).heap.size = s.heap.size := by js_norm
  simp only [hbz] at hF1 hA1 hp1 hsym1
  simp (config := { maxDischargeDepth := 6 }) only [js_simp, ↓reduceIte] at hfu1 hr1 hp1
  -- (what `useState` left alone: its frame from the component's start)
  have hFs := frame_trans (frame_bodyState (frame_refl ({} : Footprint) s) fK dK tK argsK) hF1
  have hfo : ∀ o, o < s.heap.size → o ≠ C1 → o ≠ H0 → o ≠ Q → w.objEntry o = s.objEntry o := by
    intro o ho h1 h2 h3
    refine objEntry_frame hFs ho ?_
    simp [fpU, ReactHooks.fpW, fpR, Footprint.union, Ne.symm h1, Ne.symm h2, Ne.symm h3, Nat.ne_of_gt ho]
  have hfe : ∀ e, e < s.envs.size → e ≠ d.env → w.envEntry e = s.envEntry e := by
    intro e he h1
    refine envEntry_frame hFs he ?_
    simp [fpU, ReactHooks.fpW, fpR, Footprint.union, Ne.symm h1]
  have hEK : s.envs.size < w.envs.size := envs_frame hF1 (by js_norm)
  have hEKe : w.envEntry s.envs.size = (bodyState s fK dK tK argsK).envEntry s.envs.size :=
    envEntry_frame hF1 (by js_norm) (by simp [fpU, ReactHooks.fpW, fpR, Footprint.union, Nat.ne_of_gt hG, Ne.symm (Nat.ne_of_gt hG)])
  have hzw : s.heap.size + 2 ≤ w.heap.size := Nat.succ_le_of_lt hA1.1
  simp only [realm_bodyState, realms_bodyState] at hr1 hp1
  -- (`const [n, setN] = …`: the array's iterator, two steps)
  have hdK : Scope.declLike? (w.envEntry s.envs.size) = some (((∅ : HashMap JSStr Binding).insert
      (JSStr.ofString "n") { mutable := false, strict := true }).insert (JSStr.ofString "setN")
      { mutable := false, strict := true }, some dK.env) := by
    rw [hEKe]; js_norm [hpn, hv, hpn', hv', ha', hl, hnames, hconst, ha]
  have hcur : w.curRealm = s.realms[dK.realm]! := by simp only [State.curRealm, hr1, hFs.realms_eq]
  have hw : ∀ o, o < s.heap.size → o < w.heap.size := fun o ho => heap_frame hFs ho
  rw [hbz]
  refine wp_mono (bindPair_spec (n := n + 4) (k := 999990) (A := s.heap.size + 1) (AP := AP) (fV := fV) (fN := fN)
    (AIP := AIP) (IP := IP) (OP := OP) (v0 := vE) (v1 := dv) (L := Conv.ofSmallInt 2) (Q := fun _ _ _ => True)
    hA1.1 hA1.2.1 hsym1 (by rw [hp1, hAP]) (hw AP hP) (by rw [hfo AP hP dAP.1 dAP.2.1 dAP.2.2]; exact hPk)
    (by rw [hfo AP hP dAP.1 dAP.2.1 dAP.2.2]; exact hPv) (hw fV hV) (by rw [hfo fV hV dfV.1 dfV.2.1 dfV.2.2]; exact hVk)
    hVfn (by rw [hr1]; exact hVr) (by rw [hcur]; exact hII) (hw AIP hAIP)
    (by rw [hfo AIP hAIP dAIP.1 dAIP.2.1 dAIP.2.2]; exact hAIPk) (by rw [hfo AIP hAIP dAIP.1 dAIP.2.1 dAIP.2.2]; exact hAIPn)
    (hw fN hN) (by rw [hfo fN hN dfN.1 dfN.2.1 dfN.2.2]; exact hNk) hNfn (by rw [hr1]; exact hNr)
    (by have := hA1.2.2.2.1; simpa using this) (by decide)
    (by have := hA1.2.2.2.2.1 0 (by decide); simpa using this) (by have := hA1.2.2.2.2.1 1 (by decide); simpa using this)
    (by rw [hfo AIP hAIP dAIP.1 dAIP.2.1 dAIP.2.2]; exact hAIPp) (by rw [hfo AIP hAIP dAIP.1 dAIP.2.1 dAIP.2.2]; exact hAIPr)
    (hw IP hIP) (by rw [hfo IP hIP dIP.1 dIP.2.1 dIP.2.2]; exact hIPk) (by rw [hfo IP hIP dIP.1 dIP.2.1 dIP.2.2]; exact hIPr)
    (by rw [hfo IP hIP dIP.1 dIP.2.1 dIP.2.2]; exact hIPp) (hw OP hOP)
    (by rw [hfo OP hOP dOP.1 dOP.2.1 dOP.2.2]; exact Kind.isReadPlain_of_isPlain hOPk) (by rw [hfo OP hOP dOP.1 dOP.2.1 dOP.2.2]; exact hOPr)
    (by rw [hfo OP hOP dOP.1 dOP.2.1 dOP.2.2]; exact hOPp) hEK hdK (by simp) (by simp) (by omega)) ?post2
  intro _ W h2 ⟨hW, hh2⟩
  subst h2
  -- (what the destructuring changed: the component's `n` and `setN`; the iterator and its two results are new)
  have hIt : w.heap.size < ({ w with fuel := w.fuel - 1, heap := w.heap.push (iterObj AIP (s.heap.size + 1)) } : State).heap.size := by simp
  have hWo : ∀ o, o < w.heap.size → W.objEntry o = w.objEntry o := by
    intro o ho
    have h1 : o < (elemState { w with fuel := w.fuel - 1, heap := w.heap.push (iterObj AIP (s.heap.size + 1)) }
        w.heap.size (s.heap.size + 1) 0 vE s.envs.size (JSStr.ofString "n")).heap.size := by
      rw [elemState_size]; simp only [Array.size_push]; exact Nat.lt_succ_of_lt (Nat.lt_succ_of_lt ho)
    rw [hW, elemState_old _ _ _ _ _ _ _ h1 (Nat.ne_of_lt ho)
        (by rw [elemState_size]; simp only [Array.size_push]; exact Nat.lt_succ_of_lt (Nat.lt_succ_self _)),
      elemState_old _ _ _ _ _ _ _ (by simp only [Array.size_push]; exact Nat.lt_succ_of_lt ho) (Nat.ne_of_lt ho) hIt,
      push_old _ _ _ ho]
  have hWe : ∀ e, e ≠ s.envs.size → W.envEntry e = w.envEntry e := by
    intro e he
    rw [hW, elemState_envEntry_ne _ _ _ _ _ _ _ he, elemState_envEntry_ne _ _ _ _ _ _ _ he]; rfl
  have hWd := elemState_declLike (elemState { w with fuel := w.fuel - 1, heap := w.heap.push (iterObj AIP (s.heap.size + 1)) }
      w.heap.size (s.heap.size + 1) 0 vE s.envs.size (JSStr.ofString "n")) w.heap.size (s.heap.size + 1) 1 dv
      s.envs.size (JSStr.ofString "setN") (by rw [elemState_envs_size]; exact hEK)
      (elemState_declLike _ _ _ _ _ _ _ hEK hdK)
  rw [← hW] at hWd
  have hWz : W.heap.size = w.heap.size + 3 := by rw [hW, elemState_size, elemState_size]; simp
  have hWr : W.realm = dK.realm := by rw [hW, elemState_realm, elemState_realm]; exact hr1
  have hWrs : W.realms = s.realms := by rw [hW, elemState_realms, elemState_realms]; exact hFs.realms_eq
  have hWf : W.fuel = w.fuel - 1 - 1 - 1 := by rw [hW, elemState_fuel, elemState_fuel]
  have hWE : W.envs.size = w.envs.size := by rw [hW, elemState_envs_size, elemState_envs_size]
  have hWj : W.jobs = w.jobs := by rw [hW]; simp [elemState, nextState, State.withEnvs, State.withHeap]
  clear hW
  have hWK : W.envEntry dK.env = s.envEntry dK.env := by
    rw [hWe _ (Ne.symm hneA), hfe dK.env hAG hKd]
  have hWIJ : W.objEntry IJ = s.objEntry IJ := by
    rw [hWo IJ (hw IJ hIJ), hfo IJ hIJ dIJ.1 dIJ.2.1 dIJ.2.2]
  have hWcur : W.curRealm = s.realms[dK.realm]! := by simp only [State.curRealm, hWr, hWrs]
  have hIJW : IJ < W.heap.size := by rw [hWz]; exact Nat.lt_of_lt_of_le (hw IJ hIJ) (Nat.le_add_right _ _)
  have hEKW : s.envs.size < W.envs.size := by rw [hWE]; exact hEK
  have hAGW : dK.env < W.envs.size := by rw [hWE]; exact envs_frame hFs hAG
  have hAGw : dK.env < w.envs.size := envs_frame hFs hAG
  have hIJw3 : IJ < w.heap.size + 3 := Nat.lt_of_lt_of_le (hw IJ hIJ) (Nat.le_add_right _ _)
  -- (`return (0, import_jsx_runtime.jsx)("button", { … })`)
  js [hWd, hEKW, hAGW, hAGw, hIJw3, hEK, hWE, hWz, hWK, hAGe, hAJ, hAJv, hWIJ, hIJW, hIJk, hIJj, hneA, Ne.symm hneA, FDI.fdiCtx, Sem.inner]
  refine wp_callValueC ?_
  js [hWd, hEKW, hAGW, hAGw, hIJw3, hEK, hWE, hWz, hWK, hAGe, hAJ, hAJv, hWIJ, hIJW, hIJk, hIJj, hneA, Ne.symm hneA, FDI.fdiCtx, Sem.inner]
  -- (`onClick: () => setN(n + 1)`: the arrow function, named `onClick`)
  refine wp_namedArrow ⟨rfl, rfl, rfl, rfl, rfl⟩ (by show (W.curRealm.intrinsics["%Function.prototype%"]?).isSome = true; rw [hWcur]; exact hFP) ?_
  js [hWd, hEKW, hAGW, hAGw, hIJw3, hEK, hWE, hWz, hWK, hAGe, hAJ, hAJv, hWIJ, hIJW, hIJk, hIJj, hneA, Ne.symm hneA, FDI.fdiCtx, Sem.inner]
  -- (`children: `Count: ${n}``)
  refine wp_template1 ?_
  js [hWd, hEKW, hAGW, hAGw, hIJw3, hEK, hWE, hWz, hWK, hAGe, hAJ, hAJv, hWIJ, hIJW, hIJk, hIJj, hneA, Ne.symm hneA, FDI.fdiCtx, Sem.inner, hvE]
  rw [toStr_num]
  refine wp_of_eq rfl ?_
  js [hWd, hEKW, hAGW, hAGw, hIJw3, hEK, hWE, hWz, hWK, hAGe, hAJ, hAJv, hWIJ, hIJW, hIJk, hIJj, hneA, Ne.symm hneA, FDI.fdiCtx, Sem.inner, hvE]
  -- (`jsx("button", props)`: the element)
  have hWfJ : W.objEntry fJ = s.objEntry fJ := by rw [hWo fJ (hw fJ hJ), hfo fJ hJ dfJ.1 dfJ.2.1 dfJ.2.2]
  have hWOP : W.objEntry OP = s.objEntry OP := by rw [hWo OP (hw OP hOP), hfo OP hOP dOP.1 dOP.2.1 dOP.2.2]
  have hfJw3 : fJ < w.heap.size + 3 := Nat.lt_of_lt_of_le (hw fJ hJ) (Nat.le_add_right _ _)
  have hOPw3 : OP < w.heap.size + 3 := Nat.lt_of_lt_of_le (hw OP hOP) (Nat.le_add_right _ _)
  have hfJw4 : fJ < w.heap.size + 3 + 1 := Nat.lt_succ_of_lt hfJw3
  have hfJw5 : fJ < w.heap.size + 3 + 1 + 1 := Nat.lt_succ_of_lt hfJw4
  have hOPw4 : OP < w.heap.size + 3 + 1 := Nat.lt_succ_of_lt hOPw3
  have hOPw5 : OP < w.heap.size + 3 + 1 + 1 := Nat.lt_succ_of_lt hOPw4
  have hJGw : dJ.env < w.envs.size := envs_frame hFs hJG
  have hWJ : W.envEntry dJ.env = s.envEntry dJ.env := by
    rw [hWe _ (Nat.ne_of_lt hJG), hfe dJ.env hJG hJd]
  refine ⟨by js_norm [CallableC, hWd, hEKW, hAGW, hAGw, hIJw3, hEK, hWE, hWz, hWK, hAGe, hAJ, hAJv, hWIJ, hIJW, hIJk, hIJj, hneA, Ne.symm hneA, FDI.fdiCtx, Sem.inner, hWfJ, hWOP, hfJw3, hOPw3, hfJw4, hfJw5, hOPw4, hOPw5, Nat.ne_of_lt hfJw4, Nat.ne_of_gt hfJw4, Nat.ne_of_lt hOPw4, Nat.ne_of_gt hOPw4, hJGw, hWJ, hJGe, hJT, hJTv, hJk, hOPk, hOPp, hOPkey, hOPref, Nat.ne_of_lt hfJw3, Nat.ne_of_gt hfJw3, Nat.ne_of_lt hOPw3, Nat.ne_of_gt hOPw3], ?_⟩
  refine wp_mono (ReactJsx.spec (bG := bJ) (oG := oJ) (bdT := bdT) (C := w.heap.size + 3) (OP := OP)
    (ty := .str (JSStr.ofString "button")) (vT := vT) ?_ ?_ ?_ hJcode hJcls hJmode ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) ?post3
  all_goals first
    | (rw [ES.setProp_proto, ES.setProp_proto, arrowState_objEntry_lt _ _ _ _ _
        (by simp only [State.allocObj, State.withHeap, Array.size_push, hWz]; exact Nat.lt_succ_self _), ← hWz,
        State.allocObj_entry_new]; done)
    | (js_norm [hWd, hEKW, hAGW, hAGw, hIJw3, hEK, hWE, hWz, hWK, hAGe, hAJ, hAJv, hWIJ, hIJW, hIJk, hIJj, hneA, Ne.symm hneA, FDI.fdiCtx, Sem.inner, hWfJ, hWOP, hfJw3, hOPw3, hfJw4, hfJw5, hOPw4, hOPw5, Nat.ne_of_lt hfJw4, Nat.ne_of_gt hfJw4, Nat.ne_of_lt hOPw4, Nat.ne_of_gt hOPw4, hJGw, hWJ, hJGe, hJT, hJTv, hJk, hOPk, hOPp, hOPkey, hOPref, Nat.ne_of_lt hfJw3, Nat.ne_of_gt hfJw3, Nat.ne_of_lt hOPw3, Nat.ne_of_gt hOPw3]; done)
    | (js_norm [hWd, hEKW, hAGW, hAGw, hIJw3, hEK, hWE, hWz, hWK, hAGe, hAJ, hAJv, hWIJ, hIJW, hIJk, hIJj, hneA, Ne.symm hneA, FDI.fdiCtx, Sem.inner, hWfJ, hWOP, hfJw3, hOPw3, hfJw4, hfJw5, hOPw4, hOPw5, Nat.ne_of_lt hfJw4, Nat.ne_of_gt hfJw4, Nat.ne_of_lt hOPw4, Nat.ne_of_gt hOPw4, hJGw, hWJ, hJGe, hJT, hJTv, hJk, hOPk, hOPp, hOPkey, hOPref, Nat.ne_of_lt hfJw3, Nat.ne_of_gt hfJw3, Nat.ne_of_lt hOPw3, Nat.ne_of_gt hOPw3]; omega)
    | skip
  case post3 =>
  intro v3 w3 h3 ⟨hv3, hF3, hfu3, hh3, hz3, hEk, hEp, hEt, hEty, hEkey, hEref, hEpr, hr3⟩
  subst hvE
  simp only [hbz] at hkm1 hkb1 hkbq1 hkq1 hkn1 hkk1 hm1
  have hWzC : w.heap.size + 3 = W.heap.size := hWz.symm
  -- (from the final state back to `W`: `jsx` made a new object; the props object and the arrow are new)
  have hSo : ∀ o, o < W.heap.size → w3.objEntry o = W.objEntry o := by
    intro o ho
    have hne : w.heap.size + 3 ≠ o := by rw [hWzC]; exact Nat.ne_of_gt ho
    have hne1 : w.heap.size + 3 + 1 ≠ o := by rw [hWzC]; exact Nat.ne_of_gt (Nat.lt_succ_of_lt ho)
    rw [objEntry_frame0 hF3 (by simp only [js_simp]; exact Nat.lt_succ_of_lt (Nat.lt_succ_of_lt ho))]
    rw [State.setProp_entry_ne _ _ _ _ _ hne, State.setProp_entry_ne _ _ _ _ _ hne,
      arrowState_objEntry_lt _ _ _ _ _ (by simp only [State.allocObj, State.withHeap, Array.size_push]; exact Nat.lt_succ_of_lt ho),
      State.allocObj_entry_lt _ _ _ ho]
  have hSe : ∀ e, e < W.envs.size → w3.envEntry e = W.envEntry e := by
    intro e he
    rw [envEntry_frame0 hF3 (by simp only [js_simp]; exact he)]
    simp only [js_simp]
  have hfin : ∀ o, o < w.heap.size → w3.objEntry o = w.objEntry o := fun o ho =>
    (hSo o (by rw [hWz]; exact Nat.lt_of_lt_of_le ho (Nat.le_add_right _ _))).trans (hWo o ho)
  have hfinE : ∀ e, e < w.envs.size → e ≠ s.envs.size → w3.envEntry e = w.envEntry e := fun e he hne =>
    (hSe e (by rw [hWE]; exact he)).trans (hWe e hne)
  have hCC : w.heap.size + 3 < (W.allocObj { proto := .obj OP }).heap.size := by
    simp only [State.allocObj, State.withHeap, Array.size_push, hWz]; exact Nat.lt_succ_self _
  have hCC2 : w.heap.size + 3 < W.heap.size + 1 + 1 := by rw [hWz]; exact Nat.lt_succ_of_lt (Nat.lt_succ_self _)
  have hSz : W.heap.size ≤ w3.heap.size := by
    have h := hF3.heap_le; simp only [js_simp] at h; exact Nat.le_trans (Nat.le_succ _) (Nat.le_trans (Nat.le_succ _) h)
  have hSE : W.envs.size ≤ w3.envs.size := by
    have h := hF3.envs_le; simp only [js_simp] at h; exact h
  have hCne : w.heap.size + 3 ≠ w.heap.size + 3 + 1 := Nat.ne_of_lt (Nat.lt_succ_self _)
  have hC3 : w3.objEntry (w.heap.size + 3) = _ := objEntry_frame0 hF3 (by simp only [js_simp]; rw [hWzC]; exact Nat.lt_succ_of_lt (Nat.lt_succ_self _))
  have hF3e : w3.objEntry (w.heap.size + 3 + 1) = _ := objEntry_frame0 hF3 (by simp only [js_simp]; rw [hWzC]; exact Nat.lt_succ_self _)
  rw [State.setProp_entry_ne _ _ _ _ _ hCne, State.setProp_entry_ne _ _ _ _ _ hCne] at hF3e
  have hAz : (W.allocObj { proto := .obj OP }).heap.size = w.heap.size + 3 + 1 := by
    simp only [State.allocObj, State.withHeap, Array.size_push, hWz]
  have hFnew := arrowState_new (W.allocObj { proto := .obj OP }) onClickFunc
    { lex := s.envs.size, var := s.envs.size, priv := dK.privEnv, strict := true, fn := some fK, realm := dK.realm,
      script := dK.script, annexB := funcIds #[] } (funcProto (W.allocObj { proto := .obj OP })) (JSStr.ofString "onClick")
  rw [hAz] at hFnew
  have hSt2 : W.heap.size + 1 + 1 ≤ w3.heap.size := by have h := hF3.heap_le; simp only [js_simp] at h; exact h
  refine ⟨_, w.heap.size + 3, w.heap.size + 3 + 1, _, hv3, by rw [hz3]; exact Nat.lt_succ_self _,
    by rw [hWzC]; exact Nat.lt_of_lt_of_le (Nat.lt_succ_of_lt (Nat.lt_succ_self _)) hSt2,
    by rw [hWzC]; exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hSt2,
    Nat.lt_of_lt_of_le (Nat.lt_of_succ_lt hA1.1) (Nat.le_trans (by rw [hWz]; exact Nat.le_add_right _ _) hSz),
    Nat.lt_of_lt_of_le hEK (by rw [← hWE]; exact hSE), ?Eb, Nat.le_trans (Nat.le_of_lt (Nat.lt_of_succ_lt hA1.1))
    (Nat.le_add_right _ _), ?fr, ?fu, hh3, hEt, hEty, hEkey, hEref, hEpr, ?ch, ?oc, hEk, ?Ck, ?Cp, ?Cr,
    by rw [hF3e]; exact hFnew.1, rfl, rfl, rfl, ?dK, ?dG, ?c1, ?k1, ?k2, ?k3, ?k4, ?k5, ?h0, ?q1, ?q2, ?q3, ?np⟩
  case ch => rw [hC3]; js_norm [hCC, hCC2]
  case oc => rw [hC3]; js_norm [hCC, hCC2]
  case Eb =>
    have h1 : s.heap.size ≤ W.heap.size :=
      Nat.le_trans (Nat.le_of_lt (Nat.lt_of_succ_lt hA1.1)) (by rw [hWz]; exact Nat.le_add_right _ _)
    simp only [js_simp]
    exact Nat.le_trans h1 (Nat.le_trans (Nat.le_succ _) (Nat.le_succ _))
  case Ck =>
    rw [hC3, State.setProp_entry_self _ _ _ _ (by simp only [js_simp]; rw [hWzC]; exact Nat.lt_succ_of_lt (Nat.lt_succ_self _)), Obj.withProps_kind, State.setProp_entry_self _ _ _ _ (by simp only [js_simp]; rw [hWzC]; exact Nat.lt_succ_of_lt (Nat.lt_succ_self _)),
      Obj.withProps_kind, arrowState_objEntry_lt _ _ _ _ _
      (by simp only [State.allocObj, State.withHeap, Array.size_push, hWz]; exact Nat.lt_succ_self _), ← hWz,
      State.allocObj_entry_new]
  case Cr =>
    rw [hC3, State.setProp_entry_self _ _ _ _ (by simp only [js_simp]; rw [hWzC]; exact Nat.lt_succ_of_lt (Nat.lt_succ_self _)), Obj.withProps_props, PropMap.get?_insert_ne _ _ _ _ (by decide),
      State.setProp_entry_self _ _ _ _ (by simp only [js_simp]; rw [hWzC]; exact Nat.lt_succ_of_lt (Nat.lt_succ_self _)), Obj.withProps_props, PropMap.get?_insert_ne _ _ _ _ (by decide),
      arrowState_objEntry_lt _ _ _ _ _
      (by simp only [State.allocObj, State.withHeap, Array.size_push, hWz]; exact Nat.lt_succ_self _), ← hWz,
      State.allocObj_entry_new]
    simp [PropMap.get?_empty]
  case Cp =>
    rw [hC3, ES.setProp_proto, ES.setProp_proto, arrowState_objEntry_lt _ _ _ _ _
      (by simp only [State.allocObj, State.withHeap, Array.size_push, hWz]; exact Nat.lt_succ_self _), ← hWz,
      State.allocObj_entry_new]
  case np =>
    refine ⟨by rw [hWzC]; exact Nat.lt_of_lt_of_le (Nat.lt_succ_of_lt (Nat.lt_succ_self _)) hSt2, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [restore_objEntry]; rw [hC3, State.setProp_entry_self _ _ _ _ (by simp only [js_simp]; rw [hWzC]; exact Nat.lt_succ_of_lt (Nat.lt_succ_self _)), Obj.withProps_kind, State.setProp_entry_self _ _ _ _ (by simp only [js_simp]; rw [hWzC]; exact Nat.lt_succ_of_lt (Nat.lt_succ_self _)),
        Obj.withProps_kind, arrowState_objEntry_lt _ _ _ _ _
        (by simp only [State.allocObj, State.withHeap, Array.size_push, hWz]; exact Nat.lt_succ_self _), ← hWz,
        State.allocObj_entry_new]
    · simp only [restore_objEntry]; rw [hC3, ES.setProp_proto, ES.setProp_proto, arrowState_objEntry_lt _ _ _ _ _
        (by simp only [State.allocObj, State.withHeap, Array.size_push, hWz]; exact Nat.lt_succ_self _), ← hWz,
        State.allocObj_entry_new]
    · simp only [restore_objEntry]; rw [hC3, State.setProp_entry_self _ _ _ _ (by simp only [js_simp]; rw [hWzC]; exact Nat.lt_succ_of_lt (Nat.lt_succ_self _)), Obj.withProps_props,
        State.setProp_entry_self _ _ _ _ (by simp only [js_simp]; rw [hWzC]; exact Nat.lt_succ_of_lt (Nat.lt_succ_self _)), Obj.withProps_props, arrowState_objEntry_lt _ _ _ _ _
        (by simp only [State.allocObj, State.withHeap, Array.size_push, hWz]; exact Nat.lt_succ_self _), ← hWz,
        State.allocObj_entry_new]
      exact ReactNewProps.keys_two _ _ _ _ (by decide)
    · simp only [restore_objEntry]; rw [hC3]; js_norm [hCC, hCC2]
    · simp only [restore_objEntry]; rw [hC3]; js_norm [hCC, hCC2]
    · simp only [restore_objEntry]; rw [hC3, State.setProp_entry_self _ _ _ _ (by simp only [js_simp]; rw [hWzC]; exact Nat.lt_succ_of_lt (Nat.lt_succ_self _)), Obj.withProps_props, PropMap.get?_insert_ne _ _ _ _ (by decide),
        State.setProp_entry_self _ _ _ _ (by simp only [js_simp]; rw [hWzC]; exact Nat.lt_succ_of_lt (Nat.lt_succ_self _)), Obj.withProps_props, PropMap.get?_insert_ne _ _ _ _ (by decide), arrowState_objEntry_lt _ _ _ _ _
        (by simp only [State.allocObj, State.withHeap, Array.size_push, hWz]; exact Nat.lt_succ_self _), ← hWz,
        State.allocObj_entry_new]
      simp [PropMap.get?_empty]
    · simp only [restore_objEntry]; rw [hC3, State.setProp_entry_self _ _ _ _ (by simp only [js_simp]; rw [hWzC]; exact Nat.lt_succ_of_lt (Nat.lt_succ_self _)), Obj.withProps_props, PropMap.get?_insert_ne _ _ _ _ (by decide),
        State.setProp_entry_self _ _ _ _ (by simp only [js_simp]; rw [hWzC]; exact Nat.lt_succ_of_lt (Nat.lt_succ_self _)), Obj.withProps_props, PropMap.get?_insert_ne _ _ _ _ (by decide), arrowState_objEntry_lt _ _ _ _ _
        (by simp only [State.allocObj, State.withHeap, Array.size_push, hWz]; exact Nat.lt_succ_self _), ← hWz,
        State.allocObj_entry_new]
      simp [PropMap.get?_empty]
  case dK => rw [hSe _ hEKW]; exact hWd
  case dG => rw [hfinE _ (envs_frame hFs hG) (Nat.ne_of_lt hG)]; exact hdl1
  case c1 => rw [hfin _ (hw C1 hC1)]; exact hm1
  case k1 => rw [hfin _ (by have := hA1.1; exact Nat.lt_of_succ_lt this)]; exact hkm1
  case k2 => rw [hfin _ (by have := hA1.1; exact Nat.lt_of_succ_lt this)]; exact hkb1
  case k3 => rw [hfin _ (by have := hA1.1; exact Nat.lt_of_succ_lt this)]; exact hkbq1
  case k4 => rw [hfin _ (by have := hA1.1; exact Nat.lt_of_succ_lt this)]; exact hkq1
  case k5 => rw [hfin _ (by have := hA1.1; exact Nat.lt_of_succ_lt this)]; exact hkn1
  case h0 => rw [hfin _ (hw H0 hH0)]; exact hH0b1
  case q1 => rw [hfin _ (hw Q hQ)]; exact hQp1
  case q2 => rw [hfin _ (hw Q hQ)]; exact hQr1
  case q3 => rw [hfin _ (hw Q hQ)]; exact hQl1
  case fu =>
    simp only [js_simp] at hfu3
    rw [hWf] at hfu3
    omega
  case fr =>
    refine frame_restore (frame_mono (frame_of_agree hFs (fun e he => hfinE e (envs_frame hFs he) (Nat.ne_of_lt he))
      (fun o ho => hfin o (hw o ho)) ?_ ?_ ?_ ?_) (fun p hp => by simpa [Footprint.union] using hp)
      (fun p hp => by simpa [Footprint.union] using hp) (fun _ => rfl)) s
    · rw [← hWE]; exact hSE
    · exact Nat.le_trans (by rw [hWz]; exact Nat.le_add_right _ _) hSz
    · rw [hF3.realms_eq]; show W.realms = w.realms; rw [hWrs, hFs.realms_eq]
    · rw [hF3.jobs_eq rfl]; show W.jobs = w.jobs; exact hWj

end

end ReactCounter
