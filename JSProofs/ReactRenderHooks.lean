import JSProofs.ReactCounter
import JSProofs.ReactFinishHooks
import JSProofs.RWHGen

/-!
# `renderWithHooks` for the counter's re-render after a click (zippy docs/react-proofs.md)

`renderWithHooks(current, workInProgress, Counter, props, undefined, 2)`: the render's module variables and the
update dispatcher installed (`ReactSharedInternals.H`), the component called (`ReactCounter.click_spec`), then
`finishRenderingHooks(current)` (`ReactFinishHooks.spec`): the button element.
-/

open ES ES.M HostRuns Logic ReactReducer ReactUpdateReducer ReactUseState ReactCounter
open Std (HashMap)

namespace ReactRenderHooks

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ}

/-- What it writes: its own variables and fields, the component's (`fpU`), `finishRenderingHooks`' (`fpF`). -/
def fpRWH (g : EnvId) (C1 K H0 Q RSI : ObjId) : Footprint :=
  ⟨[(g, "renderLanes"), (g, "currentlyRenderingFiber"), (g, "shouldDoubleInvokeUserFnsInHooksDEV"), (g, "currentHook"),
    (g, "workInProgressHook"), (g, "didReceiveUpdate"), (g, "didScheduleRenderPhaseUpdate"), (g, "thenableIndexCounter"),
    (g, "thenableState")],
   [(C1, .str "memoizedState"), (C1, .str "updateQueue"), (C1, .str "lanes"), (RSI, .str "H"), (K, .str "memoizedState"),
    (K, .str "baseState"), (K, .str "baseQueue"), (H0, .str "baseQueue"), (Q, .str "pending"),
    (Q, .str "lastRenderedReducer"), (Q, .str "lastRenderedState")], false⟩

theorem wp_gen_state {n : Nat} {h : σ} {α : Type} {x : M α} {s : State} {Q : α → State → σ → Prop}
    (hw : ∀ St, St = s → WP eng answer n h x St Q) : WP eng answer n h x s Q := hw s rfl

theorem simpleRW (d : FuncData) (hc : d.code = RWHGen.renderWithHooks_func) : FDI.Simple d := by
  constructor <;> rw [hc] <;> try rfl
  simp [RWHGen.renderWithHooks_func, Func.params, Func.info]

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- **`renderWithHooks(current, workInProgress, Counter, props, undefined, 2)`** in the click's re-render. -/
theorem click_spec {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {s : State}
    {bG : HashMap JSStr Binding} {oG : Option EnvId} {fD : ObjId} {dD : FuncData} {fS RSI HD : ObjId} {dS : FuncData} {bR : HashMap JSStr Binding}
    {oR : Option EnvId} {fK IR IJ fJ AP fV fN AIP IP OP : ObjId} {dK dJ : FuncData} {vT P ms1 vH0 vCO uq ln tRW : Value} {fF fRW : ObjId} {dF dRW : FuncData}
    {bdHU bdRSd bdDP bdFR bdCO bdDS bdTI bdTS : Binding} {uw ue uc lw le lc nw' ne' nc' : Bool}
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
    (hIH : (s.objEntry RSI).props.get? (.str "H") = some (.data vH0 true re rc))
    (hHD : HD < s.heap.size) (hHDk : (s.objEntry HD).kind.isPlain = true)
    (hHDu : (s.objEntry HD).props.get? (.str "useState") = some (.data (.obj fD) uw ue' uc))
    (hD : fD < s.heap.size) (hDk : (s.objEntry fD).kind = .func dD) (hDcode : dD.code = USDGen.fn1_func)
    (hDcls : dD.isClassCtor = false) (hDmode : dD.thisMode = .strict) (hDenv : dD.env = d.env)
    (hGU : bG[JSStr.ofString "updateReducer"]? = some bdU) (hGUv : bdU.value = some (.obj fo))
    (hGB : bG[JSStr.ofString "basicStateReducer"]? = some bdB) (hGBv : bdB.value = some r)
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : 300 ≤ s.fuel)
    (hcode : d.code = URGen.updateReducer_func) (hcls : d.isClassCtor = false) (hmode : d.thisMode = .strict)
    (hG : d.env < s.envs.size) (hGe : Scope.declLike? (s.envEntry d.env) = some (bG, oG))
    -- (`updateWorkInProgressHook`'s module variables)
    (hGC : bG[JSStr.ofString "currentHook"]? = some bdC) (hGCm : bdC.mutable = true) (hGCv : bdC.value = some .null)
    (hGW : bG[JSStr.ofString "workInProgressHook"]? = some bdW) (hGWm : bdW.mutable = true)
    (hGWv : bdW.value = some .null)
    (hGF : bG[JSStr.ofString "currentlyRenderingFiber"]? = some bdF) (hGFm : bdF.mutable = true) (hGFi : bdF.value.isSome = true)
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
    (hGRL : bG[JSStr.ofString "renderLanes"]? = some bdRL) (hGRLm : bdRL.mutable = true) (hGRLi : bdRL.value.isSome = true)
    (hGCE : bG[JSStr.ofString "currentEntangledLane"]? = some bdCE) (hGCEv : bdCE.value = some zero)
    (hGSD : bG[JSStr.ofString "shouldDoubleInvokeUserFnsInHooksDEV"]? = some bdSD)
    (hGSDm : bdSD.mutable = true) (hGSDi : bdSD.value.isSome = true)
    (hGDR : bG[JSStr.ofString "didReceiveUpdate"]? = some bdDR) (hGDRm : bdDR.mutable = true)
    (hGDRi : bdDR.value.isSome = true)
    (hGIs : bG[JSStr.ofString "objectIs"]? = some bdIs) (hGIsv : bdIs.value = some (.obj fIs))
    (hIs : fIs < s.heap.size) (hIsk : (s.objEntry fIs).kind = .builtin bdIsb)
    (hIstab : eng.builtins[bdIsb.id]? = some objectIs)
    -- (the work in progress `C1`, its current `C0`, the current first hook `H0`, its queue `Q`, the update `U`)
    (hC1 : C1 < s.heap.size) (hC1k : (s.objEntry C1).kind.isPlain = true)
    (hC1a : (s.objEntry C1).props.get? (.str "alternate") = some (.data (.obj C0) aw ae ac))
    (hC1m : (s.objEntry C1).props.get? (.str "memoizedState") = some (.data ms1 true me mc))
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
    (hKd : dK.env ≠ d.env) (hJd : dJ.env ≠ d.env)
    -- (renderWithHooks: the update dispatcher, react-dom's `ReactSharedInternals`, no render-phase update scheduled;
    -- finishRenderingHooks and its variables)
    (hGHU : bG[JSStr.ofString "HooksDispatcherOnUpdate"]? = some bdHU) (hGHUv : bdHU.value = some (.obj HD))
    (hGRSd : bG[JSStr.ofString "ReactSharedInternals"]? = some bdRSd) (hGRSdv : bdRSd.value = some (.obj RSI))
    (hGDP : bG[JSStr.ofString "didScheduleRenderPhaseUpdateDuringThisPass"]? = some bdDP)
    (hGDPv : bdDP.value = some (.bool false))
    (hGFR : bG[JSStr.ofString "finishRenderingHooks"]? = some bdFR) (hGFRv : bdFR.value = some (.obj fF))
    (hFF : fF < s.heap.size) (hFFk : (s.objEntry fF).kind = .func dF)
    (hFFcode : dF.code = FRHGen.finishRenderingHooks_func) (hFFcls : dF.isClassCtor = false)
    (hFFmode : dF.thisMode = .strict) (hFFenv : dF.env = d.env)
    (hGCO : bG[JSStr.ofString "ContextOnlyDispatcher"]? = some bdCO) (hGCOv : bdCO.value = some vCO)
    (hGDS : bG[JSStr.ofString "didScheduleRenderPhaseUpdate"]? = some bdDS) (hGDSm : bdDS.mutable = true)
    (hGDSi : bdDS.value.isSome = true)
    (hGTI : bG[JSStr.ofString "thenableIndexCounter"]? = some bdTI) (hGTIm : bdTI.mutable = true)
    (hGTIi : bdTI.value.isSome = true)
    (hGTS : bG[JSStr.ofString "thenableState"]? = some bdTS) (hGTSm : bdTS.mutable = true)
    (hGTSi : bdTS.value.isSome = true)
    -- (the work in progress's fields renderWithHooks resets; the current hook is the only one)
    (hC1u : (s.objEntry C1).props.get? (.str "updateQueue") = some (.data uq true uw uc))
    (hC1l : (s.objEntry C1).props.get? (.str "lanes") = some (.data ln true lw lc))
    (hH0n : (s.objEntry H0).props.get? (.str "next") = some (.data .null nw' ne' nc'))
    -- (the objects the component reads are neither the work in progress nor ReactSharedInternals; react's module
    -- scope is not react-dom's)
    (hdist : ∀ X ∈ [fo, fW, fR, fIs, C0, H0, Q, U, fD, HD, fS, IR, IJ, fJ, AP, fV, AIP, fN, IP, OP, fK, fF],
      X ≠ C1 ∧ X ≠ RSI) (dRC : RSI ≠ C1) (hSd : dS.env ≠ d.env)
    -- (renderWithHooks itself, a function of react-dom's module)
    (hRW : fRW < s.heap.size) (hRWk : (s.objEntry fRW).kind = .func dRW)
    (hRWcode : dRW.code = RWHGen.renderWithHooks_func) (hRWcls : dRW.isClassCtor = false)
    (hRWmode : dRW.thisMode = .strict) (hRWenv : dRW.env = d.env)
    (dFH : fF ≠ H0 ∧ fF ≠ Q) (dRQ : RSI ≠ Q) :
    WP eng answer (n + 6) h (callImpl eng (.obj fRW) tRW #[.obj C0, .obj C1, .obj fK, P, .undefined, two]) s
      fun v w h' =>
      ∃ E C F dF', v = .obj E ∧ Frame (fpRWH d.env C1 s.heap.size H0 Q RSI) s w ∧ s.fuel ≤ w.fuel + 300 ∧ h' = h ∧
      w.realm = s.realm ∧
      -- (the button element)
      (w.objEntry E).props.get? (.str "$$typeof") = some (.data vT true true true) ∧
      (w.objEntry E).props.get? (.str "type") = some (.data (.str (JSStr.ofString "button")) true true true) ∧
      (w.objEntry E).props.get? (.str "key") = some (.data .null true true true) ∧
      (w.objEntry E).props.get? (.str "ref") = some (.data .null true true true) ∧
      (w.objEntry E).props.get? (.str "props") = some (.data (.obj C) true true true) ∧
      (w.objEntry C).props.get? (.str "children") =
        some (.data (.str (JSStr.ofString "Count: " ++ numberToJSStr xE ++ JSStr.ofString "")) true true true) ∧
      (w.objEntry C).props.get? (.str "onClick") = some (.data (.obj F) true true true) ∧
      E < w.heap.size ∧ C < w.heap.size ∧ s.heap.size ≤ E ∧ s.heap.size ≤ C ∧
      (w.objEntry E).kind = .ordinary ∧ (w.objEntry C).kind = .ordinary ∧ (w.objEntry C).proto = .obj OP ∧
      (w.objEntry C).props.get? (.str "ref") = none ∧
      (w.objEntry F).kind = .func dF' ∧ dF'.code = onClickFunc ∧ dF'.env = s.envs.size + 1 ∧
      dF'.thisMode = .lexical ∧
      Scope.declLike? (w.envEntry (s.envs.size + 1)) = some (((((∅ : HashMap JSStr Binding).insert
        (JSStr.ofString "n") { mutable := false, strict := true }).insert (JSStr.ofString "setN")
        { mutable := false, strict := true }).modify (JSStr.ofString "n") (fun bd => { bd with value := some (.num xE) })).modify
        (JSStr.ofString "setN") (fun bd => { bd with value := some dv }), some dK.env) ∧
      -- (the module's variables after the render, the dispatcher reset)
      Scope.declLike? (w.envEntry d.env) = some (ReactFinishHooks.resetMap (((((((bG.modify (JSStr.ofString "renderLanes") (fun bd => { bd with value := some two })).modify
        (JSStr.ofString "currentlyRenderingFiber") (fun bd => { bd with value := some (.obj C1) })).modify
        (JSStr.ofString "shouldDoubleInvokeUserFnsInHooksDEV") (fun bd => { bd with value := some (.bool false) })).modify
        (JSStr.ofString "currentHook") (fun bd => { bd with value := some (.obj H0) })).modify
        (JSStr.ofString "workInProgressHook") (fun bd => { bd with value := some (.obj s.heap.size) })).modify
        (JSStr.ofString "didReceiveUpdate") (fun bd => { bd with value := some (.bool true) })).modify
        (JSStr.ofString "shouldDoubleInvokeUserFnsInHooksDEV") (fun bd => { bd with value := some (.bool false) })), oG) ∧
      (w.objEntry RSI).props.get? (.str "H") = some (.data vCO true re rc) ∧
      -- (the work in progress: its new first hook, its update queue and lanes cleared)
      (w.objEntry C1).props.get? (.str "memoizedState") = some (.data (.obj s.heap.size) true me mc) ∧
      (w.objEntry C1).props.get? (.str "updateQueue") = some (.data .null true uw uc) ∧
      (w.objEntry C1).props.get? (.str "lanes") = some (.data (.num (F64.fin false 0 (-1074))) true lw lc) ∧
      (w.objEntry s.heap.size).props.get? (.str "memoizedState") = some (.data (.num xE) true true true) ∧
      (w.objEntry s.heap.size).props.get? (.str "baseState") = some (.data (.num xE) true true true) ∧
      (w.objEntry s.heap.size).props.get? (.str "baseQueue") = some (.data .null true true true) ∧
      (w.objEntry s.heap.size).props.get? (.str "queue") = some (.data (.obj Q) true true true) ∧
      (w.objEntry s.heap.size).props.get? (.str "next") = some (.data .null true true true) ∧
      (w.objEntry H0).props.get? (.str "baseQueue") = some (.data (.obj U) true e3 c3) ∧
      (w.objEntry Q).props.get? (.str "pending") = some (.data .null true qp.2.1 qp.2.2) ∧
      (w.objEntry Q).props.get? (.str "lastRenderedReducer") = some (.data r true qr.2.1 qr.2.2) ∧
      (w.objEntry Q).props.get? (.str "lastRenderedState") = some (.data (.num xE) true ql.2.1 ql.2.2) ∧
      ReactNewProps.NewProps w C F OP (JSStr.ofString "Count: " ++ numberToJSStr xE ++ JSStr.ofString "") := by
  apply wp_callGen RWHGen.renderWithHooks_eq (by decide) hRW hRWk (by omega) hRWcls hRWmode
    (by rw [hRWcode]; rfl) (by rw [hRWcode]; rfl) (simpleRW dRW hRWcode) (by rw [hRWcode]; rfl) (by rw [hRWcode]; rfl)
  have hpn : dRW.code.info.fdi.paramNames = #[JSStr.ofString "current", JSStr.ofString "workInProgress",
      JSStr.ofString "Component", JSStr.ofString "props", JSStr.ofString "secondArg", JSStr.ofString "nextRenderLanes"] := by
    rw [hRWcode]; rfl
  have hv : dRW.code.info.fdi.varNames = #[] := by rw [hRWcode]; rfl
  have hl : FDI.lexDecls dRW = #[] := by simp [FDI.lexDecls, hRWcode, RWHGen.renderWithHooks_func, Func.info]
  have ha : dRW.code.isAsync = false := by rw [hRWcode]; rfl
  have hne : s.envs.size ≠ d.env := Nat.ne_of_gt hG
  have hG1 : d.env < s.envs.size + 1 := Nat.lt_succ_of_lt hG
  have dfo1 : fo ≠ C1 := (hdist fo (by simp)).1
  have dfo2 : fo ≠ RSI := (hdist fo (by simp)).2
  have dfW1 : fW ≠ C1 := (hdist fW (by simp)).1
  have dfW2 : fW ≠ RSI := (hdist fW (by simp)).2
  have dfR1 : fR ≠ C1 := (hdist fR (by simp)).1
  have dfR2 : fR ≠ RSI := (hdist fR (by simp)).2
  have dfIs1 : fIs ≠ C1 := (hdist fIs (by simp)).1
  have dfIs2 : fIs ≠ RSI := (hdist fIs (by simp)).2
  have dC01 : C0 ≠ C1 := (hdist C0 (by simp)).1
  have dC02 : C0 ≠ RSI := (hdist C0 (by simp)).2
  have dH01 : H0 ≠ C1 := (hdist H0 (by simp)).1
  have dH02 : H0 ≠ RSI := (hdist H0 (by simp)).2
  have dQ1 : Q ≠ C1 := (hdist Q (by simp)).1
  have dQ2 : Q ≠ RSI := (hdist Q (by simp)).2
  have dU1 : U ≠ C1 := (hdist U (by simp)).1
  have dU2 : U ≠ RSI := (hdist U (by simp)).2
  have dfD1 : fD ≠ C1 := (hdist fD (by simp)).1
  have dfD2 : fD ≠ RSI := (hdist fD (by simp)).2
  have dHD1 : HD ≠ C1 := (hdist HD (by simp)).1
  have dHD2 : HD ≠ RSI := (hdist HD (by simp)).2
  have dfS1 : fS ≠ C1 := (hdist fS (by simp)).1
  have dfS2 : fS ≠ RSI := (hdist fS (by simp)).2
  have dIR1 : IR ≠ C1 := (hdist IR (by simp)).1
  have dIR2 : IR ≠ RSI := (hdist IR (by simp)).2
  have dIJ1 : IJ ≠ C1 := (hdist IJ (by simp)).1
  have dIJ2 : IJ ≠ RSI := (hdist IJ (by simp)).2
  have dfJ1 : fJ ≠ C1 := (hdist fJ (by simp)).1
  have dfJ2 : fJ ≠ RSI := (hdist fJ (by simp)).2
  have dAP1 : AP ≠ C1 := (hdist AP (by simp)).1
  have dAP2 : AP ≠ RSI := (hdist AP (by simp)).2
  have dfV1 : fV ≠ C1 := (hdist fV (by simp)).1
  have dfV2 : fV ≠ RSI := (hdist fV (by simp)).2
  have dAIP1 : AIP ≠ C1 := (hdist AIP (by simp)).1
  have dAIP2 : AIP ≠ RSI := (hdist AIP (by simp)).2
  have dfN1 : fN ≠ C1 := (hdist fN (by simp)).1
  have dfN2 : fN ≠ RSI := (hdist fN (by simp)).2
  have dIP1 : IP ≠ C1 := (hdist IP (by simp)).1
  have dIP2 : IP ≠ RSI := (hdist IP (by simp)).2
  have dOP1 : OP ≠ C1 := (hdist OP (by simp)).1
  have dOP2 : OP ≠ RSI := (hdist OP (by simp)).2
  have dfK1 : fK ≠ C1 := (hdist fK (by simp)).1
  have dfK2 : fK ≠ RSI := (hdist fK (by simp)).2
  have dfF1 : fF ≠ C1 := (hdist fF (by simp)).1
  have dfF2 : fF ≠ RSI := (hdist fF (by simp)).2
  clear hRWcode
  simp only [RWHGen.renderWithHooks]
  js [hpn, hv, hl, ha, hRWenv, hG, hG1, hne, Ne.symm hne, hGe, hGRL, hGRLm, hGRLi, hGF, hGFm, hGFi, hGSD, hGSDm,
    hGSDi, hGHU, hGHUv, hGRSd, hGRSdv, hC1, hC1k, hC1m, hC1u, hC1l, hC0, hC0k, hC0m, hI, hIk, hIH, dRC, Ne.symm dRC,
    hK, hKk, FDI.fdiCtx, Sem.inner]
  refine ⟨by js_norm [CallableC, hK, hKk, dfK1, dfK2, Ne.symm dfK1, Ne.symm dfK2], ?_⟩
  -- (the call's state: what renderWithHooks wrote)
  refine wp_gen_state fun St hSt => ?_
  have hStO : ∀ X, X ≠ C1 → X ≠ RSI → St.objEntry X = s.objEntry X := by
    intro X h1 h2; rw [hSt]; js_norm [h1, h2, Ne.symm h1, Ne.symm h2]
  have hStz : St.heap.size = s.heap.size := by rw [hSt]; js_norm
  have hStE : St.envs.size = s.envs.size + 1 := by rw [hSt]; js_norm
  have hStEe : ∀ e, e < s.envs.size → e ≠ d.env → St.envEntry e = s.envEntry e := by
    intro e he hd; rw [hSt]; js_norm [he, hd, Ne.symm hd, Nat.ne_of_lt he, Nat.ne_of_gt he]
  have hStd : Scope.declLike? (St.envEntry d.env) = some (((bG.modify (JSStr.ofString "renderLanes")
      (fun bd => { bd with value := some two })).modify (JSStr.ofString "currentlyRenderingFiber")
      (fun bd => { bd with value := some (.obj C1) })).modify (JSStr.ofString "shouldDoubleInvokeUserFnsInHooksDEV")
      (fun bd => { bd with value := some (.bool false) }), oG) := by
    rw [hSt]; js_norm [hG, hG1, hGe, hne, Ne.symm hne]
  have hStR : St.realms = s.realms := by rw [hSt]; rfl
  have hStF : St.fuel = s.fuel - 1 := by rw [hSt]; js_norm
  have hC1k' : (St.objEntry C1).kind.isPlain = true := by rw [hSt]; js_norm [hC1, hC1k, dRC, Ne.symm dRC]
  have hC1a' : (St.objEntry C1).props.get? (.str "alternate") = some (.data (.obj C0) aw ae ac) := by
    rw [hSt]; js_norm [hC1, hC1a, dRC, Ne.symm dRC]
  have hC1m' : (St.objEntry C1).props.get? (.str "memoizedState") = some (.data .null true me mc) := by
    rw [hSt]; js_norm [hC1, hC1m, dRC, Ne.symm dRC]
  have hIk' : (St.objEntry RSI).kind.isPlain = true := by rw [hSt]; js_norm [hI, hIk, dRC, Ne.symm dRC]
  have hIH' : (St.objEntry RSI).props.get? (.str "H") = some (.data (.obj HD) true re rc) := by
    rw [hSt]; js_norm [hI, hIH, dRC, Ne.symm dRC]
  have hF0 : Frame (fpRWH d.env C1 s.heap.size H0 Q RSI) s St := by
    rw [hSt]; simp only [fpRWH]; frame_go' [*, hne, Ne.symm hne, hG1]
  have hC1u' : (St.objEntry C1).props.get? (.str "updateQueue") = some (.data .null true uw uc) := by
    rw [hSt]; js_norm [hC1, hC1u, dRC, Ne.symm dRC]
  have hC1l' : (St.objEntry C1).props.get? (.str "lanes") = some (.data (.num (F64.fin false 0 (-1074))) true lw lc) := by
    rw [hSt]; js_norm [hC1, hC1l, dRC, Ne.symm dRC]
  have hStK : St.envEntry s.envs.size =
      (bodyState s fRW dRW tRW #[.obj C0, .obj C1, .obj fK, P, .undefined, two]).envEntry s.envs.size := by
    rw [hSt]; js_norm [hne, Ne.symm hne]
  clear hSt
  -- (`Counter(props, undefined)`)
  refine wp_mono (ReactCounter.click_spec (bG := ((bG.modify (JSStr.ofString "renderLanes")
      (fun bd => { bd with value := some two })).modify (JSStr.ofString "currentlyRenderingFiber")
      (fun bd => { bd with value := some (.obj C1) })).modify (JSStr.ofString "shouldDoubleInvokeUserFnsInHooksDEV")
      (fun bd => { bd with value := some (.bool false) })) (oG := oG)
      (bdF := { bdF with value := some (.obj C1) }) (bdRL := { bdRL with value := some two })
      (bdSD := { bdSD with value := some (.bool false) }) (tK := .undefined) (argsK := #[P, .undefined])
      (hS := (by rw [hStz]; exact hS)) (hSk := (by rw [hStO fS dfS1 dfS2]; exact hSk)) (hScode := hScode)
      (hScls := hScls) (hSmode := hSmode) (hSG := (by rw [hStE]; exact Nat.lt_succ_of_lt hSG))
      (hSGe := (by rw [hStEe _ hSG hSd]; exact hSGe)) (hRSI := hRSI) (hRSIv := hRSIv)
      (hI := (by rw [hStz]; exact hI)) (hIk := hIk') (hIH := hIH') (hHD := (by rw [hStz]; exact hHD))
      (hHDk := (by rw [hStO HD dHD1 dHD2]; exact hHDk)) (hHDu := (by rw [hStO HD dHD1 dHD2]; exact hHDu))
      (hD := (by rw [hStz]; exact hD)) (hDk := (by rw [hStO fD dfD1 dfD2]; exact hDk)) (hDcode := hDcode)
      (hDcls := hDcls) (hDmode := hDmode) (hDenv := hDenv) (hGU := (by js_norm [hGU])) (hGUv := hGUv)
      (hGB := (by js_norm [hGB])) (hGBv := hGBv) (hlt := (by rw [hStz]; exact hlt))
      (hk := (by rw [hStO fo dfo1 dfo2]; exact hk)) (hf := (by rw [hStF]; omega)) (hcode := hcode) (hcls := hcls)
      (hmode := hmode) (hG := (by rw [hStE]; exact Nat.lt_succ_of_lt hG)) (hGe := hStd) (hGC := (by js_norm [hGC]))
      (hGCm := hGCm) (hGCv := hGCv) (hGW := (by js_norm [hGW])) (hGWm := hGWm) (hGWv := hGWv)
      (hGF := (by js_norm [hGF])) (hGFv := rfl) (hGUW := (by js_norm [hGUW])) (hGUWv := hGUWv)
      (hW := (by rw [hStz]; exact hW)) (hWk := (by rw [hStO fW dfW1 dfW2]; exact hWk)) (hWcode := hWcode)
      (hWcls := hWcls) (hWmode := hWmode) (hWenv := hWenv) (hGUR := (by js_norm [hGUR])) (hGURv := hGURv)
      (hR := (by rw [hStz]; exact hR)) (hRk := (by rw [hStO fR dfR1 dfR2]; exact hRk)) (hRcode := hRcode)
      (hRcls := hRcls) (hRmode := hRmode) (hRenv := hRenv) (hGRL := (by js_norm [hGRL])) (hGRLv := rfl)
      (hGCE := (by js_norm [hGCE])) (hGCEv := hGCEv) (hGSD := (by js_norm [hGSD])) (hGSDv := rfl)
      (hGDR := (by js_norm [hGDR])) (hGDRm := hGDRm) (hGDRi := hGDRi) (hGIs := (by js_norm [hGIs])) (hGIsv := hGIsv)
      (hIs := (by rw [hStz]; exact hIs)) (hIsk := (by rw [hStO fIs dfIs1 dfIs2]; exact hIsk)) (hIstab := hIstab)
      (hC1 := (by rw [hStz]; exact hC1)) (hC1k := hC1k') (hC1a := hC1a') (hC1m := hC1m')
      (hC0 := (by rw [hStz]; exact hC0)) (hC0k := (by rw [hStO C0 dC01 dC02]; exact hC0k))
      (hC0m := (by rw [hStO C0 dC01 dC02]; exact hC0m)) (hH0 := (by rw [hStz]; exact hH0))
      (hH0k := (by rw [hStO H0 dH01 dH02]; exact hH0k)) (hHm := (by rw [hStO H0 dH01 dH02]; exact hHm))
      (hHb := (by rw [hStO H0 dH01 dH02]; exact hHb)) (hHbq := (by rw [hStO H0 dH01 dH02]; exact hHbq))
      (hHq := (by rw [hStO H0 dH01 dH02]; exact hHq)) (hQ := (by rw [hStz]; exact hQ))
      (hQk := (by rw [hStO Q dQ1 dQ2]; exact hQk)) (hQp := (by rw [hStO Q dQ1 dQ2]; exact hQp))
      (hQr := (by rw [hStO Q dQ1 dQ2]; exact hQr)) (hQl := (by rw [hStO Q dQ1 dQ2]; exact hQl))
      (hQd := (by rw [hStO Q dQ1 dQ2]; exact hQd)) (hU := (by rw [hStz]; exact hU))
      (hUk := (by rw [hStO U dU1 dU2]; exact hUk)) (hUl := (by rw [hStO U dU1 dU2]; exact hUl))
      (hUr := (by rw [hStO U dU1 dU2]; exact hUr)) (hUa := (by rw [hStO U dU1 dU2]; exact hUa))
      (hUe := (by rw [hStO U dU1 dU2]; exact hUe)) (hUv := (by rw [hStO U dU1 dU2]; exact hUv))
      (hUn := (by rw [hStO U dU1 dU2]; exact hUn)) (hdiff := hdiff) (d1 := d1) (d2 := d2) (d3 := d3) (d4 := d4)
      (d5 := d5) (d6 := d6) (d7 := d7) (d8 := d8) (d9 := d9) (d10 := d10) (d11 := d11) (d12 := d12)
      (hK := (by rw [hStz]; exact hK)) (hKk := (by rw [hStO fK dfK1 dfK2]; exact hKk)) (hKcode := hKcode)
      (hKcls := hKcls) (hKmode := hKmode) (hAG := (by rw [hStE]; exact Nat.lt_succ_of_lt hAG))
      (hAGe := (by rw [hStEe _ hAG hKd]; exact hAGe)) (hAR := hAR) (hARv := hARv) (hIR := (by rw [hStz]; exact hIR))
      (hIRk := (by rw [hStO IR dIR1 dIR2]; exact hIRk)) (hIRu := (by rw [hStO IR dIR1 dIR2]; exact hIRu))
      (hAJ := hAJ) (hAJv := hAJv) (hIJ := (by rw [hStz]; exact hIJ))
      (hIJk := (by rw [hStO IJ dIJ1 dIJ2]; exact hIJk)) (hIJj := (by rw [hStO IJ dIJ1 dIJ2]; exact hIJj))
      (hJ := (by rw [hStz]; exact hJ)) (hJk := (by rw [hStO fJ dfJ1 dfJ2]; exact hJk)) (hJcode := hJcode)
      (hJcls := hJcls) (hJmode := hJmode) (hJG := (by rw [hStE]; exact Nat.lt_succ_of_lt hJG))
      (hJGe := (by rw [hStEe _ hJG hJd]; exact hJGe)) (hJT := hJT) (hJTv := hJTv) (hAP := (by rw [hStR]; exact hAP))
      (hP := (by rw [hStz]; exact hP)) (hPk := (by rw [hStO AP dAP1 dAP2]; exact hPk))
      (hPv := (by rw [hStO AP dAP1 dAP2]; exact hPv)) (hV := (by rw [hStz]; exact hV))
      (hVk := (by rw [hStO fV dfV1 dfV2]; exact hVk)) (hVfn := hVfn) (hVr := hVr) (hII := (by rw [hStR]; exact hII))
      (hAIP := (by rw [hStz]; exact hAIP)) (hAIPk := (by rw [hStO AIP dAIP1 dAIP2]; exact hAIPk))
      (hAIPn := (by rw [hStO AIP dAIP1 dAIP2]; exact hAIPn)) (hN := (by rw [hStz]; exact hN))
      (hNk := (by rw [hStO fN dfN1 dfN2]; exact hNk)) (hNfn := hNfn) (hNr := hNr)
      (hAIPp := (by rw [hStO AIP dAIP1 dAIP2]; exact hAIPp)) (hAIPr := (by rw [hStO AIP dAIP1 dAIP2]; exact hAIPr))
      (hIP := (by rw [hStz]; exact hIP)) (hIPk := (by rw [hStO IP dIP1 dIP2]; exact hIPk))
      (hIPr := (by rw [hStO IP dIP1 dIP2]; exact hIPr)) (hIPp := (by rw [hStO IP dIP1 dIP2]; exact hIPp))
      (hOPe := (by rw [hStR]; exact hOPe)) (hOP := (by rw [hStz]; exact hOP))
      (hOPk := (by rw [hStO OP dOP1 dOP2]; exact hOPk)) (hOPr := (by rw [hStO OP dOP1 dOP2]; exact hOPr))
      (hOPp := (by rw [hStO OP dOP1 dOP2]; exact hOPp)) (hOPkey := (by rw [hStO OP dOP1 dOP2]; exact hOPkey))
      (hOPref := (by rw [hStO OP dOP1 dOP2]; exact hOPref)) (hFP := (by rw [hStR]; exact hFP)) (hvE := hvE)
      (dAP := dAP) (dfV := dfV) (dAIP := dAIP) (dfN := dfN) (dIP := dIP) (dOP := dOP) (dIJ := dIJ) (dfJ := dfJ)
      (hKd := hKd) (hJd := hJd)) ?post
  intro v w h1 ⟨E, C, F, dF', hvE, hEb, hCb, hFb, hKb, hEKb, hEge, hCge, hFc, hfuc, hhc, hEt, hEty, hEkey, hEref, hEpr, hCch, hCoc, hEk', hCk', hCp', hCr', hFk, hFcode, hFenv, hFthis,
    hdK', hdG, hm1, hk1, hk2, hk3, hk4, hk5, hH0b, hQp1, hQr1, hQl1, hNP⟩
  subst v h1
  rw [hStz] at hFc
  -- (renderWithHooks' own record, untouched by the component)
  have hRWe : w.envEntry s.envs.size = St.envEntry s.envs.size :=
    envEntry_frame hFc (by rw [hStE]; exact Nat.lt_succ_self _)
      (by simp [fpU, ReactHooks.fpW, fpR, Footprint.union, Nat.ne_of_gt hG, Ne.symm (Nat.ne_of_gt hG)])
  have hEw : s.envs.size < w.envs.size := envs_frame hFc (by rw [hStE]; exact Nat.lt_succ_self _)
  have hGw : d.env < w.envs.size := envs_frame hFc (by rw [hStE]; exact Nat.lt_succ_of_lt hG)
  js [hpn, hv, hl, ha, hEw, hRWe, hStK, hGw, hdG, hGSD, hGDP, hGDPv, hGFR, hGFRv, hne, Ne.symm hne, FDI.fdiCtx, Sem.inner]
  -- (`finishRenderingHooks(current)`: the objects it reads are as the component left them)
  have hfpU : ∀ o, o ≠ C1 → o ≠ s.heap.size → o ≠ H0 → o ≠ Q →
      (fpU d.env C1 s.heap.size H0 Q).props.all (fun p => p.1 != o) = true := by
    intro o h1 h2 h3 h4; simp [fpU, ReactHooks.fpW, fpR, Footprint.union, Ne.symm h1, Ne.symm h2, Ne.symm h3, Ne.symm h4]
  have hwF : w.objEntry fF = s.objEntry fF := by
    rw [objEntry_frame hFc (by rw [hStz]; exact hFF) (hfpU fF dfF1 (Nat.ne_of_lt hFF) dFH.1 dFH.2), hStO fF dfF1 dfF2]
  have hFw : fF < w.heap.size := heap_frame hFc (by rw [hStz]; exact hFF)
  have hwI : w.objEntry RSI = St.objEntry RSI :=
    objEntry_frame hFc (by rw [hStz]; exact hI) (hfpU RSI dRC (Nat.ne_of_lt hI) (Ne.symm dH02) dRQ)
  have hIw : RSI < w.heap.size := heap_frame hFc (by rw [hStz]; exact hI)
  have hwH0n : (w.objEntry H0).props.get? (.str "next") = some (.data .null nw' ne' nc') := by
    rw [props_frame hFc (by rw [hStz]; exact hH0) (by simp [fpU, ReactHooks.fpW, fpR, Footprint.union]),
      hStO H0 dH01 dH02]; exact hH0n
  have hwH0k : (w.objEntry H0).kind.isPlain = true := by
    rw [kind_frame hFc (by rw [hStz]; exact hH0), hStO H0 dH01 dH02]; exact hH0k
  have hH0w : H0 < w.heap.size := heap_frame hFc (by rw [hStz]; exact hH0)
  have hfw : 99 ≤ w.fuel := by rw [hStF] at hfuc; omega
  refine ⟨by js_norm [CallableC, hwF, hFFk, hFw, hwI, hIk', hIH', hIw, hwH0n, hwH0k, hH0w, hGw, hne, Ne.symm hne, hEw, hRWe, hStK, hdG, hGRSd, hGRSdv, hGCO, hGCOv, hGC, hGCm, hGRL, hGRLm, hGW, hGWm, hGF, hGFm, hGDS, hGDSm, hGDSi, hGTI, hGTIm, hGTIi, hGTS, hGTSm, hGTSi, hGDR, Ne.symm dH02, hfw, hFFenv], ?_⟩
  refine wp_mono (ReactFinishHooks.spec (bG := ((((((bG.modify (JSStr.ofString "renderLanes") (fun bd => { bd with value := some two })).modify
        (JSStr.ofString "currentlyRenderingFiber") (fun bd => { bd with value := some (.obj C1) })).modify
        (JSStr.ofString "shouldDoubleInvokeUserFnsInHooksDEV") (fun bd => { bd with value := some (.bool false) })).modify
        (JSStr.ofString "currentHook") (fun bd => { bd with value := some (.obj H0) })).modify
        (JSStr.ofString "workInProgressHook") (fun bd => { bd with value := some (.obj s.heap.size) })).modify
        (JSStr.ofString "didReceiveUpdate") (fun bd => { bd with value := some (.bool true) })).modify
        (JSStr.ofString "shouldDoubleInvokeUserFnsInHooksDEV") (fun bd => { bd with value := some (.bool false) })) (oG := oG) (bdRS := bdRSd) (bdCO := bdCO)
      (bdCH := { bdC with value := some (.obj H0) }) (bdRL := { bdRL with value := some two })
      (bdWH := { bdW with value := some (.obj s.heap.size) }) (bdCF := { bdF with value := some (.obj C1) })
      (bdDS := bdDS) (bdTI := bdTI) (bdTS := bdTS) (bdDR := { bdDR with value := some (.bool true) }) (RSI := RSI)
      (H0 := H0) (vCO := vCO) (vH := .obj HD) (re := re) (rc := rc) (nw := nw') (ne := ne') (nc := nc')
      ?_ ?_ ?_ hFFcode hFFcls hFFmode ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) ?post2
  all_goals first
    | (js_norm [hwF, hFFk, hFw, hwI, hIk', hIH', hIw, hwH0n, hwH0k, hH0w, hGw, hne, Ne.symm hne, hEw, hRWe, hStK, hdG, hGRSd, hGRSdv, hGCO, hGCOv, hGC, hGCm, hGRL, hGRLm, hGW, hGWm, hGF, hGFm, hGDS, hGDSm, hGDSi, hGTI, hGTIm, hGTIi, hGTS, hGTSm, hGTSi, hGDR, Ne.symm dH02, hfw, hFFenv]; done)
    | (js_norm [hwF, hFFk, hFw, hwI, hIk', hIH', hIw, hwH0n, hwH0k, hH0w, hGw, hne, Ne.symm hne, hEw, hRWe, hStK, hdG, hGRSd, hGRSdv, hGCO, hGCOv, hGC, hGCm, hGRL, hGRLm, hGW, hGWm, hGF, hGFm, hGDS, hGDSm, hGDSi, hGTI, hGTIm, hGTIi, hGTS, hGTSm, hGTSi, hGDR, Ne.symm dH02, hfw, hFFenv]; omega)
    | (simp; done)
    | (rw [hFFenv]; js_norm [hdG, hGw, hne, Ne.symm hne, hEw, hStz]; done)
    | skip
  case post2 =>
  intro v2 w2 h2 ⟨hv2, hF2, hfu2, hh2, hr2, hdl2, hRSIH2⟩
  subst v2 h2
  rw [hFFenv] at hF2 hdl2
  have hw2K := envEntry_frame hF2 (e := s.envs.size) (by js_norm [hEw]) (by simp [ReactFinishHooks.fpF, hne, Ne.symm hne])
  have hw2E := envs_frame hF2 (e := s.envs.size) (by js_norm [hEw])
  simp (config := { maxDischargeDepth := 6 }) only [js_simp, ↓reduceIte, hne, Ne.symm hne, hRWe, hStK, hEw] at hw2K hw2E
  have hfw2 : 69 ≤ w2.fuel := by simp only [js_simp] at hfu2; omega
  js [hpn, hv, hl, ha, hw2K, hw2E, hfw2, hne, Ne.symm hne, FDI.fdiCtx, Sem.inner]
  -- (the facts at the end: through finishRenderingHooks' frame, whose only object write is ReactSharedInternals.H)
  rw [hStz] at hk1 hk2 hk3 hk4 hk5 hm1 hdG
  rw [hStE] at hdK' hFenv
  have hpw : ∀ o k, o < w.heap.size → k ≠ PropKey.str (JSStr.ofString "H") →
      (w2.objEntry o).props.get? k = (w.objEntry o).props.get? k := by
    intro o k ho hk
    rw [props_frame hF2 (by simp only [js_simp]; exact ho) (by simp [ReactFinishHooks.fpF]; intro _; exact hk)]
    simp only [js_simp]
  have hpC : ∀ o k, o < s.heap.size → o ≠ C1 → o ≠ s.heap.size → o ≠ H0 → o ≠ Q →
      (w.objEntry o).props.get? k = (St.objEntry o).props.get? k := by
    intro o k ho h1 h2 h3 h4
    rw [objEntry_frame hFc (by rw [hStz]; exact ho) (hfpU o h1 h2 h3 h4)]
  have hC1w : C1 < w.heap.size := heap_frame hFc (by rw [hStz]; exact hC1)
  have hKw : s.heap.size < w.heap.size := by rw [← hStz]; exact hKb
  have hQw : Q < w.heap.size := heap_frame hFc (by rw [hStz]; exact hQ)
  have hH0w' : H0 < w.heap.size := hH0w
  have hfF : Frame (fpRWH d.env C1 s.heap.size H0 Q RSI) s w :=
    frame_extend hF0 hFc (by simp [fpU, ReactHooks.fpW, fpR, Footprint.union, fpRWH])
      (by simp [fpU, ReactHooks.fpW, fpR, Footprint.union, fpRWH]) (fun _ => rfl)
  subst hvE
  have hKe : s.envs.size + 1 < w.envs.size := by rw [← hStE]; exact hEKb
  have Et := (hpw E _ hEb (by decide)).trans hEt
  have Ety := (hpw E _ hEb (by decide)).trans hEty
  have Ek := (hpw E _ hEb (by decide)).trans hEkey
  have Er := (hpw E _ hEb (by decide)).trans hEref
  have Ep := (hpw E _ hEb (by decide)).trans hEpr
  have Cch := (hpw C _ hCb (by decide)).trans hCch
  have Coc := (hpw C _ hCb (by decide)).trans hCoc
  have Ek2 : (w2.objEntry E).kind = .ordinary := by
    rw [kind_frame hF2 (by simp only [js_simp]; exact hEb)]; simp only [js_simp]; exact hEk'
  have Ck2 : (w2.objEntry C).kind = .ordinary := by
    rw [kind_frame hF2 (by simp only [js_simp]; exact hCb)]; simp only [js_simp]; exact hCk'
  have Cp2 : (w2.objEntry C).proto = .obj OP := by
    rw [(hF2.obj_agree C (by simp only [js_simp]; exact hCb)).2.1]; simp only [js_simp]; exact hCp'
  have Cr2 := (hpw C _ hCb (by decide)).trans hCr'
  have Ege2 : s.heap.size ≤ E := by rw [← hStz]; exact hEge
  have NP2 : ReactNewProps.NewProps w2 C F OP (JSStr.ofString "Count: " ++ numberToJSStr xE ++ JSStr.ofString "") := by
    refine ReactNewProps.NewProps.frame hF2 ?_ ?_
    · unfold ReactNewProps.NewProps at hNP ⊢; simp only [js_simp]; exact hNP
    · intro k hk
      have hIC : RSI ≠ C := Nat.ne_of_lt (Nat.lt_of_lt_of_le hI (by rw [← hStz]; exact hCge))
      simp [ReactFinishHooks.fpF, Ne.symm hIC] at hk
  have Cge2 : s.heap.size ≤ C := by rw [← hStz]; exact hCge
  have Eb2 : E < w2.heap.size := Nat.lt_of_lt_of_le (by simp only [js_simp]; exact hEb) hF2.heap_le
  have Cb2 : C < w2.heap.size := Nat.lt_of_lt_of_le (by simp only [js_simp]; exact hCb) hF2.heap_le
  have Fk : (w2.objEntry F).kind = .func dF' := by
    rw [kind_frame hF2 (by simp only [js_simp]; exact hFb)]; simp only [js_simp]; exact hFk
  have dK2 : Scope.declLike? (w2.envEntry (s.envs.size + 1)) = some (((((∅ : HashMap JSStr Binding).insert
      (JSStr.ofString "n") { mutable := false, strict := true }).insert (JSStr.ofString "setN")
      { mutable := false, strict := true }).modify (JSStr.ofString "n") (fun bd => { bd with value := some (.num xE) })).modify
      (JSStr.ofString "setN") (fun bd => { bd with value := some dv }), some dK.env) := by
    rw [envEntry_frame hF2 (e := s.envs.size + 1) (by simp only [js_simp]; exact hKe)
      (by simp [ReactFinishHooks.fpF, Nat.ne_of_lt (Nat.lt_succ_of_lt hG)])]
    simp only [js_simp, Nat.ne_of_lt (Nat.lt_succ_of_lt hG), Ne.symm (Nat.ne_of_lt (Nat.lt_succ_of_lt hG)),
      Nat.succ_ne_self, ↓reduceIte, hKe]
    exact hdK'
  have m1 := (hpw C1 _ hC1w (by decide)).trans hm1
  have u1 := (hpw C1 _ hC1w (by decide)).trans ((props_frame hFc (by rw [hStz]; exact hC1)
    (by simp [fpU, ReactHooks.fpW, fpR, Footprint.union])).trans hC1u')
  have l1 := (hpw C1 _ hC1w (by decide)).trans ((props_frame hFc (by rw [hStz]; exact hC1)
    (by simp [fpU, ReactHooks.fpW, fpR, Footprint.union])).trans hC1l')
  have k1 := (hpw _ _ hKw (by decide)).trans hk1
  have k2 := (hpw _ _ hKw (by decide)).trans hk2
  have k3 := (hpw _ _ hKw (by decide)).trans hk3
  have k4 := (hpw _ _ hKw (by decide)).trans hk4
  have k5 := (hpw _ _ hKw (by decide)).trans hk5
  have h0 := (hpw H0 _ hH0w' (by decide)).trans hH0b
  have q1 := (hpw Q _ hQw (by decide)).trans hQp1
  have q2 := (hpw Q _ hQw (by decide)).trans hQr1
  have q3 := (hpw Q _ hQw (by decide)).trans hQl1
  have hfuel : s.fuel ≤ w2.fuel + 300 := by
    simp only [js_simp] at hfu2
    rw [hStF] at hfuc
    omega
  have hframe : Frame (fpRWH d.env C1 s.heap.size H0 Q RSI) s (w2.restore s) := by
    refine frame_restore (frame_extend ?h12 hF2 (by simp [ReactFinishHooks.fpF, fpRWH])
      (by simp [ReactFinishHooks.fpF, fpRWH]) (fun _ => by simp [ReactFinishHooks.fpF])) s
    case h12 =>
      clear hFc hF0
      simp only [fpRWH] at hfF ⊢
      frame_go' [hfF, hdG, hne, Ne.symm hne, hG, hEw, hGw]
  refine ⟨E, C, F, dF', ?_⟩
  repeat' apply And.intro
  all_goals first
    | rfl | exact hfuel | exact hframe | exact Ek2 | exact Ck2 | exact Cp2 | exact Cr2 | exact Eb2 | exact Cb2 | exact Ege2 | exact Cge2 | exact Et | exact Ety | exact Ek | exact Er | exact Ep | exact Cch | exact Coc | exact Fk
    | exact hFcode | exact hFenv | exact hFthis | exact dK2 | exact hdl2 | exact hRSIH2 | exact m1 | exact u1
    | exact l1 | exact k1 | exact k2 | exact k3 | exact k4 | exact k5 | exact h0 | exact q1 | exact q2 | exact q3
    | (simp only [restore_objEntry]; first | exact NP2.2.2.2.1 | exact NP2.2.2.2.2.2.2.1 | exact NP2.2.2.2.2.2.2.2.2)
    | exact NP2.2.2.2.2.2.2.2.2
    | skip


end

end ReactRenderHooks
