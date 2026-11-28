import JSProofs.ReactRenderHooks
import JSProofs.ReactReconcileChildren
import JSProofs.ReactRenderPrep
import JSProofs.UFCGen
import JSProofs.FrameExt

/-!
# `updateFunctionComponent` for the counter's re-render after a click (zippy docs/react-proofs.md)

`prepareToReadContext` (`ReactRenderPrep`), `renderWithHooks` (`ReactRenderHooks.click_spec`: the button element),
`checkDidRenderIdHook` (false), no bailout (`didReceiveUpdate` is true), the work in progress's `PerformedWork` flag,
`reconcileChildren` (`ReactReconcileChildren.click_spec`: the current button fiber's alternate reused); returns it.
-/

open ES ES.M HostRuns Logic ReactReducer ReactUpdateReducer ReactUseState ReactCounter ReactRenderHooks
open Std (HashMap)

namespace ReactUpdateFunction

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ}

/-- What it writes: the render's module variables, the work in progress's fields, ReactSharedInternals.H, the
current hook's base queue, the update queue, the reused button fiber's fields. -/
def fpUF (g : EnvId) (C1 H0 Q RSI X : ObjId) : Footprint :=
  ⟨[(g, "currentlyRenderingFiber$1"), (g, "lastContextDependency"), (g, "renderLanes"), (g, "currentlyRenderingFiber"),
    (g, "shouldDoubleInvokeUserFnsInHooksDEV"), (g, "currentHook"), (g, "workInProgressHook"), (g, "didReceiveUpdate"),
    (g, "didScheduleRenderPhaseUpdate"), (g, "thenableIndexCounter"), (g, "thenableState"), (g, "localIdCounter"),
    (g, "thenableIndexCounter$1"), (g, "thenableState$1")],
   [(C1, .str "memoizedState"), (C1, .str "updateQueue"), (C1, .str "lanes"), (C1, .str "flags"), (C1, .str "child"),
    (RSI, .str "H"), (H0, .str "baseQueue"), (Q, .str "pending"), (Q, .str "lastRenderedReducer"),
    (Q, .str "lastRenderedState")] ++ (ReactReconcileImpl.fpI X).props, false⟩

/-- What it writes before `reconcileChildren`: `fpUF` without the reused button fiber's fields. -/
def fpUF0 (g : EnvId) (C1 H0 Q RSI : ObjId) : Footprint :=
  ⟨[(g, "currentlyRenderingFiber$1"), (g, "lastContextDependency"), (g, "renderLanes"), (g, "currentlyRenderingFiber"),
    (g, "shouldDoubleInvokeUserFnsInHooksDEV"), (g, "currentHook"), (g, "workInProgressHook"), (g, "didReceiveUpdate"),
    (g, "didScheduleRenderPhaseUpdate"), (g, "thenableIndexCounter"), (g, "thenableState"), (g, "localIdCounter"),
    (g, "thenableIndexCounter$1"), (g, "thenableState$1")],
   [(C1, .str "memoizedState"), (C1, .str "updateQueue"), (C1, .str "lanes"), (C1, .str "flags"), (C1, .str "child"),
    (RSI, .str "H"), (H0, .str "baseQueue"), (Q, .str "pending"), (Q, .str "lastRenderedReducer"),
    (Q, .str "lastRenderedState")], false⟩

theorem simpleUF (d : FuncData) (hc : d.code = UFCGen.updateFunctionComponent_func) : FDI.Simple d := by
  constructor <;> rw [hc] <;> try rfl
  simp [UFCGen.updateFunctionComponent_func, Func.params, Func.info]

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
/-- **`updateFunctionComponent(current, workInProgress, Counter, props, 2)`** in the click's re-render. -/
theorem click_spec {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {s : State}
    {bG : HashMap JSStr Binding} {oG : Option EnvId} {fD : ObjId} {dD : FuncData} {fS RSI HD : ObjId} {dS : FuncData} {bR : HashMap JSStr Binding}
    {oR : Option EnvId} {fK IR IJ fJ AP fV fN AIP IP OP : ObjId} {dK dJ : FuncData} {vT P ms1 vH0 vCO uq ln tRW : Value} {fF fRW : ObjId} {dF dRW : FuncData}
    {bdHU bdRSd bdDP bdFR bdCO bdDS bdTI bdTS : Binding} {uw ue uc lw le lc nw' ne' nc' : Bool}
    {bA bJ : HashMap JSStr Binding} {oA oJ : Option EnvId} {bdIR bdIJ bdT : Binding} {bdV bdN : BuiltinData} {xE : F64}
    {irw ire irc ijw ije ijc pw pe pc nnw nne nnc : Bool} {bdRSI : Binding} {rw re rc uw ue' uc : Bool} {bdU bdB : Binding}
    {bdC bdW bdF bdUW bdUR bdRL bdCE bdSD bdDR bdIs : Binding} {bdIsb : BuiltinData}
    {fW fR fIs C1 C0 H0 Q U fBS : ObjId} {dW dR dBS : FuncData} {r ms bs vE a dv : Value}
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
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : 500 ≤ s.fuel)
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
    (hUe : (s.objEntry U).props.get? (.str "hasEagerState") = some (.data (.bool false) ue.1 ue.2.1 ue.2.2))
    (hUv : (s.objEntry U).props.get? (.str "action") = some (.data vE uv.1 uv.2.1 uv.2.2))
    (hUn : (s.objEntry U).props.get? (.str "next") = some (.data (.obj U) un.1 un.2.1 un.2.2))
    (hdiff : sameValue vE ms = false)
    (hrBS : r = .obj fBS) (hBS : fBS < s.heap.size) (hBSk : (s.objEntry fBS).kind = .func dBS)
    (hBScode : dBS.code = BSRGen.basicStateReducer_func) (hBScls : dBS.isClassCtor = false)
    (hBSmode : dBS.thisMode = .strict)
    (dBS1 : C1 ≠ fBS) (dBS2 : fBS ≠ H0) (dBS3 : fBS ≠ Q) (dBS4 : fBS ≠ U)
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
    (hdist : ∀ X ∈ [fo, fW, fR, fIs, fBS, C0, H0, Q, U, fD, HD, fS, IR, IJ, fJ, AP, fV, AIP, fN, IP, OP, fK, fF],
      X ≠ C1 ∧ X ≠ RSI) (dRC : RSI ≠ C1) (hSd : dS.env ≠ d.env)
    -- (renderWithHooks itself, a function of react-dom's module)
    (hRW : fRW < s.heap.size) (hRWk : (s.objEntry fRW).kind = .func dRW)
    (hRWcode : dRW.code = RWHGen.renderWithHooks_func) (hRWcls : dRW.isClassCtor = false)
    (hRWmode : dRW.thisMode = .strict) (hRWenv : dRW.env = d.env)
    (dFH : fF ≠ H0 ∧ fF ≠ Q) (dRQ : RSI ≠ Q)
    -- (reconcileChildren's premises, its objects renamed)
    {r_fo : ObjId} {r_d : FuncData} {fU : ObjId} {dU : FuncData} {r_bR : HashMap JSStr Binding} {bdCW : Binding}
    {H X : ObjId} {fl : F64}
    {vHT vCL vL vC vMP vMS vUQ vI vR vRC o0 o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 o11 o12 o13 o14 o15 : Value}
    {r0w r0e r0c r1w r1e r1c r2w r2e r2c r3w r3e r3c r4w r4e r4c r5w r5e r5c r6w r6e r6c r7w r7e r7c r8w r8e r8c r9w r9e r9c r10w r10e r10c r11w r11e r11c r12w r12e r12c r13w r13e r13c e0 c0 r_e1 r_c1 r_e2 r_c2 r_e3 r_c3 r_e4 r_c4 e5 c5 e6 c6 e7 c7 e8 c8 e9 c9 e10 c10 e11 c11 e12 c12 e13 c13 e14 c14 e15 c15 : Bool}
    {fI fDel fPl fCR : ObjId} {dI dDel dPl dCR : FuncData} {vFr : Value}
    {bdDel bdUF bdPl bdST bdFr bdEl bdCR : Binding}
    {ew ee ec kw ke kc yw ye yc r_pw r_pe r_pc bkw bke bkc bew bee bec r_aw r_ae r_ac rew rec : Bool}
    {rv0 : Value} {r_fR : ObjId} {r_dR : FuncData} {bdRI r_bdT r_bdTS : Binding} {fC : ObjId} {dC : FuncData}
    {bdRCF : Binding} {c0w c0e c0c cw cc : Bool} {ch0 : Value}
    (rhU : fU < s.heap.size) (rhUk : (s.objEntry fU).kind = .func dU) (rhUcode : dU.code = CCRGen.useFiber_func)
    (rhUcls : dU.isClassCtor = false) (rhUmode : dU.thisMode = .strict) (rhE : dU.env < s.envs.size)
    (rhEe : Scope.declLike? (s.envEntry dU.env) = some (r_bR, some d.env))
    (rhEn : r_bR[JSStr.ofString "createWorkInProgress"]? = none)
    (rhGC : bG[JSStr.ofString "createWorkInProgress"]? = some bdCW) (rhGCv : bdCW.value = some (.obj r_fo))
    (rhlt : r_fo < s.heap.size) (rhk : (s.objEntry r_fo).kind = .func r_d) (rhf : 170 ≤ s.fuel)
    (rhcode : r_d.code = CWIPGen.createWorkInProgress_func) (rhcls : r_d.isClassCtor = false)
    (rhmode : r_d.thisMode = .strict) (rhH : H < s.heap.size) (rhHk : (s.objEntry H).kind.isPlain = true)
    (rhX : X < s.heap.size) (rhXk : (s.objEntry X).kind.isPlain = true) (rhHX : H ≠ X)
    (rhHa : (s.objEntry H).props.get? (.str "alternate") = some (.data (.obj X) r11w r11e r11c))
    (rhHf : (s.objEntry H).props.get? (.str "flags") = some (.data (.num fl) r12w r12e r12c))
    (rhHd : (s.objEntry H).props.get? (.str "dependencies") = some (.data .null r13w r13e r13c))
    (rhH_type : (s.objEntry H).props.get? (.str "type") = some (.data vHT r0w r0e r0c))
    (rhH_childLanes : (s.objEntry H).props.get? (.str "childLanes") = some (.data vCL r1w r1e r1c))
    (rhH_lanes : (s.objEntry H).props.get? (.str "lanes") = some (.data vL r2w r2e r2c))
    (rhH_child : (s.objEntry H).props.get? (.str "child") = some (.data vC r3w r3e r3c))
    (rhH_memoizedProps : (s.objEntry H).props.get? (.str "memoizedProps") = some (.data vMP r4w r4e r4c))
    (rhH_memoizedState : (s.objEntry H).props.get? (.str "memoizedState") = some (.data vMS r5w r5e r5c))
    (rhH_updateQueue : (s.objEntry H).props.get? (.str "updateQueue") = some (.data vUQ r6w r6e r6c))
    (rhH_sibling : (s.objEntry H).props.get? (.str "sibling") = some (.data .null r7w r7e r7c))
    (rhH_index : (s.objEntry H).props.get? (.str "index") = some (.data vI r8w r8e r8c))
    (rhH_ref : (s.objEntry H).props.get? (.str "ref") = some (.data vR r9w r9e r9c))
    (rhH_refCleanup : (s.objEntry H).props.get? (.str "refCleanup") = some (.data vRC r10w r10e r10c))
    (rhX_pendingProps : (s.objEntry X).props.get? (.str "pendingProps") = some (.data o0 true e0 c0))
    (rhX_type : (s.objEntry X).props.get? (.str "type") = some (.data o1 true r_e1 r_c1))
    (rhX_flags : (s.objEntry X).props.get? (.str "flags") = some (.data o2 true r_e2 r_c2))
    (rhX_subtreeFlags : (s.objEntry X).props.get? (.str "subtreeFlags") = some (.data o3 true r_e3 r_c3))
    (rhX_deletions : (s.objEntry X).props.get? (.str "deletions") = some (.data o4 true r_e4 r_c4))
    (rhX_childLanes : (s.objEntry X).props.get? (.str "childLanes") = some (.data o5 true e5 c5))
    (rhX_lanes : (s.objEntry X).props.get? (.str "lanes") = some (.data o6 true e6 c6))
    (rhX_child : (s.objEntry X).props.get? (.str "child") = some (.data o7 true e7 c7))
    (rhX_memoizedProps : (s.objEntry X).props.get? (.str "memoizedProps") = some (.data o8 true e8 c8))
    (rhX_memoizedState : (s.objEntry X).props.get? (.str "memoizedState") = some (.data o9 true e9 c9))
    (rhX_updateQueue : (s.objEntry X).props.get? (.str "updateQueue") = some (.data o10 true e10 c10))
    (rhX_dependencies : (s.objEntry X).props.get? (.str "dependencies") = some (.data o11 true e11 c11))
    (rhX_sibling : (s.objEntry X).props.get? (.str "sibling") = some (.data o12 true e12 c12))
    (rhX_index : (s.objEntry X).props.get? (.str "index") = some (.data o13 true e13 c13))
    (rhX_ref : (s.objEntry X).props.get? (.str "ref") = some (.data o14 true e14 c14))
    (rhX_refCleanup : (s.objEntry X).props.get? (.str "refCleanup") = some (.data o15 true e15 c15))
    (rhI : fI < s.heap.size) (rhIk : (s.objEntry fI).kind = .func dI)
    (rhIcode : dI.code = CCRGen.reconcileChildFibersImpl_func) (rhIcls : dI.isClassCtor = false)
    (rhImode : dI.thisMode = .strict) (rhIenv : dI.env = dU.env)
    (rhRDel : r_bR[JSStr.ofString "deleteRemainingChildren"]? = some bdDel)
    (rhRDelv : bdDel.value = some (.obj fDel)) (rhDel : fDel < s.heap.size)
    (rhDelk : (s.objEntry fDel).kind = .func dDel) (rhDelcode : dDel.code = CCRGen.deleteRemainingChildren_func)
    (rhDelcls : dDel.isClassCtor = false) (rhDelmode : dDel.thisMode = .strict) (rhDelenv : dDel.env = dU.env)
    (rhRUF : r_bR[JSStr.ofString "useFiber"]? = some bdUF) (rhRUFv : bdUF.value = some (.obj fU))
    (rhRPl : r_bR[JSStr.ofString "placeSingleChild"]? = some bdPl) (rhRPlv : bdPl.value = some (.obj fPl))
    (rhPl : fPl < s.heap.size) (rhPlk : (s.objEntry fPl).kind = .func dPl)
    (rhPlcode : dPl.code = CCRGen.placeSingleChild_func) (rhPlcls : dPl.isClassCtor = false)
    (rhPlmode : dPl.thisMode = .strict) (rhPlenv : dPl.env = dU.env)
    (rhRST : r_bR[JSStr.ofString "shouldTrackSideEffects"]? = some bdST) (rhRSTv : bdST.value = some (.bool true))
    (rhRnF : r_bR[JSStr.ofString "REACT_FRAGMENT_TYPE"]? = none)
    (rhRnE : r_bR[JSStr.ofString "REACT_ELEMENT_TYPE"]? = none) (rhRnC : r_bR[JSStr.ofString "coerceRef"]? = none)
    (rhGFr : bG[JSStr.ofString "REACT_FRAGMENT_TYPE"]? = some bdFr) (rhGFrv : bdFr.value = some vFr)
    (rhGEl : bG[JSStr.ofString "REACT_ELEMENT_TYPE"]? = some bdEl) (rhGElv : bdEl.value = some vT)
    (rhFrs : ∃ i, vFr = .sym i) (rhEls : ∃ i, vT = .sym i) (rhFrEl : vFr ≠ vT)
    (rhGCR : bG[JSStr.ofString "coerceRef"]? = some bdCR) (rhGCRv : bdCR.value = some (.obj fCR))
    (rhCR : fCR < s.heap.size) (rhCRk : (s.objEntry fCR).kind = .func dCR)
    (rhCRcode : dCR.code = CRGen.coerceRef_func) (rhCRcls : dCR.isClassCtor = false)
    (rhCRmode : dCR.thisMode = .strict)
    (rhHkey : (s.objEntry H).props.get? (.str "key") = some (.data .null bkw bke bkc))
    (rhHet : (s.objEntry H).props.get? (.str "elementType") = some (.data (.str (JSStr.ofString "button")) bew bee bec))
    (rhXa : (s.objEntry X).props.get? (.str "alternate") = some (.data (.obj H) r_aw r_ae r_ac))
    (rhXret : (s.objEntry X).props.get? (.str "return") = some (.data rv0 true rew rec))
    (rhdX : ∀ Y ∈ [fCR, fPl, OP], Y ≠ X) (rhR : r_fR < s.heap.size) (rhRk : (s.objEntry r_fR).kind = .func r_dR)
    (rhRcode : r_dR.code = CCRGen.fn34_func) (rhRcls : r_dR.isClassCtor = false)
    (rhRmode : r_dR.thisMode = .strict) (rhRenv : r_dR.env = dU.env)
    (rhRRI : r_bR[JSStr.ofString "reconcileChildFibersImpl"]? = some bdRI) (rhRRIv : bdRI.value = some (.obj fI))
    (rhRnT : r_bR[JSStr.ofString "thenableIndexCounter$1"]? = none)
    (rhRnS : r_bR[JSStr.ofString "thenableState$1"]? = none)
    (rhGT : bG[JSStr.ofString "thenableIndexCounter$1"]? = some r_bdT) (rhGTm : r_bdT.mutable = true)
    (rhGTi : r_bdT.value.isSome = true) (rhGS : bG[JSStr.ofString "thenableState$1"]? = some r_bdTS)
    (rhGSm : r_bdTS.mutable = true) (rhGSi : r_bdTS.value.isSome = true) (rhgU : d.env ≠ dU.env)
    (rhRC : fC < s.heap.size) (rhRCk : (s.objEntry fC).kind = .func dC)
    (rhRCcode : dC.code = RChGen.reconcileChildren_func) (rhRCcls : dC.isClassCtor = false)
    (rhRCmode : dC.thisMode = .strict) (rhRCenv : dC.env = d.env)
    (rhGRCF : bG[JSStr.ofString "reconcileChildFibers"]? = some bdRCF) (rhGRCFv : bdRCF.value = some (.obj r_fR))
    (rhC0c : (s.objEntry C0).props.get? (.str "child") = some (.data (.obj H) c0w c0e c0c))
    (rhRFc : (s.objEntry C1).props.get? (.str "child") = some (.data ch0 true cw cc)) (rhRFX : C1 ≠ X)
    {fUF fP fCD : ObjId} {dUF dP dCD : FuncData} {tUF : Value} {fl1 : F64} {bdP bdRWb bdCD bdRCb bdHy bdF1 bdL1 bdLI : Binding}
    {dpw dpe dpc fw fe fc : Bool}
    -- (updateFunctionComponent and its callees, functions of react-dom's module)
    (hUF : fUF < s.heap.size) (hUFk : (s.objEntry fUF).kind = .func dUF)
    (hUFcode : dUF.code = UFCGen.updateFunctionComponent_func) (hUFcls : dUF.isClassCtor = false)
    (hUFmode : dUF.thisMode = .strict) (hUFenv : dUF.env = d.env)
    (hGP : bG[JSStr.ofString "prepareToReadContext"]? = some bdP) (hGPv : bdP.value = some (.obj fP))
    (hPR : fP < s.heap.size) (hPRk : (s.objEntry fP).kind = .func dP) (hPRcode : dP.code = PRCGen.prepareToReadContext_func)
    (hPRcls : dP.isClassCtor = false) (hPRmode : dP.thisMode = .strict) (hPRenv : dP.env = d.env)
    (hGRWb : bG[JSStr.ofString "renderWithHooks"]? = some bdRWb) (hGRWbv : bdRWb.value = some (.obj fRW))
    (hGCD : bG[JSStr.ofString "checkDidRenderIdHook"]? = some bdCD) (hGCDv : bdCD.value = some (.obj fCD))
    (hCD : fCD < s.heap.size) (hCDk : (s.objEntry fCD).kind = .func dCD) (hCDcode : dCD.code = CDRGen.checkDidRenderIdHook_func)
    (hCDcls : dCD.isClassCtor = false) (hCDmode : dCD.thisMode = .strict) (hCDenv : dCD.env = d.env)
    (hGRCb : bG[JSStr.ofString "reconcileChildren"]? = some bdRCb) (hGRCbv : bdRCb.value = some (.obj fC))
    (hGHy : bG[JSStr.ofString "isHydrating"]? = some bdHy) (hGHyv : bdHy.value = some (.bool false))
    (hGF1 : bG[JSStr.ofString "currentlyRenderingFiber$1"]? = some bdF1) (hGF1m : bdF1.mutable = true)
    (hGF1i : bdF1.value.isSome = true)
    (hGL1 : bG[JSStr.ofString "lastContextDependency"]? = some bdL1) (hGL1m : bdL1.mutable = true)
    (hGL1i : bdL1.value.isSome = true)
    (hGLI : bG[JSStr.ofString "localIdCounter"]? = some bdLI) (hGLIm : bdLI.mutable = true)
    (hGLIv : bdLI.value = some (.num (F64.fin false 0 (-1074))))
    -- (the work in progress: no context dependencies; its flags)
    (hC1d : (s.objEntry C1).props.get? (.str "dependencies") = some (.data .null dpw dpe dpc))
    (hC1f : (s.objEntry C1).props.get? (.str "flags") = some (.data (.num fl1) true fe fc))
    -- (reconcileChildren's objects are not what renderWithHooks writes; its closure record is not the module's)
    (hdW : ∀ Y ∈ [r_fo, fU, fI, fDel, fPl, fCR, r_fR, fC, H, X, fCD, C0], Y ≠ C1 ∧ Y ≠ H0 ∧ Y ≠ Q ∧ Y ≠ RSI)
    (hdUe : dU.env ≠ d.env) :
    WP eng answer (n + 7) h (callImpl eng (.obj fUF) tUF #[.obj C0, .obj C1, .obj fK, P, two]) s fun v w h' =>
      ∃ C : ObjId, v = .obj X ∧ Frame (fpUF d.env C1 H0 Q RSI X) s w ∧ s.fuel ≤ w.fuel + 500 ∧ h' = h ∧ w.realm = s.realm ∧
      (w.objEntry X).props.get? (.str "pendingProps") = some (.data (.obj C) true e0 c0) ∧
      (w.objEntry X).props.get? (.str "type") = some (.data (vHT) true r_e1 r_c1) ∧
      (w.objEntry X).props.get? (.str "flags") = some (.data (.num (numberBinOp .bitAnd fl (F64.fin false 5062151534280704 (-22)))) true r_e2 r_c2) ∧
      (w.objEntry X).props.get? (.str "subtreeFlags") = some (.data (.num (F64.fin false 0 (-1074))) true r_e3 r_c3) ∧
      (w.objEntry X).props.get? (.str "deletions") = some (.data (.null) true r_e4 r_c4) ∧
      (w.objEntry X).props.get? (.str "childLanes") = some (.data (vCL) true e5 c5) ∧
      (w.objEntry X).props.get? (.str "lanes") = some (.data (vL) true e6 c6) ∧
      (w.objEntry X).props.get? (.str "child") = some (.data (vC) true e7 c7) ∧
      (w.objEntry X).props.get? (.str "memoizedProps") = some (.data (vMP) true e8 c8) ∧
      (w.objEntry X).props.get? (.str "memoizedState") = some (.data (vMS) true e9 c9) ∧
      (w.objEntry X).props.get? (.str "updateQueue") = some (.data (vUQ) true e10 c10) ∧
      (w.objEntry X).props.get? (.str "dependencies") = some (.data (.null) true e11 c11) ∧
      (w.objEntry X).props.get? (.str "sibling") = some (.data .null true e12 c12) ∧
      (w.objEntry X).props.get? (.str "index") = some (.data (.num (F64.fin false 0 (-1074))) true e13 c13) ∧
      (w.objEntry X).props.get? (.str "ref") = some (.data .null true e14 c14) ∧
      (w.objEntry X).props.get? (.str "refCleanup") = some (.data (vRC) true e15 c15) ∧
      (w.objEntry X).props.get? (.str "return") = some (.data (.obj C1) true rew rec) ∧
      (w.objEntry C1).props.get? (.str "child") = some (.data (.obj X) true cw cc) ∧
      (w.objEntry C).props.get? (.str "children") =
        some (.data (.str (JSStr.ofString "Count: " ++ numberToJSStr xE ++ JSStr.ofString "")) true true true) ∧
      (w.objEntry C1).props.get? (.str "lanes") = some (.data (.num (F64.fin false 0 (-1074))) true lw lc) ∧
      (w.objEntry C1).props.get? (.str "flags") = some (.data (.num (numberBinOp .bitOr fl1 (F64.fin false 4503599627370496 (-52)))) true fe fc) ∧
      (w.objEntry C).kind.isPlain = true ∧ C < w.heap.size ∧ s.heap.size ≤ C ∧
      (∃ F, ReactNewProps.NewProps w C F OP (JSStr.ofString "Count: " ++ numberToJSStr xE ++ JSStr.ofString "")) ∧
      ∃ bm, Scope.declLike? (w.envEntry d.env) = some (bm, oG) ∧
        (∃ bd, bm[JSStr.ofString "didReceiveUpdate"]? = some bd ∧ bd.mutable = true ∧ bd.value.isSome = true) ∧
        (∃ bd, bm[JSStr.ofString "thenableIndexCounter$1"]? = some bd ∧ bd.mutable = true ∧ bd.value.isSome = true) ∧
        ∃ bd, bm[JSStr.ofString "thenableState$1"]? = some bd ∧ bd.mutable = true ∧ bd.value.isSome = true ∧
        (∃ bd, bm[JSStr.ofString "lastContextDependency"]? = some bd ∧ bd.mutable = true ∧ bd.value.isSome = true) ∧
        (∃ bd, bm[JSStr.ofString "currentlyRenderingFiber$1"]? = some bd ∧ bd.mutable = true ∧ bd.value.isSome = true) := by
  subst hrBS
  apply wp_callGen UFCGen.updateFunctionComponent_eq (by decide) hUF hUFk (by omega) hUFcls hUFmode
    (by rw [hUFcode]; rfl) (by rw [hUFcode]; rfl) (simpleUF dUF hUFcode) (by rw [hUFcode]; rfl) (by rw [hUFcode]; rfl)
  have hpn : dUF.code.info.fdi.paramNames = #[JSStr.ofString "current", JSStr.ofString "workInProgress",
      JSStr.ofString "Component", JSStr.ofString "nextProps", JSStr.ofString "renderLanes"] := by rw [hUFcode]; rfl
  have hv : dUF.code.info.fdi.varNames = #[] := by rw [hUFcode]; rfl
  have hl : FDI.lexDecls dUF = #[] := by simp [FDI.lexDecls, hUFcode, UFCGen.updateFunctionComponent_func, Func.info]
  have ha : dUF.code.isAsync = false := by rw [hUFcode]; rfl
  have hne : s.envs.size ≠ d.env := Nat.ne_of_gt hG
  have hG1 : d.env < s.envs.size + 1 := Nat.lt_succ_of_lt hG
  clear hUFcode
  simp only [UFCGen.updateFunctionComponent]
  js [hpn, hv, hl, ha, hUFenv, hG, hG1, hne, Ne.symm hne, hGe, hGP, hGPv, hPR, hPRk, FDI.fdiCtx, Sem.inner]
  -- (`prepareToReadContext(workInProgress)`)
  refine ⟨by js_norm [CallableC, hPR, hPRk], ?_⟩
  refine wp_mono (ReactRenderPrep.prepare_spec (bG := bG) (oG := oG) hPR hPRk (by js_norm; omega) hPRcode hPRcls hPRmode
    (by js_norm [hPRenv, hG, hG1]) (by js_norm [hPRenv, hGe, hne, Ne.symm hne]) hGF1 hGF1m hGF1i hGL1 hGL1m hGL1i
    hC1 hC1k hC1d) ?postP
  intro v1 w1 h1 ⟨hv1, hF1, hfu1, hh1, hr1, hd1⟩
  subst v1 h1
  rw [hPRenv] at hF1 hd1
  have hw1o : ∀ o, o < s.heap.size → w1.objEntry o = s.objEntry o := fun o ho =>
    objEntry_frame hF1 (by js_norm [ho]) (by simp [ReactRenderPrep.fpP])
  have hw1e : ∀ e, e < s.envs.size + 1 → e ≠ d.env → w1.envEntry e = (bodyState s fUF dUF tUF
      #[.obj C0, .obj C1, .obj fK, P, two]).envEntry e := fun e he hne' =>
    envEntry_frame hF1 (by js_norm [he]) (by simp [ReactRenderPrep.fpP, Ne.symm hne'])
  have hw1K := hw1e s.envs.size (Nat.lt_succ_self _) hne
  simp only [js_simp, ↓reduceIte] at hw1K
  have hw1E : s.envs.size + 1 ≤ w1.envs.size := by have := hF1.envs_le; simp only [js_simp] at this; exact this
  have hw1z : s.heap.size ≤ w1.heap.size := by have := hF1.heap_le; simp only [js_simp] at this; exact this
  have hw1f : 400 ≤ w1.fuel := by simp only [js_simp] at hfu1; omega
  have hGw1 : d.env < w1.envs.size := Nat.lt_of_lt_of_le hG1 hw1E
  have hEw1 : s.envs.size < w1.envs.size := Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hw1E
  js [hpn, hv, hl, ha, hw1K, hEw1, hGw1, hd1, hGRWb, hGRWbv, hw1o, hRW, hRWk, hw1f, FDI.fdiCtx, Sem.inner]
  refine wp_void ?_
  js [hpn, hv, hl, ha, hw1K, hEw1, hGw1, hd1, hGRWb, hGRWbv, hw1o, hRW, hRWk, hw1f, FDI.fdiCtx, Sem.inner]
  -- (`renderWithHooks(current, workInProgress, Counter, props, undefined, 2)`)
  have hw1s : ∀ e, e < s.envs.size → e ≠ d.env → w1.envEntry e = s.envEntry e := by
    intro e he hne'; rw [hw1e e (Nat.lt_succ_of_lt he) hne']; js_norm [Nat.ne_of_lt he, Nat.ne_of_gt he, he]
  have hw1R : w1.realms = s.realms := by rw [hF1.realms_eq]; rfl
  refine ⟨by js_norm [CallableC, hw1o, hRW, hRWk, Nat.lt_of_lt_of_le hRW hw1z], ?_⟩
  refine wp_mono (ReactRenderHooks.click_spec (bG := ((bG.modify (JSStr.ofString "currentlyRenderingFiber$1")
      (fun bd => { bd with value := some (.obj C1) })).modify (JSStr.ofString "lastContextDependency")
      (fun bd => { bd with value := some .null }))) (oG := oG) (tRW := .undefined) (rw := false) (ue := false) (le := false) (uw := uw) (uc := uc)
      (hS := (Nat.lt_of_lt_of_le hS hw1z)) (hSk := (by rw [hw1o fS hS]; exact hSk)) (hScode := hScode)
      (hScls := hScls) (hSmode := hSmode) (hSG := (Nat.lt_of_lt_of_le (Nat.lt_succ_of_lt hSG) hw1E))
      (hSGe := (by rw [hw1s _ hSG hSd]; exact hSGe)) (hRSI := hRSI) (hRSIv := hRSIv)
      (hI := (Nat.lt_of_lt_of_le hI hw1z)) (hIk := (by rw [hw1o RSI hI]; exact hIk))
      (hIH := (by rw [hw1o RSI hI]; exact hIH)) (hHD := (Nat.lt_of_lt_of_le hHD hw1z))
      (hHDk := (by rw [hw1o HD hHD]; exact hHDk)) (hHDu := (by rw [hw1o HD hHD]; exact hHDu))
      (hD := (Nat.lt_of_lt_of_le hD hw1z)) (hDk := (by rw [hw1o fD hD]; exact hDk)) (hDcode := hDcode)
      (hDcls := hDcls) (hDmode := hDmode) (hDenv := hDenv) (hGU := (by js_norm [hGU])) (hGUv := hGUv)
      (hGB := (by js_norm [hGB])) (hGBv := hGBv) (hlt := (Nat.lt_of_lt_of_le hlt hw1z))
      (hk := (by rw [hw1o fo hlt]; exact hk)) (hf := (by omega)) (hcode := hcode) (hcls := hcls) (hmode := hmode)
      (hG := (Nat.lt_of_lt_of_le (Nat.lt_succ_of_lt hG) hw1E)) (hGe := hd1) (hGC := (by js_norm [hGC]))
      (hGCm := hGCm) (hGCv := hGCv) (hGW := (by js_norm [hGW])) (hGWm := hGWm) (hGWv := hGWv)
      (hGF := (by js_norm [hGF])) (hGFm := hGFm) (hGFi := hGFi) (hGUW := (by js_norm [hGUW])) (hGUWv := hGUWv)
      (hW := (Nat.lt_of_lt_of_le hW hw1z)) (hWk := (by rw [hw1o fW hW]; exact hWk)) (hWcode := hWcode)
      (hWcls := hWcls) (hWmode := hWmode) (hWenv := hWenv) (hGUR := (by js_norm [hGUR])) (hGURv := hGURv)
      (hR := (Nat.lt_of_lt_of_le hR hw1z)) (hRk := (by rw [hw1o fR hR]; exact hRk)) (hRcode := hRcode)
      (hRcls := hRcls) (hRmode := hRmode) (hRenv := hRenv) (hGRL := (by js_norm [hGRL])) (hGRLm := hGRLm)
      (hGRLi := hGRLi) (hGCE := (by js_norm [hGCE])) (hGCEv := hGCEv) (hGSD := (by js_norm [hGSD])) (hGSDm := hGSDm)
      (hGSDi := hGSDi) (hGDR := (by js_norm [hGDR])) (hGDRm := hGDRm) (hGDRi := hGDRi) (hGIs := (by js_norm [hGIs]))
      (hGIsv := hGIsv) (hIs := (Nat.lt_of_lt_of_le hIs hw1z)) (hIsk := (by rw [hw1o fIs hIs]; exact hIsk))
      (hIstab := hIstab) (hC1 := (Nat.lt_of_lt_of_le hC1 hw1z)) (hC1k := (by rw [hw1o C1 hC1]; exact hC1k))
      (hC1a := (by rw [hw1o C1 hC1]; exact hC1a)) (hC1m := (by rw [hw1o C1 hC1]; exact hC1m))
      (hC0 := (Nat.lt_of_lt_of_le hC0 hw1z)) (hC0k := (by rw [hw1o C0 hC0]; exact hC0k))
      (hC0m := (by rw [hw1o C0 hC0]; exact hC0m)) (hH0 := (Nat.lt_of_lt_of_le hH0 hw1z))
      (hH0k := (by rw [hw1o H0 hH0]; exact hH0k)) (hHm := (by rw [hw1o H0 hH0]; exact hHm))
      (hHb := (by rw [hw1o H0 hH0]; exact hHb)) (hHbq := (by rw [hw1o H0 hH0]; exact hHbq))
      (hHq := (by rw [hw1o H0 hH0]; exact hHq)) (hQ := (Nat.lt_of_lt_of_le hQ hw1z))
      (hQk := (by rw [hw1o Q hQ]; exact hQk)) (hQp := (by rw [hw1o Q hQ]; exact hQp))
      (hQr := (by rw [hw1o Q hQ]; exact hQr)) (hQl := (by rw [hw1o Q hQ]; exact hQl))
      (hQd := (by rw [hw1o Q hQ]; exact hQd)) (hU := (Nat.lt_of_lt_of_le hU hw1z))
      (hUk := (by rw [hw1o U hU]; exact hUk)) (hUl := (by rw [hw1o U hU]; exact hUl))
      (hUr := (by rw [hw1o U hU]; exact hUr)) (hUa := (by rw [hw1o U hU]; exact hUa))
      (hUe := (by rw [hw1o U hU]; exact hUe)) (hUv := (by rw [hw1o U hU]; exact hUv))
      (hUn := (by rw [hw1o U hU]; exact hUn)) (hdiff := hdiff) (hrBS := rfl) (hBS := (Nat.lt_of_lt_of_le hBS hw1z))
      (hBSk := (by rw [hw1o fBS hBS]; exact hBSk)) (hBScode := hBScode) (hBScls := hBScls) (hBSmode := hBSmode)
      (dBS1 := dBS1) (dBS2 := dBS2) (dBS3 := dBS3) (dBS4 := dBS4) (d1 := d1) (d2 := d2) (d3 := d3) (d4 := d4)
      (d5 := d5) (d6 := d6) (d7 := d7) (d8 := d8) (d9 := d9) (d10 := d10) (d11 := d11) (d12 := d12)
      (hK := (Nat.lt_of_lt_of_le hK hw1z)) (hKk := (by rw [hw1o fK hK]; exact hKk)) (hKcode := hKcode)
      (hKcls := hKcls) (hKmode := hKmode) (hAG := (Nat.lt_of_lt_of_le (Nat.lt_succ_of_lt hAG) hw1E))
      (hAGe := (by rw [hw1s _ hAG hKd]; exact hAGe)) (hAR := hAR) (hARv := hARv)
      (hIR := (Nat.lt_of_lt_of_le hIR hw1z)) (hIRk := (by rw [hw1o IR hIR]; exact hIRk))
      (hIRu := (by rw [hw1o IR hIR]; exact hIRu)) (hAJ := hAJ) (hAJv := hAJv) (hIJ := (Nat.lt_of_lt_of_le hIJ hw1z))
      (hIJk := (by rw [hw1o IJ hIJ]; exact hIJk)) (hIJj := (by rw [hw1o IJ hIJ]; exact hIJj))
      (hJ := (Nat.lt_of_lt_of_le hJ hw1z)) (hJk := (by rw [hw1o fJ hJ]; exact hJk)) (hJcode := hJcode)
      (hJcls := hJcls) (hJmode := hJmode) (hJG := (Nat.lt_of_lt_of_le (Nat.lt_succ_of_lt hJG) hw1E))
      (hJGe := (by rw [hw1s _ hJG hJd]; exact hJGe)) (hJT := hJT) (hJTv := hJTv) (hAP := (by rw [hw1R]; exact hAP))
      (hP := (Nat.lt_of_lt_of_le hP hw1z)) (hPk := (by rw [hw1o AP hP]; exact hPk))
      (hPv := (by rw [hw1o AP hP]; exact hPv)) (hV := (Nat.lt_of_lt_of_le hV hw1z))
      (hVk := (by rw [hw1o fV hV]; exact hVk)) (hVfn := hVfn) (hVr := hVr) (hII := (by rw [hw1R]; exact hII))
      (hAIP := (Nat.lt_of_lt_of_le hAIP hw1z)) (hAIPk := (by rw [hw1o AIP hAIP]; exact hAIPk))
      (hAIPn := (by rw [hw1o AIP hAIP]; exact hAIPn)) (hN := (Nat.lt_of_lt_of_le hN hw1z))
      (hNk := (by rw [hw1o fN hN]; exact hNk)) (hNfn := hNfn) (hNr := hNr)
      (hAIPp := (by rw [hw1o AIP hAIP]; exact hAIPp)) (hAIPr := (by rw [hw1o AIP hAIP]; exact hAIPr))
      (hIP := (Nat.lt_of_lt_of_le hIP hw1z)) (hIPk := (by rw [hw1o IP hIP]; exact hIPk))
      (hIPr := (by rw [hw1o IP hIP]; exact hIPr)) (hIPp := (by rw [hw1o IP hIP]; exact hIPp))
      (hOPe := (by rw [hw1R]; exact hOPe)) (hOP := (Nat.lt_of_lt_of_le hOP hw1z))
      (hOPk := (by rw [hw1o OP hOP]; exact hOPk)) (hOPr := (by rw [hw1o OP hOP]; exact hOPr))
      (hOPp := (by rw [hw1o OP hOP]; exact hOPp)) (hOPkey := (by rw [hw1o OP hOP]; exact hOPkey))
      (hOPref := (by rw [hw1o OP hOP]; exact hOPref)) (hFP := (by rw [hw1R]; exact hFP)) (hvE := hvE) (dAP := dAP)
      (dfV := dfV) (dAIP := dAIP) (dfN := dfN) (dIP := dIP) (dOP := dOP) (dIJ := dIJ) (dfJ := dfJ) (hKd := hKd)
      (hJd := hJd) (hGHU := (by js_norm [hGHU])) (hGHUv := hGHUv) (hGRSd := (by js_norm [hGRSd])) (hGRSdv := hGRSdv)
      (hGDP := (by js_norm [hGDP])) (hGDPv := hGDPv) (hGFR := (by js_norm [hGFR])) (hGFRv := hGFRv)
      (hFF := (Nat.lt_of_lt_of_le hFF hw1z)) (hFFk := (by rw [hw1o fF hFF]; exact hFFk)) (hFFcode := hFFcode)
      (hFFcls := hFFcls) (hFFmode := hFFmode) (hFFenv := hFFenv) (hGCO := (by js_norm [hGCO])) (hGCOv := hGCOv)
      (hGDS := (by js_norm [hGDS])) (hGDSm := hGDSm) (hGDSi := hGDSi) (hGTI := (by js_norm [hGTI])) (hGTIm := hGTIm)
      (hGTIi := hGTIi) (hGTS := (by js_norm [hGTS])) (hGTSm := hGTSm) (hGTSi := hGTSi)
      (hC1u := (by rw [hw1o C1 hC1]; exact hC1u)) (hC1l := (by rw [hw1o C1 hC1]; exact hC1l))
      (hH0n := (by rw [hw1o H0 hH0]; exact hH0n)) (hdist := hdist) (dRC := dRC) (hSd := hSd)
      (hRW := (Nat.lt_of_lt_of_le hRW hw1z)) (hRWk := (by rw [hw1o fRW hRW]; exact hRWk)) (hRWcode := hRWcode)
      (hRWcls := hRWcls) (hRWmode := hRWmode) (hRWenv := hRWenv) (dFH := dFH) (dRQ := dRQ)) ?postRW
  intro v2 w2 h2 ⟨E, C, F, dF', hvE, hF2, hfu2, hh2, hr2, hEt, hEty, hEkey, hEref, hEpr, hCch, hCoc, hEb, hCb, hEge, hCge, hEk, hCk,
    hCp, hCr, hFk, hFcode, hFenv, hFthis, hcomp, hmod, hRSIH, hC1m', hC1u', hC1l', hk1, hk2, hk3, hk4, hk5, hH0b', hQp',
    hQr', hQl', hNP⟩
  subst v2 h2
  -- (what renderWithHooks left: its footprint's objects are C1, the new hook, H0, Q, RSI)
  have hfpW : ∀ o, o ≠ C1 → o ≠ w1.heap.size → o ≠ H0 → o ≠ Q → o ≠ RSI →
      (fpRWH d.env C1 w1.heap.size H0 Q RSI).props.all (fun p => p.1 != o) = true := by
    intro o h1 h2 h3 h4 h5; simp [fpRWH, Ne.symm h1, Ne.symm h2, Ne.symm h3, Ne.symm h4, Ne.symm h5]
  have hw2o : ∀ o, o < s.heap.size → o ≠ C1 → o ≠ H0 → o ≠ Q → o ≠ RSI → w2.objEntry o = s.objEntry o := by
    intro o ho h1 h3 h4 h5
    rw [objEntry_frame hF2 (Nat.lt_of_lt_of_le ho hw1z) (hfpW o h1 (Nat.ne_of_lt (Nat.lt_of_lt_of_le ho hw1z)) h3 h4 h5),
      hw1o o ho]
  have hw2E : w1.envs.size ≤ w2.envs.size := hF2.envs_le
  have hw2z : w1.heap.size ≤ w2.heap.size := hF2.heap_le
  have hw2K : w2.envEntry s.envs.size = w1.envEntry s.envs.size :=
    envEntry_frame hF2 hEw1 (by simp [fpRWH, hne, Ne.symm hne])
  rw [hw1K] at hw2K
  have hEw2 : s.envs.size < w2.envs.size := Nat.lt_of_lt_of_le hEw1 hw2E
  have hGw2 : d.env < w2.envs.size := Nat.lt_of_lt_of_le hGw1 hw2E
  have hw2f : 189 ≤ w2.fuel := by simp only [js_simp] at hfu1 hfu2; omega
  have hdCD := hdW fCD (by simp)
  have hw2CD : w2.objEntry fCD = s.objEntry fCD := hw2o fCD hCD hdCD.1 hdCD.2.1 hdCD.2.2.1 hdCD.2.2.2
  js [hpn, hv, hl, ha, hw2K, hEw2, hGw2, hmod, hGCD, hGCDv, hw2CD, hCD, hCDk, Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hCD hw1z) hw2z,
    hw2f, ReactFinishHooks.resetMap, FDI.fdiCtx, Sem.inner]
  -- (`checkDidRenderIdHook()`: false)
  have hCDw2 : fCD < w2.heap.size := Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hCD hw1z) hw2z
  refine ⟨by js_norm [CallableC, hw2CD, hCDk, hCDw2], ?_⟩
  refine wp_mono (ReactRenderPrep.check_spec (oG := oG) (bdI := bdLI) (by js_norm [hCDw2]) (by js_norm [hw2CD, hCDk])
    (by js_norm; omega) hCDcode hCDcls hCDmode (by js_norm [hCDenv, hGw2]) (by rw [hCDenv]; js_norm [hne, Ne.symm hne, hEw2, hGw2]; exact hmod)
    (by js_norm [hGLI, ReactFinishHooks.resetMap]) hGLIm hGLIv) ?postCD
  intro v3 w3 h3 ⟨hv3, hF3, hfu3, hh3, hr3, hmod3⟩
  subst v3 h3
  rw [hCDenv] at hF3 hmod3
  have hw3K := envEntry_frame hF3 (e := s.envs.size) (by js_norm [hEw2]) (by simp [hne, Ne.symm hne])
  simp only [js_simp, ↓reduceIte, hEw2, hne, Ne.symm hne] at hw3K
  have hw3o : ∀ o, o < w2.heap.size → w3.objEntry o = w2.objEntry o := by
    intro o ho; rw [objEntry_frame hF3 (by js_norm [ho]) (by simp)]; js_norm
  have hw3E : w2.envs.size ≤ w3.envs.size := by have := hF3.envs_le; simp only [js_simp] at this; exact this
  have hw3z : w2.heap.size ≤ w3.heap.size := by have := hF3.heap_le; simp only [js_simp] at this; exact this
  have hC1w2 : C1 < w2.heap.size := Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hC1 hw1z) hw2z
  have hC1f2 : (w2.objEntry C1).props.get? (.str "flags") = some (.data (.num fl1) true fe fc) := by
    rw [props_frame hF2 (Nat.lt_of_lt_of_le hC1 hw1z) (by simp [fpRWH]), hw1o C1 hC1]; exact hC1f
  have hC1k2 : (w2.objEntry C1).kind.isPlain = true := by
    rw [kind_frame hF2 (Nat.lt_of_lt_of_le hC1 hw1z), hw1o C1 hC1]; exact hC1k
  have hC1f3 : (w3.objEntry C1).props.get? (.str "flags") = some (.data (.num fl1) true fe fc) := by
    rw [hw3o C1 hC1w2]; exact hC1f2
  have hC1k3 : (w3.objEntry C1).kind.isPlain = true := by rw [hw3o C1 hC1w2]; exact hC1k2
  have hEw3 : s.envs.size < w3.envs.size := Nat.lt_of_lt_of_le hEw2 hw3E
  have hGw3 : d.env < w3.envs.size := Nat.lt_of_lt_of_le hGw2 hw3E
  have hw3f : 179 ≤ w3.fuel := by simp only [js_simp] at hfu3; omega
  js [hpn, hv, hl, ha, hw3K, hEw3, hGw3, hmod3, hGHy, hGHyv, hGRCb, hGRCbv, hC1f3, hC1k3, hC1f2, hC1k2, hC1w2,
    Nat.lt_of_lt_of_le hC1w2 hw3z, hw3f, ReactFinishHooks.resetMap, FDI.fdiCtx, Sem.inner]
  -- (`reconcileChildren(current, workInProgress, Component, renderLanes)`)
  have hdRC := hdW fC (by simp)
  have hw3RC : w3.objEntry fC = s.objEntry fC := by
    rw [hw3o fC (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le rhRC hw1z) hw2z), hw2o fC rhRC hdRC.1 hdRC.2.1 hdRC.2.2.1 hdRC.2.2.2]
  refine ⟨by js_norm [CallableC, hw3RC, rhRCk, hdRC.1, Ne.symm hdRC.1,
    Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le rhRC hw1z) hw2z) hw3z], ?_⟩
  refine wp_gen_state fun St hSt => ?_
  have hEC1 : E ≠ C1 := Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hC1 hw1z) hEge)
  have hCC1 : C ≠ C1 := Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hC1 hw1z) hCge)
  have hSo2 : ∀ o, o < w2.heap.size → o ≠ C1 → St.objEntry o = w2.objEntry o := by
    intro o ho h1; rw [hSt]; js_norm [h1, Ne.symm h1, hw3o o ho]
  have hSo : ∀ o, o < s.heap.size → o ≠ C1 → o ≠ H0 → o ≠ Q → o ≠ RSI → St.objEntry o = s.objEntry o :=
    fun o ho a b c e => (hSo2 o (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le ho hw1z) hw2z) a).trans (hw2o o ho a b c e)
  have hSz2 : w2.heap.size ≤ St.heap.size := by rw [hSt]; simp only [js_simp]; exact hw3z
  have hSz : s.heap.size ≤ St.heap.size := Nat.le_trans (Nat.le_trans hw1z hw2z) hSz2
  have hSE : s.envs.size + 1 ≤ St.envs.size := by
    rw [hSt]; simp only [js_simp]; exact Nat.le_trans hw1E (Nat.le_trans hw2E hw3E)
  have hGw3S : d.env < St.envs.size := Nat.lt_of_lt_of_le hG1 hSE
  have hUs := rhE
  have hw3U : w3.envEntry dU.env = s.envEntry dU.env := by
    rw [envEntry_frame hF3 (e := dU.env) (by js_norm [Nat.lt_of_lt_of_le hUs (Nat.le_of_lt hEw2)]) (by simp [hdUe, Ne.symm hdUe])]
    js_norm [Nat.ne_of_lt hUs, Nat.ne_of_gt hUs]
    rw [envEntry_frame hF2 (e := dU.env) (Nat.lt_of_lt_of_le hUs (Nat.le_of_lt hEw1)) (by simp [fpRWH, hdUe, Ne.symm hdUe]),
      hw1s _ hUs hdUe]
  have hSU : St.envEntry dU.env = s.envEntry dU.env := by
    rw [hSt]; js_norm [Nat.ne_of_lt hUs, Nat.ne_of_gt hUs, hw3U]
  have hSd : Scope.declLike? (St.envEntry d.env) = some (((ReactFinishHooks.resetMap ((((((((((bG.modify (JSStr.ofString "currentlyRenderingFiber$1") (fun bd => { bd with value := some (.obj C1) })).modify
        (JSStr.ofString "lastContextDependency") (fun bd => { bd with value := some .null })).modify (JSStr.ofString "renderLanes") (fun bd => { bd with value := some two })).modify
        (JSStr.ofString "currentlyRenderingFiber") (fun bd => { bd with value := some (.obj C1) })).modify
        (JSStr.ofString "shouldDoubleInvokeUserFnsInHooksDEV") (fun bd => { bd with value := some (.bool false) })).modify
        (JSStr.ofString "currentHook") (fun bd => { bd with value := some (.obj H0) })).modify
        (JSStr.ofString "workInProgressHook") (fun bd => { bd with value := some (.obj w1.heap.size) })).modify
        (JSStr.ofString "didReceiveUpdate") (fun bd => { bd with value := some (.bool true) })).modify
        (JSStr.ofString "shouldDoubleInvokeUserFnsInHooksDEV") (fun bd => { bd with value := some (.bool false) })))).modify (JSStr.ofString "localIdCounter")
        (fun bd => { bd with value := some (.num (F64.fin false 0 (-1074))) })), oG) := by
    rw [hSt]; js_norm [hne, Ne.symm hne, hGw3]; exact hmod3
  have hSC1k : (St.objEntry C1).kind.isPlain = true := by rw [hSt]; js_norm [hC1k3, Nat.lt_of_lt_of_le hC1w2 hw3z]
  have hSC1c : (St.objEntry C1).props.get? (.str "child") = some (.data ch0 true cw cc) := by
    rw [hSt]; js_norm [Nat.lt_of_lt_of_le hC1w2 hw3z, hw3o C1 hC1w2]
    rw [props_frame hF2 (Nat.lt_of_lt_of_le hC1 hw1z) (by simp [fpRWH]), hw1o C1 hC1]; exact rhRFc
  have hSF : 179 ≤ St.fuel := by rw [hSt]; simp only [js_simp]; omega
  have hSC1f : (St.objEntry C1).props.get? (.str "flags") = some (.data (.num (numberBinOp .bitOr fl1 (F64.fin false 4503599627370496 (-52)))) true fe fc) := by
    rw [hSt]; js_norm [Nat.lt_of_lt_of_le hC1w2 hw3z, hC1f3]
  have hSC1l : (St.objEntry C1).props.get? (.str "lanes") = some (.data (.num (F64.fin false 0 (-1074))) true lw lc) := by
    rw [hSt]; js_norm [Nat.lt_of_lt_of_le hC1w2 hw3z, hw3o C1 hC1w2, hC1l']
  have hdX' : ∀ Y ∈ [fCR, fPl, E, C, OP], Y ≠ X := by
    intro Y hY
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hY
    rcases hY with rfl | rfl | rfl | rfl | rfl
    · exact rhdX _ (by simp)
    · exact rhdX _ (by simp)
    · exact Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le rhX hw1z) hEge)
    · exact Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le rhX hw1z) hCge)
    · exact rhdX _ (by simp)
  have dC01 := (hdW C0 (by simp)).1
  have dC02 := (hdW C0 (by simp)).2.1
  have dC03 := (hdW C0 (by simp)).2.2.1
  have dC04 := (hdW C0 (by simp)).2.2.2
  have dOPR : OP ≠ RSI := (hdist OP (by simp)).2
  have F0 : Frame (fpUF d.env C1 H0 Q RSI X) s (bodyState s fUF dUF tUF #[.obj C0, .obj C1, .obj fK, P, two]) :=
    frame_mono (frame_bodyState (frame_refl ({} : Footprint) s) _ _ _ _) (by simp) (by simp) (fun _ => rfl)
  have F1 := frame_extend' F0 hF1 (fun q hq _ => by revert q; simp [ReactRenderPrep.fpP, fpUF]) (fun q hq _ => by
    revert q; simp [ReactRenderPrep.fpP]) (fun _ => rfl)
  have F2 := frame_extend' F1 hF2 (fun q hq _ => by revert q; simp [fpRWH, fpUF]) (fun q hq hlt => by
    simp only [fpRWH, List.mem_cons, List.mem_nil_iff, or_false] at hq
    rcases hq with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      first | (simp [fpUF]; done) | exact absurd (Nat.lt_of_lt_of_le hlt hw1z) (Nat.lt_irrefl _)) (fun _ => rfl)
  have F3 := frame_extend' (frame_setEnv_new F2 (Nat.le_refl _) _) hF3 (fun q hq _ => by revert q; simp [fpUF])
    (fun q hq _ => by revert q; simp) (fun _ => rfl)
  have FSt : Frame (fpUF d.env C1 H0 Q RSI X) s St := by
    rw [hSt]; clear hF1 hF2 hF3 F0 F1 F2; simp only [fpUF, ReactReconcileImpl.fpI, ReactCreateWIP.fp] at F3 ⊢
    frame_go' [F3, hC1, Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hC1w2 hw3z) (Nat.le_refl _)]
  have hStF3 : St.fuel = w3.fuel := by rw [hSt]; simp only [js_simp]
  have hStKe := congrArg (fun st : State => st.envEntry s.envs.size) hSt
  simp only [js_simp, ↓reduceIte, hEw3] at hStKe
  clear hSt
  refine wp_mono (ReactReconcileChildren.click_spec (El := E) (C := C) (RF := C1) (g := d.env) (ln := two) (vEl := vT)
      (tC := .undefined)
      (hU := (Nat.lt_of_lt_of_le rhU hSz))
      (hUk := (by rw [hSo fU (by assumption) (hdW fU (by simp)).1 (hdW fU (by simp)).2.1 (hdW fU (by simp)).2.2.1 (hdW fU (by simp)).2.2.2]; exact rhUk))
      (hUcode := rhUcode) (hUcls := rhUcls) (hUmode := rhUmode)
      (hE := (Nat.lt_of_lt_of_le (Nat.lt_succ_of_lt rhE) hSE)) (hEe := (by rw [hSU]; exact rhEe)) (hEn := rhEn)
      (hG := hGw3S) (hGe := hSd) (hGC := (by js_norm [rhGC, ReactFinishHooks.resetMap])) (hGCv := rhGCv)
      (hlt := (Nat.lt_of_lt_of_le rhlt hSz))
      (hk := (by rw [hSo r_fo (by assumption) (hdW r_fo (by simp)).1 (hdW r_fo (by simp)).2.1 (hdW r_fo (by simp)).2.2.1 (hdW r_fo (by simp)).2.2.2]; exact rhk))
      (hf := (Nat.le_trans (by decide) hSF)) (hcode := rhcode) (hcls := rhcls) (hmode := rhmode)
      (hH := (Nat.lt_of_lt_of_le rhH hSz))
      (hHk := (by rw [hSo H (by assumption) (hdW H (by simp)).1 (hdW H (by simp)).2.1 (hdW H (by simp)).2.2.1 (hdW H (by simp)).2.2.2]; exact rhHk))
      (hX := (Nat.lt_of_lt_of_le rhX hSz))
      (hXk := (by rw [hSo X (by assumption) (hdW X (by simp)).1 (hdW X (by simp)).2.1 (hdW X (by simp)).2.2.1 (hdW X (by simp)).2.2.2]; exact rhXk))
      (hHX := rhHX)
      (hHa := (by rw [hSo H (by assumption) (hdW H (by simp)).1 (hdW H (by simp)).2.1 (hdW H (by simp)).2.2.1 (hdW H (by simp)).2.2.2]; exact rhHa))
      (hHf := (by rw [hSo H (by assumption) (hdW H (by simp)).1 (hdW H (by simp)).2.1 (hdW H (by simp)).2.2.1 (hdW H (by simp)).2.2.2]; exact rhHf))
      (hHd := (by rw [hSo H (by assumption) (hdW H (by simp)).1 (hdW H (by simp)).2.1 (hdW H (by simp)).2.2.1 (hdW H (by simp)).2.2.2]; exact rhHd))
      (hH_type := (by rw [hSo H (by assumption) (hdW H (by simp)).1 (hdW H (by simp)).2.1 (hdW H (by simp)).2.2.1 (hdW H (by simp)).2.2.2]; exact rhH_type))
      (hH_childLanes := (by rw [hSo H (by assumption) (hdW H (by simp)).1 (hdW H (by simp)).2.1 (hdW H (by simp)).2.2.1 (hdW H (by simp)).2.2.2]; exact rhH_childLanes))
      (hH_lanes := (by rw [hSo H (by assumption) (hdW H (by simp)).1 (hdW H (by simp)).2.1 (hdW H (by simp)).2.2.1 (hdW H (by simp)).2.2.2]; exact rhH_lanes))
      (hH_child := (by rw [hSo H (by assumption) (hdW H (by simp)).1 (hdW H (by simp)).2.1 (hdW H (by simp)).2.2.1 (hdW H (by simp)).2.2.2]; exact rhH_child))
      (hH_memoizedProps := (by rw [hSo H (by assumption) (hdW H (by simp)).1 (hdW H (by simp)).2.1 (hdW H (by simp)).2.2.1 (hdW H (by simp)).2.2.2]; exact rhH_memoizedProps))
      (hH_memoizedState := (by rw [hSo H (by assumption) (hdW H (by simp)).1 (hdW H (by simp)).2.1 (hdW H (by simp)).2.2.1 (hdW H (by simp)).2.2.2]; exact rhH_memoizedState))
      (hH_updateQueue := (by rw [hSo H (by assumption) (hdW H (by simp)).1 (hdW H (by simp)).2.1 (hdW H (by simp)).2.2.1 (hdW H (by simp)).2.2.2]; exact rhH_updateQueue))
      (hH_sibling := (by rw [hSo H (by assumption) (hdW H (by simp)).1 (hdW H (by simp)).2.1 (hdW H (by simp)).2.2.1 (hdW H (by simp)).2.2.2]; exact rhH_sibling))
      (hH_index := (by rw [hSo H (by assumption) (hdW H (by simp)).1 (hdW H (by simp)).2.1 (hdW H (by simp)).2.2.1 (hdW H (by simp)).2.2.2]; exact rhH_index))
      (hH_ref := (by rw [hSo H (by assumption) (hdW H (by simp)).1 (hdW H (by simp)).2.1 (hdW H (by simp)).2.2.1 (hdW H (by simp)).2.2.2]; exact rhH_ref))
      (hH_refCleanup := (by rw [hSo H (by assumption) (hdW H (by simp)).1 (hdW H (by simp)).2.1 (hdW H (by simp)).2.2.1 (hdW H (by simp)).2.2.2]; exact rhH_refCleanup))
      (hX_pendingProps := (by rw [hSo X (by assumption) (hdW X (by simp)).1 (hdW X (by simp)).2.1 (hdW X (by simp)).2.2.1 (hdW X (by simp)).2.2.2]; exact rhX_pendingProps))
      (hX_type := (by rw [hSo X (by assumption) (hdW X (by simp)).1 (hdW X (by simp)).2.1 (hdW X (by simp)).2.2.1 (hdW X (by simp)).2.2.2]; exact rhX_type))
      (hX_flags := (by rw [hSo X (by assumption) (hdW X (by simp)).1 (hdW X (by simp)).2.1 (hdW X (by simp)).2.2.1 (hdW X (by simp)).2.2.2]; exact rhX_flags))
      (hX_subtreeFlags := (by rw [hSo X (by assumption) (hdW X (by simp)).1 (hdW X (by simp)).2.1 (hdW X (by simp)).2.2.1 (hdW X (by simp)).2.2.2]; exact rhX_subtreeFlags))
      (hX_deletions := (by rw [hSo X (by assumption) (hdW X (by simp)).1 (hdW X (by simp)).2.1 (hdW X (by simp)).2.2.1 (hdW X (by simp)).2.2.2]; exact rhX_deletions))
      (hX_childLanes := (by rw [hSo X (by assumption) (hdW X (by simp)).1 (hdW X (by simp)).2.1 (hdW X (by simp)).2.2.1 (hdW X (by simp)).2.2.2]; exact rhX_childLanes))
      (hX_lanes := (by rw [hSo X (by assumption) (hdW X (by simp)).1 (hdW X (by simp)).2.1 (hdW X (by simp)).2.2.1 (hdW X (by simp)).2.2.2]; exact rhX_lanes))
      (hX_child := (by rw [hSo X (by assumption) (hdW X (by simp)).1 (hdW X (by simp)).2.1 (hdW X (by simp)).2.2.1 (hdW X (by simp)).2.2.2]; exact rhX_child))
      (hX_memoizedProps := (by rw [hSo X (by assumption) (hdW X (by simp)).1 (hdW X (by simp)).2.1 (hdW X (by simp)).2.2.1 (hdW X (by simp)).2.2.2]; exact rhX_memoizedProps))
      (hX_memoizedState := (by rw [hSo X (by assumption) (hdW X (by simp)).1 (hdW X (by simp)).2.1 (hdW X (by simp)).2.2.1 (hdW X (by simp)).2.2.2]; exact rhX_memoizedState))
      (hX_updateQueue := (by rw [hSo X (by assumption) (hdW X (by simp)).1 (hdW X (by simp)).2.1 (hdW X (by simp)).2.2.1 (hdW X (by simp)).2.2.2]; exact rhX_updateQueue))
      (hX_dependencies := (by rw [hSo X (by assumption) (hdW X (by simp)).1 (hdW X (by simp)).2.1 (hdW X (by simp)).2.2.1 (hdW X (by simp)).2.2.2]; exact rhX_dependencies))
      (hX_sibling := (by rw [hSo X (by assumption) (hdW X (by simp)).1 (hdW X (by simp)).2.1 (hdW X (by simp)).2.2.1 (hdW X (by simp)).2.2.2]; exact rhX_sibling))
      (hX_index := (by rw [hSo X (by assumption) (hdW X (by simp)).1 (hdW X (by simp)).2.1 (hdW X (by simp)).2.2.1 (hdW X (by simp)).2.2.2]; exact rhX_index))
      (hX_ref := (by rw [hSo X (by assumption) (hdW X (by simp)).1 (hdW X (by simp)).2.1 (hdW X (by simp)).2.2.1 (hdW X (by simp)).2.2.2]; exact rhX_ref))
      (hX_refCleanup := (by rw [hSo X (by assumption) (hdW X (by simp)).1 (hdW X (by simp)).2.1 (hdW X (by simp)).2.2.1 (hdW X (by simp)).2.2.2]; exact rhX_refCleanup))
      (hI := (Nat.lt_of_lt_of_le rhI hSz))
      (hIk := (by rw [hSo fI (by assumption) (hdW fI (by simp)).1 (hdW fI (by simp)).2.1 (hdW fI (by simp)).2.2.1 (hdW fI (by simp)).2.2.2]; exact rhIk))
      (hIcode := rhIcode) (hIcls := rhIcls) (hImode := rhImode) (hIenv := rhIenv) (hRDel := rhRDel)
      (hRDelv := rhRDelv) (hDel := (Nat.lt_of_lt_of_le rhDel hSz))
      (hDelk := (by rw [hSo fDel (by assumption) (hdW fDel (by simp)).1 (hdW fDel (by simp)).2.1 (hdW fDel (by simp)).2.2.1 (hdW fDel (by simp)).2.2.2]; exact rhDelk))
      (hDelcode := rhDelcode) (hDelcls := rhDelcls) (hDelmode := rhDelmode) (hDelenv := rhDelenv) (hRUF := rhRUF)
      (hRUFv := rhRUFv) (hRPl := rhRPl) (hRPlv := rhRPlv) (hPl := (Nat.lt_of_lt_of_le rhPl hSz))
      (hPlk := (by rw [hSo fPl (by assumption) (hdW fPl (by simp)).1 (hdW fPl (by simp)).2.1 (hdW fPl (by simp)).2.2.1 (hdW fPl (by simp)).2.2.2]; exact rhPlk))
      (hPlcode := rhPlcode) (hPlcls := rhPlcls) (hPlmode := rhPlmode) (hPlenv := rhPlenv) (hRST := rhRST)
      (hRSTv := rhRSTv) (hRnF := rhRnF) (hRnE := rhRnE) (hRnC := rhRnC)
      (hGFr := (by js_norm [rhGFr, ReactFinishHooks.resetMap])) (hGFrv := rhGFrv)
      (hGEl := (by js_norm [rhGEl, ReactFinishHooks.resetMap])) (hGElv := rhGElv) (hFrs := rhFrs) (hEls := rhEls)
      (hFrEl := rhFrEl) (hGCR := (by js_norm [rhGCR, ReactFinishHooks.resetMap])) (hGCRv := rhGCRv)
      (hCR := (Nat.lt_of_lt_of_le rhCR hSz))
      (hCRk := (by rw [hSo fCR (by assumption) (hdW fCR (by simp)).1 (hdW fCR (by simp)).2.1 (hdW fCR (by simp)).2.2.1 (hdW fCR (by simp)).2.2.2]; exact rhCRk))
      (hCRcode := rhCRcode) (hCRcls := rhCRcls) (hCRmode := rhCRmode) (hEl := (Nat.lt_of_lt_of_le hEb hSz2))
      (hElk := (by rw [hSo2 E hEb hEC1]; exact hEk)) (hEltyp := (by rw [hSo2 E hEb hEC1]; exact hEt))
      (hElkey := (by rw [hSo2 E hEb hEC1]; exact hEkey)) (hElty := (by rw [hSo2 E hEb hEC1]; exact hEty))
      (hElp := (by rw [hSo2 E hEb hEC1]; exact hEpr)) (hC := (Nat.lt_of_lt_of_le hCb hSz2))
      (hCk := (by rw [hSo2 C hCb hCC1, hCk]; rfl)) (hCp := (by rw [hSo2 C hCb hCC1]; exact hCp))
      (hCr := (by rw [hSo2 C hCb hCC1]; exact hCr)) (hOP := (Nat.lt_of_lt_of_le hOP hSz))
      (hOPk := (by rw [hSo OP hOP dOP.1 dOP.2.1 dOP.2.2 dOPR]; exact hOPk))
      (hOPp := (by rw [hSo OP hOP dOP.1 dOP.2.1 dOP.2.2 dOPR]; exact hOPp))
      (hOPr := (by rw [hSo OP hOP dOP.1 dOP.2.1 dOP.2.2 dOPR]; exact hOPref))
      (hHkey := (by rw [hSo H (by assumption) (hdW H (by simp)).1 (hdW H (by simp)).2.1 (hdW H (by simp)).2.2.1 (hdW H (by simp)).2.2.2]; exact rhHkey))
      (hHet := (by rw [hSo H (by assumption) (hdW H (by simp)).1 (hdW H (by simp)).2.1 (hdW H (by simp)).2.2.1 (hdW H (by simp)).2.2.2]; exact rhHet))
      (hXa := (by rw [hSo X (by assumption) (hdW X (by simp)).1 (hdW X (by simp)).2.1 (hdW X (by simp)).2.2.1 (hdW X (by simp)).2.2.2]; exact rhXa))
      (hXret := (by rw [hSo X (by assumption) (hdW X (by simp)).1 (hdW X (by simp)).2.1 (hdW X (by simp)).2.2.1 (hdW X (by simp)).2.2.2]; exact rhXret))
      (hdX := hdX') (hR := (Nat.lt_of_lt_of_le rhR hSz))
      (hRk := (by rw [hSo r_fR (by assumption) (hdW r_fR (by simp)).1 (hdW r_fR (by simp)).2.1 (hdW r_fR (by simp)).2.2.1 (hdW r_fR (by simp)).2.2.2]; exact rhRk))
      (hRcode := rhRcode) (hRcls := rhRcls) (hRmode := rhRmode) (hRenv := rhRenv) (hRRI := rhRRI) (hRRIv := rhRRIv)
      (hRnT := rhRnT) (hRnS := rhRnS) (hGT := (by js_norm [rhGT, ReactFinishHooks.resetMap])) (hGTm := rhGTm)
      (hGTi := rhGTi) (hGS := (by js_norm [rhGS, ReactFinishHooks.resetMap])) (hGSm := rhGSm) (hGSi := rhGSi)
      (hgU := rhgU) (hRC := (Nat.lt_of_lt_of_le rhRC hSz))
      (hRCk := (by rw [hSo fC (by assumption) (hdW fC (by simp)).1 (hdW fC (by simp)).2.1 (hdW fC (by simp)).2.2.1 (hdW fC (by simp)).2.2.2]; exact rhRCk))
      (hRCcode := rhRCcode) (hRCcls := rhRCcls) (hRCmode := rhRCmode) (hRCenv := rhRCenv)
      (hGRCF := (by js_norm [rhGRCF, ReactFinishHooks.resetMap])) (hGRCFv := rhGRCFv)
      (hC0 := (Nat.lt_of_lt_of_le hC0 hSz)) (hC0k := (by rw [hSo C0 hC0 dC01 dC02 dC03 dC04]; exact hC0k))
      (hC0c := (by rw [hSo C0 (by assumption) (hdW C0 (by simp)).1 (hdW C0 (by simp)).2.1 (hdW C0 (by simp)).2.2.1 (hdW C0 (by simp)).2.2.2]; exact rhC0c))
      (hRF := (Nat.lt_of_lt_of_le hC1 hSz)) (hRFk := hSC1k) (hRFc := hSC1c) (hRFX := rhRFX)) ?postRC
  intro v4 w4 h4 ⟨hv4, hF4, hfu4, hh4, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, hr4, xret,
    hmod4, hC1c4⟩
  subst v4 h4
  have hw4K : w4.envEntry s.envs.size = St.envEntry s.envs.size :=
    envEntry_frame hF4 (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hSE)
      (by simp [ReactReconcileChildren.fpC, ReactReconcileFibers.fpR, hne, Ne.symm hne])
  have hCch4 : (w4.objEntry C).props.get? (.str "children") =
      some (.data (.str (JSStr.ofString "Count: " ++ numberToJSStr xE ++ JSStr.ofString "")) true true true) := by
    rw [props_frame hF4 (Nat.lt_of_lt_of_le hCb hSz2) (by simp [ReactReconcileChildren.fpC, ReactReconcileFibers.fpR,
      ReactReconcileImpl.fpI, ReactCreateWIP.fp, hCC1]), hSo2 C hCb hCC1]
    exact hCch
  have hNP4 : ReactNewProps.NewProps w4 C F OP (JSStr.ofString "Count: " ++ numberToJSStr xE ++ JSStr.ofString "") := by
    refine ReactNewProps.NewProps.frame hF4 ?_ ?_
    · unfold ReactNewProps.NewProps at hNP ⊢; rw [hSo2 C hCb hCC1]; exact ⟨Nat.lt_of_lt_of_le hNP.1 hSz2, hNP.2⟩
    · intro k hk
      have hCX : C ≠ X := Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le rhX hw1z) hCge)
      simp [ReactReconcileChildren.fpC, ReactReconcileFibers.fpR, ReactReconcileImpl.fpI, ReactCreateWIP.fp, hCC1, hCX] at hk
  have FW := frame_extend' FSt hF4 (fun q hq _ => by revert q; simp [ReactReconcileChildren.fpC, ReactReconcileFibers.fpR, fpUF])
    (fun q hq _ => by
      simp only [ReactReconcileChildren.fpC, ReactReconcileFibers.fpR, List.mem_append, List.mem_cons, List.mem_nil_iff,
        or_false] at hq
      simp only [fpUF, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false]
      rcases hq with hq | hq
      · exact Or.inr hq
      · subst hq; simp) (fun _ => rfl)
  have hw4f : 9 ≤ w4.fuel := by omega
  rw [hStKe] at hw4K
  js [hpn, hv, hl, ha, hw4K, Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_trans hSE hF4.envs_le), hC1c4, hw4f,
    FDI.fdiCtx, Sem.inner]
  have hC1St : C1 < St.heap.size := Nat.lt_of_lt_of_le hC1 hSz
  refine ⟨Nat.lt_of_lt_of_le hC1St hF4.heap_le, by rw [kind_frame hF4 hC1St]; exact hSC1k, C, frame_restore FW s, ?_,
    rfl, rfl, hCch4, ?_, ?_, ?_, Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hCb hSz2) hF4.heap_le, ?_,
    ⟨F, by first | exact hNP4 | (unfold ReactNewProps.NewProps at hNP4 ⊢; simp only [restore_objEntry, restore_heap]; exact hNP4)⟩, ?_⟩
  · simp only [js_simp] at hfu1 hfu2 hfu3
    omega
  · rw [props_frame hF4 hC1St (by simp [ReactReconcileChildren.fpC, ReactReconcileFibers.fpR, ReactReconcileImpl.fpI, ReactCreateWIP.fp, rhRFX, Ne.symm rhRFX])]; exact hSC1l
  · rw [props_frame hF4 hC1St (by simp [ReactReconcileChildren.fpC, ReactReconcileFibers.fpR, ReactReconcileImpl.fpI, ReactCreateWIP.fp, rhRFX, Ne.symm rhRFX])]; exact hSC1f
  · show (w4.objEntry C).kind.isPlain = true
    rw [kind_frame hF4 (Nat.lt_of_lt_of_le hCb hSz2), hSo2 C hCb hCC1, hCk]; rfl
  · exact Nat.le_trans (by have := hF1.heap_le; simp only [js_simp] at this; exact this) hCge
  · exact Exists.intro _ ⟨by first | rfl | (rw [restore_envEntry]; exact hmod4),
      by simp [Std.HashMap.getElem?_modify, ReactFinishHooks.resetMap, hGDR, hGDRm, hGDRi],
      by simp [Std.HashMap.getElem?_modify, ReactFinishHooks.resetMap, rhGT, rhGTm, rhGTi],
      by simp [Std.HashMap.getElem?_modify, ReactFinishHooks.resetMap, rhGS, rhGSm, rhGSi, hGL1, hGL1m, hGF1, hGF1m]⟩


set_option linter.unusedVariables false in
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
/-- `click_spec_c` with its callee as a contract (`facts_compose` composes it). -/
theorem click_spec_c {n : Nat}
    {h : σ}
    {fo : ObjId}
    {d : FuncData}
    {s : State}
    {bG : HashMap JSStr Binding}
    {oG : Option EnvId}
    {fD : ObjId}
    {dD : FuncData}
    {fS RSI HD : ObjId}
    {dS : FuncData}
    {bR : HashMap JSStr Binding}
    {oR : Option EnvId}
    {fK IR IJ fJ AP fV fN AIP IP OP : ObjId}
    {dK dJ : FuncData}
    {vT P ms1 vH0 vCO uq ln tRW : Value}
    {fF fRW : ObjId}
    {dF dRW : FuncData}
    {bdHU bdRSd bdDP bdFR bdCO bdDS bdTI bdTS : Binding}
    {uw ue uc lw le lc nw' ne' nc' : Bool}
    {bA bJ : HashMap JSStr Binding}
    {oA oJ : Option EnvId}
    {bdIR bdIJ bdT : Binding}
    {bdV bdN : BuiltinData}
    {xE : F64}
    {irw ire irc ijw ije ijc pw pe pc nnw nne nnc : Bool}
    {bdRSI : Binding}
    {rw re rc uw ue' uc : Bool}
    {bdU bdB : Binding}
    {bdC bdW bdF bdUW bdUR bdRL bdCE bdSD bdDR bdIs : Binding}
    {bdIsb : BuiltinData}
    {fW fR fIs C1 C0 H0 Q U fBS : ObjId}
    {dW dR dBS : FuncData}
    {r ms bs vE a dv : Value}
    {aw ae ac me mc nw ne nc w1 e1 c1 w2 e2 c2 e3 c3 w4 e4 c4 : Bool}
    {qp qr ql qd ul ur ua ue uv un : Bool × Bool × Bool}
    -- (`react`'s module scope: `ReactSharedInternals`, whose `H` is the update dispatcher `HD`)
    (hI : RSI < s.heap.size)
    (hIk : (s.objEntry RSI).kind.isPlain = true)
    (hlt : fo < s.heap.size)
    (hk : (s.objEntry fo).kind = .func d)
    (hf : 500 ≤ s.fuel)
    (hcode : d.code = URGen.updateReducer_func)
    (hcls : d.isClassCtor = false)
    (hmode : d.thisMode = .strict)
    (hG : d.env < s.envs.size)
    (hGe : Scope.declLike? (s.envEntry d.env) = some (bG, oG))
    -- (`updateWorkInProgressHook`'s module variables)
    (hGC : bG[JSStr.ofString "currentHook"]? = some bdC)
    (hGCv : bdC.value = some .null)
    -- (the two callees, functions of the same module)
    (hR : fR < s.heap.size)
    (hRk : (s.objEntry fR).kind = .func dR)
    (hRcode : dR.code = URIGen.updateReducerImpl_func)
    (hRcls : dR.isClassCtor = false)
    (hRmode : dR.thisMode = .strict)
    (hRenv : dR.env = d.env)
    -- (`updateReducerImpl`'s module variables)
    (hGDR : bG[JSStr.ofString "didReceiveUpdate"]? = some bdDR)
    (hGDRm : bdDR.mutable = true)
    (hGDRi : bdDR.value.isSome = true)
    -- (the work in progress `C1`, its current `C0`, the current first hook `H0`, its queue `Q`, the update `U`)
    (hC1 : C1 < s.heap.size)
    (hC1k : (s.objEntry C1).kind.isPlain = true)
    (hC0 : C0 < s.heap.size)
    (hC0k : (s.objEntry C0).kind.isPlain = true)
    (hU : U < s.heap.size)
    (hUk : (s.objEntry U).kind.isPlain = true)
    (hrBS : r = .obj fBS)
    (dBS1 : C1 ≠ fBS)
    (dBS2 : fBS ≠ H0)
    (dBS3 : fBS ≠ Q)
    (dBS4 : fBS ≠ U)
    (d1 : C1 ≠ C0)
    (d2 : C1 ≠ H0)
    (d3 : C1 ≠ Q)
    (d4 : C1 ≠ U)
    (d5 : C1 ≠ fIs)
    (d6 : C1 ≠ fR)
    (d7 : H0 ≠ Q)
    (d8 : H0 ≠ U)
    (d9 : Q ≠ U)
    (d10 : fIs ≠ H0)
    (d11 : fIs ≠ Q)
    (d12 : fIs ≠ U)
    -- (the component and its module scope: `import_react`, `import_jsx_runtime`)
    -- (`jsxProd` and its module's `REACT_ELEMENT_TYPE`)
    -- (the realm's built-ins the destructuring and the object literal use)
    (hOP : OP < s.heap.size)
    (hOPk : (s.objEntry OP).kind.isPlain = true)
    (hOPr : (s.objEntry OP).props.get? (.str "return") = none)
    (hOPp : (s.objEntry OP).proto = .null)
    (hOPref : (s.objEntry OP).props.get? (.str "ref") = none)
    -- (the new state is a Number)
    (hvE : vE = .num xE)
    -- (the realm's and the other modules' objects are not React's fiber, hook, or queue; the module scopes differ)
    (dAP : AP ≠ C1 ∧ AP ≠ H0 ∧ AP ≠ Q)
    (dfV : fV ≠ C1 ∧ fV ≠ H0 ∧ fV ≠ Q)
    (dAIP : AIP ≠ C1 ∧ AIP ≠ H0 ∧ AIP ≠ Q)
    (dfN : fN ≠ C1 ∧ fN ≠ H0 ∧ fN ≠ Q)
    (dIP : IP ≠ C1 ∧ IP ≠ H0 ∧ IP ≠ Q)
    (dOP : OP ≠ C1 ∧ OP ≠ H0 ∧ OP ≠ Q)
    (dIJ : IJ ≠ C1 ∧ IJ ≠ H0 ∧ IJ ≠ Q)
    (dfJ : fJ ≠ C1 ∧ fJ ≠ H0 ∧ fJ ≠ Q)
    (hKd : dK.env ≠ d.env)
    (hJd : dJ.env ≠ d.env)
    -- (renderWithHooks: the update dispatcher, react-dom's `ReactSharedInternals`, no render-phase update scheduled;
    -- finishRenderingHooks and its variables)
    -- (the work in progress's fields renderWithHooks resets; the current hook is the only one)
    -- (the objects the component reads are neither the work in progress nor ReactSharedInternals; react's module
    -- scope is not react-dom's)
    (hdist : ∀ X ∈ [fo, fW, fR, fIs, fBS, C0, H0, Q, U, fD, HD, fS, IR, IJ, fJ, AP, fV, AIP, fN, IP, OP, fK, fF],
      X ≠ C1 ∧ X ≠ RSI)
    (dRC : RSI ≠ C1)
    (hSd : dS.env ≠ d.env)
    -- (renderWithHooks itself, a function of react-dom's module)
    (hRW : fRW < s.heap.size)
    (hRWk : (s.objEntry fRW).kind = .func dRW)
    (dFH : fF ≠ H0 ∧ fF ≠ Q)
    (dRQ : RSI ≠ Q)
    -- (reconcileChildren's premises, its objects renamed)
    {r_fo : ObjId}
    {r_d : FuncData}
    {fU : ObjId}
    {dU : FuncData}
    {r_bR : HashMap JSStr Binding}
    {bdCW : Binding}
    {H X : ObjId}
    {fl : F64}
    {vHT vCL vL vC vMP vMS vUQ vI vR vRC o0 o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 o11 o12 o13 o14 o15 : Value}
    {r0w r0e r0c r1w r1e r1c r2w r2e r2c r3w r3e r3c r4w r4e r4c r5w r5e r5c r6w r6e r6c r7w r7e r7c r8w r8e r8c r9w r9e r9c r10w r10e r10c r11w r11e r11c r12w r12e r12c r13w r13e r13c e0 c0 r_e1 r_c1 r_e2 r_c2 r_e3 r_c3 r_e4 r_c4 e5 c5 e6 c6 e7 c7 e8 c8 e9 c9 e10 c10 e11 c11 e12 c12 e13 c13 e14 c14 e15 c15 : Bool}
    {fI fDel fPl fCR : ObjId}
    {dI dDel dPl dCR : FuncData}
    {vFr : Value}
    {bdDel bdUF bdPl bdST bdFr bdEl bdCR : Binding}
    {ew ee ec kw ke kc yw ye yc r_pw r_pe r_pc bkw bke bkc bew bee bec r_aw r_ae r_ac rew rec : Bool}
    {rv0 : Value}
    {r_fR : ObjId}
    {r_dR : FuncData}
    {bdRI r_bdT r_bdTS : Binding}
    {fC : ObjId}
    {dC : FuncData}
    {bdRCF : Binding}
    {c0w c0e c0c cw cc : Bool}
    {ch0 : Value}
    (rhE : dU.env < s.envs.size)
    (rhX : X < s.heap.size)
    (rhHX : H ≠ X)
    (rhFrEl : vFr ≠ vT)
    (rhdX : ∀ Y ∈ [fCR, fPl, OP], Y ≠ X)
    (rhGT : bG[JSStr.ofString "thenableIndexCounter$1"]? = some r_bdT)
    (rhGTm : r_bdT.mutable = true)
    (rhGTi : r_bdT.value.isSome = true)
    (rhGS : bG[JSStr.ofString "thenableState$1"]? = some r_bdTS)
    (rhGSm : r_bdTS.mutable = true)
    (rhGSi : r_bdTS.value.isSome = true)
    (rhgU : d.env ≠ dU.env)
    (rhRC : fC < s.heap.size)
    (rhRCk : (s.objEntry fC).kind = .func dC)
    (rhRFc : (s.objEntry C1).props.get? (.str "child") = some (.data ch0 true cw cc))
    (rhRFX : C1 ≠ X)
    {fUF fP fCD : ObjId}
    {dUF dP dCD : FuncData}
    {tUF : Value}
    {fl1 : F64}
    {bdP bdRWb bdCD bdRCb bdHy bdF1 bdL1 bdLI : Binding}
    {dpw dpe dpc fw fe fc : Bool}
    -- (updateFunctionComponent and its callees, functions of react-dom's module)
    (hUF : fUF < s.heap.size)
    (hUFk : (s.objEntry fUF).kind = .func dUF)
    (hUFcode : dUF.code = UFCGen.updateFunctionComponent_func)
    (hUFcls : dUF.isClassCtor = false)
    (hUFmode : dUF.thisMode = .strict)
    (hUFenv : dUF.env = d.env)
    (hGP : bG[JSStr.ofString "prepareToReadContext"]? = some bdP)
    (hGPv : bdP.value = some (.obj fP))
    (hPR : fP < s.heap.size)
    (hPRk : (s.objEntry fP).kind = .func dP)
    (hPRcode : dP.code = PRCGen.prepareToReadContext_func)
    (hPRcls : dP.isClassCtor = false)
    (hPRmode : dP.thisMode = .strict)
    (hPRenv : dP.env = d.env)
    (hGRWb : bG[JSStr.ofString "renderWithHooks"]? = some bdRWb)
    (hGRWbv : bdRWb.value = some (.obj fRW))
    (hGCD : bG[JSStr.ofString "checkDidRenderIdHook"]? = some bdCD)
    (hGCDv : bdCD.value = some (.obj fCD))
    (hCD : fCD < s.heap.size)
    (hCDk : (s.objEntry fCD).kind = .func dCD)
    (hCDcode : dCD.code = CDRGen.checkDidRenderIdHook_func)
    (hCDcls : dCD.isClassCtor = false)
    (hCDmode : dCD.thisMode = .strict)
    (hCDenv : dCD.env = d.env)
    (hGRCb : bG[JSStr.ofString "reconcileChildren"]? = some bdRCb)
    (hGRCbv : bdRCb.value = some (.obj fC))
    (hGHy : bG[JSStr.ofString "isHydrating"]? = some bdHy)
    (hGHyv : bdHy.value = some (.bool false))
    (hGF1 : bG[JSStr.ofString "currentlyRenderingFiber$1"]? = some bdF1)
    (hGF1m : bdF1.mutable = true)
    (hGF1i : bdF1.value.isSome = true)
    (hGL1 : bG[JSStr.ofString "lastContextDependency"]? = some bdL1)
    (hGL1m : bdL1.mutable = true)
    (hGL1i : bdL1.value.isSome = true)
    (hGLI : bG[JSStr.ofString "localIdCounter"]? = some bdLI)
    (hGLIm : bdLI.mutable = true)
    (hGLIv : bdLI.value = some (.num (F64.fin false 0 (-1074))))
    -- (the work in progress: no context dependencies; its flags)
    (hC1d : (s.objEntry C1).props.get? (.str "dependencies") = some (.data .null dpw dpe dpc))
    (hC1f : (s.objEntry C1).props.get? (.str "flags") = some (.data (.num fl1) true fe fc))
    -- (reconcileChildren's objects are not what renderWithHooks writes; its closure record is not the module's)
    (hdW : ∀ Y ∈ [r_fo, fU, fI, fDel, fPl, fCR, r_fR, fC, H, X, fCD, C0], Y ≠ C1 ∧ Y ≠ H0 ∧ Y ≠ Q ∧ Y ≠ RSI)
    (hdUe : dU.env ≠ d.env)
    (hcRW : ∀ w h1, Frame (Footprint.union {} (ReactRenderPrep.fpP d.env)) s w → 300 ≤ w.fuel →
      Scope.declLike? (w.envEntry d.env) = some ((bG.modify (JSStr.ofString "currentlyRenderingFiber$1")
        (fun bd => { bd with value := some (.obj C1) })).modify (JSStr.ofString "lastContextDependency")
        (fun bd => { bd with value := some .null }), oG) →
      WP eng answer (n + 6) h1 (callImpl eng (.obj fRW) .undefined #[.obj C0, .obj C1, .obj fK, P, .undefined, two]) w fun v w' h' =>
        ∃ E C F dF', v = .obj E ∧ Frame (fpRWH d.env C1 w.heap.size H0 Q RSI) w w' ∧ w.fuel ≤ w'.fuel + 300 ∧ h' = h1 ∧ w'.realm = w.realm ∧ (w'.objEntry E).props.get? (.str "$$typeof") = some (.data vT true true true) ∧ (w'.objEntry E).props.get? (.str "type") = some (.data (.str (JSStr.ofString "button")) true true true) ∧ (w'.objEntry E).props.get? (.str "key") = some (.data .null true true true) ∧ (w'.objEntry E).props.get? (.str "ref") = some (.data .null true true true) ∧ (w'.objEntry E).props.get? (.str "props") = some (.data (.obj C) true true true) ∧ (w'.objEntry C).props.get? (.str "children") = some (.data (.str (JSStr.ofString "Count: " ++ numberToJSStr xE ++ JSStr.ofString "")) true true true) ∧ (w'.objEntry C).props.get? (.str "onClick") = some (.data (.obj F) true true true) ∧ E < w'.heap.size ∧ C < w'.heap.size ∧ w.heap.size ≤ E ∧ w.heap.size ≤ C ∧ (w'.objEntry E).kind = .ordinary ∧ (w'.objEntry C).kind = .ordinary ∧ (w'.objEntry C).proto = .obj OP ∧ (w'.objEntry C).props.get? (.str "ref") = none ∧ (w'.objEntry F).kind = .func dF' ∧ dF'.code = onClickFunc ∧ dF'.env = w.envs.size + 1 ∧ dF'.thisMode = .lexical ∧ Scope.declLike? (w'.envEntry (w.envs.size + 1)) = some (((((∅ : HashMap JSStr Binding).insert (JSStr.ofString "n") { mutable := false, strict := true }).insert (JSStr.ofString "setN") { mutable := false, strict := true }).modify (JSStr.ofString "n") (fun bd => { bd with value := some (.num xE) })).modify (JSStr.ofString "setN") (fun bd => { bd with value := some dv }), some dK.env) ∧ Scope.declLike? (w'.envEntry d.env) = some (ReactFinishHooks.resetMap ((((((((((bG.modify (JSStr.ofString "currentlyRenderingFiber$1")
        (fun bd => { bd with value := some (.obj C1) })).modify (JSStr.ofString "lastContextDependency")
        (fun bd => { bd with value := some .null }))).modify (JSStr.ofString "renderLanes") (fun bd => { bd with value := some two })).modify (JSStr.ofString "currentlyRenderingFiber") (fun bd => { bd with value := some (.obj C1) })).modify (JSStr.ofString "shouldDoubleInvokeUserFnsInHooksDEV") (fun bd => { bd with value := some (.bool false) })).modify (JSStr.ofString "currentHook") (fun bd => { bd with value := some (.obj H0) })).modify (JSStr.ofString "workInProgressHook") (fun bd => { bd with value := some (.obj w.heap.size) })).modify (JSStr.ofString "didReceiveUpdate") (fun bd => { bd with value := some (.bool true) })).modify (JSStr.ofString "shouldDoubleInvokeUserFnsInHooksDEV") (fun bd => { bd with value := some (.bool false) })), oG) ∧ (w'.objEntry RSI).props.get? (.str "H") = some (.data vCO true re rc) ∧ (w'.objEntry C1).props.get? (.str "memoizedState") = some (.data (.obj w.heap.size) true me mc) ∧ (w'.objEntry C1).props.get? (.str "updateQueue") = some (.data .null true uw uc) ∧ (w'.objEntry C1).props.get? (.str "lanes") = some (.data (.num (F64.fin false 0 (-1074))) true lw lc) ∧ (w'.objEntry w.heap.size).props.get? (.str "memoizedState") = some (.data (.num xE) true true true) ∧ (w'.objEntry w.heap.size).props.get? (.str "baseState") = some (.data (.num xE) true true true) ∧ (w'.objEntry w.heap.size).props.get? (.str "baseQueue") = some (.data .null true true true) ∧ (w'.objEntry w.heap.size).props.get? (.str "queue") = some (.data (.obj Q) true true true) ∧ (w'.objEntry w.heap.size).props.get? (.str "next") = some (.data .null true true true) ∧ (w'.objEntry H0).props.get? (.str "baseQueue") = some (.data (.obj U) true e3 c3) ∧ (w'.objEntry Q).props.get? (.str "pending") = some (.data .null true qp.2.1 qp.2.2) ∧ (w'.objEntry Q).props.get? (.str "lastRenderedReducer") = some (.data r true qr.2.1 qr.2.2) ∧ (w'.objEntry Q).props.get? (.str "lastRenderedState") = some (.data (.num xE) true ql.2.1 ql.2.2) ∧ ReactNewProps.NewProps w' C F OP (JSStr.ofString "Count: " ++ numberToJSStr xE ++ JSStr.ofString ""))
    (hcRC : ∀ w h1 (E C : ObjId) (bGc : HashMap JSStr Binding) (oG : Option EnvId) (ew : Bool) (ee : Bool) (ec : Bool) (kw : Bool) (ke : Bool) (kc : Bool) (yw : Bool) (ye : Bool) (yc : Bool) (pw : Bool) (pe : Bool) (pc : Bool), Frame (fpUF0 d.env C1 H0 Q RSI) s w → 170 ≤ w.fuel →
      d.env < w.envs.size →
      Scope.declLike? (w.envEntry d.env) = some (bGc, oG) →
      bGc[JSStr.ofString "thenableIndexCounter$1"]? = some r_bdT →
      bGc[JSStr.ofString "thenableState$1"]? = some r_bdTS →
      E < w.heap.size →
      (w.objEntry E).kind = .ordinary →
      (w.objEntry E).props.get? (.str "$$typeof") = some (.data vT ew ee ec) →
      (w.objEntry E).props.get? (.str "key") = some (.data .null kw ke kc) →
      (w.objEntry E).props.get? (.str "type") = some (.data (.str (JSStr.ofString "button")) yw ye yc) →
      (w.objEntry E).props.get? (.str "props") = some (.data (.obj C) pw pe pc) →
      C < w.heap.size →
      (w.objEntry C).kind.isPlain = true →
      (w.objEntry C).proto = .obj OP →
      (w.objEntry C).props.get? (.str "ref") = none →
      OP < w.heap.size →
      (w.objEntry OP).kind.isPlain = true →
      (w.objEntry OP).proto = .null →
      (w.objEntry OP).props.get? (.str "ref") = none →
      C0 < w.heap.size →
      (w.objEntry C0).kind.isPlain = true →
      C1 < w.heap.size →
      (w.objEntry C1).kind.isPlain = true →
      (w.objEntry C1).props.get? (.str "child") = some (.data ch0 true cw cc) →
      E ≠ X → C ≠ X →
      WP eng answer (n + 6) h1 (callImpl eng (.obj fC) .undefined #[.obj C0, .obj C1, .obj E, two]) w fun v w' h' =>
        v = .undefined ∧ Logic.Frame (ReactReconcileChildren.fpC d.env X C1) w w' ∧ w.fuel ≤ w'.fuel + 170 ∧ h' = h1 ∧ (w'.objEntry X).props.get? (.str "pendingProps") = some (.data (.obj C) true e0 c0) ∧ (w'.objEntry X).props.get? (.str "type") = some (.data (vHT) true r_e1 r_c1) ∧ (w'.objEntry X).props.get? (.str "flags") = some (.data (.num (numberBinOp .bitAnd fl (F64.fin false 5062151534280704 (-22)))) true r_e2 r_c2) ∧ (w'.objEntry X).props.get? (.str "subtreeFlags") = some (.data (.num (F64.fin false 0 (-1074))) true r_e3 r_c3) ∧ (w'.objEntry X).props.get? (.str "deletions") = some (.data (.null) true r_e4 r_c4) ∧ (w'.objEntry X).props.get? (.str "childLanes") = some (.data (vCL) true e5 c5) ∧ (w'.objEntry X).props.get? (.str "lanes") = some (.data (vL) true e6 c6) ∧ (w'.objEntry X).props.get? (.str "child") = some (.data (vC) true e7 c7) ∧ (w'.objEntry X).props.get? (.str "memoizedProps") = some (.data (vMP) true e8 c8) ∧ (w'.objEntry X).props.get? (.str "memoizedState") = some (.data (vMS) true e9 c9) ∧ (w'.objEntry X).props.get? (.str "updateQueue") = some (.data (vUQ) true e10 c10) ∧ (w'.objEntry X).props.get? (.str "dependencies") = some (.data (.null) true e11 c11) ∧ (w'.objEntry X).props.get? (.str "sibling") = some (.data .null true e12 c12) ∧ (w'.objEntry X).props.get? (.str "index") = some (.data (.num (F64.fin false 0 (-1074))) true e13 c13) ∧ (w'.objEntry X).props.get? (.str "ref") = some (.data .null true e14 c14) ∧ (w'.objEntry X).props.get? (.str "refCleanup") = some (.data (vRC) true e15 c15) ∧ w'.realm = w.realm ∧ (w'.objEntry X).props.get? (.str "return") = some (.data (.obj C1) true rew rec) ∧ Scope.declLike? (w'.envEntry d.env) = some ((bGc.modify (JSStr.ofString "thenableIndexCounter$1") (fun bd => { bd with value := some (.num (F64.fin false 0 (-1074))) })).modify (JSStr.ofString "thenableState$1") (fun bd => { bd with value := some .null }), oG) ∧ (w'.objEntry C1).props.get? (.str "child") = some (.data (.obj X) true cw cc)) :
    WP eng answer (n + 7) h (callImpl eng (.obj fUF) tUF #[.obj C0, .obj C1, .obj fK, P, two]) s fun v w h' =>
      ∃ C : ObjId, v = .obj X ∧ Frame (fpUF d.env C1 H0 Q RSI X) s w ∧ s.fuel ≤ w.fuel + 500 ∧ h' = h ∧ w.realm = s.realm ∧
      (w.objEntry X).props.get? (.str "pendingProps") = some (.data (.obj C) true e0 c0) ∧
      (w.objEntry X).props.get? (.str "type") = some (.data (vHT) true r_e1 r_c1) ∧
      (w.objEntry X).props.get? (.str "flags") = some (.data (.num (numberBinOp .bitAnd fl (F64.fin false 5062151534280704 (-22)))) true r_e2 r_c2) ∧
      (w.objEntry X).props.get? (.str "subtreeFlags") = some (.data (.num (F64.fin false 0 (-1074))) true r_e3 r_c3) ∧
      (w.objEntry X).props.get? (.str "deletions") = some (.data (.null) true r_e4 r_c4) ∧
      (w.objEntry X).props.get? (.str "childLanes") = some (.data (vCL) true e5 c5) ∧
      (w.objEntry X).props.get? (.str "lanes") = some (.data (vL) true e6 c6) ∧
      (w.objEntry X).props.get? (.str "child") = some (.data (vC) true e7 c7) ∧
      (w.objEntry X).props.get? (.str "memoizedProps") = some (.data (vMP) true e8 c8) ∧
      (w.objEntry X).props.get? (.str "memoizedState") = some (.data (vMS) true e9 c9) ∧
      (w.objEntry X).props.get? (.str "updateQueue") = some (.data (vUQ) true e10 c10) ∧
      (w.objEntry X).props.get? (.str "dependencies") = some (.data (.null) true e11 c11) ∧
      (w.objEntry X).props.get? (.str "sibling") = some (.data .null true e12 c12) ∧
      (w.objEntry X).props.get? (.str "index") = some (.data (.num (F64.fin false 0 (-1074))) true e13 c13) ∧
      (w.objEntry X).props.get? (.str "ref") = some (.data .null true e14 c14) ∧
      (w.objEntry X).props.get? (.str "refCleanup") = some (.data (vRC) true e15 c15) ∧
      (w.objEntry X).props.get? (.str "return") = some (.data (.obj C1) true rew rec) ∧
      (w.objEntry C1).props.get? (.str "child") = some (.data (.obj X) true cw cc) ∧
      (w.objEntry C).props.get? (.str "children") =
        some (.data (.str (JSStr.ofString "Count: " ++ numberToJSStr xE ++ JSStr.ofString "")) true true true) ∧
      (w.objEntry C1).props.get? (.str "lanes") = some (.data (.num (F64.fin false 0 (-1074))) true lw lc) ∧
      (w.objEntry C1).props.get? (.str "flags") = some (.data (.num (numberBinOp .bitOr fl1 (F64.fin false 4503599627370496 (-52)))) true fe fc) ∧
      -- (the dispatcher `finishRenderingHooks` left: `ContextOnlyDispatcher`)
      (w.objEntry RSI).props.get? (.str "H") = some (.data vCO true re rc) ∧
      (w.objEntry C).kind.isPlain = true ∧ C < w.heap.size ∧ s.heap.size ≤ C ∧
      (∃ F, ReactNewProps.NewProps w C F OP (JSStr.ofString "Count: " ++ numberToJSStr xE ++ JSStr.ofString "")) ∧
      ∃ bm, Scope.declLike? (w.envEntry d.env) = some (bm, oG) ∧
        (∃ bd, bm[JSStr.ofString "didReceiveUpdate"]? = some bd ∧ bd.mutable = true ∧ bd.value.isSome = true) ∧
        (∃ bd, bm[JSStr.ofString "thenableIndexCounter$1"]? = some bd ∧ bd.mutable = true ∧ bd.value.isSome = true) ∧
        ∃ bd, bm[JSStr.ofString "thenableState$1"]? = some bd ∧ bd.mutable = true ∧ bd.value.isSome = true ∧
        (∃ bd, bm[JSStr.ofString "lastContextDependency"]? = some bd ∧ bd.mutable = true ∧ bd.value.isSome = true) ∧
        (∃ bd, bm[JSStr.ofString "currentlyRenderingFiber$1"]? = some bd ∧ bd.mutable = true ∧ bd.value.isSome = true) := by
  subst hrBS
  apply wp_callGen UFCGen.updateFunctionComponent_eq (by decide) hUF hUFk (by omega) hUFcls hUFmode
    (by rw [hUFcode]; rfl) (by rw [hUFcode]; rfl) (simpleUF dUF hUFcode) (by rw [hUFcode]; rfl) (by rw [hUFcode]; rfl)
  have hpn : dUF.code.info.fdi.paramNames = #[JSStr.ofString "current", JSStr.ofString "workInProgress",
      JSStr.ofString "Component", JSStr.ofString "nextProps", JSStr.ofString "renderLanes"] := by rw [hUFcode]; rfl
  have hv : dUF.code.info.fdi.varNames = #[] := by rw [hUFcode]; rfl
  have hl : FDI.lexDecls dUF = #[] := by simp [FDI.lexDecls, hUFcode, UFCGen.updateFunctionComponent_func, Func.info]
  have ha : dUF.code.isAsync = false := by rw [hUFcode]; rfl
  have hne : s.envs.size ≠ d.env := Nat.ne_of_gt hG
  have hG1 : d.env < s.envs.size + 1 := Nat.lt_succ_of_lt hG
  clear hUFcode
  simp only [UFCGen.updateFunctionComponent]
  js [hpn, hv, hl, ha, hUFenv, hG, hG1, hne, Ne.symm hne, hGe, hGP, hGPv, hPR, hPRk, FDI.fdiCtx, Sem.inner]
  -- (`prepareToReadContext(workInProgress)`)
  refine ⟨by js_norm [CallableC, hPR, hPRk], ?_⟩
  refine wp_mono (ReactRenderPrep.prepare_spec (bG := bG) (oG := oG) hPR hPRk (by js_norm; omega) hPRcode hPRcls hPRmode
    (by js_norm [hPRenv, hG, hG1]) (by js_norm [hPRenv, hGe, hne, Ne.symm hne]) hGF1 hGF1m hGF1i hGL1 hGL1m hGL1i
    hC1 hC1k hC1d) ?postP
  intro v1 w1 h1 ⟨hv1, hF1, hfu1, hh1, hr1, hd1⟩
  subst v1 h1
  rw [hPRenv] at hF1 hd1
  have hw1o : ∀ o, o < s.heap.size → w1.objEntry o = s.objEntry o := fun o ho =>
    objEntry_frame hF1 (by js_norm [ho]) (by simp [ReactRenderPrep.fpP])
  have hw1e : ∀ e, e < s.envs.size + 1 → e ≠ d.env → w1.envEntry e = (bodyState s fUF dUF tUF
      #[.obj C0, .obj C1, .obj fK, P, two]).envEntry e := fun e he hne' =>
    envEntry_frame hF1 (by js_norm [he]) (by simp [ReactRenderPrep.fpP, Ne.symm hne'])
  have hw1K := hw1e s.envs.size (Nat.lt_succ_self _) hne
  simp only [js_simp, ↓reduceIte] at hw1K
  have hw1E : s.envs.size + 1 ≤ w1.envs.size := by have := hF1.envs_le; simp only [js_simp] at this; exact this
  have hw1z : s.heap.size ≤ w1.heap.size := by have := hF1.heap_le; simp only [js_simp] at this; exact this
  have hw1f : 400 ≤ w1.fuel := by simp only [js_simp] at hfu1; omega
  have hGw1 : d.env < w1.envs.size := Nat.lt_of_lt_of_le hG1 hw1E
  have hEw1 : s.envs.size < w1.envs.size := Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hw1E
  js [hpn, hv, hl, ha, hw1K, hEw1, hGw1, hd1, hGRWb, hGRWbv, hw1o, hRW, hRWk, hw1f, FDI.fdiCtx, Sem.inner]
  refine wp_void ?_
  js [hpn, hv, hl, ha, hw1K, hEw1, hGw1, hd1, hGRWb, hGRWbv, hw1o, hRW, hRWk, hw1f, FDI.fdiCtx, Sem.inner]
  -- (`renderWithHooks(current, workInProgress, Counter, props, undefined, 2)`)
  have hw1s : ∀ e, e < s.envs.size → e ≠ d.env → w1.envEntry e = s.envEntry e := by
    intro e he hne'; rw [hw1e e (Nat.lt_succ_of_lt he) hne']; js_norm [Nat.ne_of_lt he, Nat.ne_of_gt he, he]
  have hw1R : w1.realms = s.realms := by rw [hF1.realms_eq]; rfl
  refine ⟨by js_norm [CallableC, hw1o, hRW, hRWk, Nat.lt_of_lt_of_le hRW hw1z], ?_⟩
  refine wp_mono (hcRW _ _  (frame_trans (frame_bodyState (frame_refl ({} : Footprint) s) fUF dUF tUF _) hF1) (by omega) hd1) ?postRW
  clear hcRW
  intro v2 w2 h2 ⟨E, C, F, dF', hvE, hF2, hfu2, hh2, hr2, hEt, hEty, hEkey, hEref, hEpr, hCch, hCoc, hEb, hCb, hEge, hCge, hEk, hCk,
    hCp, hCr, hFk, hFcode, hFenv, hFthis, hcomp, hmod, hRSIH, hC1m', hC1u', hC1l', hk1, hk2, hk3, hk4, hk5, hH0b', hQp',
    hQr', hQl', hNP⟩
  subst v2 h2
  -- (what renderWithHooks left: its footprint's objects are C1, the new hook, H0, Q, RSI)
  have hfpW : ∀ o, o ≠ C1 → o ≠ w1.heap.size → o ≠ H0 → o ≠ Q → o ≠ RSI →
      (fpRWH d.env C1 w1.heap.size H0 Q RSI).props.all (fun p => p.1 != o) = true := by
    intro o h1 h2 h3 h4 h5; simp [fpRWH, Ne.symm h1, Ne.symm h2, Ne.symm h3, Ne.symm h4, Ne.symm h5]
  have hw2o : ∀ o, o < s.heap.size → o ≠ C1 → o ≠ H0 → o ≠ Q → o ≠ RSI → w2.objEntry o = s.objEntry o := by
    intro o ho h1 h3 h4 h5
    rw [objEntry_frame hF2 (Nat.lt_of_lt_of_le ho hw1z) (hfpW o h1 (Nat.ne_of_lt (Nat.lt_of_lt_of_le ho hw1z)) h3 h4 h5),
      hw1o o ho]
  have hw2E : w1.envs.size ≤ w2.envs.size := hF2.envs_le
  have hw2z : w1.heap.size ≤ w2.heap.size := hF2.heap_le
  have hw2K : w2.envEntry s.envs.size = w1.envEntry s.envs.size :=
    envEntry_frame hF2 hEw1 (by simp [fpRWH, hne, Ne.symm hne])
  rw [hw1K] at hw2K
  have hEw2 : s.envs.size < w2.envs.size := Nat.lt_of_lt_of_le hEw1 hw2E
  have hGw2 : d.env < w2.envs.size := Nat.lt_of_lt_of_le hGw1 hw2E
  have hw2f : 189 ≤ w2.fuel := by simp only [js_simp] at hfu1 hfu2; omega
  have hdCD := hdW fCD (by simp)
  have hw2CD : w2.objEntry fCD = s.objEntry fCD := hw2o fCD hCD hdCD.1 hdCD.2.1 hdCD.2.2.1 hdCD.2.2.2
  js [hpn, hv, hl, ha, hw2K, hEw2, hGw2, hmod, hGCD, hGCDv, hw2CD, hCD, hCDk, Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hCD hw1z) hw2z,
    hw2f, ReactFinishHooks.resetMap, FDI.fdiCtx, Sem.inner]
  -- (`checkDidRenderIdHook()`: false)
  have hCDw2 : fCD < w2.heap.size := Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hCD hw1z) hw2z
  refine ⟨by js_norm [CallableC, hw2CD, hCDk, hCDw2], ?_⟩
  refine wp_mono (ReactRenderPrep.check_spec (oG := oG) (bdI := bdLI) (by js_norm [hCDw2]) (by js_norm [hw2CD, hCDk])
    (by js_norm; omega) hCDcode hCDcls hCDmode (by js_norm [hCDenv, hGw2]) (by rw [hCDenv]; js_norm [hne, Ne.symm hne, hEw2, hGw2]; exact hmod)
    (by js_norm [hGLI, ReactFinishHooks.resetMap]) hGLIm hGLIv) ?postCD
  intro v3 w3 h3 ⟨hv3, hF3, hfu3, hh3, hr3, hmod3⟩
  subst v3 h3
  rw [hCDenv] at hF3 hmod3
  have hw3K := envEntry_frame hF3 (e := s.envs.size) (by js_norm [hEw2]) (by simp [hne, Ne.symm hne])
  simp only [js_simp, ↓reduceIte, hEw2, hne, Ne.symm hne] at hw3K
  have hw3o : ∀ o, o < w2.heap.size → w3.objEntry o = w2.objEntry o := by
    intro o ho; rw [objEntry_frame hF3 (by js_norm [ho]) (by simp)]; js_norm
  have hw3E : w2.envs.size ≤ w3.envs.size := by have := hF3.envs_le; simp only [js_simp] at this; exact this
  have hw3z : w2.heap.size ≤ w3.heap.size := by have := hF3.heap_le; simp only [js_simp] at this; exact this
  have hC1w2 : C1 < w2.heap.size := Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hC1 hw1z) hw2z
  have hC1f2 : (w2.objEntry C1).props.get? (.str "flags") = some (.data (.num fl1) true fe fc) := by
    rw [props_frame hF2 (Nat.lt_of_lt_of_le hC1 hw1z) (by simp [fpRWH]), hw1o C1 hC1]; exact hC1f
  have hC1k2 : (w2.objEntry C1).kind.isPlain = true := by
    rw [kind_frame hF2 (Nat.lt_of_lt_of_le hC1 hw1z), hw1o C1 hC1]; exact hC1k
  have hC1f3 : (w3.objEntry C1).props.get? (.str "flags") = some (.data (.num fl1) true fe fc) := by
    rw [hw3o C1 hC1w2]; exact hC1f2
  have hC1k3 : (w3.objEntry C1).kind.isPlain = true := by rw [hw3o C1 hC1w2]; exact hC1k2
  have hEw3 : s.envs.size < w3.envs.size := Nat.lt_of_lt_of_le hEw2 hw3E
  have hGw3 : d.env < w3.envs.size := Nat.lt_of_lt_of_le hGw2 hw3E
  have hw3f : 179 ≤ w3.fuel := by simp only [js_simp] at hfu3; omega
  js [hpn, hv, hl, ha, hw3K, hEw3, hGw3, hmod3, hGHy, hGHyv, hGRCb, hGRCbv, hC1f3, hC1k3, hC1f2, hC1k2, hC1w2,
    Nat.lt_of_lt_of_le hC1w2 hw3z, hw3f, ReactFinishHooks.resetMap, FDI.fdiCtx, Sem.inner]
  -- (`reconcileChildren(current, workInProgress, Component, renderLanes)`)
  have hdRC := hdW fC (by simp)
  have hw3RC : w3.objEntry fC = s.objEntry fC := by
    rw [hw3o fC (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le rhRC hw1z) hw2z), hw2o fC rhRC hdRC.1 hdRC.2.1 hdRC.2.2.1 hdRC.2.2.2]
  refine ⟨by js_norm [CallableC, hw3RC, rhRCk, hdRC.1, Ne.symm hdRC.1,
    Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le rhRC hw1z) hw2z) hw3z], ?_⟩
  refine wp_gen_state fun St hSt => ?_
  have hEC1 : E ≠ C1 := Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hC1 hw1z) hEge)
  have hCC1 : C ≠ C1 := Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hC1 hw1z) hCge)
  have hSo2 : ∀ o, o < w2.heap.size → o ≠ C1 → St.objEntry o = w2.objEntry o := by
    intro o ho h1; rw [hSt]; js_norm [h1, Ne.symm h1, hw3o o ho]
  have hSo : ∀ o, o < s.heap.size → o ≠ C1 → o ≠ H0 → o ≠ Q → o ≠ RSI → St.objEntry o = s.objEntry o :=
    fun o ho a b c e => (hSo2 o (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le ho hw1z) hw2z) a).trans (hw2o o ho a b c e)
  have hSz2 : w2.heap.size ≤ St.heap.size := by rw [hSt]; simp only [js_simp]; exact hw3z
  have hSz : s.heap.size ≤ St.heap.size := Nat.le_trans (Nat.le_trans hw1z hw2z) hSz2
  have hSE : s.envs.size + 1 ≤ St.envs.size := by
    rw [hSt]; simp only [js_simp]; exact Nat.le_trans hw1E (Nat.le_trans hw2E hw3E)
  have hGw3S : d.env < St.envs.size := Nat.lt_of_lt_of_le hG1 hSE
  have hUs := rhE
  have hw3U : w3.envEntry dU.env = s.envEntry dU.env := by
    rw [envEntry_frame hF3 (e := dU.env) (by js_norm [Nat.lt_of_lt_of_le hUs (Nat.le_of_lt hEw2)]) (by simp [hdUe, Ne.symm hdUe])]
    js_norm [Nat.ne_of_lt hUs, Nat.ne_of_gt hUs]
    rw [envEntry_frame hF2 (e := dU.env) (Nat.lt_of_lt_of_le hUs (Nat.le_of_lt hEw1)) (by simp [fpRWH, hdUe, Ne.symm hdUe]),
      hw1s _ hUs hdUe]
  have hSU : St.envEntry dU.env = s.envEntry dU.env := by
    rw [hSt]; js_norm [Nat.ne_of_lt hUs, Nat.ne_of_gt hUs, hw3U]
  have hSd : Scope.declLike? (St.envEntry d.env) = some (((ReactFinishHooks.resetMap ((((((((((bG.modify (JSStr.ofString "currentlyRenderingFiber$1") (fun bd => { bd with value := some (.obj C1) })).modify
        (JSStr.ofString "lastContextDependency") (fun bd => { bd with value := some .null })).modify (JSStr.ofString "renderLanes") (fun bd => { bd with value := some two })).modify
        (JSStr.ofString "currentlyRenderingFiber") (fun bd => { bd with value := some (.obj C1) })).modify
        (JSStr.ofString "shouldDoubleInvokeUserFnsInHooksDEV") (fun bd => { bd with value := some (.bool false) })).modify
        (JSStr.ofString "currentHook") (fun bd => { bd with value := some (.obj H0) })).modify
        (JSStr.ofString "workInProgressHook") (fun bd => { bd with value := some (.obj w1.heap.size) })).modify
        (JSStr.ofString "didReceiveUpdate") (fun bd => { bd with value := some (.bool true) })).modify
        (JSStr.ofString "shouldDoubleInvokeUserFnsInHooksDEV") (fun bd => { bd with value := some (.bool false) })))).modify (JSStr.ofString "localIdCounter")
        (fun bd => { bd with value := some (.num (F64.fin false 0 (-1074))) })), oG) := by
    rw [hSt]; js_norm [hne, Ne.symm hne, hGw3]; exact hmod3
  have hSC1k : (St.objEntry C1).kind.isPlain = true := by rw [hSt]; js_norm [hC1k3, Nat.lt_of_lt_of_le hC1w2 hw3z]
  have hSC1c : (St.objEntry C1).props.get? (.str "child") = some (.data ch0 true cw cc) := by
    rw [hSt]; js_norm [Nat.lt_of_lt_of_le hC1w2 hw3z, hw3o C1 hC1w2]
    rw [props_frame hF2 (Nat.lt_of_lt_of_le hC1 hw1z) (by simp [fpRWH]), hw1o C1 hC1]; exact rhRFc
  have hSF : 179 ≤ St.fuel := by rw [hSt]; simp only [js_simp]; omega
  have hSC1f : (St.objEntry C1).props.get? (.str "flags") = some (.data (.num (numberBinOp .bitOr fl1 (F64.fin false 4503599627370496 (-52)))) true fe fc) := by
    rw [hSt]; js_norm [Nat.lt_of_lt_of_le hC1w2 hw3z, hC1f3]
  have hSC1l : (St.objEntry C1).props.get? (.str "lanes") = some (.data (.num (F64.fin false 0 (-1074))) true lw lc) := by
    rw [hSt]; js_norm [Nat.lt_of_lt_of_le hC1w2 hw3z, hw3o C1 hC1w2, hC1l']
  have hdX' : ∀ Y ∈ [fCR, fPl, E, C, OP], Y ≠ X := by
    intro Y hY
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hY
    rcases hY with rfl | rfl | rfl | rfl | rfl
    · exact rhdX _ (by simp)
    · exact rhdX _ (by simp)
    · exact Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le rhX hw1z) hEge)
    · exact Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le rhX hw1z) hCge)
    · exact rhdX _ (by simp)
  have dC01 := (hdW C0 (by simp)).1
  have dC02 := (hdW C0 (by simp)).2.1
  have dC03 := (hdW C0 (by simp)).2.2.1
  have dC04 := (hdW C0 (by simp)).2.2.2
  have dOPR : OP ≠ RSI := (hdist OP (by simp)).2
  have F0 : Frame (fpUF d.env C1 H0 Q RSI X) s (bodyState s fUF dUF tUF #[.obj C0, .obj C1, .obj fK, P, two]) :=
    frame_mono (frame_bodyState (frame_refl ({} : Footprint) s) _ _ _ _) (by simp) (by simp) (fun _ => rfl)
  have F1 := frame_extend' F0 hF1 (fun q hq _ => by revert q; simp [ReactRenderPrep.fpP, fpUF]) (fun q hq _ => by
    revert q; simp [ReactRenderPrep.fpP]) (fun _ => rfl)
  have F2 := frame_extend' F1 hF2 (fun q hq _ => by revert q; simp [fpRWH, fpUF]) (fun q hq hlt => by
    simp only [fpRWH, List.mem_cons, List.mem_nil_iff, or_false] at hq
    rcases hq with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      first | (simp [fpUF]; done) | exact absurd (Nat.lt_of_lt_of_le hlt hw1z) (Nat.lt_irrefl _)) (fun _ => rfl)
  have F3 := frame_extend' (frame_setEnv_new F2 (Nat.le_refl _) _) hF3 (fun q hq _ => by revert q; simp [fpUF])
    (fun q hq _ => by revert q; simp) (fun _ => rfl)
  have FSt : Frame (fpUF d.env C1 H0 Q RSI X) s St := by
    rw [hSt]; clear hF1 hF2 hF3 F0 F1 F2; simp only [fpUF, ReactReconcileImpl.fpI, ReactCreateWIP.fp] at F3 ⊢
    frame_go' [F3, hC1, Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hC1w2 hw3z) (Nat.le_refl _)]
  have F0' : Frame (fpUF0 d.env C1 H0 Q RSI) s (bodyState s fUF dUF tUF #[.obj C0, .obj C1, .obj fK, P, two]) :=
    frame_mono (frame_bodyState (frame_refl ({} : Footprint) s) _ _ _ _) (by simp) (by simp) (fun _ => rfl)
  have F1' := frame_extend' F0' hF1 (fun q hq _ => by revert q; simp [ReactRenderPrep.fpP, fpUF0]) (fun q hq _ => by
    revert q; simp [ReactRenderPrep.fpP]) (fun _ => rfl)
  have F2' := frame_extend' F1' hF2 (fun q hq _ => by revert q; simp [fpRWH, fpUF0]) (fun q hq hlt => by
    simp only [fpRWH, List.mem_cons, List.mem_nil_iff, or_false] at hq
    rcases hq with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      first | (simp [fpUF0]; done) | exact absurd (Nat.lt_of_lt_of_le hlt hw1z) (Nat.lt_irrefl _)) (fun _ => rfl)
  have F3' := frame_extend' (frame_setEnv_new F2' (Nat.le_refl _) _) hF3 (fun q hq _ => by revert q; simp [fpUF0])
    (fun q hq _ => by revert q; simp) (fun _ => rfl)
  have FSt0 : Frame (fpUF0 d.env C1 H0 Q RSI) s St := by
    rw [hSt]; clear hF1 hF2 hF3 F0 F1 F2 F3 F0' F1' F2'; simp only [fpUF0] at F3' ⊢
    frame_go' [F3', hC1, Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hC1w2 hw3z) (Nat.le_refl _)]
  have hStF3 : St.fuel = w3.fuel := by rw [hSt]; simp only [js_simp]
  have hStKe := congrArg (fun st : State => st.envEntry s.envs.size) hSt
  simp only [js_simp, ↓reduceIte, hEw3] at hStKe
  clear hSt
  refine wp_mono (hcRC St _ E C _ _ _ _ _ _ _ _ _ _ _ _ _ _ FSt0 (Nat.le_trans (by decide) hSF) hGw3S hSd
    (by simp [Std.HashMap.getElem?_modify, ReactFinishHooks.resetMap, rhGT])
    (by simp [Std.HashMap.getElem?_modify, ReactFinishHooks.resetMap, rhGS]) ((Nat.lt_of_lt_of_le hEb hSz2)) ((by rw [hSo2 E hEb hEC1]; exact hEk)) ((by rw [hSo2 E hEb hEC1]; exact hEt)) ((by rw [hSo2 E hEb hEC1]; exact hEkey)) ((by rw [hSo2 E hEb hEC1]; exact hEty)) ((by rw [hSo2 E hEb hEC1]; exact hEpr)) ((Nat.lt_of_lt_of_le hCb hSz2)) ((by rw [hSo2 C hCb hCC1, hCk]; rfl)) ((by rw [hSo2 C hCb hCC1]; exact hCp)) ((by rw [hSo2 C hCb hCC1]; exact hCr)) ((Nat.lt_of_lt_of_le hOP hSz)) ((by rw [hSo OP hOP dOP.1 dOP.2.1 dOP.2.2 dOPR]; exact hOPk)) ((by rw [hSo OP hOP dOP.1 dOP.2.1 dOP.2.2 dOPR]; exact hOPp)) ((by rw [hSo OP hOP dOP.1 dOP.2.1 dOP.2.2 dOPR]; exact hOPref)) ((Nat.lt_of_lt_of_le hC0 hSz)) ((by rw [hSo C0 hC0 dC01 dC02 dC03 dC04]; exact hC0k)) ((Nat.lt_of_lt_of_le hC1 hSz)) hSC1k hSC1c
    (Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le rhX hw1z) hEge))
    (Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le rhX hw1z) hCge))) ?postRC
  clear hcRC
  intro v4 w4 h4 ⟨hv4, hF4, hfu4, hh4, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, hr4, xret,
    hmod4, hC1c4⟩
  subst v4 h4
  have hw4K : w4.envEntry s.envs.size = St.envEntry s.envs.size :=
    envEntry_frame hF4 (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hSE)
      (by simp [ReactReconcileChildren.fpC, ReactReconcileFibers.fpR, hne, Ne.symm hne])
  have hCch4 : (w4.objEntry C).props.get? (.str "children") =
      some (.data (.str (JSStr.ofString "Count: " ++ numberToJSStr xE ++ JSStr.ofString "")) true true true) := by
    rw [props_frame hF4 (Nat.lt_of_lt_of_le hCb hSz2) (by simp [ReactReconcileChildren.fpC, ReactReconcileFibers.fpR,
      ReactReconcileImpl.fpI, ReactCreateWIP.fp, hCC1]), hSo2 C hCb hCC1]
    exact hCch
  have hNP4 : ReactNewProps.NewProps w4 C F OP (JSStr.ofString "Count: " ++ numberToJSStr xE ++ JSStr.ofString "") := by
    refine ReactNewProps.NewProps.frame hF4 ?_ ?_
    · unfold ReactNewProps.NewProps at hNP ⊢; rw [hSo2 C hCb hCC1]; exact ⟨Nat.lt_of_lt_of_le hNP.1 hSz2, hNP.2⟩
    · intro k hk
      have hCX : C ≠ X := Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le rhX hw1z) hCge)
      simp [ReactReconcileChildren.fpC, ReactReconcileFibers.fpR, ReactReconcileImpl.fpI, ReactCreateWIP.fp, hCC1, hCX] at hk
  have FW := frame_extend' FSt hF4 (fun q hq _ => by revert q; simp [ReactReconcileChildren.fpC, ReactReconcileFibers.fpR, fpUF])
    (fun q hq _ => by
      simp only [ReactReconcileChildren.fpC, ReactReconcileFibers.fpR, List.mem_append, List.mem_cons, List.mem_nil_iff,
        or_false] at hq
      simp only [fpUF, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false]
      rcases hq with hq | hq
      · exact Or.inr hq
      · subst hq; simp) (fun _ => rfl)
  have hw4f : 9 ≤ w4.fuel := by omega
  rw [hStKe] at hw4K
  js [hpn, hv, hl, ha, hw4K, Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_trans hSE hF4.envs_le), hC1c4, hw4f,
    FDI.fdiCtx, Sem.inner]
  have hC1St : C1 < St.heap.size := Nat.lt_of_lt_of_le hC1 hSz
  refine ⟨Nat.lt_of_lt_of_le hC1St hF4.heap_le, by rw [kind_frame hF4 hC1St]; exact hSC1k, C, frame_restore FW s, ?_,
    rfl, rfl, hCch4, ?_, ?_, ?_, ?_, Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hCb hSz2) hF4.heap_le, ?_,
    ⟨F, by first | exact hNP4 | (unfold ReactNewProps.NewProps at hNP4 ⊢; simp only [restore_objEntry, restore_heap]; exact hNP4)⟩, ?_⟩
  · simp only [js_simp] at hfu1 hfu2 hfu3
    omega
  · rw [props_frame hF4 hC1St (by simp [ReactReconcileChildren.fpC, ReactReconcileFibers.fpR, ReactReconcileImpl.fpI, ReactCreateWIP.fp, rhRFX, Ne.symm rhRFX])]; exact hSC1l
  · rw [props_frame hF4 hC1St (by simp [ReactReconcileChildren.fpC, ReactReconcileFibers.fpR, ReactReconcileImpl.fpI, ReactCreateWIP.fp, rhRFX, Ne.symm rhRFX])]; exact hSC1f
  · -- (`RSI.H`: renderWithHooks' post, kept by the check and the reconciliation, whose objects are `X` and `C1`)
    have hRw2 : RSI < w2.heap.size := Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hI hw1z) hw2z
    have hXR : X ≠ RSI := (hdW X (by simp)).2.2.2
    rw [props_frame hF4 (Nat.lt_of_lt_of_le hRw2 hSz2) (by simp [ReactReconcileChildren.fpC, ReactReconcileFibers.fpR,
      ReactReconcileImpl.fpI, ReactCreateWIP.fp, dRC, hXR, Ne.symm hXR, Ne.symm dRC]), hSo2 RSI hRw2 dRC]
    exact hRSIH
  · show (w4.objEntry C).kind.isPlain = true
    rw [kind_frame hF4 (Nat.lt_of_lt_of_le hCb hSz2), hSo2 C hCb hCC1, hCk]; rfl
  · exact Nat.le_trans (by have := hF1.heap_le; simp only [js_simp] at this; exact this) hCge
  · exact Exists.intro _ ⟨by first | rfl | (rw [restore_envEntry]; exact hmod4),
      by simp [Std.HashMap.getElem?_modify, ReactFinishHooks.resetMap, hGDR, hGDRm, hGDRi],
      by simp [Std.HashMap.getElem?_modify, ReactFinishHooks.resetMap, rhGT, rhGTm, rhGTi],
      by simp [Std.HashMap.getElem?_modify, ReactFinishHooks.resetMap, rhGS, rhGSm, rhGSi, hGL1, hGL1m, hGF1, hGF1m]⟩

end

end ReactUpdateFunction
