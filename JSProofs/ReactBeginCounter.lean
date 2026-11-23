import JSProofs.ReactUpdateFunction
import JSProofs.ReactRootBailout
import JSProofs.BWGen
import JSProofs.BWSwitch

/-!
# `beginWork` for the counter fiber in the click's render (zippy docs/react-proofs.md)

`beginWork(current, workInProgress, 2)` for the counter's function-component fiber: its props unchanged (the root's
bailout cloned it), an update scheduled in lane 2 (`checkScheduledUpdateOrContext`), so no early bailout;
`didReceiveUpdate` from the current fiber's flags, the work in progress's lanes cleared, then (tag 0)
`updateFunctionComponent` (`ReactUpdateFunction.click_spec`).
-/

open ES ES.M HostRuns Logic ReactReducer ReactUpdateReducer ReactUseState ReactCounter ReactRenderHooks
  ReactUpdateFunction
open Std (HashMap)

namespace ReactBeginCounter

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ}

theorem wp_gen_state {n : Nat} {h : σ} {α : Type} {x : M α} {s : State} {Q : α → State → σ → Prop}
    (hw : ∀ St, St = s → WP eng answer n h x St Q) : WP eng answer n h x s Q := hw s rfl

/-- What it writes: updateFunctionComponent's (whose footprint has the fiber's lanes) and `didReceiveUpdate`. -/
def fpB (g : EnvId) (C1 H0 Q RSI X : ObjId) : Footprint := fpUF g C1 H0 Q RSI X

set_option linter.unusedVariables false in
set_option maxRecDepth 10000 in
/-- **`checkScheduledUpdateOrContext(current, 2)`** with an update in lane 2: `true`. -/
theorem check_lane {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t : Value} {s : State}
    {H : ObjId} {hl : F64} {lw le lc : Bool}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : 10 ≤ s.fuel)
    (hcode : d.code = CSUGen.checkScheduledUpdateOrContext_func) (hcls : d.isClassCtor = false)
    (hmode : d.thisMode = .strict)
    (hH : H < s.heap.size) (hHk : (s.objEntry H).kind.isPlain = true)
    (hHl : (s.objEntry H).props.get? (.str "lanes") = some (.data (.num hl) lw le lc))
    (hl0 : isStrictlyEqual (.num (F64.fin false 0 (-1074)))
      (.num (numberBinOp .bitAnd hl (F64.fin false 4503599627370496 (-51)))) = false) :
    WP eng answer n h (callImpl eng (.obj fo) t #[.obj H, .num (F64.fin false 4503599627370496 (-51))]) s
      fun v w h' => v = .bool true ∧ Frame {} s w ∧ s.fuel ≤ w.fuel + 10 ∧ h' = h ∧ w.realm = s.realm := by
  apply wp_callGen CSUGen.checkScheduledUpdateOrContext_eq (by decide) hlt hk (by omega) hcls hmode
    (by rw [hcode]; rfl) (by rw [hcode]; rfl) (ReactRootBailout.simpleC d hcode) (by rw [hcode]; rfl)
    (by rw [hcode]; rfl)
  have hpn : d.code.info.fdi.paramNames = #[JSStr.ofString "current", JSStr.ofString "renderLanes"] := by
    rw [hcode]; rfl
  have hv : d.code.info.fdi.varNames = #[] := by rw [hcode]; rfl
  have hl : FDI.lexDecls d = #[] := by
    simp [FDI.lexDecls, hcode, CSUGen.checkScheduledUpdateOrContext_func, Func.info]
  have ha : d.code.isAsync = false := by rw [hcode]; rfl
  clear hcode
  simp only [CSUGen.checkScheduledUpdateOrContext]
  js [hpn, hv, hl, ha, hH, hHk, hHl, hl0, FDI.fdiCtx, Sem.inner]
  all_goals (repeat' apply And.intro)
  all_goals first | rfl | omega | (simp only [js_simp]; omega) | frame_go' [*]

theorem simpleB (d : FuncData) (hc : d.code = BWGen.beginWork_func) : FDI.Simple d := by
  constructor <;> rw [hc] <;> try rfl
  simp [BWGen.beginWork_func, Func.params, Func.info]

set_option linter.unusedSimpArgs false in
set_option linter.unusedVariables false in
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
/-- **`beginWork(current, workInProgress, 2)`** for the counter fiber in the click's render. -/
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
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : 520 ≤ s.fuel)
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
    {fUF fP fCD : ObjId} {dUF dP dCD : FuncData} {fl1 : F64} {bdP bdRWb bdCD bdRCb bdHy bdF1 bdL1 bdLI : Binding}
    {dpw dpe dpc fw fe fc : Bool}
    -- (updateFunctionComponent and its callees, functions of react-dom's module)
    (hUF : fUF < s.heap.size) (hUFk : (s.objEntry fUF).kind = .func dUF)
    (hUFcode : dUF.code = UFCGen.updateFunctionComponent_func) (hUFcls : dUF.isClassCtor = false)
    (hUFmode : dUF.thisMode = .strict) (hUFenv : dUF.env = d.env) (hoG : oG = none)
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
    (hdUe : dU.env ≠ d.env)
    {fB fCS : ObjId} {dB dCS : FuncData} {tB : Value} {bdCS bdUFb : Binding} {Pp : ObjId} {f0 : F64}
    {mpw mpe mpc ppw ppe ppc c0lw c0le c0lc c0fw c0fe c0fc tgw tge tgc tyw tye tyc : Bool}
    -- (beginWork and checkScheduledUpdateOrContext, functions of react-dom's module)
    (hBW : fB < s.heap.size) (hBWk : (s.objEntry fB).kind = .func dB) (hBWcode : dB.code = BWGen.beginWork_func)
    (hBWcls : dB.isClassCtor = false) (hBWmode : dB.thisMode = .strict) (hBWenv : dB.env = d.env)
    (hGCS : bG[JSStr.ofString "checkScheduledUpdateOrContext"]? = some bdCS) (hGCSv : bdCS.value = some (.obj fCS))
    (hCS : fCS < s.heap.size) (hCSk : (s.objEntry fCS).kind = .func dCS)
    (hCScode : dCS.code = CSUGen.checkScheduledUpdateOrContext_func) (hCScls : dCS.isClassCtor = false)
    (hCSmode : dCS.thisMode = .strict)
    (hGUFb : bG[JSStr.ofString "updateFunctionComponent"]? = some bdUFb) (hGUFbv : bdUFb.value = some (.obj fUF))
    -- (the current counter fiber: its props are the work in progress's (cloned by the root's bailout), an update in
    -- lane 2, no forced re-render flag; the work in progress: a function component (tag 0) of the counter)
    (hPp : P = .obj Pp)
    (hC0mp : (s.objEntry C0).props.get? (.str "memoizedProps") = some (.data (.obj Pp) mpw mpe mpc))
    (hC1pp : (s.objEntry C1).props.get? (.str "pendingProps") = some (.data (.obj Pp) ppw ppe ppc))
    (hC0l : (s.objEntry C0).props.get? (.str "lanes") = some (.data two c0lw c0le c0lc))
    (hC0f : (s.objEntry C0).props.get? (.str "flags") = some (.data (.num f0) c0fw c0fe c0fc))
    (hf0 : numberBinOp .bitAnd f0 (F64.fin false 4503599627370496 (-35)) = F64.fin false 0 (-1074))
    (hC1tag : (s.objEntry C1).props.get? (.str "tag") = some (.data (.num (F64.fin false 0 (-1074))) tgw tge tgc))
    (hC1ty : (s.objEntry C1).props.get? (.str "type") = some (.data (.obj fK) tyw tye tyc))
    (dUFC1 : fUF ≠ C1) :
    WP eng answer (n + 8) h (callImpl eng (.obj fB) tB #[.obj C0, .obj C1, two]) s fun v w h' =>
      ∃ C : ObjId, v = .obj X ∧ Frame (fpB d.env C1 H0 Q RSI X) s w ∧ s.fuel ≤ w.fuel + 530 ∧ h' = h ∧ w.realm = s.realm ∧
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
      ∃ bm, Scope.declLike? (w.envEntry d.env) = some (bm, none) ∧
        (∃ bd, bm[JSStr.ofString "didReceiveUpdate"]? = some bd ∧ bd.mutable = true ∧ bd.value.isSome = true) ∧
        (∃ bd, bm[JSStr.ofString "thenableIndexCounter$1"]? = some bd ∧ bd.mutable = true ∧ bd.value.isSome = true) ∧
        ∃ bd, bm[JSStr.ofString "thenableState$1"]? = some bd ∧ bd.mutable = true ∧ bd.value.isSome = true := by
  apply wp_callGen BWGen.beginWork_eq (by decide) hBW hBWk (by omega) hBWcls hBWmode
    (by rw [hBWcode]; rfl) (by rw [hBWcode]; rfl) (simpleB dB hBWcode) (by rw [hBWcode]; rfl) (by rw [hBWcode]; rfl)
  have hpn : dB.code.info.fdi.paramNames = #[JSStr.ofString "current", JSStr.ofString "workInProgress",
      JSStr.ofString "renderLanes"] := by rw [hBWcode]; rfl
  have hv : dB.code.info.fdi.varNames = #[JSStr.ofString "props", JSStr.ofString "$$typeof", JSStr.ofString "prevState",
    JSStr.ofString "nextState"] := by rw [hBWcode]; rfl
  have hl : FDI.lexDecls dB = #[] := by simp [FDI.lexDecls, hBWcode, BWGen.beginWork_func, Func.info]
  have ha : dB.code.isAsync = false := by rw [hBWcode]; rfl
  have hne : s.envs.size ≠ d.env := Nat.ne_of_gt hG
  have hG1 : d.env < s.envs.size + 1 := Nat.lt_succ_of_lt hG
  subst hPp
  subst hoG
  clear hBWcode
  simp only [BWGen.beginWork]
  js [hpn, hv, hl, ha, hBWenv, hG, hG1, hne, Ne.symm hne, hGe, hC0, hC0k, hC0mp, hC1, hC1k, hC1pp, beq_self_eq_true, hGCS, hGCSv, hCS,
    hCSk, FDI.fdiCtx, Sem.inner]
  refine ⟨by js_norm [CallableC, hCS, hCSk], ?_⟩
  refine wp_mono (check_lane hCS hCSk (by js_norm; omega) hCScode hCScls hCSmode hC0 hC0k hC0l (by js_norm)) ?postC
  intro v1 w1 h1 ⟨hv1, hF1, hfu1, hh1, hr1⟩
  subst v1 h1
  have hw1K := envEntry_frame0 hF1 (e := s.envs.size) (by js_norm)
  have hw1G := envEntry_frame0 hF1 (e := d.env) (by js_norm [hG1])
  simp only [js_simp, ↓reduceIte, hne, Ne.symm hne] at hw1K hw1G
  have hw1o : ∀ o, o < s.heap.size → w1.objEntry o = s.objEntry o := fun o ho =>
    (objEntry_frame0 hF1 (by js_norm [ho])).trans rfl
  have hw1E : s.envs.size + 1 ≤ w1.envs.size := by have := hF1.envs_le; simp only [js_simp] at this; exact this
  have hw1z : s.heap.size ≤ w1.heap.size := by have := hF1.heap_le; simp only [js_simp] at this; exact this
  have hw1f : 509 ≤ w1.fuel := by simp only [js_simp] at hfu1; omega
  have hEw1' : s.envs.size < w1.envs.size := Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hw1E
  have hGw1' : d.env < w1.envs.size := Nat.lt_of_lt_of_le hG1 hw1E
  have hnw1 : w1.envs.size ≠ s.envs.size := Nat.ne_of_gt hEw1'
  have hnw1G : w1.envs.size ≠ d.env := Nat.ne_of_gt hGw1'
  have hz00 : isStrictlyEqual (.num (F64.fin false 0 (-1074))) (.num (F64.fin false 0 (-1074))) = true := by decide
  iterate 32 (first | js_go | js_norm [hpn, hv, hl, ha, hBWenv, hw1K, hw1G, hGe, hne, Ne.symm hne, Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hw1E, Nat.lt_of_lt_of_le hG1 hw1E, hw1o, hC0, hC0k, hC1, hC0f, hf0, hz00, hEw1', hGw1', Nat.lt_succ_of_lt hEw1', Nat.lt_succ_of_lt hGw1', hnw1, hnw1G, Ne.symm hnw1, Ne.symm hnw1G, hC1, hC1k, hC1l, hC1tag, hC1ty, hC1pp, hGDR, hGDRm, hGDRi, hGUFb, hGUFbv, hUF, hUFk, Nat.lt_of_lt_of_le hC1 hw1z, Nat.lt_of_lt_of_le hUF hw1z, Nat.lt_of_lt_of_le hC0 hw1z, hw1f, FDI.fdiCtx, Sem.inner] | js_split)
  refine wp_switchC BWSwitch.lex ?_
  js [hpn, hv, hl, ha, hBWenv, hw1K, hw1G, hGe, hne, Ne.symm hne, Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hw1E, Nat.lt_of_lt_of_le hG1 hw1E, hw1o, hC0, hC0k, hC1, hC0f, hf0, hz00, hEw1', hGw1', Nat.lt_succ_of_lt hEw1', Nat.lt_succ_of_lt hGw1', hnw1, hnw1G, Ne.symm hnw1, Ne.symm hnw1G, hC1, hC1k, hC1l, hC1tag, hC1ty, hC1pp, hGDR, hGDRm, hGDRi, hGUFb, hGUFbv, hUF, hUFk, Nat.lt_of_lt_of_le hC1 hw1z, Nat.lt_of_lt_of_le hUF hw1z, Nat.lt_of_lt_of_le hC0 hw1z, hw1f, FDI.fdiCtx, Sem.inner]
  -- (`return updateFunctionComponent(current, workInProgress, workInProgress.type, workInProgress.pendingProps, 2)`)
  refine ⟨by js_norm [CallableC, hw1o, hUF, hUFk, Nat.lt_of_lt_of_le hUF hw1z, dUFC1, Ne.symm dUFC1], ?_⟩
  refine wp_gen_state fun St hSt => ?_
  have gSp : ∀ o k, o < s.heap.size → (o = C1 → k ≠ PropKey.str (JSStr.ofString "lanes")) →
      (St.objEntry o).props.get? k = (s.objEntry o).props.get? k := by
    intro o k ho hk
    rw [hSt]; js_norm [Nat.lt_of_lt_of_le ho hw1z, Nat.lt_of_lt_of_le hC1 hw1z]
    by_cases hoc : C1 = o
    · subst hoc; simp [PropMap.get?_insert_ne _ _ _ _ (Ne.symm (hk rfl)), hw1o C1 hC1]
    · simp [hoc, hw1o o ho]
  have gSk : ∀ o, o < s.heap.size → (St.objEntry o).kind = (s.objEntry o).kind := by
    intro o ho
    rw [hSt]; js_norm [Nat.lt_of_lt_of_le ho hw1z, Nat.lt_of_lt_of_le hC1 hw1z]
    by_cases hoc : C1 = o
    · subst hoc; simp [hw1o C1 hC1]
    · simp [hoc, hw1o o ho]
  have gSpr : ∀ o, o < s.heap.size → (St.objEntry o).proto = (s.objEntry o).proto := by
    intro o ho
    rw [hSt]; js_norm [Nat.lt_of_lt_of_le ho hw1z, Nat.lt_of_lt_of_le hC1 hw1z]
    by_cases hoc : C1 = o
    · subst hoc; simp [hw1o C1 hC1]
    · simp [hoc, hw1o o ho]
  have gSC1l : (St.objEntry C1).props.get? (.str "lanes") = some (.data (.num (F64.fin false 0 (-1074))) true lw lc) := by
    rw [hSt]; js_norm [Nat.lt_of_lt_of_le hC1 hw1z]
  have gSz : s.heap.size ≤ St.heap.size := by rw [hSt]; simp only [js_simp]; exact hw1z
  have gSE : s.envs.size ≤ St.envs.size := by rw [hSt]; simp only [js_simp]; omega
  have gSe : ∀ e, e < s.envs.size → e ≠ d.env → St.envEntry e = s.envEntry e := by
    intro e he hne'
    rw [hSt]; js_norm [he, hne', Ne.symm hne', Nat.ne_of_lt he, Nat.ne_of_gt he, Nat.lt_of_lt_of_le he (Nat.le_of_lt hEw1'),
      Nat.ne_of_lt (Nat.lt_trans he hEw1'), Nat.ne_of_gt (Nat.lt_trans he hEw1')]
    rw [envEntry_frame0 hF1 (by js_norm [Nat.lt_succ_of_lt he])]; js_norm [Nat.ne_of_lt he, Nat.ne_of_gt he]
  have gSd : Scope.declLike? (St.envEntry d.env) = some (bG.modify (JSStr.ofString "didReceiveUpdate")
      (fun bd => { bd with value := some (.bool false) }), none) := by
    rw [hSt]; js_norm [hGw1', hnw1G, Ne.symm hnw1G, hw1G, hGe, hne, Ne.symm hne]
  have gSR : St.realms = s.realms := by rw [hSt]; show w1.realms = s.realms; rw [hF1.realms_eq]; rfl
  have gSF : 505 ≤ St.fuel := by rw [hSt]; simp only [js_simp]; omega
  have gF1 : Frame (fpB d.env C1 H0 Q RSI X) s w1 := frame_mono (frame_trans (frame_bodyState
    (frame_refl ({} : Footprint) s) fB dB tB #[.obj C0, .obj C1, two]) hF1) (by simp) (by simp) (fun _ => rfl)
  have gFSt : Frame (fpB d.env C1 H0 Q RSI X) s St := by
    rw [hSt, ← hw1G]
    refine frame_pushEnv (frame_mono (fp' := fpB d.env C1 H0 Q RSI X) (frame_setProp_prop (frame_mono (fp' := fpB d.env C1 H0 Q RSI X) (frame_setEnv_bind gF1 hG (by rw [hw1G]; exact hGe)
      _ _) ?_ ?_ ?_) hC1 _ _) ?_ ?_ ?_) _
    · intro p hp; simp only [List.mem_cons] at hp; rcases hp with rfl | hp
      · simp [fpB, fpUF]
      · exact hp
    · intro p hp; exact hp
    · intro h; exact h
    · intro p hp; exact hp
    · intro p hp; simp only [List.mem_cons] at hp; rcases hp with rfl | hp
      · simp [fpB, fpUF]
      · exact hp
    · intro h; exact h
  have gSFe : St.fuel = w1.fuel := by rw [hSt]; simp only [js_simp]
  have gStK : St.envEntry s.envs.size = w1.envEntry s.envs.size := by
    rw [hSt]; js_norm [hEw1', hnw1, Ne.symm hnw1, hne, Ne.symm hne]
  clear hSt
  refine wp_mono (ReactUpdateFunction.click_spec (bG := bG.modify (JSStr.ofString "didReceiveUpdate")
      (fun bd => { bd with value := some (.bool false) })) (oG := none) (bdDR := { bdDR with value := some (.bool false) })
      (ln := .num (F64.fin false 0 (-1074))) (tUF := .undefined) (ec := false) (ee := false) (ew := false) (fw := false)
      (kc := false) (ke := false) (kw := false) (le := false) (r_pc := false) (r_pe := false) (r_pw := false) (rw := false)
      (tRW := .undefined) (ue := false) (yc := false) (ye := false) (yw := false) (uw := uw) (uc := uc)
      (hS := (Nat.lt_of_lt_of_le hS gSz)) (hSk := (by rw [gSk fS hS]; exact hSk)) (hScode := hScode)
      (hScls := hScls) (hSmode := hSmode) (hSG := (Nat.lt_of_lt_of_le hSG gSE))
      (hSGe := (by rw [gSe _ hSG hSd]; exact hSGe)) (hRSI := hRSI) (hRSIv := hRSIv)
      (hI := (Nat.lt_of_lt_of_le hI gSz)) (hIk := (by rw [gSk RSI hI]; exact hIk))
      (hIH := (by rw [gSp RSI _ hI (fun h => by first | decide | exact absurd h (by assumption) | exact absurd h (Ne.symm (by assumption)) | exact absurd h ((hdW _ (by simp)).1))]; exact hIH))
      (hHD := (Nat.lt_of_lt_of_le hHD gSz)) (hHDk := (by rw [gSk HD hHD]; exact hHDk))
      (hHDu := (by rw [gSp HD _ hHD (fun h => by first | decide | exact absurd h (by assumption) | exact absurd h (Ne.symm (by assumption)) | exact absurd h ((hdW _ (by simp)).1))]; exact hHDu))
      (hD := (Nat.lt_of_lt_of_le hD gSz)) (hDk := (by rw [gSk fD hD]; exact hDk)) (hDcode := hDcode)
      (hDcls := hDcls) (hDmode := hDmode) (hDenv := hDenv) (hGU := (by js_norm [hGU])) (hGUv := hGUv)
      (hGB := (by js_norm [hGB])) (hGBv := hGBv) (hlt := (Nat.lt_of_lt_of_le hlt gSz))
      (hk := (by rw [gSk fo hlt]; exact hk)) (hf := (Nat.le_trans (by decide) gSF)) (hcode := hcode) (hcls := hcls)
      (hmode := hmode) (hG := (Nat.lt_of_lt_of_le hG gSE)) (hGe := gSd) (hGC := (by js_norm [hGC])) (hGCm := hGCm)
      (hGCv := hGCv) (hGW := (by js_norm [hGW])) (hGWm := hGWm) (hGWv := hGWv) (hGF := (by js_norm [hGF]))
      (hGFm := hGFm) (hGFi := hGFi) (hGUW := (by js_norm [hGUW])) (hGUWv := hGUWv)
      (hW := (Nat.lt_of_lt_of_le hW gSz)) (hWk := (by rw [gSk fW hW]; exact hWk)) (hWcode := hWcode)
      (hWcls := hWcls) (hWmode := hWmode) (hWenv := hWenv) (hGUR := (by js_norm [hGUR])) (hGURv := hGURv)
      (hR := (Nat.lt_of_lt_of_le hR gSz)) (hRk := (by rw [gSk fR hR]; exact hRk)) (hRcode := hRcode)
      (hRcls := hRcls) (hRmode := hRmode) (hRenv := hRenv) (hGRL := (by js_norm [hGRL])) (hGRLm := hGRLm)
      (hGRLi := hGRLi) (hGCE := (by js_norm [hGCE])) (hGCEv := hGCEv) (hGSD := (by js_norm [hGSD])) (hGSDm := hGSDm)
      (hGSDi := hGSDi) (hGDR := (by js_norm [hGDR])) (hGDRm := hGDRm) (hGDRi := rfl) (hGIs := (by js_norm [hGIs]))
      (hGIsv := hGIsv) (hIs := (Nat.lt_of_lt_of_le hIs gSz)) (hIsk := (by rw [gSk fIs hIs]; exact hIsk))
      (hIstab := hIstab) (hC1 := (Nat.lt_of_lt_of_le hC1 gSz)) (hC1k := (by rw [gSk C1 hC1]; exact hC1k))
      (hC1a := (by rw [gSp C1 _ hC1 (fun h => by first | decide | exact absurd h (by assumption) | exact absurd h (Ne.symm (by assumption)) | exact absurd h ((hdW _ (by simp)).1))]; exact hC1a))
      (hC1m := (by rw [gSp C1 _ hC1 (fun h => by first | decide | exact absurd h (by assumption) | exact absurd h (Ne.symm (by assumption)) | exact absurd h ((hdW _ (by simp)).1))]; exact hC1m))
      (hC0 := (Nat.lt_of_lt_of_le hC0 gSz)) (hC0k := (by rw [gSk C0 hC0]; exact hC0k))
      (hC0m := (by rw [gSp C0 _ hC0 (fun h => by first | decide | exact absurd h (by assumption) | exact absurd h (Ne.symm (by assumption)) | exact absurd h ((hdW _ (by simp)).1))]; exact hC0m))
      (hH0 := (Nat.lt_of_lt_of_le hH0 gSz)) (hH0k := (by rw [gSk H0 hH0]; exact hH0k))
      (hHm := (by rw [gSp H0 _ hH0 (fun h => by first | decide | exact absurd h (by assumption) | exact absurd h (Ne.symm (by assumption)) | exact absurd h ((hdW _ (by simp)).1))]; exact hHm))
      (hHb := (by rw [gSp H0 _ hH0 (fun h => by first | decide | exact absurd h (by assumption) | exact absurd h (Ne.symm (by assumption)) | exact absurd h ((hdW _ (by simp)).1))]; exact hHb))
      (hHbq := (by rw [gSp H0 _ hH0 (fun h => by first | decide | exact absurd h (by assumption) | exact absurd h (Ne.symm (by assumption)) | exact absurd h ((hdW _ (by simp)).1))]; exact hHbq))
      (hHq := (by rw [gSp H0 _ hH0 (fun h => by first | decide | exact absurd h (by assumption) | exact absurd h (Ne.symm (by assumption)) | exact absurd h ((hdW _ (by simp)).1))]; exact hHq))
      (hQ := (Nat.lt_of_lt_of_le hQ gSz)) (hQk := (by rw [gSk Q hQ]; exact hQk))
      (hQp := (by rw [gSp Q _ hQ (fun h => by first | decide | exact absurd h (by assumption) | exact absurd h (Ne.symm (by assumption)) | exact absurd h ((hdW _ (by simp)).1))]; exact hQp))
      (hQr := (by rw [gSp Q _ hQ (fun h => by first | decide | exact absurd h (by assumption) | exact absurd h (Ne.symm (by assumption)) | exact absurd h ((hdW _ (by simp)).1))]; exact hQr))
      (hQl := (by rw [gSp Q _ hQ (fun h => by first | decide | exact absurd h (by assumption) | exact absurd h (Ne.symm (by assumption)) | exact absurd h ((hdW _ (by simp)).1))]; exact hQl))
      (hQd := (by rw [gSp Q _ hQ (fun h => by first | decide | exact absurd h (by assumption) | exact absurd h (Ne.symm (by assumption)) | exact absurd h ((hdW _ (by simp)).1))]; exact hQd))
      (hU := (Nat.lt_of_lt_of_le hU gSz)) (hUk := (by rw [gSk U hU]; exact hUk))
      (hUl := (by rw [gSp U _ hU (fun h => by first | decide | exact absurd h (by assumption) | exact absurd h (Ne.symm (by assumption)) | exact absurd h ((hdW _ (by simp)).1))]; exact hUl))
      (hUr := (by rw [gSp U _ hU (fun h => by first | decide | exact absurd h (by assumption) | exact absurd h (Ne.symm (by assumption)) | exact absurd h ((hdW _ (by simp)).1))]; exact hUr))
      (hUa := (by rw [gSp U _ hU (fun h => by first | decide | exact absurd h (by assumption) | exact absurd h (Ne.symm (by assumption)) | exact absurd h ((hdW _ (by simp)).1))]; exact hUa))
      (hUe := (by rw [gSp U _ hU (fun h => by first | decide | exact absurd h (by assumption) | exact absurd h (Ne.symm (by assumption)) | exact absurd h ((hdW _ (by simp)).1))]; exact hUe))
      (hUv := (by rw [gSp U _ hU (fun h => by first | decide | exact absurd h (by assumption) | exact absurd h (Ne.symm (by assumption)) | exact absurd h ((hdW _ (by simp)).1))]; exact hUv))
      (hUn := (by rw [gSp U _ hU (fun h => by first | decide | exact absurd h (by assumption) | exact absurd h (Ne.symm (by assumption)) | exact absurd h ((hdW _ (by simp)).1))]; exact hUn))
      (hdiff := hdiff) (d1 := d1) (d2 := d2) (d3 := d3) (d4 := d4) (d5 := d5) (d6 := d6) (d7 := d7) (d8 := d8)
      (d9 := d9) (d10 := d10) (d11 := d11) (d12 := d12) (hK := (Nat.lt_of_lt_of_le hK gSz))
      (hKk := (by rw [gSk fK hK]; exact hKk)) (hKcode := hKcode) (hKcls := hKcls) (hKmode := hKmode)
      (hAG := (Nat.lt_of_lt_of_le hAG gSE)) (hAGe := (by rw [gSe _ hAG hKd]; exact hAGe)) (hAR := hAR)
      (hARv := hARv) (hIR := (Nat.lt_of_lt_of_le hIR gSz)) (hIRk := (by rw [gSk IR hIR]; exact hIRk))
      (hIRu := (by rw [gSp IR _ hIR (fun h => by first | decide | exact absurd h (by assumption) | exact absurd h (Ne.symm (by assumption)) | exact absurd h ((hdW _ (by simp)).1))]; exact hIRu))
      (hAJ := hAJ) (hAJv := hAJv) (hIJ := (Nat.lt_of_lt_of_le hIJ gSz)) (hIJk := (by rw [gSk IJ hIJ]; exact hIJk))
      (hIJj := (by rw [gSp IJ _ hIJ (fun h => by first | decide | exact absurd h (by assumption) | exact absurd h (Ne.symm (by assumption)) | exact absurd h ((hdW _ (by simp)).1))]; exact hIJj))
      (hJ := (Nat.lt_of_lt_of_le hJ gSz)) (hJk := (by rw [gSk fJ hJ]; exact hJk)) (hJcode := hJcode)
      (hJcls := hJcls) (hJmode := hJmode) (hJG := (Nat.lt_of_lt_of_le hJG gSE))
      (hJGe := (by rw [gSe _ hJG hJd]; exact hJGe)) (hJT := hJT) (hJTv := hJTv) (hAP := (by rw [gSR]; exact hAP))
      (hP := (Nat.lt_of_lt_of_le hP gSz)) (hPk := (by rw [gSk AP hP]; exact hPk))
      (hPv := (by rw [gSp AP _ hP (fun h => by first | decide | exact absurd h (by assumption) | exact absurd h (Ne.symm (by assumption)) | exact absurd h ((hdW _ (by simp)).1))]; exact hPv))
      (hV := (Nat.lt_of_lt_of_le hV gSz)) (hVk := (by rw [gSk fV hV]; exact hVk)) (hVfn := hVfn) (hVr := hVr)
      (hII := (by rw [gSR]; exact hII)) (hAIP := (Nat.lt_of_lt_of_le hAIP gSz))
      (hAIPk := (by rw [gSk AIP hAIP]; exact hAIPk))
      (hAIPn := (by rw [gSp AIP _ hAIP (fun h => by first | decide | exact absurd h (by assumption) | exact absurd h (Ne.symm (by assumption)) | exact absurd h ((hdW _ (by simp)).1))]; exact hAIPn))
      (hN := (Nat.lt_of_lt_of_le hN gSz)) (hNk := (by rw [gSk fN hN]; exact hNk)) (hNfn := hNfn) (hNr := hNr)
      (hAIPp := (by rw [gSpr AIP hAIP]; exact hAIPp))
      (hAIPr := (by rw [gSp AIP _ hAIP (fun h => by first | decide | exact absurd h (by assumption) | exact absurd h (Ne.symm (by assumption)) | exact absurd h ((hdW _ (by simp)).1))]; exact hAIPr))
      (hIP := (Nat.lt_of_lt_of_le hIP gSz)) (hIPk := (by rw [gSk IP hIP]; exact hIPk))
      (hIPr := (by rw [gSp IP _ hIP (fun h => by first | decide | exact absurd h (by assumption) | exact absurd h (Ne.symm (by assumption)) | exact absurd h ((hdW _ (by simp)).1))]; exact hIPr))
      (hIPp := (by rw [gSpr IP hIP]; exact hIPp)) (hOPe := (by rw [gSR]; exact hOPe))
      (hOP := (Nat.lt_of_lt_of_le hOP gSz)) (hOPk := (by rw [gSk OP hOP]; exact hOPk))
      (hOPr := (by rw [gSp OP _ hOP (fun h => by first | decide | exact absurd h (by assumption) | exact absurd h (Ne.symm (by assumption)) | exact absurd h ((hdW _ (by simp)).1))]; exact hOPr))
      (hOPp := (by rw [gSpr OP hOP]; exact hOPp))
      (hOPkey := (by rw [gSp OP _ hOP (fun h => by first | decide | exact absurd h (by assumption) | exact absurd h (Ne.symm (by assumption)) | exact absurd h ((hdW _ (by simp)).1))]; exact hOPkey))
      (hOPref := (by rw [gSp OP _ hOP (fun h => by first | decide | exact absurd h (by assumption) | exact absurd h (Ne.symm (by assumption)) | exact absurd h ((hdW _ (by simp)).1))]; exact hOPref))
      (hFP := (by rw [gSR]; exact hFP)) (hvE := hvE) (dAP := dAP) (dfV := dfV) (dAIP := dAIP) (dfN := dfN)
      (dIP := dIP) (dOP := dOP) (dIJ := dIJ) (dfJ := dfJ) (hKd := hKd) (hJd := hJd) (hGHU := (by js_norm [hGHU]))
      (hGHUv := hGHUv) (hGRSd := (by js_norm [hGRSd])) (hGRSdv := hGRSdv) (hGDP := (by js_norm [hGDP]))
      (hGDPv := hGDPv) (hGFR := (by js_norm [hGFR])) (hGFRv := hGFRv) (hFF := (Nat.lt_of_lt_of_le hFF gSz))
      (hFFk := (by rw [gSk fF hFF]; exact hFFk)) (hFFcode := hFFcode) (hFFcls := hFFcls) (hFFmode := hFFmode)
      (hFFenv := hFFenv) (hGCO := (by js_norm [hGCO])) (hGCOv := hGCOv) (hGDS := (by js_norm [hGDS]))
      (hGDSm := hGDSm) (hGDSi := hGDSi) (hGTI := (by js_norm [hGTI])) (hGTIm := hGTIm) (hGTIi := hGTIi)
      (hGTS := (by js_norm [hGTS])) (hGTSm := hGTSm) (hGTSi := hGTSi)
      (hC1u := (by rw [gSp C1 _ hC1 (fun h => by first | decide | exact absurd h (by assumption) | exact absurd h (Ne.symm (by assumption)) | exact absurd h ((hdW _ (by simp)).1))]; exact hC1u))
      (hC1l := gSC1l)
      (hH0n := (by rw [gSp H0 _ hH0 (fun h => by first | decide | exact absurd h (by assumption) | exact absurd h (Ne.symm (by assumption)) | exact absurd h ((hdW _ (by simp)).1))]; exact hH0n))
      (hdist := hdist) (dRC := dRC) (hSd := hSd) (hRW := (Nat.lt_of_lt_of_le hRW gSz))
      (hRWk := (by rw [gSk fRW hRW]; exact hRWk)) (hRWcode := hRWcode) (hRWcls := hRWcls) (hRWmode := hRWmode)
      (hRWenv := hRWenv) (dFH := dFH) (dRQ := dRQ) (rhU := (Nat.lt_of_lt_of_le rhU gSz))
      (rhUk := (by rw [gSk fU rhU]; exact rhUk)) (rhUcode := rhUcode) (rhUcls := rhUcls) (rhUmode := rhUmode)
      (rhE := (Nat.lt_of_lt_of_le rhE gSE)) (rhEe := (by rw [gSe _ rhE hdUe]; exact rhEe)) (rhEn := rhEn)
      (rhGC := (by js_norm [rhGC])) (rhGCv := rhGCv) (rhlt := (Nat.lt_of_lt_of_le rhlt gSz))
      (rhk := (by rw [gSk r_fo rhlt]; exact rhk)) (rhf := (Nat.le_trans (by decide) gSF)) (rhcode := rhcode)
      (rhcls := rhcls) (rhmode := rhmode) (rhH := (Nat.lt_of_lt_of_le rhH gSz))
      (rhHk := (by rw [gSk H rhH]; exact rhHk)) (rhX := (Nat.lt_of_lt_of_le rhX gSz))
      (rhXk := (by rw [gSk X rhX]; exact rhXk)) (rhHX := rhHX)
      (rhHa := (by rw [gSp H _ rhH (fun h => by first | decide | exact absurd h (by assumption) | exact absurd h (Ne.symm (by assumption)) | exact absurd h ((hdW _ (by simp)).1))]; exact rhHa))
      (rhHf := (by rw [gSp H _ rhH (fun h => by first | decide | exact absurd h (by assumption) | exact absurd h (Ne.symm (by assumption)) | exact absurd h ((hdW _ (by simp)).1))]; exact rhHf))
      (rhHd := (by rw [gSp H _ rhH (fun h => by first | decide | exact absurd h (by assumption) | exact absurd h (Ne.symm (by assumption)) | exact absurd h ((hdW _ (by simp)).1))]; exact rhHd))
      (rhH_type := (by rw [gSp H _ rhH (fun h => by first | decide | exact absurd h (by assumption) | exact absurd h (Ne.symm (by assumption)) | exact absurd h ((hdW _ (by simp)).1))]; exact rhH_type))
      (rhH_childLanes := (by rw [gSp H _ rhH (fun h => by first | decide | exact absurd h (by assumption) | exact absurd h (Ne.symm (by assumption)) | exact absurd h ((hdW _ (by simp)).1))]; exact rhH_childLanes))
      (rhH_lanes := (by rw [gSp H _ rhH (fun h => by first | decide | exact absurd h (by assumption) | exact absurd h (Ne.symm (by assumption)) | exact absurd h ((hdW _ (by simp)).1))]; exact rhH_lanes))
      (rhH_child := (by rw [gSp H _ rhH (fun h => by first | decide | exact absurd h (by assumption) | exact absurd h (Ne.symm (by assumption)) | exact absurd h ((hdW _ (by simp)).1))]; exact rhH_child))
      (rhH_memoizedProps := (by rw [gSp H _ rhH (fun h => by first | decide | exact absurd h (by assumption) | exact absurd h (Ne.symm (by assumption)) | exact absurd h ((hdW _ (by simp)).1))]; exact rhH_memoizedProps))
      (rhH_memoizedState := (by rw [gSp H _ rhH (fun h => by first | decide | exact absurd h (by assumption) | exact absurd h (Ne.symm (by assumption)) | exact absurd h ((hdW _ (by simp)).1))]; exact rhH_memoizedState))
      (rhH_updateQueue := (by rw [gSp H _ rhH (fun h => by first | decide | exact absurd h (by assumption) | exact absurd h (Ne.symm (by assumption)) | exact absurd h ((hdW _ (by simp)).1))]; exact rhH_updateQueue))
      (rhH_sibling := (by rw [gSp H _ rhH (fun h => by first | decide | exact absurd h (by assumption) | exact absurd h (Ne.symm (by assumption)) | exact absurd h ((hdW _ (by simp)).1))]; exact rhH_sibling))
      (rhH_index := (by rw [gSp H _ rhH (fun h => by first | decide | exact absurd h (by assumption) | exact absurd h (Ne.symm (by assumption)) | exact absurd h ((hdW _ (by simp)).1))]; exact rhH_index))
      (rhH_ref := (by rw [gSp H _ rhH (fun h => by first | decide | exact absurd h (by assumption) | exact absurd h (Ne.symm (by assumption)) | exact absurd h ((hdW _ (by simp)).1))]; exact rhH_ref))
      (rhH_refCleanup := (by rw [gSp H _ rhH (fun h => by first | decide | exact absurd h (by assumption) | exact absurd h (Ne.symm (by assumption)) | exact absurd h ((hdW _ (by simp)).1))]; exact rhH_refCleanup))
      (rhX_pendingProps := (by rw [gSp X _ rhX (fun h => by first | decide | exact absurd h (by assumption) | exact absurd h (Ne.symm (by assumption)) | exact absurd h ((hdW _ (by simp)).1))]; exact rhX_pendingProps))
      (rhX_type := (by rw [gSp X _ rhX (fun h => by first | decide | exact absurd h (by assumption) | exact absurd h (Ne.symm (by assumption)) | exact absurd h ((hdW _ (by simp)).1))]; exact rhX_type))
      (rhX_flags := (by rw [gSp X _ rhX (fun h => by first | decide | exact absurd h (by assumption) | exact absurd h (Ne.symm (by assumption)) | exact absurd h ((hdW _ (by simp)).1))]; exact rhX_flags))
      (rhX_subtreeFlags := (by rw [gSp X _ rhX (fun h => by first | decide | exact absurd h (by assumption) | exact absurd h (Ne.symm (by assumption)) | exact absurd h ((hdW _ (by simp)).1))]; exact rhX_subtreeFlags))
      (rhX_deletions := (by rw [gSp X _ rhX (fun h => by first | decide | exact absurd h (by assumption) | exact absurd h (Ne.symm (by assumption)) | exact absurd h ((hdW _ (by simp)).1))]; exact rhX_deletions))
      (rhX_childLanes := (by rw [gSp X _ rhX (fun h => by first | decide | exact absurd h (by assumption) | exact absurd h (Ne.symm (by assumption)) | exact absurd h ((hdW _ (by simp)).1))]; exact rhX_childLanes))
      (rhX_lanes := (by rw [gSp X _ rhX (fun h => by first | decide | exact absurd h (by assumption) | exact absurd h (Ne.symm (by assumption)) | exact absurd h ((hdW _ (by simp)).1))]; exact rhX_lanes))
      (rhX_child := (by rw [gSp X _ rhX (fun h => by first | decide | exact absurd h (by assumption) | exact absurd h (Ne.symm (by assumption)) | exact absurd h ((hdW _ (by simp)).1))]; exact rhX_child))
      (rhX_memoizedProps := (by rw [gSp X _ rhX (fun h => by first | decide | exact absurd h (by assumption) | exact absurd h (Ne.symm (by assumption)) | exact absurd h ((hdW _ (by simp)).1))]; exact rhX_memoizedProps))
      (rhX_memoizedState := (by rw [gSp X _ rhX (fun h => by first | decide | exact absurd h (by assumption) | exact absurd h (Ne.symm (by assumption)) | exact absurd h ((hdW _ (by simp)).1))]; exact rhX_memoizedState))
      (rhX_updateQueue := (by rw [gSp X _ rhX (fun h => by first | decide | exact absurd h (by assumption) | exact absurd h (Ne.symm (by assumption)) | exact absurd h ((hdW _ (by simp)).1))]; exact rhX_updateQueue))
      (rhX_dependencies := (by rw [gSp X _ rhX (fun h => by first | decide | exact absurd h (by assumption) | exact absurd h (Ne.symm (by assumption)) | exact absurd h ((hdW _ (by simp)).1))]; exact rhX_dependencies))
      (rhX_sibling := (by rw [gSp X _ rhX (fun h => by first | decide | exact absurd h (by assumption) | exact absurd h (Ne.symm (by assumption)) | exact absurd h ((hdW _ (by simp)).1))]; exact rhX_sibling))
      (rhX_index := (by rw [gSp X _ rhX (fun h => by first | decide | exact absurd h (by assumption) | exact absurd h (Ne.symm (by assumption)) | exact absurd h ((hdW _ (by simp)).1))]; exact rhX_index))
      (rhX_ref := (by rw [gSp X _ rhX (fun h => by first | decide | exact absurd h (by assumption) | exact absurd h (Ne.symm (by assumption)) | exact absurd h ((hdW _ (by simp)).1))]; exact rhX_ref))
      (rhX_refCleanup := (by rw [gSp X _ rhX (fun h => by first | decide | exact absurd h (by assumption) | exact absurd h (Ne.symm (by assumption)) | exact absurd h ((hdW _ (by simp)).1))]; exact rhX_refCleanup))
      (rhI := (Nat.lt_of_lt_of_le rhI gSz)) (rhIk := (by rw [gSk fI rhI]; exact rhIk)) (rhIcode := rhIcode)
      (rhIcls := rhIcls) (rhImode := rhImode) (rhIenv := rhIenv) (rhRDel := rhRDel) (rhRDelv := rhRDelv)
      (rhDel := (Nat.lt_of_lt_of_le rhDel gSz)) (rhDelk := (by rw [gSk fDel rhDel]; exact rhDelk))
      (rhDelcode := rhDelcode) (rhDelcls := rhDelcls) (rhDelmode := rhDelmode) (rhDelenv := rhDelenv)
      (rhRUF := rhRUF) (rhRUFv := rhRUFv) (rhRPl := rhRPl) (rhRPlv := rhRPlv)
      (rhPl := (Nat.lt_of_lt_of_le rhPl gSz)) (rhPlk := (by rw [gSk fPl rhPl]; exact rhPlk)) (rhPlcode := rhPlcode)
      (rhPlcls := rhPlcls) (rhPlmode := rhPlmode) (rhPlenv := rhPlenv) (rhRST := rhRST) (rhRSTv := rhRSTv)
      (rhRnF := rhRnF) (rhRnE := rhRnE) (rhRnC := rhRnC) (rhGFr := (by js_norm [rhGFr])) (rhGFrv := rhGFrv)
      (rhGEl := (by js_norm [rhGEl])) (rhGElv := rhGElv) (rhFrs := rhFrs) (rhEls := rhEls) (rhFrEl := rhFrEl)
      (rhGCR := (by js_norm [rhGCR])) (rhGCRv := rhGCRv) (rhCR := (Nat.lt_of_lt_of_le rhCR gSz))
      (rhCRk := (by rw [gSk fCR rhCR]; exact rhCRk)) (rhCRcode := rhCRcode) (rhCRcls := rhCRcls)
      (rhCRmode := rhCRmode)
      (rhHkey := (by rw [gSp H _ rhH (fun h => by first | decide | exact absurd h (by assumption) | exact absurd h (Ne.symm (by assumption)) | exact absurd h ((hdW _ (by simp)).1))]; exact rhHkey))
      (rhHet := (by rw [gSp H _ rhH (fun h => by first | decide | exact absurd h (by assumption) | exact absurd h (Ne.symm (by assumption)) | exact absurd h ((hdW _ (by simp)).1))]; exact rhHet))
      (rhXa := (by rw [gSp X _ rhX (fun h => by first | decide | exact absurd h (by assumption) | exact absurd h (Ne.symm (by assumption)) | exact absurd h ((hdW _ (by simp)).1))]; exact rhXa))
      (rhXret := (by rw [gSp X _ rhX (fun h => by first | decide | exact absurd h (by assumption) | exact absurd h (Ne.symm (by assumption)) | exact absurd h ((hdW _ (by simp)).1))]; exact rhXret))
      (rhdX := rhdX) (rhR := (Nat.lt_of_lt_of_le rhR gSz)) (rhRk := (by rw [gSk r_fR rhR]; exact rhRk))
      (rhRcode := rhRcode) (rhRcls := rhRcls) (rhRmode := rhRmode) (rhRenv := rhRenv) (rhRRI := rhRRI)
      (rhRRIv := rhRRIv) (rhRnT := rhRnT) (rhRnS := rhRnS) (rhGT := (by js_norm [rhGT])) (rhGTm := rhGTm)
      (rhGTi := rhGTi) (rhGS := (by js_norm [rhGS])) (rhGSm := rhGSm) (rhGSi := rhGSi) (rhgU := rhgU)
      (rhRC := (Nat.lt_of_lt_of_le rhRC gSz)) (rhRCk := (by rw [gSk fC rhRC]; exact rhRCk)) (rhRCcode := rhRCcode)
      (rhRCcls := rhRCcls) (rhRCmode := rhRCmode) (rhRCenv := rhRCenv) (rhGRCF := (by js_norm [rhGRCF]))
      (rhGRCFv := rhGRCFv)
      (rhC0c := (by rw [gSp C0 _ hC0 (fun h => by first | decide | exact absurd h (by assumption) | exact absurd h (Ne.symm (by assumption)) | exact absurd h ((hdW _ (by simp)).1))]; exact rhC0c))
      (rhRFc := (by rw [gSp C1 _ hC1 (fun h => by first | decide | exact absurd h (by assumption) | exact absurd h (Ne.symm (by assumption)) | exact absurd h ((hdW _ (by simp)).1))]; exact rhRFc))
      (rhRFX := rhRFX) (hUF := (Nat.lt_of_lt_of_le hUF gSz)) (hUFk := (by rw [gSk fUF hUF]; exact hUFk))
      (hUFcode := hUFcode) (hUFcls := hUFcls) (hUFmode := hUFmode) (hUFenv := hUFenv) (hoG := rfl)
      (hGP := (by js_norm [hGP])) (hGPv := hGPv) (hPR := (Nat.lt_of_lt_of_le hPR gSz))
      (hPRk := (by rw [gSk fP hPR]; exact hPRk)) (hPRcode := hPRcode) (hPRcls := hPRcls) (hPRmode := hPRmode)
      (hPRenv := hPRenv) (hGRWb := (by js_norm [hGRWb])) (hGRWbv := hGRWbv) (hGCD := (by js_norm [hGCD]))
      (hGCDv := hGCDv) (hCD := (Nat.lt_of_lt_of_le hCD gSz)) (hCDk := (by rw [gSk fCD hCD]; exact hCDk))
      (hCDcode := hCDcode) (hCDcls := hCDcls) (hCDmode := hCDmode) (hCDenv := hCDenv)
      (hGRCb := (by js_norm [hGRCb])) (hGRCbv := hGRCbv) (hGHy := (by js_norm [hGHy])) (hGHyv := hGHyv)
      (hGF1 := (by js_norm [hGF1])) (hGF1m := hGF1m) (hGF1i := hGF1i) (hGL1 := (by js_norm [hGL1])) (hGL1m := hGL1m)
      (hGL1i := hGL1i) (hGLI := (by js_norm [hGLI])) (hGLIm := hGLIm) (hGLIv := hGLIv)
      (hC1d := (by rw [gSp C1 _ hC1 (fun h => by first | decide | exact absurd h (by assumption) | exact absurd h (Ne.symm (by assumption)) | exact absurd h ((hdW _ (by simp)).1))]; exact hC1d))
      (hC1f := (by rw [gSp C1 _ hC1 (fun h => by first | decide | exact absurd h (by assumption) | exact absurd h (Ne.symm (by assumption)) | exact absurd h ((hdW _ (by simp)).1))]; exact hC1f))
      (hdW := hdW) (hdUe := hdUe)) ?postU
  intro v2 w2 h2 ⟨C, hv2, hF2, hfu2, hh2, hr2, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, xret,
    hch, hCch, hC1l2, hC1f2, hCk2, hCb2, hCge2, hNP2, hB2⟩
  subst v2 h2
  have FW := frame_extend' gFSt hF2 (fun q hq _ => hq) (fun q hq _ => hq) (fun _ => rfl)
  have hfw : s.fuel ≤ w2.fuel + 530 := by simp only [js_simp] at hfu1; omega
  exact ⟨C, rfl, frame_restore FW s, hfw, rfl, rfl, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15,
    xret, hch, hCch, hC1l2, hC1f2, hCk2, hCb2, Nat.le_trans gSz hCge2, hNP2, hB2⟩

end

end ReactBeginCounter
