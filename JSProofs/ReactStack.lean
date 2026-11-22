import JSProofs.JsTactic
import JSProofs.PushGen
import JSProofs.PopGen

/-!
# React's value stack: `push` and `pop` (zippy docs/react-proofs.md)

`push(cursor, value)` saves `cursor.current` at `valueStack[++index]` and sets it; `pop(cursor)` restores it. In the
steady state the stack array keeps the slots earlier renders made (popping writes `null`, never shrinks), so both
write existing elements.
-/

open ES ES.M HostRuns Logic
open Std (HashMap)

namespace ReactStack

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ}

theorem simpleU (d : FuncData) (hc : d.code = PushGen.push_func) : FDI.Simple d := by
  constructor <;> rw [hc] <;> try rfl
  simp [PushGen.push_func, Func.params, Func.info]

set_option maxRecDepth 10000 in
theorem push_spec {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t value : Value} {s : State}
    {bG : HashMap JSStr Binding} {oG : Option EnvId} {bdI bdV : Binding} {VS Cu : ObjId} {iv nv L : F64}
    {cur old : Value} {ce cc oe oc lw le lc : Bool} {i : Nat}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : 10 ≤ s.fuel)
    (hcode : d.code = PushGen.push_func) (hcls : d.isClassCtor = false) (hmode : d.thisMode = .strict)
    (hG : d.env < s.envs.size) (hGe : Scope.declLike? (s.envEntry d.env) = some (bG, oG))
    (hGI : bG[JSStr.ofString "index"]? = some bdI) (hGIm : bdI.mutable = true) (hGIv : bdI.value = some (.num iv))
    (hGV : bG[JSStr.ofString "valueStack"]? = some bdV) (hGVv : bdV.value = some (.obj VS))
    (hVS : VS < s.heap.size) (hVSk : (s.objEntry VS).kind = .array) (hCu : Cu < s.heap.size)
    (hCuk : (s.objEntry Cu).kind.isPlain = true) (hVC : VS ≠ Cu)
    (hCc : (s.objEntry Cu).props.get? (.str "current") = some (.data cur true ce cc))
    (hnv : Conv.addF iv F64.one = nv)
    (hslot : (s.objEntry VS).props.get? (.str (numberToJSStr nv)) = some (.data old true oe oc))
    (hidx : (PropKey.str (numberToJSStr nv)).arrayIndex? = some i)
    (hlen : (s.objEntry VS).props.get? (.str "length") = some (.data (.num L) lw le lc))
    (hiL : i < (Conv.toNat? L).getD 0)
    (hnl : (PropKey.str (numberToJSStr nv) == PropKey.str (JSStr.ofString "length")) = false) :
    WP eng answer n h (callImpl eng (.obj fo) t #[.obj Cu, value]) s fun v w h' =>
      v = .undefined ∧ Frame ⟨[(d.env, "index")], [(VS, .str (numberToJSStr nv)), (Cu, .str "current")], false⟩ s w ∧
      s.fuel ≤ w.fuel + 10 ∧ h' = h ∧
      Scope.declLike? (w.envEntry d.env) =
        some (bG.modify (JSStr.ofString "index") (fun bd => { bd with value := some (.num nv) }), oG) ∧
      (w.objEntry VS).props.get? (.str (numberToJSStr nv)) = some (.data cur true oe oc) ∧
      (w.objEntry Cu).props.get? (.str "current") = some (.data value true ce cc) := by
  apply wp_callGen PushGen.push_eq (by decide) hlt hk (by omega) hcls hmode
    (by rw [hcode]; rfl) (by rw [hcode]; rfl) (simpleU d hcode) (by rw [hcode]; rfl) (by rw [hcode]; rfl)
  have hpn : d.code.info.fdi.paramNames = #[JSStr.ofString "cursor", JSStr.ofString "value"] := by rw [hcode]; rfl
  have hv : d.code.info.fdi.varNames = #[] := by rw [hcode]; rfl
  have hl : FDI.lexDecls d = #[] := by simp [FDI.lexDecls, hcode, PushGen.push_func, Func.info]
  have ha : d.code.isAsync = false := by rw [hcode]; rfl
  have hne : s.envs.size ≠ d.env := Nat.ne_of_gt hG
  have hG1 : d.env < s.envs.size + 1 := Nat.lt_succ_of_lt hG
  clear hcode
  simp only [PushGen.push]
  subst hnv
  js [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGI, hGIm, hGIv, hGV, hGVv, hVS, hVSk, hCu, hCuk, hVC,
    Ne.symm hVC, hCc, hslot, hidx, hlen, hiL, hnl, FDI.fdiCtx, Sem.inner]
  all_goals (repeat' apply And.intro)
  all_goals first | rfl | omega | (simp only [js_simp]; omega) | (refine ⟨_, rfl, _, by simp, rfl⟩) | frame_go' [*, hne, Ne.symm hne, hG1] | skip

set_option maxRecDepth 10000 in
theorem push_exact {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t value : Value} {s : State}
    {bG : HashMap JSStr Binding} {oG : Option EnvId} {bdI bdV : Binding} {VS Cu : ObjId} {iv nv L : F64}
    {cur old : Value} {ce cc oe oc lw le lc : Bool} {i : Nat}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : 10 ≤ s.fuel)
    (hcode : d.code = PushGen.push_func) (hcls : d.isClassCtor = false) (hmode : d.thisMode = .strict)
    (hG : d.env < s.envs.size) (hGe : Scope.declLike? (s.envEntry d.env) = some (bG, oG))
    (hGI : bG[JSStr.ofString "index"]? = some bdI) (hGIm : bdI.mutable = true) (hGIv : bdI.value = some (.num iv))
    (hGV : bG[JSStr.ofString "valueStack"]? = some bdV) (hGVv : bdV.value = some (.obj VS))
    (hVS : VS < s.heap.size) (hVSk : (s.objEntry VS).kind = .array) (hCu : Cu < s.heap.size)
    (hCuk : (s.objEntry Cu).kind.isPlain = true) (hVC : VS ≠ Cu)
    (hCc : (s.objEntry Cu).props.get? (.str "current") = some (.data cur true ce cc))
    (hnv : Conv.addF iv F64.one = nv)
    (hslot : (s.objEntry VS).props.get? (.str (numberToJSStr nv)) = some (.data old true oe oc))
    (hidx : (PropKey.str (numberToJSStr nv)).arrayIndex? = some i)
    (hlen : (s.objEntry VS).props.get? (.str "length") = some (.data (.num L) lw le lc))
    (hiL : i < (Conv.toNat? L).getD 0)
    (hnl : (PropKey.str (numberToJSStr nv) == PropKey.str (JSStr.ofString "length")) = false) :
    WP eng answer n h (callImpl eng (.obj fo) t #[.obj Cu, value]) s fun v w h' =>
      v = .undefined ∧ h' = h ∧
      w = ((((bodyState s fo d t #[.obj Cu, value]).setEnv d.env ((s.envEntry d.env).withBindings fun x =>
          x.modify (JSStr.ofString "index") fun bd => { bd with value := some (.num nv) })).setProp
        VS (.str (numberToJSStr nv)) (.data cur true oe oc)).setProp Cu (.str "current") (.data value true ce cc)).restore s := by
  apply wp_callGen PushGen.push_eq (by decide) hlt hk (by omega) hcls hmode
    (by rw [hcode]; rfl) (by rw [hcode]; rfl) (simpleU d hcode) (by rw [hcode]; rfl) (by rw [hcode]; rfl)
  have hpn : d.code.info.fdi.paramNames = #[JSStr.ofString "cursor", JSStr.ofString "value"] := by rw [hcode]; rfl
  have hv : d.code.info.fdi.varNames = #[] := by rw [hcode]; rfl
  have hl : FDI.lexDecls d = #[] := by simp [FDI.lexDecls, hcode, PushGen.push_func, Func.info]
  have ha : d.code.isAsync = false := by rw [hcode]; rfl
  have hne : s.envs.size ≠ d.env := Nat.ne_of_gt hG
  have hG1 : d.env < s.envs.size + 1 := Nat.lt_succ_of_lt hG
  clear hcode
  simp only [PushGen.push]
  subst hnv
  js [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGI, hGIm, hGIv, hGV, hGVv, hVS, hVSk, hCu, hCuk, hVC,
    Ne.symm hVC, hCc, hslot, hidx, hlen, hiL, hnl, FDI.fdiCtx, Sem.inner]
  all_goals (repeat' apply And.intro)
  all_goals rfl

theorem binaryOp_gt_num (a b : F64) (s : State) :
    Sem.binaryOp .gt (.num a) (.num b) s = .ok (.bool (ltNum b a)) s := by
  simp only [Sem.binaryOp, isLessThan, M.bind_eq, M.bind_apply, ↓reduceIte, Logic.toPrim_num, M.bindRes_ok, Bool.false_eq_true,
    FDI.pure_app, Logic.toNumeric_num, ltNum]

/-- **`a > b`** of two Numbers. -/
theorem wp_gtNum {n : Nat} {h : σ} {a b : F64} {s : State} {Q : Value → State → σ → Prop}
    (hq : Q (.bool (ltNum b a)) s h) : WP eng answer n h (Sem.binaryOp .gt (.num a) (.num b)) s Q :=
  wp_of_eq (binaryOp_gt_num a b s) hq

/-- **`x--`** of a variable holding a Number: the old value; the variable decremented. -/
theorem wp_postDecIdentC {n : Nat} {h : σ} {x : JSStr} {ctx : Ctx} {s : State} {Q : Value → State → σ → Prop}
    (hk : depth ≤ s.fuel)
    (hw : match Scope.resolve s depth ctx.lex x, Scope.lookup s depth ctx.lex x with
      | some e, some (.num a) => SetsC s e x (.num (Conv.subF a F64.one)) fun w' => Q (.num a) w' h
      | _, _ => False) :
    WP eng answer n h (Sem.update false false (Sem.identRef x) ctx) s Q := by
  cases hr : Scope.resolve s depth ctx.lex x with
  | none => rw [hr] at hw; exact hw.elim
  | some e =>
    cases hl : Scope.lookup s depth ctx.lex x with
    | none => rw [hr, hl] at hw; exact hw.elim
    | some v =>
      rw [hr, hl] at hw
      cases v with
      | num a =>
        simp only at hw
        obtain ⟨bm, o, bd, he, hd, hb, hv⟩ := resolve_lookup s x (.num a) depth ctx.lex e hr hl
        obtain ⟨bm', o', bd', he', hd', hb', hv', hm', q⟩ := setsC_setsVar hw
        have h1 : Sem.identRef x ctx s = .ok (.env (some e) x ctx.strict) s :=
          Scope.resolveBinding_of_resolve s depth ctx.lex x ctx.strict e hr hk
        have h2 := Scope.getRefValue_env s e x ctx.strict he bm o hd bd (.num a) hb hv
        have h3 := setMutableBinding_declLike e x (.num (Conv.subF a F64.one)) ctx.strict s he' hd' hb' hv' hm'
        apply wp_of_eq _ q
        simp only [Sem.update, M.bind_eq, M.bind_apply, h1, M.bindRes_ok, getRefValueOnce, h2, FDI.pure_app,
          Logic.toNumeric_num, putRefValue, ite_true, if_true, Bool.false_eq_true, ↓reduceIte]
        rw [h3]
        rfl
      | _ => exact hw.elim

theorem simpleO (d : FuncData) (hc : d.code = PopGen.pop_func) : FDI.Simple d := by
  constructor <;> rw [hc] <;> try rfl
  simp [PopGen.pop_func, Func.params, Func.info]

set_option maxRecDepth 40000 in
theorem pop_spec {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t : Value} {s : State}
    {bG : HashMap JSStr Binding} {oG : Option EnvId} {bdI bdV : Binding} {VS Cu : ObjId} {iv L : F64}
    {cur saved : Value} {ce cc oe oc lw le lc : Bool} {i : Nat}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : 10 ≤ s.fuel)
    (hcode : d.code = PopGen.pop_func) (hcls : d.isClassCtor = false) (hmode : d.thisMode = .strict)
    (hG : d.env < s.envs.size) (hGe : Scope.declLike? (s.envEntry d.env) = some (bG, oG))
    (hGI : bG[JSStr.ofString "index"]? = some bdI) (hGIm : bdI.mutable = true) (hGIv : bdI.value = some (.num iv))
    (hGV : bG[JSStr.ofString "valueStack"]? = some bdV) (hGVv : bdV.value = some (.obj VS))
    (hVS : VS < s.heap.size) (hVSk : (s.objEntry VS).kind = .array) (hCu : Cu < s.heap.size)
    (hCuk : (s.objEntry Cu).kind.isPlain = true) (hVC : VS ≠ Cu)
    (hCc : (s.objEntry Cu).props.get? (.str "current") = some (.data cur true ce cc))
    (hslot : (s.objEntry VS).props.get? (.str (numberToJSStr iv)) = some (.data saved true oe oc))
    (hidx : (PropKey.str (numberToJSStr iv)).arrayIndex? = some i)
    (hlen : (s.objEntry VS).props.get? (.str "length") = some (.data (.num L) lw le lc))
    (hiL : i < (Conv.toNat? L).getD 0)
    (hnl : (PropKey.str (numberToJSStr iv) == PropKey.str (JSStr.ofString "length")) = false)
    (hpos : ltNum iv (F64.fin false 0 (-1074)) = false) :
    WP eng answer n h (callImpl eng (.obj fo) t #[.obj Cu]) s fun v w h' =>
      v = .undefined ∧ Frame ⟨[(d.env, "index")], [(VS, .str (numberToJSStr iv)), (Cu, .str "current")], false⟩ s w ∧
      s.fuel ≤ w.fuel + 10 ∧ h' = h ∧
      Scope.declLike? (w.envEntry d.env) =
        some (bG.modify (JSStr.ofString "index") (fun bd => { bd with value := some (.num (Conv.subF iv F64.one)) }), oG) ∧
      (w.objEntry VS).props.get? (.str (numberToJSStr iv)) = some (.data .null true oe oc) ∧
      (w.objEntry Cu).props.get? (.str "current") = some (.data saved true ce cc) := by
  apply wp_callGen PopGen.pop_eq (by decide) hlt hk (by omega) hcls hmode
    (by rw [hcode]; rfl) (by rw [hcode]; rfl) (simpleO d hcode) (by rw [hcode]; rfl) (by rw [hcode]; rfl)
  have hpn : d.code.info.fdi.paramNames = #[JSStr.ofString "cursor"] := by rw [hcode]; rfl
  have hv : d.code.info.fdi.varNames = #[] := by rw [hcode]; rfl
  have hl : FDI.lexDecls d = #[] := by simp [FDI.lexDecls, hcode, PopGen.pop_func, Func.info]
  have ha : d.code.isAsync = false := by rw [hcode]; rfl
  have hne : s.envs.size ≠ d.env := Nat.ne_of_gt hG
  have hG1 : d.env < s.envs.size + 1 := Nat.lt_succ_of_lt hG
  clear hcode
  simp only [PopGen.pop]
  js [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGI, hGIm, hGIv, hGV, hGVv, hVS, hVSk, hCu, hCuk, hVC,
    Ne.symm hVC, hCc, hslot, hidx, hlen, hiL, hnl, FDI.fdiCtx, Sem.inner]
  refine wp_gtNum ?_
  simp only [hpos, Bool.false_eq_true, ↓reduceIte]
  iterate 17 (first | js_go | js_norm [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGI, hGIm, hGIv, hGV, hGVv, hVS, hVSk, hCu, hCuk, hVC, Ne.symm hVC, hCc, hslot, hidx, hlen, hiL, hnl, FDI.fdiCtx, Sem.inner] | js_split)
  refine wp_postDecIdentC (by simp [depth]; omega) ?_
  js [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGI, hGIm, hGIv, hGV, hGVv, hVS, hVSk, hCu, hCuk, hVC, Ne.symm hVC, hCc, hslot, hidx, hlen, hiL, hnl, FDI.fdiCtx, Sem.inner]
  trace_state
  all_goals (repeat' apply And.intro)
  all_goals first | rfl | omega | (simp only [js_simp]; omega) | frame_go' [*, hne, Ne.symm hne, hG1] | skip


set_option maxRecDepth 40000 in
theorem pop_exact {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t : Value} {s : State}
    {bG : HashMap JSStr Binding} {oG : Option EnvId} {bdI bdV : Binding} {VS Cu : ObjId} {iv L : F64}
    {cur saved : Value} {ce cc oe oc lw le lc : Bool} {i : Nat}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : 10 ≤ s.fuel)
    (hcode : d.code = PopGen.pop_func) (hcls : d.isClassCtor = false) (hmode : d.thisMode = .strict)
    (hG : d.env < s.envs.size) (hGe : Scope.declLike? (s.envEntry d.env) = some (bG, oG))
    (hGI : bG[JSStr.ofString "index"]? = some bdI) (hGIm : bdI.mutable = true) (hGIv : bdI.value = some (.num iv))
    (hGV : bG[JSStr.ofString "valueStack"]? = some bdV) (hGVv : bdV.value = some (.obj VS))
    (hVS : VS < s.heap.size) (hVSk : (s.objEntry VS).kind = .array) (hCu : Cu < s.heap.size)
    (hCuk : (s.objEntry Cu).kind.isPlain = true) (hVC : VS ≠ Cu)
    (hCc : (s.objEntry Cu).props.get? (.str "current") = some (.data cur true ce cc))
    (hslot : (s.objEntry VS).props.get? (.str (numberToJSStr iv)) = some (.data saved true oe oc))
    (hidx : (PropKey.str (numberToJSStr iv)).arrayIndex? = some i)
    (hlen : (s.objEntry VS).props.get? (.str "length") = some (.data (.num L) lw le lc))
    (hiL : i < (Conv.toNat? L).getD 0)
    (hnl : (PropKey.str (numberToJSStr iv) == PropKey.str (JSStr.ofString "length")) = false)
    (hpos : ltNum iv (F64.fin false 0 (-1074)) = false) :
    WP eng answer n h (callImpl eng (.obj fo) t #[.obj Cu]) s fun v w h' =>
      v = .undefined ∧ h' = h ∧
      w = ((((bodyState s fo d t #[.obj Cu]).setProp Cu (.str "current") (.data saved true ce cc)).setProp
        VS (.str (numberToJSStr iv)) (.data .null true oe oc)).setEnv d.env ((s.envEntry d.env).withBindings fun x =>
          x.modify (JSStr.ofString "index") fun bd => { bd with value := some (.num (Conv.subF iv F64.one)) })).restore s := by
  apply wp_callGen PopGen.pop_eq (by decide) hlt hk (by omega) hcls hmode
    (by rw [hcode]; rfl) (by rw [hcode]; rfl) (simpleO d hcode) (by rw [hcode]; rfl) (by rw [hcode]; rfl)
  have hpn : d.code.info.fdi.paramNames = #[JSStr.ofString "cursor"] := by rw [hcode]; rfl
  have hv : d.code.info.fdi.varNames = #[] := by rw [hcode]; rfl
  have hl : FDI.lexDecls d = #[] := by simp [FDI.lexDecls, hcode, PopGen.pop_func, Func.info]
  have ha : d.code.isAsync = false := by rw [hcode]; rfl
  have hne : s.envs.size ≠ d.env := Nat.ne_of_gt hG
  have hG1 : d.env < s.envs.size + 1 := Nat.lt_succ_of_lt hG
  clear hcode
  simp only [PopGen.pop]
  js [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGI, hGIm, hGIv, hGV, hGVv, hVS, hVSk, hCu, hCuk, hVC,
    Ne.symm hVC, hCc, hslot, hidx, hlen, hiL, hnl, FDI.fdiCtx, Sem.inner]
  refine wp_gtNum ?_
  simp only [hpos, Bool.false_eq_true, ↓reduceIte]
  iterate 17 (first | js_go | js_norm [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGI, hGIm, hGIv, hGV, hGVv, hVS, hVSk, hCu, hCuk, hVC, Ne.symm hVC, hCc, hslot, hidx, hlen, hiL, hnl, FDI.fdiCtx, Sem.inner] | js_split)
  refine wp_postDecIdentC (by simp [depth]; omega) ?_
  js [hpn, hv, hl, ha, hG, hG1, hne, Ne.symm hne, hGe, hGI, hGIm, hGIv, hGV, hGVv, hVS, hVSk, hCu, hCuk, hVC, Ne.symm hVC, hCc, hslot, hidx, hlen, hiL, hnl, FDI.fdiCtx, Sem.inner]
  trace_state
  all_goals (repeat' apply And.intro)
  all_goals rfl

end

end ReactStack
