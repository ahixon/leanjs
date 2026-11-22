import JSProofs.Builtins

/-!
# Arrays: writing an existing element (zippy docs/react-proofs.md)

React's update queue is a module-level array written in place (`concurrentQueues[concurrentQueuesIndex++] = fiber`);
once the first update has grown it, each later update writes elements that exist, below `length`. [[Set]] there is
the ordinary set's own-property case, then the array's [[DefineOwnProperty]] for an index below `length`: the value
replaced, `length` unchanged (`set_array_own`).
-/

open ES ES.M HostRuns
open Std (HashMap)

namespace Logic

theorem readObj_kind (o : ObjId) (s : State) (h : o < s.heap.size) :
    objKind o s = .ok (s.objEntry o).kind s := readObj_entry o _ s h

theorem ownProp_entry (o : ObjId) (k : PropKey) (s : State) (h : o < s.heap.size) :
    ownProp o k s = .ok ((s.objEntry o).props.get? k) s := readObj_entry o _ s h

/-- **[[Set]] of an existing writable element of an array below its `length`** (the array its own receiver): the
element replaced. -/
theorem set_array_own (n : Nat) (o : ObjId) (k : PropKey) (v : Value) (s : State) (h : o < s.heap.size)
    (hk : (s.objEntry o).kind = .array) {v0 : Value} {e c : Bool}
    (hp : (s.objEntry o).props.get? k = some (.data v0 true e c)) {i : Nat} (hi : k.arrayIndex? = some i)
    (hkl : (k == .str kLength) = false) {L : F64} {lw le lc : Bool}
    (hlen : (s.objEntry o).props.get? (.str kLength) = some (.data (.num L) lw le lc))
    (hil : i < (Conv.toNat? L).getD 0) :
    ES.set (n + 4) o k v (.obj o) s = .ok true (s.setProp o k (.data v true e c)) := by
  have hge : ¬ (i ≥ (Conv.toNat? L).getD 0) := by omega
  simp only [ES.set, M.bind_eq, M.bind_apply, readObj_kind o s h, M.bindRes_ok, hk]
  simp only [ordinarySet, ES.getOwnProperty, M.bind_eq, M.bind_apply, readObj_kind o s h, M.bindRes_ok, hk,
    ownProp_entry o k s h, hp, FDI.pure_app, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  simp only [ES.defineOwnProperty, M.bind_eq, M.bind_apply, readObj_kind o s h, M.bindRes_ok, hk, hkl,
    Bool.false_eq_true, ↓reduceIte, hi, ownProp_entry o _ s h, hlen, hge, Bool.false_and]
  simp only [decide_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte, M.bind_apply]
  rw [ordinaryDefineOwnProperty_entry o k _ s h, hp]
  simp [validateAndApply, PropDesc.isGeneric, PropDesc.isAccessor, PropDesc.isData, Property.configurable,
    Property.enumerable, State.setProp, FDI.pure_app]

theorem toPropertyKey_num (x : F64) (s : State) :
    toPropertyKey (.num x) s = .ok (.str (numberToJSStr x)) s := by
  have h1 : ES.toPrimitive maxDepth (.num x) (some false) s = .ok (.num x) s := by
    rw [show maxDepth = 19999 + 1 from rfl]; simp only [ES.toPrimitive]; rfl
  have h2 : toJSString maxDepth (.num x) s = .ok (numberToJSStr x) s := by
    rw [show maxDepth = 19999 + 1 from rfl]; simp only [toJSString]; rfl
  simp only [toPropertyKey, toPrim, toStr, M.bind_eq, M.bind_apply, h1, M.bindRes_ok, h2]
  rfl

/-- `o[x] = v`, `o` an array whose element `x` (a Number) exists and is writable, below `length`. -/
def PutsIdxC (s : State) (base kv v : Value) (P : State → Prop) : Prop :=
  match base, kv with
  | .obj o, .num x =>
    o < s.heap.size ∧ (s.objEntry o).kind = .array ∧
    match (s.objEntry o).props.get? (.str (numberToJSStr x)), (PropKey.str (numberToJSStr x)).arrayIndex?,
      (s.objEntry o).props.get? (.str kLength) with
    | some (.data _ true e c), some i, some (.data (.num L) _ _ _) =>
      ((PropKey.str (numberToJSStr x)) == .str kLength) = false ∧ i < (Conv.toNat? L).getD 0 ∧
      P (s.setProp o (.str (numberToJSStr x)) (.data v true e c))
    | _, _, _ => False
  | _, _ => False

theorem putRefValue_idx {s : State} {o : ObjId} {x : F64} {v : Value} {strict : Bool} {P : State → Prop}
    (h : PutsIdxC s (.obj o) (.num x) v P) :
    ∃ w, putRefValue (.prop (.obj o) (.num x) strict none) v s = .ok () w ∧ P w := by
  obtain ⟨hlt, hk, hm⟩ := h
  cases hp : (s.objEntry o).props.get? (.str (numberToJSStr x)) with
  | none => simp [hp] at hm
  | some p =>
    cases p with
    | accessor => simp [hp] at hm
    | data v0 w e c =>
      cases w with
      | false => simp [hp] at hm
      | true =>
        cases hi : (PropKey.str (numberToJSStr x)).arrayIndex? with
        | none => simp [hp, hi] at hm
        | some i =>
          cases hl : (s.objEntry o).props.get? (.str kLength) with
          | none => simp [hp, hi, hl] at hm
          | some lp =>
            cases lp with
            | accessor => simp [hp, hi, hl] at hm
            | data lv lw le lc =>
              cases lv with
              | num L =>
                rw [hp, hi, hl] at hm
                obtain ⟨hkl, hil, q⟩ := hm
                refine ⟨_, ?_, q⟩
                have hset := set_array_own 19996 o (.str (numberToJSStr x)) v s hlt hk hp hi hkl hl hil
                have hset' : Obj'.set o (.str (numberToJSStr x)) v (.obj o) s =
                    .ok true (s.setProp o (.str (numberToJSStr x)) (.data v true e c)) := by
                  unfold Obj'.set; rw [show maxDepth = 19996 + 4 from rfl]; exact hset
                simp only [putRefValue, M.bind_eq, M.bind_apply, toPropertyKey_num, M.bindRes_ok, hset',
                  Option.getD_none, Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte, FDI.pure_app]
              | _ => simp [hp, hi, hl] at hm

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ}

/-- **`obj[key] = rhs`** of an existing writable array element below `length`. -/
theorem wp_assignIdxC {n : Nat} {h : σ} {obj ke rhs : Sem.CExpr} {ctx : Ctx} {s : State}
    {Q : Value → State → σ → Prop}
    (hw : WP eng answer n h (obj ctx) s fun bv w1 h1 => WP eng answer n h1 (ke ctx) w1 fun kv w2 h2 =>
      WP eng answer n h2 (rhs ctx) w2 fun v w3 h3 => PutsIdxC w3 bv kv v fun w4 => Q v w4 h3) :
    WP eng answer n h (Sem.assign (Sem.memberRef obj (.computed ke) false) rhs ctx) s Q := by
  rw [wp_iff_wpr]
  simp only [Sem.assign, Sem.memberRef, M.bind_eq, M.bind_apply]
  apply wpr_bind
  apply wpr_bind
  refine wp_mono hw fun bv w1 h1 hk => ?_
  simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  apply wp_bind
  refine wp_mono hk fun kv w2 h2 hr => ?_
  refine wp_of_eq (a := Ref.prop bv kv ctx.strict none) rfl ?_
  apply wp_bind
  refine wp_mono hr fun v w3 h3 q => ?_
  match bv, kv, q with
  | .obj o, .num x, q =>
    obtain ⟨w4, hput, hq⟩ := putRefValue_idx (strict := ctx.strict) q
    apply wp_bind
    exact wp_of_eq hput (wp_pure hq)

/-- **`obj.k op= rhs`** of a plain object's own writable data property holding a Number, a numeric operator. -/
theorem wp_assignOpMemberC {n : Nat} {h : σ} {op : BinOp} {obj rhs : Sem.CExpr} {k : JSStr} {ctx : Ctx} {s : State}
    {Q : Value → State → σ → Prop} (hop : isNumOp op = true)
    (hw : WP eng answer n h (obj ctx) s fun bv w1 h1 => GetsC w1 bv k fun cur => match cur with
      | .num a => WP eng answer n h1 (rhs ctx) w1 fun rv w2 h2 => match rv with
        | .num b => PutsC w2 bv k (.num (numberBinOp op a b)) fun w3 => Q (.num (numberBinOp op a b)) w3 h2
        | _ => False
      | _ => False) :
    WP eng answer n h (Sem.assignOp op (Sem.memberRef obj (.name k) false) rhs ctx) s Q := by
  rw [wp_iff_wpr]
  simp only [Sem.assignOp, Sem.memberRef, M.bind_eq, M.bind_apply]
  apply wpr_bind
  apply wpr_bind
  refine wp_mono hw fun bv w1 h1 hg => ?_
  simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  refine wp_of_eq (a := Ref.prop bv (.str k) ctx.strict none) rfl ?_
  match bv, hg with
  | .obj o, ⟨hlt, hk, hm⟩ =>
    cases hp : (w1.objEntry o).props.get? (.str k) with
    | none => rw [hp] at hm; exact hm.elim
    | some p =>
      rw [hp] at hm
      cases p with
      | accessor => exact hm.elim
      | data cur cw ce cc =>
        cases cur with
        | num a =>
          simp only at hm
          have hget : getRefValue (.prop (.obj o) (.str k) ctx.strict none) w1 = .ok (.num a) w1 := by
            rw [getRefValue_prop]
            have := get_entry_data 19997 o (.str k) (.obj o) w1 hlt hk (by simp [hp])
            unfold Obj'.get; rw [show maxDepth = 19997 + 3 from rfl, this, hp]; rfl
          rw [wp_iff_wpr]
          simp only [getRefValueOnce, Value.isNullish, Bool.false_eq_true, ↓reduceIte, M.bind_eq, M.bind_apply,
            toPropertyKey, FDI.pure_app, M.bindRes_ok, keyToValue, hget]
          apply wpr_bind
          refine wp_mono hm fun rv w2 h2 q => ?_
          cases rv with
          | num b =>
            obtain ⟨o', v0, e, c, hb, hlt', hk', hp', q'⟩ := putsC_putsTo q
            cases hb
            rw [wp_iff_wpr]
            simp only [M.bind_apply, applyBinaryOp_num op a b w2 hop, M.bindRes_ok,
              putRefValue_own o k ctx.strict _ w2 hlt' hk' hp', FDI.pure_app]
            exact wpr_ok q'
          | _ => exact q.elim
        | _ => exact hm.elim

end

open Lean Meta Simp in
/-- Reduce a closed term (no free or meta variables) to normal form; the kernel checks the `rfl`. -/
def reduceClosed (e : Lean.Expr) : SimpM Step := do
  if e.hasFVar || e.hasMVar then return .continue
  let r ← withTransparency .all <| reduce e
  if r == e then return .continue
  return .done { expr := r, proof? := some (← mkExpectedTypeHint (← mkEqRefl r) (← mkEq e r)) }

open Lean Meta Simp in
/-- `numberToJSStr x` of a closed integer Number: `JSStr.ofString "<digits>"` (the kernel checks the equation by
evaluation). -/
simproc [js_simp] numStrEval (numberToJSStr _) := fun e => do
  let_expr numberToJSStr x := e | return .continue
  if x.hasFVar || x.hasMVar then return .continue
  let r ← withTransparency .all <| reduce x
  let_expr F64.fin neg m ex := r | return .continue
  let some neg := neg.constName? | return .continue
  let some m := (← instantiateMVars m).rawNatLit? <|> (match m with
    | .app (.app (.app (.const ``OfNat.ofNat _) _) (.lit (.natVal k))) _ => some k | _ => none) | return .continue
  let some ex ← (do
      let ex ← whnf ex
      match ex with
      | .app (.const ``Int.ofNat _) k => pure ((← whnf k).rawNatLit?.map Int.ofNat)
      | .app (.const ``Int.negSucc _) k => pure ((← whnf k).rawNatLit?.map Int.negSucc)
      | _ => pure none) | return .continue
  let v : Option Nat := if ex ≥ 0 then some (m * 2 ^ ex.toNat) else
    let d := 2 ^ (-ex).toNat
    if m % d == 0 then some (m / d) else none
  let some v := v | return .continue
  let str := (if neg == ``Bool.true && v != 0 then "-" else "") ++ toString v
  let rhs := mkApp (mkConst ``JSStr.ofString) (mkStrLit str)
  return .done { expr := rhs, proof? := some (← mkExpectedTypeHint (← mkEqRefl rhs) (← mkEq e rhs)) }
simproc [js_simp] arrayIndexEval (PropKey.arrayIndex? _) := reduceClosed
simproc [js_simp] toNatEval (Conv.toNat? _) := reduceClosed
simproc [js_simp] addFEval (Conv.addF _ _) := reduceClosed
simproc [js_simp] propKeyBeqEval (@BEq.beq PropKey _ _ _) := reduceClosed

attribute [js_simp] PutsIdxC kLength

/-- `js_step` with array element writes. -/
macro_rules
  | `(tactic| js_step) => `(tactic| first
      | apply wp_assignIdxC
      | apply wp_assignOpMemberC (by decide))

end Logic
