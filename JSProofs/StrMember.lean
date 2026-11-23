import JSProofs.Setter
import JSProofs.Object
import JSProofs.Builtins
import ES.Builtins.Text.String

/-!
# Members of a primitive string (zippy docs/react-proofs.md)

`str.k` for a key that is neither `length` nor an index: the string is wrapped (a fresh `String` object whose
prototype is the realm's `%String.prototype%`) and `k` read from the prototype; nothing that existed before changes.
React's `isCustomElement(tag)` asks `tag.indexOf("-")`.
-/

open ES ES.M HostRuns
open Std (HashMap)

namespace Logic

theorem modify_push_last' {α : Type} (xs : Array α) (x : α) (f : α → α) :
    (xs.push x).modify xs.size f = xs.push (f x) := by
  apply Array.ext
  · simp
  · intro i h1 h2
    simp only [Array.getElem_modify, Array.getElem_push]
    by_cases hi : i = xs.size
    · subst hi; simp
    · have : i < xs.size := by simp at h1; omega
      simp [this, Ne.symm hi]

/-- The wrapper `toObject` makes of a string. -/
def strWrapper (SP : ObjId) (s : JSStr) : Obj :=
  ({ proto := .obj SP, kind := .primitive (.str s) } : Obj).withProps
    (·.insert (.str kLength) (.data (.num (Conv.ofNat s.length)) false false false))

theorem toObject_str (s : JSStr) (st : State) (SP : ObjId)
    (hSP : st.curRealm.intrinsics.get? "%String.prototype%" = some SP) :
    toObject (.str s) st = .ok st.heap.size (st.withHeap (·.push (strWrapper SP s))) := by
  simp only [toObject, toObject.wrap, intrinsic, hSP, M.bind_eq, M.bind_apply, alloc, setOwn, modifyObj]
  simp [M.bindRes_ok, State.withHeap, strWrapper, Pure.pure, M.pure]
  simp only [modifyObj, State.withHeap, M.bindRes_ok, M.pure]
  rw [modify_push_last']

theorem strWrapper_kind (SP : ObjId) (s : JSStr) : (strWrapper SP s).kind = .primitive (.str s) := rfl
theorem strWrapper_proto (SP : ObjId) (s : JSStr) : (strWrapper SP s).proto = .obj SP := rfl
theorem strWrapper_props (SP : ObjId) (s : JSStr) (k : JSStr) (hk : k ≠ kLength) :
    (strWrapper SP s).props.get? (.str k) = none := by
  simp only [strWrapper, Obj.withProps]
  rw [PropMap.get?_insert_ne _ _ _ _ (fun h => hk (by injection h with h; exact h.symm))]
  simp [PropMap.get?]

theorem objEntry_push_last (st : State) (W : Obj) : (st.withHeap (·.push W)).objEntry st.heap.size = W := by
  simp [State.objEntry, State.withHeap]

theorem objEntry_push_old (st : State) (W : Obj) (o : ObjId) (h : o < st.heap.size) :
    (st.withHeap (·.push W)).objEntry o = st.objEntry o := by
  simp [State.objEntry, State.withHeap, Array.getElem?_push, h, Nat.ne_of_lt h]

theorem size_push (st : State) (W : Obj) : (st.withHeap (·.push W)).heap.size = st.heap.size + 1 := by
  simp [State.withHeap]

/-- **`str.k`**, `k` neither `length` nor an index: `%String.prototype%`'s data property `k`; the state gains the
wrapper. -/
theorem getRefValue_str (s k : JSStr) (strict : Bool) (st : State) (SP : ObjId) (v : Value) (w e c : Bool)
    (hSP : st.curRealm.intrinsics.get? "%String.prototype%" = some SP) (hlt : SP < st.heap.size)
    (hk : (st.objEntry SP).kind.isPlain = true) (hv : (st.objEntry SP).props.get? (.str k) = some (.data v w e c))
    (hkl : (k == kLength) = false) (hki : k.toIndex? = none) :
    getRefValue (.prop (.str s) (.str k) strict none) st = .ok v (st.withHeap (·.push (strWrapper SP s))) := by
  simp only [getRefValue, Value.isNullish, toPropertyKey, M.bind_eq, M.bind_apply, hkl, hki]
  have hkl' : k ≠ kLength := by simpa using hkl
  simp [Pure.pure, M.pure, M.bindRes_ok]
  simp only [hkl', ite_false, hki, ↓reduceIte]
  rw [M.bind_apply, toObject_str s st SP hSP, M.bindRes_ok]
  have hW : st.heap.size < (st.withHeap fun x => x.push (strWrapper SP s)).heap.size := by
    rw [size_push]; omega
  have hWe := objEntry_push_last st (strWrapper SP s)
  have hSPe := objEntry_push_old st (strWrapper SP s) SP hlt
  have hSPlt : SP < (st.withHeap fun x => x.push (strWrapper SP s)).heap.size := Nat.lt_trans hlt hW
  show _ = Res.ok v (st.withHeap fun x => x.push (strWrapper SP s))
  generalize (st.withHeap fun x => x.push (strWrapper SP s)) = st2 at hW hWe hSPe hSPlt ⊢
  unfold Obj'.get; rw [maxDepth_eq]
  rw [show (19997 + 3 : Nat) = 19999 + 1 from rfl, ES.get.eq_2]
  simp only [M.bind_eq, M.bind_apply, objKind, readObj_entry' _ _ _ hW, hWe, M.bindRes_ok, strWrapper_kind]
  rw [show (19999 : Nat) = 19998 + 1 from rfl, ordinaryGet.eq_2]
  simp only [M.bind_eq, M.bind_apply]
  rw [show (19998 : Nat) = 19997 + 1 from rfl, getOwnProperty.eq_2]
  simp only [M.bind_eq, M.bind_apply, objKind, readObj_entry' _ _ _ hW, hWe, M.bindRes_ok, strWrapper_kind, ownProp,
    strWrapper_props SP s k hkl', stringGetOwnProperty, hki]
  simp only [Pure.pure, M.pure, M.bindRes_ok]
  rw [getPrototypeOf.eq_2]
  simp only [M.bind_eq, M.bind_apply, objKind, objProto, readObj_entry' _ _ _ hW, hWe, M.bindRes_ok, strWrapper_kind,
    strWrapper_proto]
  rw [show (19997 + 1 : Nat) = 19995 + 3 from rfl,
    get_entry_data 19995 SP (.str k) (.str s) st2 hSPlt (by rw [hSPe]; exact hk) (by rw [hSPe, hv]; rfl), hSPe, hv]
  rfl

end Logic

namespace Logic

theorem frame_push {fp : Footprint} (st : State) (W : Obj) : Frame fp st (st.withHeap (·.push W)) where
  envs_le := by simp [State.withHeap]
  heap_le := by simp [State.withHeap]
  env_agree e _ := by simp only [State.envEntry, State.withHeap]; exact envAgree_refl _ _
  obj_agree o ho := by rw [objEntry_push_old _ _ _ ho]; exact objAgree_refl _ _
  env_eq e _ _ := by simp [State.envEntry, State.withHeap]
  obj_eq o ho _ := objEntry_push_old _ _ _ ho
  realms_eq := by simp [State.withHeap]
  jobs_prefix := ⟨#[], by simp [State.withHeap]⟩
  jobs_eq _ := by simp [State.withHeap]

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ}

/-- `str.k` reads `%String.prototype%`'s data property `k` (not `length`, not an index). -/
def StrGets (s : State) (str : JSStr) (k : JSStr) (P : Value → Prop) : Prop :=
  ∃ SP v w e c, s.curRealm.intrinsics.get? "%String.prototype%" = some SP ∧ SP < s.heap.size ∧
    (s.objEntry SP).kind.isPlain = true ∧ (s.objEntry SP).props.get? (.str k) = some (.data v w e c) ∧
    (k == kLength) = false ∧ k.toIndex? = none ∧ P v

/-- **`str.k(args)`** on a primitive string: `%String.prototype%`'s method `k` called with the string as `this`; the
arguments are evaluated in the state with the wrapper object (`frame_push`: nothing that existed changed). -/
theorem wp_callMemberStr {n : Nat} {h : σ} {obj : Sem.CExpr} {k : JSStr} {as : Array Sem.ArgD} {name : CalleeDesc}
    {ctx : Ctx} {s : State} {Q : Value → State → σ → Prop}
    (hw : WP eng answer (n + 1) h (obj ctx) s fun bv w h1 => ∃ str, bv = .str str ∧ StrGets w str k fun fv =>
      ∀ W, ArgsWP eng answer (n + 1) ctx as.toList #[] h1 (w.withHeap (·.push W)) fun args w2 h2 =>
        CallableC w2 fv ∧ WP eng answer n h2 (callImpl eng fv (.str str) args) w2 Q) :
    WP eng answer (n + 1) h (Sem.call (Sem.memberRef obj (.name k) false) (Sem.args as) false name ctx) s Q := by
  rw [wp_iff_wpr]
  simp only [Sem.call, Sem.memberRef, M.bind_eq, M.bind_apply]
  apply wpr_bind
  apply wpr_bind
  refine wp_mono hw fun bv w h1 ⟨str, hb, SP, v, we, ee, ce, hSP, hlt, hk, hv, hkl, hki, q⟩ => ?_
  subst hb
  simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  refine wp_of_eq (a := Ref.prop (.str str) (.str k) ctx.strict none) rfl ?_
  rw [wp_iff_wpr]
  simp only [M.bind_apply, getRefValue_str str k ctx.strict w SP v we ee ce hSP hlt hk hv hkl hki, M.bindRes_ok,
    refThisValue]
  show WPR eng answer (n + 1) h1 (M.bindRes _ (M.pure (Value.str str) _)) Q
  simp only [M.pure, M.bindRes_ok]
  apply wpr_bind
  refine wp_mono (wp_args (q (strWrapper SP str))) fun args w2 h2 ⟨hcl, hq⟩ => ?_
  rw [wp_iff_wpr]
  simp only [M.bind_apply, isCallable_of hcl, M.bindRes_ok, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [← wp_iff_wpr]
  exact wp_call hq

/-- **`str.indexOf(t)`**, `t` not in `str`: `-1`; nothing changed, one step of fuel. -/
theorem indexOf_none_spec {n : Nat} {h : σ} {fo : ObjId} {bd : BuiltinData} {str t : JSStr} {s : State}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .builtin bd)
    (hfn : eng.builtins[bd.id]? = some ES.Builtins.Text.stringProtoIndexOf) (hf : s.fuel ≠ 0)
    (hno : str.indexOf t 0 = none) :
    WP eng answer n h (callImpl eng (.obj fo) (.str str) #[.str t]) s fun v w h' =>
      v = intV (-1) ∧ Frame {} s w ∧ s.fuel ≤ w.fuel + 1 ∧ h' = h := by
  rw [wp_iff_wpr, callImpl_builtin eng fo bd ES.Builtins.Text.stringProtoIndexOf (.str str) _ s hlt hk hfn hf, ← wp_iff_wpr]
  apply wp_inCallee
  refine wp_of_eq (a := ?a) (w := ?w) ?eq ?post
  case eq =>
    simp [ES.Builtins.Text.stringProtoIndexOf, ES.Builtins.Text.thisStr, arg, ES.Builtins.Text.clampIndex, toStr,
      Value.isNullish, M.bind_apply, Pure.pure]
    rw [maxDepth_eq]
    simp [toJSString, toIntClamp, ES.toIntegerOrInfinity, toNum, toNumber, maxDepth_eq, M.bind_apply, Pure.pure,
      M.pure]
    have hz : Conv.toIntegerOrInf F64.nan = .inr 0 := by decide
    rw [hz]
    have h0 : (max 0 (min (↑str.length : Int) 0)).toNat = 0 := by omega
    rw [h0]
    have hno' : str.indexOf t 0 = none := hno
    rw [hno']
    rfl
  case post => exact ⟨rfl, frame_same rfl rfl rfl rfl, by first | omega | (simp; omega) | simp, rfl⟩

end

end Logic
