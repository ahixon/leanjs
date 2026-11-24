import JSProofs.ReadChain
import JSProofs.Destructure
import JSProofs.Loops2

/-!
# `v instanceof C` false (zippy docs/react-proofs.md)

`instanceofOperator(O, C)` where `C`'s `@@hasInstance` is `Function.prototype`'s (found along a read-plain chain):
its call, `OrdinaryHasInstance(C, O)`, reads `C.prototype` and walks `O`'s prototype chain; when the walk reaches
`null` without meeting `C.prototype` (`NotOnChain`), the result is `false`. React's `getActiveElementDeep` asks
`element instanceof win.HTMLIFrameElement` of the focused element.
-/

open ES ES.M HostRuns
open Std (HashMap)

namespace Logic

/-- Walking from `o` by [[GetPrototypeOf]] (read-plain objects) reaches `null` within `n` objects without meeting `p`. -/
def NotOnChain (s : State) : Nat → ObjId → ObjId → Prop
  | 0, _, _ => False
  | n + 1, o, p =>
    o < s.heap.size ∧ (s.objEntry o).kind.isReadPlain = true ∧
      match (s.objEntry o).proto with
      | .obj q => q ≠ p ∧ NotOnChain s n q p
      | _ => True

/-- OrdinaryHasInstance's step 6 loop from `o`, `p` not on its chain: `false`, the state unchanged. -/
theorem loop_notOnChain (s : State) (p : ObjId) :
    ∀ (n : Nat) (o : ObjId) (b : Nat), NotOnChain s n o p → n ≤ b →
      M.loop (fun cur => do
        match ← Obj'.getPrototypeOf cur with
        | .obj nxt => if sameValue (.obj nxt) (.obj p) then return .inr true else return .inl nxt
        | _ => return .inr false) b o s = .ok false s := by
  intro n
  induction n with
  | zero => intro o b h; exact absurd h id
  | succ n ih =>
    intro o b ⟨hlt, hk, hrest⟩ hb
    obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
    have hg : Obj'.getPrototypeOf o s = .ok (s.objEntry o).proto s := by
      unfold Obj'.getPrototypeOf
      rw [show maxDepth = 19999 + 1 from rfl]
      exact getPrototypeOf_read 19999 o s hlt hk
    simp only [M.loop, M.bind_eq, M.bind_apply, hg, M.bindRes_ok]
    cases hpr : (s.objEntry o).proto with
    | obj q =>
      rw [hpr] at hrest
      obtain ⟨hne, hq⟩ := hrest
      have hsv : sameValue (.obj q) (.obj p) = false := by simp [sameValue, hne]
      simp only [hsv, Bool.false_eq_true, ↓reduceIte, Pure.pure, M.pure, M.loopRes]
      exact ih q b' hq (by omega)
    | _ => simp [Pure.pure, M.pure, M.loopRes]

/-- **OrdinaryHasInstance(C, O) false**: `C` a built-in function (not bound) with an own data property `prototype`
(an object `PC`), `PC` not on `O`'s chain (within the fuel the loop is bounded by). -/
theorem ordinaryHasInstance_false (s : State) (C O PC : ObjId) (bd : BuiltinData) (n : Nat) {w e c : Bool}
    (hC : C < s.heap.size) (hCk : (s.objEntry C).kind = .builtin bd)
    (hCp : (s.objEntry C).props.get? (.str kPrototype) = some (.data (.obj PC) w e c))
    (hO : NotOnChain s n O PC) (hn : n ≤ s.fuel) :
    ordinaryHasInstance (.obj C) (.obj O) s = .ok false s := by
  have hrc : ReadChain s 1 C (.str kPrototype) := ⟨hC, by rw [hCk]; rfl, fun h => by rw [hCp] at h; cases h⟩
  have hgp : getProp C (.str kPrototype) s = .ok (.obj PC) s := by
    have := get_readChain s (.str kPrototype) (.obj C) 1 C maxDepth hrc (by rw [show maxDepth = 20000 from rfl]; omega)
      (by simp [ordLookup, hCp, noAccessor])
    unfold getProp Obj'.get
    rw [this]; simp [ordLookup, hCp, ownDataValue]
  simp only [ordinaryHasInstance, M.bind_eq, M.bind_apply, isCallable, readObj_entry' _ _ _ hC, hCk, M.bindRes_ok,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte, objKind, hgp, M.repeatFrom]
  exact loop_notOnChain s PC n O s.fuel hO hn

/-- **A read-plain chain lookup through a frame**: the same, when the key is in no object's part of the footprint. -/
theorem readChain_frame {fp : Footprint} {s w : State} (hF : Frame fp s w) (k : PropKey)
    (hk : ∀ o, fp.props.contains (o, k) = false) :
    ∀ m o, ReadChain s m o k → ReadChain w m o k ∧ ordLookup w m o k = ordLookup s m o k := by
  intro m
  induction m with
  | zero => intro o h; exact absurd h id
  | succ m ih =>
    intro o h
    obtain ⟨hlt, hpl, hrest⟩ := h
    have hp := props_frame hF hlt (hk o)
    have hpr : (w.objEntry o).proto = (s.objEntry o).proto := (hF.obj_agree o hlt).2.1
    refine ⟨⟨heap_frame hF hlt, by rw [kind_frame hF hlt]; exact hpl, ?_⟩, ?_⟩
    · intro hn
      rw [hp] at hn
      have := hrest hn
      rw [hpr]
      split
      · rename_i q hq
        rw [hq] at this
        exact (ih q this).1
      · trivial
    · simp only [ordLookup, hp, hpr]
      cases hq : (s.objEntry o).props.get? k with
      | some x => rfl
      | none =>
        have := hrest hq
        cases hpp : (s.objEntry o).proto with
        | obj q => rw [hpp] at this; simp only [hpp]; exact (ih q this).2
        | _ => rfl

/-- **The walk through a frame**: every existing object's kind and prototype are kept. -/
theorem notOnChain_frame {fp : Footprint} {s w : State} (hF : Frame fp s w) (p : ObjId) :
    ∀ n o, NotOnChain s n o p → NotOnChain w n o p := by
  intro n
  induction n with
  | zero => intro o h; exact h
  | succ n ih =>
    intro o ⟨hlt, hk, hr⟩
    have hpr : (w.objEntry o).proto = (s.objEntry o).proto := (hF.obj_agree o hlt).2.1
    refine ⟨heap_frame hF hlt, by rw [kind_frame hF hlt]; exact hk, ?_⟩
    rw [hpr]
    split
    · rename_i q hq
      rw [hq] at hr
      exact ⟨hr.1, ih q hr.2⟩
    · trivial

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ}

/-- **`O instanceof C` false**: `C`'s `@@hasInstance`, found along a read-plain chain, is the built-in
`Function.prototype[@@hasInstance]`; `C` a built-in function whose `prototype` is not on `O`'s chain. One step of fuel
(the built-in's call), nothing else changed. -/
theorem wp_instanceof_false {n : Nat} {h : σ} {O C fH PC : ObjId} {bdC bdH : BuiltinData} {mH nO : Nat}
    {s : State} {wH eH cH w e c : Bool}
    (hC : C < s.heap.size) (hCk : (s.objEntry C).kind = .builtin bdC)
    (hCp : (s.objEntry C).props.get? (.str kPrototype) = some (.data (.obj PC) w e c))
    (hHc : ReadChain s mH C (.sym WK.hasInstance)) (hHm : mH ≤ 9000)
    (hHl : ordLookup s mH C (.sym WK.hasInstance) = some (.data (.obj fH) wH eH cH))
    (hH : fH < s.heap.size) (hHk : (s.objEntry fH).kind = .builtin bdH)
    (hHfn : eng.builtins[bdH.id]? = some ES.funcProtoHasInstance)
    (hO : NotOnChain s nO O PC) (hf : nO + 1 ≤ s.fuel) :
    WP eng answer (n + 1) h (instanceofOperator (.obj O) (.obj C)) s fun b w' h' =>
      b = false ∧ Frame {} s w' ∧ s.fuel ≤ w'.fuel + 1 ∧ h' = h := by
  have hgm : getMethodOf (.obj C) (.sym WK.hasInstance) s = .ok (some (.obj fH)) s := by
    have hg := get_readChain s (.sym WK.hasInstance) (.obj C) mH C 19998 hHc (by omega) (by simp [hHl, noAccessor])
    rw [hHl] at hg
    unfold getMethodOf
    rw [show maxDepth = 19998 + 1 + 1 from rfl]
    simp only [getMethod, getV, M.bind_eq, M.bind_apply]
    simp [hg, ownDataValue, Value.isNullish, isCallable, readObj_entry' _ _ _ hH, hHk, M.bindRes_ok, Pure.pure, M.pure]
  rw [wp_iff_wpr]
  simp only [instanceofOperator, M.bind_eq, M.bind_apply, hgm, M.bindRes_ok]
  apply wpr_bind
  refine wp_call ?_
  rw [wp_iff_wpr, callImpl_builtin eng fH bdH _ _ _ s hH hHk hHfn (by omega), ← wp_iff_wpr]
  apply wp_inCallee
  generalize hu : ({ { s with fuel := s.fuel - 1 } with realm := bdH.realm, script := s.script } : State) = u
  have hus : u.heap = s.heap := by rw [← hu]
  have hent : ∀ o, u.objEntry o = s.objEntry o := by intro o; rw [← hu]; rfl
  have huf : u.fuel = s.fuel - 1 := by rw [← hu]
  have hOu : NotOnChain u nO O PC := by
    have key : ∀ m o, NotOnChain s m o PC → NotOnChain u m o PC := by
      intro m
      induction m with
      | zero => intro o h; exact h
      | succ m ih =>
        intro o ⟨hlt, hk, hr⟩
        refine ⟨by rw [hus]; exact hlt, by rw [hent]; exact hk, ?_⟩
        rw [hent]
        split
        · rename_i q hq
          rw [hq] at hr
          exact ⟨hr.1, ih q hr.2⟩
        · trivial
    exact key nO O hO
  have hohi := ordinaryHasInstance_false u C O PC bdC nO (by rw [hus]; exact hC) (by rw [hent]; exact hCk)
    (by rw [hent]; exact hCp) hOu (by omega)
  show WP eng answer n h (ES.funcProtoHasInstance fH (.obj C) #[.obj O] .undefined) u _
  rw [wp_iff_wpr]
  simp only [ES.funcProtoHasInstance, M.bind_eq, M.bind_apply, arg]
  rw [show (#[Value.obj O][0]?.getD Value.undefined) = Value.obj O from rfl, hohi, M.bindRes_ok]
  show WPR eng answer n h (Res.ok (Value.bool false) u) _
  refine wpr_ok (wp_pure ⟨rfl, ?_, ?_, rfl⟩)
  · rw [← hu]
    exact frame_withFuel (frame_refl _ s) _
  · rw [← hu]; simp only; omega

end

end Logic
