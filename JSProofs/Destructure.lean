import JSProofs.ArrayIter

/-!
# `const [a, b] = arr` (zippy docs/react-proofs.md)

Array destructuring of two names from an array, as the interpreter's `bindPattern` runs it (the iterator protocol
through the realm's built-ins: `Array.prototype[@@iterator]` is `values`, `%ArrayIteratorPrototype%.next` the
array iterator's `next`, no `return` on the iterator's chain). Vite keeps `const [n, setN] = useState(0)`.
-/

open ES ES.M HostRuns
open Std (HashMap)

namespace Logic

/-- **E1**: `@@iterator` of an array, found on its prototype (a callable built-in). -/
theorem getMethod_iterator (A AP fV : ObjId) (bd : BuiltinData) (s : State) {w e c : Bool}
    (hA : A < s.heap.size) (hAk : (s.objEntry A).kind.isReadPlain = true)
    (hAn : (s.objEntry A).props.get? (.sym WK.iterator) = none) (hAp : (s.objEntry A).proto = .obj AP)
    (hP : AP < s.heap.size) (hPk : (s.objEntry AP).kind.isReadPlain = true)
    (hPv : (s.objEntry AP).props.get? (.sym WK.iterator) = some (.data (.obj fV) w e c))
    (hV : fV < s.heap.size) (hVk : (s.objEntry fV).kind = .builtin bd) :
    getMethodOf (.obj A) (.sym WK.iterator) s = .ok (some (.obj fV)) s := by
  have hc : ReadChain s 2 A (.sym WK.iterator) :=
    ⟨hA, hAk, fun _ => by rw [hAp]; exact ⟨hP, hPk, fun h => by simp [hPv] at h⟩⟩
  have hl : ordLookup s 2 A (.sym WK.iterator) = some (.data (.obj fV) w e c) := by
    simp [ordLookup, hAn, hAp, hPv]
  have hg := get_readChain s (.sym WK.iterator) (.obj A) 2 A 19998 hc (by omega) (by simp [hl, noAccessor])
  rw [hl] at hg
  unfold getMethodOf
  rw [show maxDepth = 19998 + 1 + 1 from rfl]
  simp only [getMethod, getV, M.bind_eq, M.bind_apply]
  simp [hg, ownDataValue, Value.isNullish, isCallable, readObj_entry' _ _ _ hV, hVk, M.bindRes_ok, Pure.pure, M.pure]

/-- `GetV` of a data property found along a read-plain chain. -/
theorem getVProp_read (O : ObjId) (k : PropKey) (s : State) (m : Nat) (hc : ReadChain s m O k) (hm : m ≤ 9000)
    {v : Value} {w e c : Bool} (hl : ordLookup s m O k = some (.data v w e c)) :
    getVProp (.obj O) k s = .ok v s := by
  have hg := get_readChain s k (.obj O) m O 19999 hc (by omega) (by simp [hl, noAccessor])
  rw [hl] at hg
  unfold getVProp
  rw [show maxDepth = 19999 + 1 from rfl]
  simp only [getV]
  simpa [ownDataValue] using hg

/-- `GetMethod` of a property absent along a read-plain chain: none. -/
theorem getMethodOf_absent (O : ObjId) (k : PropKey) (s : State) (m : Nat) (hc : ReadChain s m O k) (hm : m ≤ 9000)
    (hl : ordLookup s m O k = none) :
    getMethodOf (.obj O) k s = .ok none s := by
  have hg := get_readChain s k (.obj O) m O 19998 hc (by omega) (by simp [hl, noAccessor])
  rw [hl] at hg
  unfold getMethodOf
  rw [show maxDepth = 19998 + 1 + 1 from rfl]
  simp only [getMethod, getV, M.bind_eq, M.bind_apply]
  simp [hg, ownDataValue, Value.isNullish, M.bindRes_ok, Pure.pure, M.pure]

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ}

/-- The pattern `[a, b]`. -/
def pairPat (a b : JSStr) : Pattern :=
  .arr #[some (.mk (.ident a) none), some (.mk (.ident b) none)] none

@[simp] theorem objEntry_push_new (s : State) (ob : Obj) :
    State.objEntry { s with heap := s.heap.push ob } s.heap.size = ob := by
  simp [State.objEntry]

theorem objEntry_push_old (s : State) (ob : Obj) (o : ObjId) (h : o < s.heap.size) :
    State.objEntry { s with heap := s.heap.push ob } o = s.objEntry o := by
  simp [State.objEntry, Array.getElem?_push, Nat.ne_of_lt h]

theorem foldList_cons_bind {α β : Type} (a : α) (l : List α) (b : β) (f : β → α → M β) :
    foldList (a :: l) b f = (f b a).bind (fun b' => foldList l b' f) := by
  funext s; rfl

theorem foldList_nil_pure {α β : Type} (b : β) (f : β → α → M β) : foldList [] b f = M.pure b := by
  funext s; rfl

theorem wp_mbind {α β : Type} {n : Nat} {h : σ} {x : M α} {g : α → M β} {s : State} {Q : β → State → σ → Prop}
    (hw : WP eng answer n h x s fun a w h1 => WP eng answer n h1 (g a) w Q) :
    WP eng answer n h (x.bind g) s Q := wp_bind hw

/-- A handler around a computation that ends normally (or calls). -/
theorem wp_tryCatch {α : Type} {n : Nat} {h : σ} {x : M α} {hd : Value → M α} {s : State} {Q : α → State → σ → Prop}
    (hw : WP eng answer n h x s Q) : WP eng answer n h (x.tryCatch hd) s Q := by
  rw [wp_iff_wpr] at hw ⊢
  exact wpr_tryCatch hw

theorem resolve_here (s : State) (env : EnvId) (x : JSStr) {bm : HashMap JSStr Binding} {o : Option EnvId}
    (hE : env < s.envs.size) (hd : Scope.declLike? (s.envEntry env) = some (bm, o)) (hx : bm.contains x = true) :
    Scope.resolve s 1 env x = some env := by
  simp [Scope.resolve, hE, hd, hx]

/-- InitializeReferencedBinding of a name in a declarative or function record. -/
theorem initRef_eq (env : EnvId) (x : JSStr) (st : Bool) (v : Value) (s : State) {bm : HashMap JSStr Binding}
    {o : Option EnvId} (hE : env < s.envs.size) (hd : Scope.declLike? (s.envEntry env) = some (bm, o)) :
    initializeRefBinding (.env (some env) x st) v s =
      .ok () (s.withEnvs (·.modify env (·.withBindings (·.modify x fun bd => { bd with value := some v })))) := by
  simp only [initializeRefBinding, initializeBinding, M.bind_eq, M.bind_apply, readEnv_entry env _ s hE, M.bindRes_ok, id]
  cases hen : s.envEntry env <;> rw [hen] at hd <;> simp [Scope.declLike?] at hd <;> simp [modifyEnv]


theorem kDone_ne_kValue : (PropKey.str kDone == PropKey.str kValue) = false := by decide
theorem kDone_ne_kValue' : kDone ≠ kValue := by decide

section NextState
variable (s : State) (It A : ObjId) (i : Nat) (v : Value)

theorem nextState_size : (nextState s It A i v).heap.size = s.heap.size + 1 := by
  simp [nextState, State.withHeap, Array.size_modify]

theorem nextState_res_kind (hIt : It < s.heap.size) :
    ((nextState s It A i v).objEntry s.heap.size).kind = .ordinary := by
  simp [nextState, State.objEntry, State.withHeap, Array.getElem?_modify, Array.getElem?_push, Array.size_modify, Array.getElem_modify, Array.getElem_push,
    Nat.ne_of_lt hIt, Ne.symm (Nat.ne_of_lt hIt)]

theorem nextState_res_done (hIt : It < s.heap.size) :
    ((nextState s It A i v).objEntry s.heap.size).props.get? (.str kDone) = some (.data (.bool false) true true true) := by
  simp [nextState, State.objEntry, State.withHeap, Array.getElem?_modify, Array.getElem?_push, Array.size_modify, Array.getElem_modify, Array.getElem_push,
    Nat.ne_of_lt hIt, Ne.symm (Nat.ne_of_lt hIt), Obj.withProps, PropMap.get?_insert]

theorem nextState_res_value (hIt : It < s.heap.size) :
    ((nextState s It A i v).objEntry s.heap.size).props.get? (.str kValue) = some (.data v true true true) := by
  simp [nextState, State.objEntry, State.withHeap, Array.getElem?_modify, Array.getElem?_push, Array.size_modify, Array.getElem_modify, Array.getElem_push,
    Nat.ne_of_lt hIt, Ne.symm (Nat.ne_of_lt hIt), Obj.withProps, PropMap.get?_insert, kDone_ne_kValue, kDone_ne_kValue']

theorem nextState_envs : (nextState s It A i v).envs = s.envs := by simp [nextState, State.withHeap]

theorem nextState_old (o : ObjId) (ho : o < s.heap.size) (hoIt : o ≠ It) (hIt : It < s.heap.size) :
    (nextState s It A i v).objEntry o = s.objEntry o := by
  simp [nextState, State.objEntry, State.withHeap, Array.getElem?_modify, Array.getElem?_push, Array.size_modify, Array.getElem_modify, Array.getElem_push,
    Nat.ne_of_lt ho, hoIt, Ne.symm hoIt, Nat.ne_of_gt ho, Nat.ne_of_lt hIt, Nat.ne_of_gt hIt]

theorem nextState_iter (hIt : It < s.heap.size) :
    ((nextState s It A i v).objEntry It).kind =
      .internal "Array Iterator" #[.obj A, .num (Conv.ofNat (i + 1)), .num (Conv.ofNat 1)] := by
  simp [nextState, State.objEntry, State.withHeap, Array.getElem?_modify, Array.getElem?_push, Array.size_modify, Array.getElem_modify, Array.getElem_push,
    Nat.ne_of_lt hIt, Nat.ne_of_gt hIt, hIt]

theorem nextState_iter_proto (hIt : It < s.heap.size) :
    ((nextState s It A i v).objEntry It).proto = (s.objEntry It).proto := by
  simp [nextState, State.objEntry, State.withHeap, Array.getElem?_modify, Array.getElem?_push, Array.size_modify,
    Array.getElem_modify, Array.getElem_push, Nat.ne_of_lt hIt, Nat.ne_of_gt hIt, hIt]

theorem nextState_iter_props (hIt : It < s.heap.size) :
    ((nextState s It A i v).objEntry It).props = (s.objEntry It).props := by
  simp [nextState, State.objEntry, State.withHeap, Array.getElem?_modify, Array.getElem?_push, Array.size_modify,
    Array.getElem_modify, Array.getElem_push, Nat.ne_of_lt hIt, Nat.ne_of_gt hIt, hIt]

end NextState

/-- The state after one element of `[a, b]`: the iterator's step, then the binding initialized. -/
def elemState (s : State) (It A : ObjId) (i : Nat) (v : Value) (env : EnvId) (x : JSStr) : State :=
  ({ nextState { s with fuel := s.fuel - 1 } It A i v with realm := s.realm, script := s.script }).withEnvs
    (·.modify env (·.withBindings (·.modify x fun bd => { bd with value := some v })))

section ElemState
variable (s : State) (It A : ObjId) (i : Nat) (v : Value) (env : EnvId) (x : JSStr)

theorem elemState_objEntry (o : ObjId) :
    (elemState s It A i v env x).objEntry o = (nextState { s with fuel := s.fuel - 1 } It A i v).objEntry o := rfl

theorem elemState_size : (elemState s It A i v env x).heap.size = s.heap.size + 1 := by
  simp [elemState, State.withEnvs, nextState_size]

theorem elemState_fuel : (elemState s It A i v env x).fuel = s.fuel - 1 := by
  simp [elemState, State.withEnvs, nextState, State.withHeap]

theorem elemState_envs_size : (elemState s It A i v env x).envs.size = s.envs.size := by
  simp [elemState, State.withEnvs, nextState_envs]

theorem elemState_declLike {bm : HashMap JSStr Binding} {o : Option EnvId} (hE : env < s.envs.size)
    (hd : Scope.declLike? (s.envEntry env) = some (bm, o)) :
    Scope.declLike? ((elemState s It A i v env x).envEntry env) =
      some (bm.modify x (fun bd => { bd with value := some v }), o) := by
  simp only [elemState, State.withEnvs, State.envEntry, nextState_envs, Array.getElem?_modify]
  simp only [State.envEntry] at hd
  simp [hE] at hd ⊢
  cases hen : s.envs[env] <;> rw [hen] at hd <;> simp [Scope.declLike?] at hd <;> obtain ⟨rfl, rfl⟩ := hd <;>
    simp [Env.withBindings, Scope.declLike?]

end ElemState

set_option maxRecDepth 20000 in
/-- **One element of `[a, b]`**: the name's reference, the iterator's next value (element `i`), its binding
initialized. -/
theorem elem_spec {n k : Nat} {h : σ} {ctx : Ctx} {env : EnvId} {x : JSStr} {It A fN : ObjId} {bdN : BuiltinData}
    {i : Nat} {v : Value} {L : F64} {bm : HashMap JSStr Binding} {o : Option EnvId} {s : State}
    {lw le lc w e c : Bool}
    (hIt : It < s.heap.size) (hItk : (s.objEntry It).kind = .internal "Array Iterator" #[.obj A, numV i, numV 1])
    (hA : A < s.heap.size) (hAk : (s.objEntry A).kind = .array) (hItA : It ≠ A)
    (hL : (s.objEntry A).props.get? (.str kLength) = some (.data (.num L) lw le lc)) (hi : i < lenOf L)
    (hidx : (Conv.toNat? (Conv.ofNat i)).getD 0 = i)
    (hv : (s.objEntry A).props.get? (PropKey.ofNat i) = some (.data v w e c))
    (hN : fN < s.heap.size) (hNk : (s.objEntry fN).kind = .builtin bdN)
    (hNfn : eng.builtins[bdN.id]? = some ES.arrayIteratorNext) (hNr : bdN.realm = s.realm)
    (hE : env < s.envs.size) (hd : Scope.declLike? (s.envEntry env) = some (bm, o)) (hx : bm.contains x = true)
    (hf : 10 ≤ s.fuel) :
    WP eng answer (n + 1) h (bindIterElement (k + 5) ctx (some (.mk (.ident x) none))
      { iter := .obj It, next := .obj fN } (.init (some env))) s fun r w' h' =>
        r = { iter := .obj It, next := .obj fN } ∧ w' = elemState s It A i v env x ∧ h' = h := by
  simp only [bindIterElement, targetRefOf, withIterClose, M.bind_eq]
  apply wp_mbind
  have hres := Scope.resolveBinding_of_resolve s 1 env x ctx.strict env (resolve_here s env x hE hd hx) (by omega)
  apply wp_tryCatch
  apply wp_mbind
  refine wp_of_eq hres ?_
  refine wp_of_eq rfl ?_
  simp only [Bool.false_eq_true, ↓reduceIte, iteratorStepValue, iteratorNext, M.bind_eq]
  apply wp_mbind
  apply wp_mbind
  apply wp_tryCatch
  apply wp_mbind
  refine wp_call (wp_mono (next_spec (n := n) hN hNk hNfn (by omega) hNr hIt hItk hA hAk hL hi hidx hv hItA) ?_)
  intro r1 s1 h1 ⟨hr1, hs1, hh1⟩
  subst hr1 hs1 hh1
  simp only [Value.isObject, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  refine wp_of_eq rfl ?_
  simp only [iteratorComplete, iteratorValue, M.bind_eq]
  apply wp_mbind
  apply wp_mbind
  refine wp_of_eq (getVProp_read s.heap.size (.str kDone) _ 1 ?ch1 (by omega) (v := .bool false) (w := true) (e := true) (c := true) ?lk1) ?_
  case ch1 => refine ⟨by show s.heap.size < (nextState { s with fuel := s.fuel - 1 } It A i v).heap.size; rw [nextState_size]; exact Nat.lt_succ_self _, by show ((nextState { s with fuel := s.fuel - 1 } It A i v).objEntry s.heap.size).kind.isReadPlain = true; rw [nextState_res_kind { s with fuel := s.fuel - 1 } It A i v hIt]; rfl, fun h => by change ((nextState { s with fuel := s.fuel - 1 } It A i v).objEntry s.heap.size).props.get? (.str kDone) = none at h; rw [nextState_res_done { s with fuel := s.fuel - 1 } It A i v hIt] at h; cases h⟩
  case lk1 => show ordLookup (nextState { s with fuel := s.fuel - 1 } It A i v) 1 s.heap.size (.str kDone) = _; simp only [ordLookup, nextState_res_done { s with fuel := s.fuel - 1 } It A i v hIt]
  refine wp_of_eq rfl ?_
  simp only [toBoolean, Bool.false_eq_true, ↓reduceIte]
  apply wp_mbind
  refine wp_of_eq (getVProp_read s.heap.size (.str kValue) _ 1 ?ch2 (by omega) (v := v) (w := true) (e := true) (c := true) ?lk2) ?_
  case ch2 => refine ⟨by show s.heap.size < (nextState { s with fuel := s.fuel - 1 } It A i v).heap.size; rw [nextState_size]; exact Nat.lt_succ_self _, by show ((nextState { s with fuel := s.fuel - 1 } It A i v).objEntry s.heap.size).kind.isReadPlain = true; rw [nextState_res_kind { s with fuel := s.fuel - 1 } It A i v hIt]; rfl, fun h => by change ((nextState { s with fuel := s.fuel - 1 } It A i v).objEntry s.heap.size).props.get? (.str kValue) = none at h; rw [nextState_res_value { s with fuel := s.fuel - 1 } It A i v hIt] at h; cases h⟩
  case lk2 => show ordLookup (nextState { s with fuel := s.fuel - 1 } It A i v) 1 s.heap.size (.str kValue) = _; simp only [ordLookup, nextState_res_value { s with fuel := s.fuel - 1 } It A i v hIt]
  refine wp_of_eq rfl ?_
  apply wp_mbind
  apply wp_tryCatch
  apply wp_mbind
  refine wp_of_eq rfl ?_
  simp only [Option.getD_some, putTarget]
  refine wp_of_eq (initRef_eq env x ctx.strict v _ (bm := bm) (o := o) ?hE2 ?hd2) ?_
  case hE2 => show env < (nextState { s with fuel := s.fuel - 1 } It A i v).envs.size; rw [nextState_envs]; exact hE
  case hd2 => show Scope.declLike? ((nextState { s with fuel := s.fuel - 1 } It A i v).envEntry env) = _; simp only [State.envEntry, nextState_envs]; exact hd
  exact wp_of_eq rfl ⟨rfl, rfl, rfl⟩

/-- **A destructuring declarator** (`const [a, b] = e`): the initializer, then the pattern bound to its value. -/
theorem wp_declPat {n : Nat} {h : σ} {rhs : Sem.CExpr} {bind : Ctx → Value → M Unit} {ctx : Ctx} {s : State}
    {Q : Unit → State → σ → Prop}
    (hw : WP eng answer n h (rhs ctx) s fun v w h1 => WP eng answer n h1 (bind ctx v) w Q) :
    WP eng answer n h (Sem.declPat rhs bind ctx) s Q := wp_bind hw

set_option maxRecDepth 20000 in
/-- **`const [a, b] = arr`** for an array `arr` with two elements, the realm's iterator built-ins untouched: `a` and
`b` initialized to the elements; the iterator and the two result objects allocated (fresh); nothing else changed. -/
theorem bindPair_spec {n k : Nat} {h : σ} {ctx : Ctx} {env : EnvId} {a b : JSStr} {A AP fV fN AIP IP OP : ObjId}
    {bdV bdN : BuiltinData} {v0 v1 : Value} {L : F64} {bm : HashMap JSStr Binding} {o : Option EnvId} {s : State}
    {pw pe pc nw ne nc lw le lc w0 e0 c0 w1 e1 c1 : Bool} {Q : Unit → State → σ → Prop}
    (hA : A < s.heap.size) (hAk : (s.objEntry A).kind = .array)
    (hAn : (s.objEntry A).props.get? (.sym WK.iterator) = none) (hAp : (s.objEntry A).proto = .obj AP)
    (hP : AP < s.heap.size) (hPk : (s.objEntry AP).kind.isReadPlain = true)
    (hPv : (s.objEntry AP).props.get? (.sym WK.iterator) = some (.data (.obj fV) pw pe pc))
    (hV : fV < s.heap.size) (hVk : (s.objEntry fV).kind = .builtin bdV)
    (hVfn : eng.builtins[bdV.id]? = some (ES.arrayProtoValues 1)) (hVr : bdV.realm = s.realm)
    (hI : s.curRealm.intrinsics["%ArrayIteratorPrototype%"]? = some AIP)
    (hAIP : AIP < s.heap.size) (hAIPk : (s.objEntry AIP).kind.isReadPlain = true)
    (hAIPn : (s.objEntry AIP).props.get? (.str kNext) = some (.data (.obj fN) nw ne nc))
    (hN : fN < s.heap.size) (hNk : (s.objEntry fN).kind = .builtin bdN)
    (hNfn : eng.builtins[bdN.id]? = some ES.arrayIteratorNext) (hNr : bdN.realm = s.realm)
    (hL : (s.objEntry A).props.get? (.str kLength) = some (.data (.num L) lw le lc)) (hL2 : 2 ≤ lenOf L)
    (h0 : (s.objEntry A).props.get? (PropKey.ofNat 0) = some (.data v0 w0 e0 c0))
    (h1 : (s.objEntry A).props.get? (PropKey.ofNat 1) = some (.data v1 w1 e1 c1))
    (hAIPp : (s.objEntry AIP).proto = .obj IP) (hAIPr : (s.objEntry AIP).props.get? (.str "return") = none)
    (hIP : IP < s.heap.size) (hIPk : (s.objEntry IP).kind.isReadPlain = true)
    (hIPr : (s.objEntry IP).props.get? (.str "return") = none) (hIPp : (s.objEntry IP).proto = .obj OP)
    (hOP : OP < s.heap.size) (hOPk : (s.objEntry OP).kind.isReadPlain = true)
    (hOPr : (s.objEntry OP).props.get? (.str "return") = none) (hOPp : (s.objEntry OP).proto = .null)
    (hE : env < s.envs.size) (hd : Scope.declLike? (s.envEntry env) = some (bm, o))
    (ha : bm.contains a = true) (hb : bm.contains b = true)
    (hf : 20 ≤ s.fuel) :
    WP eng answer (n + 1) h (bindPattern (k + 6) ctx (pairPat a b) (.obj A) (.init (some env))) s fun _ w h' =>
      w = elemState (elemState { s with fuel := s.fuel - 1, heap := s.heap.push (iterObj AIP A) } s.heap.size A 0 v0 env a)
        s.heap.size A 1 v1 env b ∧ h' = h := by
  simp only [pairPat, bindPattern, M.bind_eq]
  apply wp_mbind
  -- (GetIterator: @@iterator found on Array.prototype, called, `next` read)
  simp only [getIterator, M.bind_eq]
  apply wp_mbind
  refine wp_of_eq (getMethod_iterator A AP fV bdV s hA (by simp [hAk, Kind.isReadPlain]) hAn hAp hP hPk hPv hV hVk) ?_
  simp only [getIteratorFromMethod, M.bind_eq]
  apply wp_mbind
  refine wp_call (wp_mono (values_spec (n := n) hV hVk hVfn (by omega) hVr hA hAk hI) ?_)
  intro it s1 h1' ⟨hit, hs1, hh⟩
  subst hit hs1 hh
  simp only [Value.isObject, Bool.not_true, Bool.false_eq_true, ↓reduceIte, getIteratorDirect, M.bind_eq]
  apply wp_mbind
  have hAIP1 : State.objEntry { s with fuel := s.fuel - 1, heap := s.heap.push (iterObj AIP A) } AIP = s.objEntry AIP := by
    simp [State.objEntry, Array.getElem?_push, Nat.ne_of_lt hAIP]
  have hItn : ∀ k, (iterObj AIP A).props.get? k = none := fun k => by simp [iterObj, PropMap.get?_empty]
  have hIt1 : State.objEntry { s with fuel := s.fuel - 1, heap := s.heap.push (iterObj AIP A) } s.heap.size = iterObj AIP A := by
    simp [State.objEntry]
  refine wp_of_eq (getVProp_read s.heap.size (.str kNext) _ 2 ?ch (by omega) (v := .obj fN) (w := nw) (e := ne) (c := nc) ?lk) ?_
  case ch =>
    refine ⟨by simp, by rw [hIt1]; simp [iterObj, Kind.isReadPlain], fun _ => ?_⟩
    rw [hIt1, show (iterObj AIP A).proto = .obj AIP from rfl]
    exact ⟨by simp; exact Nat.lt_succ_of_lt hAIP, by rw [hAIP1]; exact hAIPk, fun h => by rw [hAIP1] at h; simp [hAIPn] at h⟩
  case lk =>
    simp only [ordLookup, hIt1, show (iterObj AIP A).proto = .obj AIP from rfl, hAIP1, hAIPn,
      hItn]
  refine wp_of_eq rfl ?_
  simp only [foldArr_toArray, List.toArray]
  apply wp_mbind
  rw [foldList_cons_bind]
  apply wp_mbind
  -- (`a`: element 0)
  have hItk1 : (State.objEntry { s with fuel := s.fuel - 1, heap := s.heap.push (iterObj AIP A) } s.heap.size).kind =
      .internal "Array Iterator" #[.obj A, numV 0, numV 1] := by rw [hIt1]; rfl
  have hA1 : State.objEntry { s with fuel := s.fuel - 1, heap := s.heap.push (iterObj AIP A) } A = s.objEntry A := by
    simp [State.objEntry, Array.getElem?_push, Nat.ne_of_lt hA]
  have hN1 : State.objEntry { s with fuel := s.fuel - 1, heap := s.heap.push (iterObj AIP A) } fN = s.objEntry fN := by
    simp [State.objEntry, Array.getElem?_push, Nat.ne_of_lt hN]
  refine wp_mono (elem_spec (n := n) (k := k) (ctx := ctx) (bm := bm) (o := o) (v := v0) (L := L) (i := 0)
    (by simp) hItk1 (by simp; exact Nat.lt_succ_of_lt hA) (by rw [hA1]; exact hAk) (Nat.ne_of_gt hA)
    (by rw [hA1]; exact hL) (by omega) (by decide) (by rw [hA1]; exact h0)
    (by simp; exact Nat.lt_succ_of_lt hN) (by rw [hN1]; exact hNk) hNfn hNr hE (by simpa [State.envEntry] using hd) ha
    (by simp; omega)) ?_
  intro r1 w1 h2 ⟨hr1, hw1, hh2⟩
  subst hr1 hw1 hh2
  rw [foldList_cons_bind]
  apply wp_mbind
  -- (`b`: element 1)
  have hS1 : ({ s with fuel := s.fuel - 1, heap := s.heap.push (iterObj AIP A) }).heap.size = s.heap.size + 1 := by simp
  have hItS : s.heap.size < ({ s with fuel := s.fuel - 1, heap := s.heap.push (iterObj AIP A) }).heap.size := by rw [hS1]; exact Nat.lt_succ_self _
  have hAS : A < ({ s with fuel := s.fuel - 1, heap := s.heap.push (iterObj AIP A) }).heap.size := by rw [hS1]; exact Nat.lt_succ_of_lt hA
  have hNS : fN < ({ s with fuel := s.fuel - 1, heap := s.heap.push (iterObj AIP A) }).heap.size := by rw [hS1]; exact Nat.lt_succ_of_lt hN
  have old : ∀ o, o < s.heap.size → State.objEntry (elemState ({ s with fuel := s.fuel - 1, heap := s.heap.push (iterObj AIP A) }) s.heap.size A 0 v0 env a) o = s.objEntry o :=
    fun o ho => by
      rw [elemState_objEntry, nextState_old _ _ _ _ _ o (by simpa using Nat.lt_succ_of_lt ho) (Nat.ne_of_lt ho)
        (by simpa using Nat.lt_succ_self s.heap.size)]
      simp [State.objEntry, Array.getElem?_push, Nat.ne_of_lt ho]
  refine wp_mono (elem_spec (n := n) (k := k) (ctx := ctx) (bm := bm.modify a (fun bd => { bd with value := some v0 }))
    (o := o) (v := v1) (L := L) (i := 1)
    (by rw [elemState_size]; simp only [Array.size_push]; exact Nat.lt_succ_of_lt (Nat.lt_succ_self _))
    (by rw [elemState_objEntry]; exact nextState_iter _ _ _ _ _ (by simp))
    (by rw [elemState_size]; simp only [Array.size_push]; exact Nat.lt_succ_of_lt (Nat.lt_succ_of_lt hA)) (by rw [old A hA]; exact hAk) (Nat.ne_of_gt hA)
    (by rw [old A hA]; exact hL) (by omega) (by decide) (by rw [old A hA]; exact h1)
    (by rw [elemState_size]; simp only [Array.size_push]; exact Nat.lt_succ_of_lt (Nat.lt_succ_of_lt hN))
    (by rw [old fN hN]; exact hNk) hNfn
    (by simp [elemState, State.withEnvs]; exact hNr)
    (by rw [elemState_envs_size]; exact hE)
    (elemState_declLike _ _ _ _ _ _ _ hE (by simpa [State.envEntry] using hd))
    (by simp [Std.HashMap.contains_modify, hb])
    (by rw [elemState_fuel]; simp; omega)) ?_
  intro r2 w2 h3 ⟨hr2, hw2, hh3⟩
  subst hr2 hw2 hh3
  rw [foldList_nil_pure]
  refine wp_of_eq rfl ?_
  apply wp_mbind
  refine wp_of_eq rfl ?_
  simp only [Bool.not_false, ↓reduceIte, iteratorClose, M.bind_eq]
  apply wp_mbind
  -- (no `return` on the iterator's chain: nothing to close)
  have old2 : ∀ o, o < s.heap.size →
      State.objEntry (elemState (elemState ({ s with fuel := s.fuel - 1, heap := s.heap.push (iterObj AIP A) }) s.heap.size A 0 v0 env a) s.heap.size A 1 v1 env b) o =
        s.objEntry o := fun o ho => by
    rw [elemState_objEntry, nextState_old _ _ _ _ _ o
      (by show o < (elemState ({ s with fuel := s.fuel - 1, heap := s.heap.push (iterObj AIP A) }) s.heap.size A 0 v0 env a).heap.size; rw [elemState_size]; simp only [Array.size_push]; exact Nat.lt_succ_of_lt (Nat.lt_succ_of_lt ho))
      (Nat.ne_of_lt ho)
      (by show s.heap.size < (elemState ({ s with fuel := s.fuel - 1, heap := s.heap.push (iterObj AIP A) }) s.heap.size A 0 v0 env a).heap.size; rw [elemState_size]; simp only [Array.size_push]; exact Nat.lt_succ_of_lt (Nat.lt_succ_self _))]
    exact old o ho
  have itP : (State.objEntry (elemState (elemState ({ s with fuel := s.fuel - 1, heap := s.heap.push (iterObj AIP A) }) s.heap.size A 0 v0 env a) s.heap.size A 1 v1 env b)
      s.heap.size).proto = .obj AIP := by
    rw [elemState_objEntry, nextState_iter_proto _ _ _ _ _ (by show s.heap.size < (elemState ({ s with fuel := s.fuel - 1, heap := s.heap.push (iterObj AIP A) }) s.heap.size A 0 v0 env a).heap.size; rw [elemState_size]; simp only [Array.size_push]; exact Nat.lt_succ_of_lt (Nat.lt_succ_self _)), show ∀ t : State, ({ t with fuel := t.fuel - 1 } : State).objEntry s.heap.size = t.objEntry s.heap.size from fun _ => rfl,
      elemState_objEntry, nextState_iter_proto _ _ _ _ _ (by simp)]
    simp [State.objEntry, iterObj]
  have itR : ∀ k, (State.objEntry (elemState (elemState ({ s with fuel := s.fuel - 1, heap := s.heap.push (iterObj AIP A) }) s.heap.size A 0 v0 env a) s.heap.size A 1 v1 env b)
      s.heap.size).props.get? k = none := fun k => by
    rw [elemState_objEntry, nextState_iter_props _ _ _ _ _ (by show s.heap.size < (elemState ({ s with fuel := s.fuel - 1, heap := s.heap.push (iterObj AIP A) }) s.heap.size A 0 v0 env a).heap.size; rw [elemState_size]; simp only [Array.size_push]; exact Nat.lt_succ_of_lt (Nat.lt_succ_self _)), show ∀ t : State, ({ t with fuel := t.fuel - 1 } : State).objEntry s.heap.size = t.objEntry s.heap.size from fun _ => rfl,
      elemState_objEntry, nextState_iter_props _ _ _ _ _ (by simp)]
    simp [State.objEntry, iterObj, PropMap.get?_empty]
  have hsz : ∀ o, o < s.heap.size + 1 → o < (elemState (elemState ({ s with fuel := s.fuel - 1, heap := s.heap.push (iterObj AIP A) }) s.heap.size A 0 v0 env a) s.heap.size A 1 v1 env b).heap.size := fun o ho => by
    rw [elemState_size, elemState_size]; simp only [Array.size_push]; exact Nat.lt_succ_of_lt (Nat.lt_succ_of_lt ho)
  have itK : (State.objEntry (elemState (elemState ({ s with fuel := s.fuel - 1, heap := s.heap.push (iterObj AIP A) }) s.heap.size A 0 v0 env a) s.heap.size A 1 v1 env b) s.heap.size).kind.isReadPlain = true := by
    rw [elemState_objEntry, nextState_iter _ _ _ _ _ (by show s.heap.size < (elemState ({ s with fuel := s.fuel - 1, heap := s.heap.push (iterObj AIP A) }) s.heap.size A 0 v0 env a).heap.size; rw [elemState_size]; simp only [Array.size_push]; exact Nat.lt_succ_of_lt (Nat.lt_succ_self _))]
    rfl
  refine wp_of_eq (getMethodOf_absent s.heap.size (.str "return") _ 4 ?ch (by omega) ?lk) ?_
  case ch =>
    refine ⟨hsz _ (Nat.lt_succ_self _), itK, fun _ => ?_⟩
    rw [itP]
    refine ⟨hsz _ (Nat.lt_succ_of_lt hAIP), by rw [old2 AIP hAIP]; exact hAIPk, fun _ => ?_⟩
    rw [old2 AIP hAIP, hAIPp]
    refine ⟨hsz _ (Nat.lt_succ_of_lt hIP), by rw [old2 IP hIP]; exact hIPk, fun _ => ?_⟩
    rw [old2 IP hIP, hIPp]
    refine ⟨hsz _ (Nat.lt_succ_of_lt hOP), by rw [old2 OP hOP]; exact hOPk, fun _ => ?_⟩
    rw [old2 OP hOP, hOPp]
    trivial
  case lk =>
    simp only [ordLookup, itR, itP, old2 AIP hAIP, hAIPr, hAIPp, old2 IP hIP, hIPr, hIPp, old2 OP hOP, hOPr, hOPp]
  exact wp_of_eq rfl ⟨rfl, rfl⟩

end

end Logic
