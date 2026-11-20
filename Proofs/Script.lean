import Proofs.DTScript

/-!
# Scripts in general: declarations, then statements run by the driver

For a script whose top level declares simple functions (distinct names, non-strict, not async or
generators) and `let` bindings of identifiers, and no Annex B functions:

* `gdi_simple`: GlobalDeclarationInstantiation ends in `instAll … (t with the lets declared)`: each
  function object created and bound on the global object, in source order;
* `instAll_facts`: where each function object is and what it is, what the global object holds, and
  that nothing else that existed changed;
* `DrivesTo` and `script_value`: the script's value is what its body's result drives to, with
  `drivesTo_call` for each call the driver answers.
-/

open ES
open Std (HashMap)

namespace Script

/-! ## Folds with an abstract step -/

theorem foldList_const {α β : Type} (l : List α) (b : β) (f : β → α → M β) (t : State)
    (hf : ∀ x ∈ l, f b x t = .ok b t) : M.foldList l b f t = .ok b t := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [M.foldList_cons, hf a (List.mem_cons_self ..), M.bindRes_ok]
    exact ih (fun x hx => hf x (List.mem_cons_of_mem _ hx))

theorem setEnv_self (t : State) (e : EnvId) (h : e < t.envs.size) : t.setEnv e (t.envEntry e) = t := by
  rw [State.envEntry_of _ _ h]
  cases t with
  | mk heap envs =>
    simp only [State.setEnv, State.mk.injEq, and_true, true_and]
    apply Array.ext (by simp)
    intro i h1 h2
    simp only [Array.getElem_modify]
    split <;> simp_all

/-- The global record's declarative part after `let` declarations of `lets`. -/
def insertLets (gb : HashMap JSStr Binding) (lets : List JSStr) : HashMap JSStr Binding :=
  lets.foldl (fun m x => m.insert x { deletable := false }) gb

theorem foldList_lets (ge g : Nat) (gtv : Value) (f : Unit → LexScoped → M Unit) :
    ∀ (lets : List JSStr) (gb : HashMap JSStr Binding) (t : State), ge < t.envs.size →
      t.envEntry ge = .global g gb gtv →
      (∀ x ∈ lets, ∀ (u : State) (gb' : HashMap JSStr Binding), ge < u.envs.size →
        u.envEntry ge = .global g gb' gtv →
        f () (.binding .let (.ident x)) u = .ok () (u.setEnv ge (.global g (gb'.insert x { deletable := false }) gtv))) →
      M.foldList (lets.map fun x => LexScoped.binding .let (.ident x)) () f t =
        .ok () (t.setEnv ge (.global g (insertLets gb lets) gtv)) := by
  intro lets
  induction lets with
  | nil =>
    intro gb t hge hE _
    simp only [List.map_nil, M.foldList_nil, insertLets, List.foldl_nil]
    congr 1
    rw [← hE, setEnv_self _ _ hge]
  | cons x lets ih =>
    intro gb t hge hE hf
    simp only [List.map_cons, M.foldList_cons, hf x (List.mem_cons_self ..) t gb hge hE, M.bindRes_ok]
    rw [ih (gb.insert x { deletable := false }) _ (by simpa using hge) (State.setEnv_envEntry_self _ _ _ hge)
      (fun y hy => hf y (List.mem_cons_of_mem _ hy))]
    simp [insertLets, List.foldl_cons]

/-- One function declaration: its object created (`Inst.instStateFn`) and bound on the global object. -/
def bindFn (ge g : Nat) (sc : Nat) (fp : ObjId) (fn : Func) (nm : JSStr) (t : State) : State :=
  let u := Inst.instStateFn fn nm t ge sc fp
  let p : Property := .data (.obj t.heap.size) true true false
  (u.setProp g (.str nm) p).setProp g (.str nm) p

/-- All of them, in order. -/
def instAll (ge g : Nat) (sc : Nat) (fp : ObjId) : List (Func × JSStr) → State → State
  | [], t => t
  | (fn, nm) :: rest, t => instAll ge g sc fp rest (bindFn ge g sc fp fn nm t)

/-- What the global object needs for the next function declaration. -/
def GoodG (g : Nat) (fp : ObjId) (t : State) : Prop :=
  g < t.heap.size ∧ (t.objEntry g).kind = .ordinary ∧ (t.objEntry g).extensible = true ∧
    t.curRealm.intrinsics["%Function.prototype%"]? = some fp

theorem bindFn_good (ge g sc fp : Nat) (fn : Func) (nm : JSStr) (t : State) (h : GoodG g fp t) :
    GoodG g fp (bindFn ge g sc fp fn nm t) ∧
    (∀ k, k ≠ PropKey.str nm → ((bindFn ge g sc fp fn nm t).objEntry g).props.get? k = (t.objEntry g).props.get? k) ∧
    ((bindFn ge g sc fp fn nm t).objEntry g).props.get? (.str nm) = some (.data (.obj t.heap.size) true true false) ∧
    ((bindFn ge g sc fp fn nm t).objEntry g).proto = (t.objEntry g).proto ∧
    (∀ x, x < t.heap.size → x ≠ g → (bindFn ge g sc fp fn nm t).objEntry x = t.objEntry x) ∧
    ((bindFn ge g sc fp fn nm t).objEntry t.heap.size).kind = .func (Inst.fnData fn t ge sc) ∧
    (bindFn ge g sc fp fn nm t).heap.size = t.heap.size + 2 ∧ (bindFn ge g sc fp fn nm t).envs = t.envs ∧
    (bindFn ge g sc fp fn nm t).fuel = t.fuel ∧ (bindFn ge g sc fp fn nm t).realms = t.realms ∧
    (bindFn ge g sc fp fn nm t).realm = t.realm := by
  obtain ⟨hgs, hk, hx, hfp⟩ := h
  have hgu : g < (Inst.instStateFn fn nm t ge sc fp).heap.size := by
    rw [Inst.instStateFn_size]; exact Nat.lt_succ_of_lt (Nat.lt_succ_of_lt hgs)
  have hug : (Inst.instStateFn fn nm t ge sc fp).objEntry g = t.objEntry g := Inst.instStateFn_entry_lt _ _ _ _ _ _ _ hgs
  have hbg : (bindFn ge g sc fp fn nm t).objEntry g = ((t.objEntry g).withProps (·.insert (.str nm)
      (.data (.obj t.heap.size) true true false))).withProps (·.insert (.str nm) (.data (.obj t.heap.size) true true false)) := by
    simp only [bindFn]
    rw [State.setProp_entry_self _ _ _ _ (by simpa using hgu), State.setProp_entry_self _ _ _ _ hgu, hug]
  have hsz : (bindFn ge g sc fp fn nm t).heap.size = t.heap.size + 2 := by
    simp [bindFn, Inst.instStateFn_size]
  have hcr : (bindFn ge g sc fp fn nm t).curRealm = t.curRealm := by
    simp [bindFn, State.curRealm, Inst.instStateFn_realms, Inst.instStateFn_realm]
  have hgfn : g ≠ t.heap.size := Nat.ne_of_lt hgs
  refine ⟨⟨by rw [hsz]; exact Nat.lt_of_lt_of_le hgs (Nat.le_add_right _ _), by rw [hbg]; simp [hk],
      by rw [hbg]; simp [hx], by rw [hcr]; exact hfp⟩, fun k hkn => ?_, ?_, by rw [hbg]; simp, fun x hx hxg => ?_,
    ?_, hsz, by simp [bindFn, Inst.instStateFn_envs], by simp [bindFn, Inst.instStateFn_fuel],
    by simp [bindFn, Inst.instStateFn_realms], by simp [bindFn, Inst.instStateFn_realm]⟩
  · rw [hbg, Obj.withProps_props, Obj.withProps_props, PropMap.get?_insert_ne _ _ _ _ (Ne.symm hkn),
      PropMap.get?_insert_ne _ _ _ _ (Ne.symm hkn)]
  · rw [hbg]; simp
  · simp only [bindFn]
    rw [State.setProp_entry_ne _ _ _ _ _ (Ne.symm hxg), State.setProp_entry_ne _ _ _ _ _ (Ne.symm hxg),
      Inst.instStateFn_entry_lt _ _ _ _ _ _ _ hx]
  · simp only [bindFn]
    rw [State.setProp_entry_ne _ _ _ _ _ hgfn, State.setProp_entry_ne _ _ _ _ _ hgfn, Inst.instStateFn_func]

theorem foldList_fns (ge g sc fp : Nat) (f : Unit → Func → M Unit) :
    ∀ (fs : List (Func × JSStr)) (t : State), GoodG g fp t → (fs.map Prod.snd).Nodup →
      (∀ p ∈ fs, (t.objEntry g).props.get? (.str p.2) = none) →
      (∀ p ∈ fs, ∀ u, GoodG g fp u → (u.objEntry g).props.get? (.str p.2) = none →
        f () p.1 u = .ok () (bindFn ge g sc fp p.1 p.2 u)) →
      M.foldList (fs.map Prod.fst) () f t = .ok () (instAll ge g sc fp fs t) := by
  intro fs
  induction fs with
  | nil => intro t _ _ _ _; simp [instAll]
  | cons p rest ih =>
    intro t hg hnd hnone hf
    obtain ⟨fn, nm⟩ := p
    simp only [List.map_cons, M.foldList_cons]
    rw [hf (fn, nm) (List.mem_cons_self ..) t hg (hnone _ (List.mem_cons_self ..)), M.bindRes_ok]
    have hb := bindFn_good ge g sc fp fn nm t hg
    simp only [List.map_cons, List.nodup_cons] at hnd
    rw [ih _ hb.1 hnd.2 (fun q hq => ?_) (fun q hq => hf q (List.mem_cons_of_mem _ hq))]
    · rfl
    · have hne : PropKey.str q.2 ≠ PropKey.str nm := by
        intro h; injection h with h; exact hnd.1 (h ▸ List.mem_map_of_mem hq)
      rw [hb.2.1 _ hne]; exact hnone q (List.mem_cons_of_mem _ hq)

theorem lexNames_eq (lets : List JSStr) :
    (lets.map fun x => LexScoped.binding .let (.ident x)).toArray.foldl (fun acc d => acc ++ d.names) #[] =
      lets.toArray := by
  have : ∀ (acc : Array JSStr), List.foldl (fun acc d => acc ++ LexScoped.names d) acc
      (lets.map fun x => LexScoped.binding .let (.ident x)) = acc ++ lets.toArray := by
    induction lets with
    | nil => intro acc; simp
    | cons x l ih =>
      intro acc
      have hx : LexScoped.names (.binding .let (.ident x)) = #[x] := rfl
      simp only [List.map_cons, List.foldl_cons]; rw [ih, hx]; simp
  simpa using this #[]

theorem varNames_eq (fs : List (Func × JSStr)) (h : ∀ p ∈ fs, p.1.name = some p.2) :
    (fs.map fun p => VarScoped.func p.1).toArray.foldl (fun acc d => acc ++ d.names) #[] =
      (fs.map Prod.snd).toArray := by
  have : ∀ (acc : Array JSStr) (l : List (Func × JSStr)), (∀ p ∈ l, p.1.name = some p.2) →
      List.foldl (fun acc d => acc ++ VarScoped.names d) acc (l.map fun p => VarScoped.func p.1) =
        acc ++ (l.map Prod.snd).toArray := by
    intro acc l
    induction l generalizing acc with
    | nil => intro _; simp
    | cons p l ih =>
      intro hl
      simp only [List.map_cons, List.foldl_cons]
      rw [ih _ (fun q hq => hl q (List.mem_cons_of_mem _ hq))]
      simp [VarScoped.names, hl p (List.mem_cons_self ..)]
  simpa using this #[] fs h

/-- Steps 5-8's fold (over the declarations in reverse): the functions to initialize, in source order. -/
theorem foldList_fnsToInit (t : State) (f : Array JSStr × Array Func → VarScoped → M (Array JSStr × Array Func)) :
    ∀ (l : List (Func × JSStr)) (names : Array JSStr) (fs0 : Array Func), (l.map Prod.snd).Nodup →
      (∀ p ∈ l, p.2 ∉ names.toList) →
      (∀ p ∈ l, ∀ (names' : Array JSStr) (fs' : Array Func), p.2 ∉ names'.toList →
        f (names', fs') (.func p.1) t = .ok (names'.push p.2, #[p.1] ++ fs') t) →
      M.foldList (l.map fun p => VarScoped.func p.1) (names, fs0) f t =
        .ok (names ++ (l.map Prod.snd).toArray, (l.map Prod.fst).reverse.toArray ++ fs0) t := by
  intro l
  induction l with
  | nil => intro names fs0 _ _ _; simp
  | cons p l ih =>
    intro names fs0 hnd hn hf
    simp only [List.map_cons, M.foldList_cons, hf p (List.mem_cons_self ..) names fs0 (hn p (List.mem_cons_self ..)),
      M.bindRes_ok]
    simp only [List.map_cons, List.nodup_cons] at hnd
    rw [ih _ _ hnd.2 (fun q hq => ?_) (fun q hq => hf q (List.mem_cons_of_mem _ hq))]
    · simp
    · simp only [Array.toList_push, List.mem_append, List.mem_singleton, not_or]
      exact ⟨hn q (List.mem_cons_of_mem _ hq), fun h => hnd.1 (h ▸ List.mem_map_of_mem hq)⟩

/-- **GlobalDeclarationInstantiation** of a script whose top level declares the simple functions `fs`
(distinct names) and `let` bindings `lets`, and no Annex B functions, on an extensible ordinary global
object that has none of the names (nor has the global record's declarative part): the lets are
declared (uninitialized), then each function object is created and bound, in order. -/
theorem gdi_simple (body : Array Stmt) (fs : List (Func × JSStr)) (lets : List JSStr) (t : State) (ge g : Nat)
    (ctx : Ctx) (gb : HashMap JSStr Binding) (gtv : Value) (fp : ObjId)
    (hvar : topLevelVarScoped body = (fs.map fun p => VarScoped.func p.1).toArray)
    (hlexd : topLevelLexicallyScoped body = (lets.map fun x => LexScoped.binding .let (.ident x)).toArray)
    (hann : annexBFunctions body lets.toArray = #[])
    (hsimple : ∀ p ∈ fs, Inst.SimpleFn p.1 p.2) (hnd : (fs.map Prod.snd).Nodup)
    (hstrict : ctx.strict = false) (hge : ge < t.envs.size) (hE : t.envEntry ge = .global g gb gtv)
    (hgbf : ∀ p ∈ fs, gb.contains p.2 = false) (hgbl : ∀ x ∈ lets, gb.contains x = false)
    (hgs : g < t.heap.size) (hk : (t.objEntry g).kind = .ordinary) (hx : (t.objEntry g).extensible = true)
    (hpf : ∀ p ∈ fs, (t.objEntry g).props.get? (.str p.2) = none)
    (hpl : ∀ x ∈ lets, (t.objEntry g).props.get? (.str x) = none)
    (hfp : t.curRealm.intrinsics["%Function.prototype%"]? = some fp) :
    globalDeclarationInstantiation body ge g ctx t =
      .ok (AddScript.gdiCtx ctx) (instAll ge g ctx.script fp fs (t.setEnv ge (.global g (insertLets gb lets) gtv))) := by
  have hnames : ∀ p ∈ fs, p.1.name = some p.2 := fun p hp => (hsimple p hp).2.2.2.2
  simp only [globalDeclarationInstantiation, hvar, hlexd, lexNames_eq, varNames_eq fs hnames, hstrict, M.bind_eq,
    M.bind_apply, M.forArr_def, M.foldArr_toArray]
  -- 3-4: the checks
  rw [foldList_const _ _ _ _ (fun x hx => ?c3)]
  rotate_left
  · simp [globalDeclRecHas, readEnv_entry _ _ _ hge, hE, hgbl x hx, hasRestrictedGlobalProperty,
      Obj'.getOwnProperty_entry _ _ _ hgs (by rw [hk]; rfl), hpl x hx, M.bind_eq, M.bind_apply, pure, M.pure]
  simp only [M.bindRes_ok, M.bind_apply]
  rw [foldList_const _ _ _ _ (fun x hx => ?c4)]
  rotate_left
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    simp [globalDeclRecHas, readEnv_entry _ _ _ hge, hE, hgbf p hp, pure, M.pure]
  simp only [M.bindRes_ok, M.bind_apply]
  -- 5-8: the functions to initialize
  rw [List.reverse_toArray, M.foldArr_toArray, ← List.map_reverse]
  rw [foldList_fnsToInit t _ fs.reverse #[] #[] (by rw [List.map_reverse]; exact List.pairwise_reverse.2 (hnd.imp Ne.symm)) (by simp)
    (fun p hp names' fs' hn => ?c5)]
  rotate_left
  · have hp' : p ∈ fs := List.mem_reverse.mp hp
    have hc : ¬ p.2 ∈ names' := by simpa using hn
    simp [hnames p hp', hc, canDeclareGlobalFunction, Obj'.getOwnProperty_entry _ _ _ hgs (by rw [hk]; rfl),
      hpf p hp', Obj'.isExtensible_entry _ _ hgs (by rw [hk]; rfl), hx, M.bind_eq, M.bind_apply, pure, M.pure]
  simp only [M.bindRes_ok, M.bind_apply]
  -- 9-10: no var names
  rw [foldList_const _ _ _ _ (fun x hx => ?c9)]
  rotate_left
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx; simp [pure, M.pure]
  -- 12: no Annex B functions
  simp only [M.bindRes_ok, M.bind_apply, Bool.false_eq_true, ↓reduceIte, hann, M.foldArr_eq, Array.toList_empty,
    M.foldList_nil]
  -- 15: the lets
  rw [foldList_lets ge g gtv _ lets gb t hge hE (fun x hx u gb' hu hEu => ?c15)]
  rotate_left
  · have hn : LexScoped.names (.binding .let (.ident x)) = #[x] := rfl
    have hk1 : (VarKind.let == VarKind.const) = false := by decide
    have hk2 : (VarKind.let == VarKind.using) = false := by decide
    have hk3 : (VarKind.let == VarKind.awaitUsing) = false := by decide
    simp [hn, LexScoped.isConstant, hk1, hk2, hk3, DTScript.createMutableBinding_global ge x false u g gb' gtv hu hEu]
  simp only [M.bindRes_ok, M.bind_apply]
  -- 16: the function objects
  have hlist : ((List.map Prod.fst fs.reverse).reverse.toArray ++ #[]).toList = fs.map Prod.fst := by
    simp [List.map_reverse]
  rw [hlist]
  obtain ⟨tL, htL⟩ : ∃ x, t.setEnv ge (.global g (insertLets gb lets) gtv) = x := ⟨_, rfl⟩
  rw [htL]
  have hoL : ∀ x, tL.objEntry x = t.objEntry x := by intro x; rw [← htL, State.setEnv_objEntry]
  have hgood : GoodG g fp tL :=
    ⟨by rw [← htL, State.setEnv_heap_size]; exact hgs, by rw [hoL]; exact hk, by rw [hoL]; exact hx,
      by rw [← htL, State.setEnv_curRealm]; exact hfp⟩
  rw [foldList_fns ge g ctx.script fp _ fs tL hgood hnd (fun p hp => by rw [hoL]; exact hpf p hp)
    (fun p hp u hu hn => ?c16)]
  rotate_left
  · obtain ⟨hgs', hk', hx', hfp'⟩ := hu
    have hi := Inst.instantiate_fn p.1 p.2 (hsimple p hp) u ge
      { ctx with strict := false, annexB := funcIds #[] } fp hfp'
    have hgi : g < (Inst.instStateFn p.1 p.2 u ge ctx.script fp).heap.size := by
      rw [Inst.instStateFn_size]; exact Nat.lt_succ_of_lt (Nat.lt_succ_of_lt hgs')
    have hui := Inst.instStateFn_entry_lt p.1 p.2 u ge ctx.script fp g hgs'
    have hc := AddScript.createGlobalFunctionBinding_new (Inst.instStateFn p.1 p.2 u ge ctx.script fp) g p.2
      (.obj u.heap.size) hgi (by rw [hui]; exact hk') (by rw [hui]; exact hx') (by rw [hui]; exact hn)
    simp only [funcNameKey, hnames p hp, Option.getD_some, M.bind_eq, M.bind_apply, hi, M.bindRes_ok]
    exact hc
  simp only [M.bindRes_ok, M.bind_apply, M.foldList_nil, pure, M.pure]
  congr 1
  cases ctx; simp_all [AddScript.gdiCtx]

/-! ## The state after the declarations -/

/-- **What the function declarations leave**: function `i` is the object `t.heap.size + 2 i`, bound
under its name on the global object; the global object is otherwise unchanged, and so is every other
object that existed. -/
theorem instAll_facts (ge g sc fp : Nat) :
    ∀ (fs : List (Func × JSStr)) (t : State), GoodG g fp t → (fs.map Prod.snd).Nodup →
      let u := instAll ge g sc fp fs t
      GoodG g fp u ∧ u.envs = t.envs ∧ u.fuel = t.fuel ∧ u.realms = t.realms ∧ u.realm = t.realm ∧
      u.heap.size = t.heap.size + 2 * fs.length ∧
      (∀ x, x < t.heap.size → x ≠ g → u.objEntry x = t.objEntry x) ∧
      (u.objEntry g).proto = (t.objEntry g).proto ∧
      (∀ k, (∀ p ∈ fs, k ≠ PropKey.str p.2) → (u.objEntry g).props.get? k = (t.objEntry g).props.get? k) ∧
      (∀ i (h : i < fs.length), (u.objEntry g).props.get? (.str fs[i].2) =
        some (.data (.obj (t.heap.size + 2 * i)) true true false)) ∧
      (∀ i (h : i < fs.length), ∃ d, (u.objEntry (t.heap.size + 2 * i)).kind = .func d ∧ d.code = fs[i].1 ∧
        d.realm = t.realm ∧ d.thisMode = .global ∧ d.isClassCtor = false) := by
  intro fs
  induction fs with
  | nil =>
    intro t hg _
    refine ⟨hg, rfl, rfl, rfl, rfl, by simp [instAll], fun _ _ _ => rfl, rfl, fun _ _ => rfl,
      fun i h => absurd h (by simp), fun i h => absurd h (by simp)⟩
  | cons p rest ih =>
    intro t hg hnd
    obtain ⟨fn, nm⟩ := p
    have hb := bindFn_good ge g sc fp fn nm t hg
    obtain ⟨hg1, hk1, hnm1, hpr1, ho1, hf1, hz1, he1, hfu1, hr1, hrl1⟩ := hb
    simp only [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨hgu, heu, hfuu, hru, hrlu, hzu, hou, hpru, hku, hiu, hdu⟩ := ih _ hg1 hnd.2
    have hgt := hg.1
    have hne : ∀ q ∈ rest, PropKey.str nm ≠ PropKey.str q.2 := by
      intro q hq h; injection h with h; exact hnd.1 (h ▸ List.mem_map_of_mem hq)
    refine ⟨hgu, heu.trans he1, hfuu.trans hfu1, hru.trans hr1, hrlu.trans hrl1, ?_, fun x hx hxg => ?_, ?_,
      fun k hk => ?_, fun i h => ?_, fun i h => ?_⟩
    · show _ = _; simp only [instAll, List.length_cons]; rw [hzu, hz1]; omega
    · simp only [instAll]; rw [hou x (by rw [hz1]; omega) hxg, ho1 x hx hxg]
    · simp only [instAll]; rw [hpru, hpr1]
    · simp only [instAll]
      rw [hku k (fun q hq => hk q (List.mem_cons_of_mem _ hq)), hk1 k (hk _ (List.mem_cons_self ..))]
    · simp only [instAll]
      cases i with
      | zero => simp only [List.getElem_cons_zero, Nat.mul_zero, Nat.add_zero]; rw [hku _ hne, hnm1]
      | succ j =>
        simp only [List.getElem_cons_succ]
        rw [hiu j (by simpa using h), hz1]
        have : t.heap.size + 2 + 2 * j = t.heap.size + 2 * (j + 1) := by omega
        rw [this]
    · simp only [instAll]
      cases i with
      | zero =>
        refine ⟨Inst.fnData fn t ge sc, ?_, Inst.fnData_code _ _ _ _, Inst.fnData_realm _ _ _ _,
          Inst.fnData_thisMode _ _ _ _, Inst.fnData_isClassCtor _ _ _ _⟩
        simp only [Nat.mul_zero, Nat.add_zero]
        rw [hou _ (by rw [hz1]; omega) (Ne.symm (Nat.ne_of_lt hgt)), hf1]
      | succ j =>
        obtain ⟨d, hd1, hd2, hd3, hd4, hd5⟩ := hdu j (by simpa using h)
        refine ⟨d, ?_, by simpa using hd2, hd3.trans hrl1, hd4, hd5⟩
        rw [hz1] at hd1
        have : t.heap.size + 2 * (j + 1) = t.heap.size + 2 + 2 * j := by omega
        rw [this]; exact hd1

/-! ## The driver -/

/-- `r` driven (its requests answered by the engine) ends in `.ok v s'`. -/
def DrivesTo {α : Type} (eng : Engine) (r : Res α) (v : α) (s' : State) : Prop :=
  ∀ cs, (drive eng callDepth r cs).1 = .ok v s'

theorem drivesTo_ok {α : Type} (eng : Engine) (v : α) (s : State) : DrivesTo eng (.ok v s) v s := by
  intro cs; simp only [callDepth]; rw [drive_ok]

/-- A call request whose callee returns `w`: driving continues with the continuation. -/
theorem drivesTo_call {α : Type} (eng : Engine) (f t : Value) (args : Array Value) (s : State)
    (k : Outcome → State → Res α) (w : Value) (s1 : State) (v : α) (s' : State)
    (h : callImpl eng f t args s = .ok w s1) (hk : DrivesTo eng (k (.normal w) s1) v s') :
    DrivesTo eng (.req (.call f t args) s k) v s' := by
  intro cs; simp only [callDepth] at hk ⊢; rw [drive_call_ok eng 3999 _ _ _ _ _ cs _ _ h]; exact hk cs

/-- What ScriptEvaluation makes of the body's completion. -/
def complValue : Compl → M Value := fun c => match c with
  | .normal v => pure (v.getD .undefined)
  | .ret v => pure v
  | _ => pure .undefined

/-! ## Scripts -/

/-- The state once ScriptEvaluation has recorded the script, and its context. -/
def scriptStart (s : State) (prog : Program) : State := { s with scripts := s.scripts.push { prog := prog, realm := s.realm, path := "" }, script := s.scripts.size }
def scriptCtx (s : State) (strict : Bool) : Ctx := AddScript.gdiCtx { lex := s.curRealm.globalEnv, var := s.curRealm.globalEnv, strict := strict, realm := s.realm, script := s.scripts.size }

/-- The state the body starts in: the lets declared, the functions created and bound. -/
def scriptState (s : State) (prog : Program) (fs : List (Func × JSStr)) (lets : List JSStr)
    (gb : HashMap JSStr Binding) (gtv : Value) (fp : ObjId) : State :=
  instAll s.curRealm.globalEnv s.curRealm.globalObj s.scripts.size fp fs
    ((scriptStart s prog).setEnv s.curRealm.globalEnv (.global s.curRealm.globalObj (insertLets gb lets) gtv))

/-- **A script's value**: for a non-strict script declaring the simple functions `fs` and the lets
`lets` (as `gdi_simple`), its value is what its body, run from `scriptState`, drives to. -/
theorem script_value (eng : Engine) (s : State) (cs : Conts) (prog : Program) (fs : List (Func × JSStr))
    (lets : List JSStr) (gb : HashMap JSStr Binding) (gtv : Value) (fp : ObjId) (v : Value) (s' : State)
    (hstr : prog.strict = false)
    (hvar : topLevelVarScoped prog.body = (fs.map fun p => VarScoped.func p.1).toArray)
    (hlexd : topLevelLexicallyScoped prog.body = (lets.map fun x => LexScoped.binding .let (.ident x)).toArray)
    (hann : annexBFunctions prog.body lets.toArray = #[])
    (hsimple : ∀ p ∈ fs, Inst.SimpleFn p.1 p.2) (hnd : (fs.map Prod.snd).Nodup)
    (hge : s.curRealm.globalEnv < s.envs.size)
    (hE : s.envEntry s.curRealm.globalEnv = .global s.curRealm.globalObj gb gtv)
    (hgbf : ∀ p ∈ fs, gb.contains p.2 = false) (hgbl : ∀ x ∈ lets, gb.contains x = false)
    (hgs : s.curRealm.globalObj < s.heap.size) (hk : (s.objEntry s.curRealm.globalObj).kind = .ordinary)
    (hx : (s.objEntry s.curRealm.globalObj).extensible = true)
    (hpf : ∀ p ∈ fs, (s.objEntry s.curRealm.globalObj).props.get? (.str p.2) = none)
    (hpl : ∀ x ∈ lets, (s.objEntry s.curRealm.globalObj).props.get? (.str x) = none)
    (hfp : s.curRealm.intrinsics["%Function.prototype%"]? = some fp)
    (hbody : DrivesTo eng (M.bindRes complValue
      (evalStmts evalDepth (scriptCtx s false) prog.body (scriptState s prog fs lets gb gtv fp))) v s') :
    (runM eng (scriptEvaluation prog) s cs).1 = .ok v s' := by
  have hgdi := gdi_simple prog.body fs lets (scriptStart s prog) s.curRealm.globalEnv s.curRealm.globalObj
    { lex := s.curRealm.globalEnv, var := s.curRealm.globalEnv, strict := false, realm := s.realm, script := s.scripts.size } gb gtv fp hvar hlexd hann hsimple hnd rfl hge hE hgbf hgbl hgs hk hx hpf hpl hfp
  simp only [runM, scriptEvaluation, M.bind_eq, M.bind_apply, M.readS_apply, M.bindRes_ok, M.modify_apply, hstr]
  rw [show ({ s with scripts := s.scripts.push { prog := prog, realm := s.realm, path := "" }, script := s.scripts.size } : State) = scriptStart s prog from rfl, hgdi]
  simp only [M.bindRes_ok, M.bind_apply]
  exact hbody cs

end Script
