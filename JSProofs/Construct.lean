import JSProofs.Nested

/-!
# `new F(args)`: the [[Construct]] of an ordinary function

`constructECMA_ord`: a sloppy, non-class function `F` whose `prototype` is an object `P` constructs a fresh
ordinary object `O` (the next heap slot) with prototype `P`, runs its body with `this = O`, and, when the body
returns a non-object, gives `O`.
-/

open ES ES.Conv

namespace Construct

theorem constructECMA_ord {Q : State → Prop} (f : ObjId) (d : FuncData) (s : State) (args : Array Value)
    (v : Value) (P : ObjId) (wr en cf : Bool)
    (hdef : d.isDefaultCtor = false) (hder : d.derived = false) (hmode : d.thisMode = .global)
    (hfields : d.fields = #[]) (hpriv : d.privMethods = #[])
    (hf : f < s.heap.size) (hfk : (s.objEntry f).kind = .func d)
    (hp : (s.objEntry f).props.get? (.str kPrototype) = some (.data (.obj P) wr en cf))
    (hv : v.isObject = false)
    (hbody : ∀ t : State, s.envs.size < t.envs.size →
      t.envEntry s.envs.size = .func ∅ (some d.env) .initialized (.obj s.heap.size) f (.obj f) →
      (∀ e, e < s.envs.size → t.envEntry e = s.envEntry e) → t.heap = (s.allocObj { proto := .obj P }).heap →
      t.fuel = s.fuel → t.realms = s.realms → t.realm = d.realm →
      ∃ t', evalFunctionBody evalDepth f d s.envs.size args t = .ok v t' ∧ Q t') :
    ∃ s', constructECMA f d args (.obj f) s = .ok (.obj s.heap.size) s' ∧ s'.realm = s.realm ∧ s'.script = s.script ∧
      ∃ t', Q t' ∧ s'.heap = t'.heap ∧ s'.envs = t'.envs ∧ s'.fuel = t'.fuel ∧ s'.realms = t'.realms := by
  let O := s.heap.size
  let s1 : State := { s with realm := d.realm, script := d.script }
  have hget : getProp f (.str kPrototype) s1 = .ok (.obj P) s1 := by
    have h := Obj'.get_entry_data f (.str kPrototype) (.obj f) s1 hf (by show (s.objEntry f).kind.isPlain = true; rw [hfk]; rfl)
      (by show isOwnData ((s.objEntry f).props.get? _) = true; rw [hp]; rfl)
    rw [getProp, h]; show Res.ok (ownDataValue ((s.objEntry f).props.get? _)) s1 = _; rw [hp]; rfl
  have hocc : ordinaryCreateFromConstructor (.obj f) "%Object.prototype%" .ordinary s1 =
      .ok O (s1.allocObj { proto := .obj P }) := by
    simp [ordinaryCreateFromConstructor, getPrototypeFromConstructor, M.bind_eq, M.bind_apply, hget, pure, M.pure]
    exact ⟨rfl, rfl⟩
  let sa : State := { (s1.allocObj { proto := .obj P }) with realm := s.realm, script := s.script }
  let sb : State := { sa with realm := d.realm, script := d.script }
  let env := s.envs.size
  let E0 : Env := .func {} (some d.env) .uninitialized .undefined f (.obj f)
  let s2 : State := { sb with envs := sb.envs.push E0 }
  let s3 := s2.setEnv env (.func {} (some d.env) .initialized (.obj O) f (.obj f))
  have hgl : (ThisMode.global == ThisMode.lexical) = false := by decide
  have hgs : (ThisMode.global == ThisMode.strict) = false := by decide
  have hnew : newFunctionEnv f d (.obj f) sb = .ok env s2 := by
    simp [hgl, newFunctionEnv, hmode, s2, sb, sa, s1, E0, env, State.allocObj]
  have henv2 : env < s2.envs.size := by simp [s2, sb, sa, s1, env, State.allocObj]
  have hbind : ordinaryCallBindThis d env (.obj O) s2 = .ok () s3 := by
    simp only [ordinaryCallBindThis, hmode]
    have hnn : (Value.obj O).isNullish = false := rfl
    have hui : (ThisStatus.uninitialized == ThisStatus.initialized) = false := by decide
    simp [hgl, hgs, hnn, hui, M.bind_eq, M.bind_apply, bindThisValue, readEnv_entry _ _ _ henv2, pure, M.pure,
      modifyEnv_eq_setEnv _ _ _ henv2, s3, toObject]
    simp [hui, State.envEntry, s2, sb, sa, s1, E0, env, modifyEnv, State.setEnv, State.allocObj]
  have hfk3 : (s3.objEntry f).kind = .func d := by
    have : s3.objEntry f = s.objEntry f := by
      simp [s3, s2, sb, sa, s1, State.objEntry, State.setEnv, State.allocObj, Array.getElem?_push, Nat.ne_of_lt hf]
    rw [this, hfk]
  have hf3 : f < s3.heap.size := by
    show f < (s2.setEnv env _).heap.size; rw [State.setEnv_heap_size]; simp [s2, sb, sa, s1, State.allocObj]; exact Nat.lt_succ_of_lt hf
  have hinit : initializeInstanceElements (.obj O) f s3 = .ok () s3 := by
    simp [initializeInstanceElements, M.bind_eq, M.bind_apply, objKind, readObj_entry' _ _ _ hf3, hfk3, hfields, hpriv,
      M.forArr, pure, M.pure]
  have henv3 : env < s3.envs.size := by simp [s3, s2, sb, sa, s1, env, State.allocObj]
  have hE3 : s3.envEntry env = .func ∅ (some d.env) .initialized (.obj O) f (.obj f) := by
    simp [s3, henv2]
  have hold : ∀ e, e < s.envs.size → s3.envEntry e = s.envEntry e := by
    intro e he
    have hne : env ≠ e := Nat.ne_of_gt he
    rw [State.setEnv_envEntry_ne _ _ _ _ hne]
    simp [State.envEntry, s2, sb, sa, s1, Array.getElem?_push, Nat.ne_of_lt he, State.allocObj]
  obtain ⟨s4, hb, hQ⟩ : ∃ t', evalFunctionBody evalDepth f d env args s3 = .ok v t' ∧ Q t' :=
    hbody s3 henv3 hE3 hold (by simp [s3, s2, sb, sa, s1, State.setEnv, State.allocObj])
      (by simp [s3, s2, sb, sa, s1, State.allocObj]) (by simp [s3, s2, sb, sa, s1, State.allocObj])
      (by simp [s3, s2, sb, sa, s1])
  refine ⟨{ s4 with realm := s.realm, script := s.script }, ?_, rfl, rfl, s4, hQ, rfl, rfl, rfl, rfl⟩
  simp only [constructECMA, hdef, hder, inCallee, M.bind_eq, M.bind_apply, M.readS_apply, M.bindRes_ok, M.modify_apply]
  simp [M.bind_apply, hocc, hnew, hbind, hinit, hb, hv, M.attempt, M.tryCatch_apply, pure, M.pure, s1]
  erw [hnew]
  simp [M.bindRes_ok, M.bind_apply, M.bind_eq, hbind, hinit, hb, hv, M.attempt, M.tryCatch_apply, pure, M.pure]
  rfl

/-! ## The driver's side -/

theorem drive_construct_ok {α : Type} (eng : Engine) (n : Nat) (f : Value) (args : Array Value) (nt : Value) (s : State)
    (k : Outcome → State → Res α) (cs : Conts) (v : Value) (s' : State)
    (h : constructImpl eng f args nt s = .ok v s') :
    drive eng (n + 1) (.req (.construct f args nt) s k) cs = drive eng (n + 1) (k (.normal v) s') cs := by
  simp [drive, driveWith, h, drive_ok, outcomeOf]

/-- [[Construct]] of an ECMAScript function object: one step of fuel, then `constructECMA`. -/
theorem constructImpl_func (eng : Engine) (fo : ObjId) (d : FuncData) (args : Array Value) (nt : Value) (s : State)
    (hfs : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : s.fuel ≠ 0) :
    constructImpl eng (.obj fo) args nt s = constructECMA fo d args nt { s with fuel := s.fuel - 1 } := by
  have hfs' : fo < ({ s with fuel := s.fuel - 1 } : State).heap.size := hfs
  have hk' : (({ s with fuel := s.fuel - 1 } : State).objEntry fo).kind = .func d := hk
  simp [constructImpl, M.tick, hf, M.bind_eq, M.bind_apply, objKind, readObj_entry' _ _ _ hfs', hk']

theorem drivesTo_construct {α : Type} (eng : Engine) (f : Value) (args : Array Value) (nt : Value) (s : State)
    (k : Outcome → State → Res α) (w : Value) (s1 : State) (v : α) (s' : State)
    (h : constructImpl eng f args nt s = .ok w s1) (hk : Script.DrivesTo eng (k (.normal w) s1) v s') :
    Script.DrivesTo eng (.req (.construct f args nt) s k) v s' := by
  intro cs; simp only [callDepth] at hk ⊢; rw [drive_construct_ok eng 3999 _ _ _ _ _ cs _ _ h]; exact hk cs

theorem runsTo_construct {β : Type} (eng : Engine) (f : Value) (args : Array Value) (nt : Value) (w : State)
    (K : Outcome → State → Res β) (x : Value) (w1 : State) (b : β) (w' : State)
    (h : constructImpl eng f args nt w = .ok x w1) (hk : Runs.RunsTo eng (K (.normal x) w1) b w') :
    Runs.RunsTo eng (.req (.construct f args nt) w K) b w' := by
  intro α k v s' hd
  show Script.DrivesTo eng (.req (.construct f args nt) w (fun o s => M.bindRes k (K o s))) v s'
  exact drivesTo_construct eng f args nt w _ x w1 v s' h (hk α k v s' hd)

end Construct
