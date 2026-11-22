import JSProofs.Body
import JSProofs.IRPUGen

/-!
# React's `isRenderPhaseUpdate` (zippy docs/react-proofs.md)

```js
function isRenderPhaseUpdate(fiber) {
  var alternate = fiber.alternate;
  return (
    fiber === currentlyRenderingFiber ||
    (null !== alternate && alternate === currentlyRenderingFiber)
  );
}
```
`dispatchSetState`'s first test: whether the update happens while rendering. For a fiber object with an own
`alternate` and the module's `currentlyRenderingFiber` (a variable of the function's enclosing record), the call
returns exactly the boolean the expression says.
-/

open ES ES.M HostRuns Logic
open Std (HashMap)

namespace ReactIRPU

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ}

theorem simple (d : FuncData) (hc : d.code = IRPUGen.isRenderPhaseUpdate_func) : FDI.Simple d := by
  constructor <;> rw [hc] <;> try rfl
  simp [IRPUGen.isRenderPhaseUpdate_func, Func.params, Func.info]

/-- The record's bindings after instantiation. -/
def B (F : ObjId) : HashMap JSStr Binding :=
  FDI.fdiMap #[JSStr.ofString "fiber"] #[.obj F] #[JSStr.ofString "alternate"] #[]

theorem record (s : State) (fo : ObjId) (d : FuncData) (t : Value) (F : ObjId)
    (hcode : d.code = IRPUGen.isRenderPhaseUpdate_func) :
    Scope.declLike? ((bodyState s fo d t #[.obj F]).envEntry s.envs.size) = some (B F, some d.env) := by
  rw [bodyState_self]
  have hp : d.code.info.fdi.paramNames = #[JSStr.ofString "fiber"] := by rw [hcode]; rfl
  have hv : d.code.info.fdi.varNames = #[JSStr.ofString "alternate"] := by rw [hcode]; rfl
  have hl : FDI.lexDecls d = #[] := by simp [FDI.lexDecls, hcode, IRPUGen.isRenderPhaseUpdate_func, Func.info]
  rw [hp, hv, hl]; rfl

theorem ne_fa : (JSStr.ofString "fiber" == JSStr.ofString "alternate") = false := by decide
theorem ne_af : (JSStr.ofString "alternate" == JSStr.ofString "fiber") = false := by decide
theorem ne_fc : (JSStr.ofString "fiber" == JSStr.ofString "currentlyRenderingFiber") = false := by decide
theorem ne_ac : (JSStr.ofString "alternate" == JSStr.ofString "currentlyRenderingFiber") = false := by decide
theorem ne_fa' : JSStr.ofString "fiber" ≠ JSStr.ofString "alternate" := by decide

set_option linter.unusedSimpArgs false in
set_option linter.deprecated false in
/-- The record after instantiation, as an explicit chain of updates. -/
theorem B_eq (F : ObjId) : B F =
    ((((({} : HashMap JSStr Binding).insert "fiber" { deletable := false }).modify "fiber"
      fun bd => { bd with value := some (.obj F) }).insert "alternate" { deletable := false }).modify "alternate"
      fun bd => { bd with value := some .undefined }) := by
  have hcont : (#[JSStr.ofString "fiber"].contains (JSStr.ofString "alternate")) = false := by
    simp [Ne.symm ne_fa']
  simp only [B, FDI.fdiMap, FDI.createParam, FDI.bindParam, FDI.createVar, List.range_succ, List.range_zero,
    List.nil_append, List.foldl_cons, List.foldl_nil, Array.toList, Array.size, List.length_cons, List.length_nil,
    Std.HashMap.contains_empty, Bool.false_eq_true, ↓reduceIte, hcont, Bool.not_false, Bool.true_and]
  rw [if_pos (by simp [Std.HashMap.contains_modify, Std.HashMap.contains_insert, ne_fa'])]
  rfl

/-- **`isRenderPhaseUpdate(fiber)`** for a plain fiber object with an own `alternate` data property. -/
theorem call_spec {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t : Value} {s : State} {F : ObjId}
    {alt cur : Value} {wa ea ca : Bool} {bG : HashMap JSStr Binding} {oG : Option EnvId} {bdG : Binding}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : 8 ≤ s.fuel)
    (hcode : d.code = IRPUGen.isRenderPhaseUpdate_func) (hcls : d.isClassCtor = false)
    (hmode : d.thisMode = .strict)
    (hG : d.env < s.envs.size) (hGd : Scope.declLike? (s.envEntry d.env) = some (bG, oG))
    (hGb : bG[JSStr.ofString "currentlyRenderingFiber"]? = some bdG) (hGv : bdG.value = some cur)
    (hF : F < s.heap.size) (hFk : (s.objEntry F).kind.isPlain = true)
    (hFp : (s.objEntry F).props.get? (.str "alternate") = some (.data alt wa ea ca)) :
    WP eng answer n h (callImpl eng (.obj fo) t #[.obj F]) s fun v _ _ =>
      v = .bool (isStrictlyEqual (.obj F) cur || (!isStrictlyEqual .null alt && isStrictlyEqual alt cur)) := by
  apply wp_call_simple hlt hk (by omega) hcls hmode (by rw [hcode]; rfl) (by rw [hcode]; rfl) (simple d hcode)
    (by rw [hcode]; rfl) (by rw [hcode]; rfl)
  change WP eng answer n h (evalStmts (999964 + 35) _ IRPUGen.isRenderPhaseUpdate_stmts) _ _
  rw [← congrFun (IRPUGen.isRenderPhaseUpdate_eq 999964) _]
  simp only [IRPUGen.isRenderPhaseUpdate]
  have hE : s.envs.size < (bodyState s fo d t #[.obj F]).envs.size := by simp
  have hrec := record s fo d t F hcode
  rw [B_eq] at hrec
  have hlex : (Sem.inner (FDI.fdiCtx fo d s.envs.size)).lex = s.envs.size := rfl
  apply wp_stmts (by simp; omega)
  simp only [StmtsWP]
  apply wp_varDecl
  simp only [DeclsWP, Array.toList]
  -- (`var alternate = fiber.alternate`)
  have hlookF : ∀ (w : State) (bm : HashMap JSStr Binding), s.envs.size < w.envs.size →
      Scope.declLike? (w.envEntry s.envs.size) = some (bm, some d.env) →
      bm[JSStr.ofString "fiber"]? = some { deletable := false, value := some (.obj F) } →
      Scope.lookup w 1 (Sem.inner (FDI.fdiCtx fo d s.envs.size)).lex (JSStr.ofString "fiber") = some (.obj F) := by
    intro w bm hw hd hb
    rw [hlex, Scope.lookup_succ]; simp [hw, hd, hb]
  have hBf : (B F)[JSStr.ofString "fiber"]? = some { deletable := false, value := some (.obj F) } := by
    rw [B_eq]
    simp only [Std.HashMap.getElem?_modify, Std.HashMap.getElem?_insert, ne_af, ne_fa, beq_self_eq_true,
      Bool.false_eq_true, ↓reduceIte, Std.HashMap.getElem?_empty, Option.map_some, Option.map_none]
  have hBa : (B F)[JSStr.ofString "alternate"]? = some { deletable := false, value := some .undefined } := by
    rw [B_eq]
    simp only [Std.HashMap.getElem?_modify, Std.HashMap.getElem?_insert, ne_af, ne_fa, beq_self_eq_true,
      Bool.false_eq_true, ↓reduceIte, Option.map_some]
  rw [← B_eq] at hrec
  have hmemA : JSStr.ofString "alternate" ∈ B F := by
    rw [Std.HashMap.mem_iff_isSome_getElem?, hBa]; rfl
  have hOL : ordLookup (bodyState s fo d t #[.obj F]) 1 F (.str (JSStr.ofString "alternate")) =
      some (.data alt wa ea ca) := ordLookup_own _ F _ (by simpa using hFp)
  apply wp_declVar 1 (e := s.envs.size) (by rw [hlex]; simp [Scope.resolve, hE, hrec, hmemA]) (by simp; omega)
  apply wp_getMember
  apply wp_ident 1 (hlookF _ (B F) hE hrec hBf) (by simp; omega)
  refine ⟨F, 1, rfl, plainChain_own _ F _ (by simpa using hF) (by simpa using hFk) (by simpa using hFp),
    by omega, by simp [hOL, noAccessor], ?_⟩
  rw [hOL, ownDataValue_data]
  refine ⟨B F, some d.env, _, hE, hrec, hBa, rfl, rfl, ?_⟩
  -- (the record now holds `alternate`)
  simp only []
  generalize hw1 : (bodyState s fo d t #[.obj F]).setEnv s.envs.size _ = w1
  have hw1E : s.envs.size < w1.envs.size := by rw [← hw1]; simp
  have hw1rec : Scope.declLike? (w1.envEntry s.envs.size) = some ((B F).modify (JSStr.ofString "alternate")
      fun bd => { bd with value := some alt }, some d.env) := by
    rw [← hw1, State.setEnv_envEntry_self _ _ _ hE]
    exact declLike_withBindings hrec _
  have hw1G : w1.envEntry d.env = s.envEntry d.env := by
    rw [← hw1, setEnv_envEntry_ne _ _ _ _ (Nat.ne_of_gt hG), bodyState_envEntry_lt _ _ _ _ _ _ hG]
  have hw1f : w1.fuel = s.fuel - 1 := by rw [← hw1]; simp
  have hGw : d.env < w1.envs.size := Nat.lt_trans hG hw1E
  -- (reading the function's own variables, and the module's)
  have hown : ∀ (c : Ctx) (x : JSStr) (v : Value), c.lex = s.envs.size →
      ((B F).modify (JSStr.ofString "alternate") fun bd => { bd with value := some alt })[x]? =
        some { deletable := false, value := some v } →
      Scope.lookup w1 1 c.lex x = some v := by
    intro c x v hc hb
    rw [hc, Scope.lookup_succ]; simp [hw1E, hw1rec, hb]
  have hmod : ∀ (c : Ctx), c.lex = s.envs.size →
      Scope.lookup w1 2 c.lex (JSStr.ofString "currentlyRenderingFiber") = some cur := by
    intro c hc
    have hnone : ((B F).modify (JSStr.ofString "alternate") fun bd => { bd with value := some alt })[
        JSStr.ofString "currentlyRenderingFiber"]? = none := by
      rw [B_eq]
      simp only [Std.HashMap.getElem?_modify, Std.HashMap.getElem?_insert, ne_ac, ne_fc,
        Bool.false_eq_true, ↓reduceIte, Std.HashMap.getElem?_empty, Option.map_none]
    rw [hc, Scope.lookup_succ]
    simp only [hw1E, ↓reduceIte, hw1rec, hnone]
    rw [Scope.lookup_succ]
    simp [hGw, hw1G, hGd, hGb, hGv]
  have hB'f : ((B F).modify (JSStr.ofString "alternate") fun bd => { bd with value := some alt })[
      JSStr.ofString "fiber"]? = some { deletable := false, value := some (.obj F) } := by
    rw [B_eq]
    simp only [Std.HashMap.getElem?_modify, Std.HashMap.getElem?_insert, ne_af, ne_fa, beq_self_eq_true,
      Bool.false_eq_true, ↓reduceIte, Std.HashMap.getElem?_empty, Option.map_some, Option.map_none]
  have hB'a : ((B F).modify (JSStr.ofString "alternate") fun bd => { bd with value := some alt })[
      JSStr.ofString "alternate"]? = some { deletable := false, value := some alt } := by
    rw [B_eq]
    simp only [Std.HashMap.getElem?_modify, Std.HashMap.getElem?_insert, ne_af, ne_fa, beq_self_eq_true,
      Bool.false_eq_true, ↓reduceIte, Option.map_some]
  -- (`return fiber === currentlyRenderingFiber || (null !== alternate && alternate === currentlyRenderingFiber)`)
  apply wp_ret (by simp [FDI.fdiCtx, hcode])
  apply wp_or
  apply wp_binary
  apply wp_ident 1 (hown _ _ _ rfl hB'f) (by omega)
  apply wp_ident 2 (hmod _ rfl) (by omega)
  apply wp_seq
  cases hb1 : isStrictlyEqual (Value.obj F) cur
  · simp only [toBoolean, Bool.false_eq_true, ↓reduceIte]
    apply wp_and
    apply wp_binary
    apply wp_lit
    apply wp_ident 1 (hown _ _ _ rfl hB'a) (by omega)
    apply wp_sne
    cases hb2 : isStrictlyEqual Value.null alt
    · simp only [litValue, hb2, toBoolean, Bool.not_false, ↓reduceIte]
      apply wp_binary
      apply wp_ident 1 (hown _ _ _ rfl hB'a) (by omega)
      apply wp_ident 2 (hmod _ rfl) (by omega)
      apply wp_seq
      simp [retVal, Compl.updateEmpty, hb2]
    · simp [litValue, hb2, toBoolean, retVal, Compl.updateEmpty]
  · simp [toBoolean, retVal, Compl.updateEmpty]

end

end ReactIRPU
