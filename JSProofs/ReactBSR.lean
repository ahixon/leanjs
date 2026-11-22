import JSProofs.SemRules
import JSProofs.BSRGen

/-!
# React's `basicStateReducer`, with the program logic (zippy docs/react-proofs.md)

```js
function basicStateReducer(state, action) {
  return "function" === typeof action ? action(state) : action;
}
```
React's `useState` reducer (react-dom 19.3 production build). `setN(v)` with a value that is not a function makes
the next state `v`: a call of the function object with a primitive `action` returns `action`, for any `this`,
state, and heap.
-/

open ES ES.M HostRuns Logic
open Std (HashMap)

namespace ReactBSR

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ}

theorem simple (d : FuncData) (hc : d.code = BSRGen.basicStateReducer_func) : FDI.Simple d := by
  constructor <;> rw [hc] <;> try rfl
  simp [BSRGen.basicStateReducer_func, Func.params, Func.info]

/-- The function's record after instantiation (`fdiMap`), as its lookups: `state` and `action` bound to the
arguments. -/
def B (st a : Value) : HashMap JSStr Binding :=
  FDI.fdiMap #[JSStr.ofString "state", JSStr.ofString "action"] #[st, a] #[] #[]

theorem ne_sa : (JSStr.ofString "state" == JSStr.ofString "action") = false := by decide
theorem ne_as : (JSStr.ofString "action" == JSStr.ofString "state") = false := by decide
theorem ne_sa' : JSStr.ofString "state" ≠ JSStr.ofString "action" := by decide
theorem ne_as' : JSStr.ofString "action" ≠ JSStr.ofString "state" := by decide

set_option linter.unusedSimpArgs false in
theorem B_action (st a : Value) :
    (B st a)[JSStr.ofString "action"]? = some ({ deletable := false, value := some a } : Binding) := by
  simp only [B, FDI.fdiMap, FDI.createParam, FDI.bindParam, List.range_succ, List.range_zero, List.nil_append,
    List.cons_append, List.foldl_cons, List.foldl_nil, Array.toList, Array.size, List.length_cons, List.length_nil,
    Std.HashMap.contains_insert, Std.HashMap.contains_empty, ne_sa, ne_as, beq_self_eq_true, Bool.or_false,
    Bool.false_or, Bool.false_eq_true, ↓reduceIte]
  simp only [Std.HashMap.getElem?_modify, Std.HashMap.getElem?_insert, ne_sa, ne_as, beq_self_eq_true,
    Bool.false_eq_true, ↓reduceIte, Option.map_some]
  rfl

theorem B_contains_action (st a : Value) : (B st a).contains (JSStr.ofString "action") = true := by
  simp [B, FDI.fdiMap, FDI.createParam, FDI.bindParam, List.range_succ, ne_sa']

theorem record (s : State) (fo : ObjId) (d : FuncData) (t st a : Value) (hcode : d.code = BSRGen.basicStateReducer_func) :
    Scope.declLike? ((bodyState s fo d t #[st, a]).envEntry s.envs.size) = some (B st a, some d.env) := by
  have hp : d.code.info.fdi.paramNames = #[JSStr.ofString "state", JSStr.ofString "action"] := by
    rw [hcode]; rfl
  have hv : d.code.info.fdi.varNames = #[] := by rw [hcode]; rfl
  have hl : FDI.lexDecls d = #[] := by simp [FDI.lexDecls, hcode, BSRGen.basicStateReducer_func, Func.info]
  simp [bodyState, entryState, hp, hv, hl, B, Scope.declLike?]

/-- **`basicStateReducer(state, action)` with a primitive `action`** returns `action`; it writes nothing (its final
state is its body's start, the caller's realm back). -/
theorem call_prim {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t st a : Value} {s : State}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : 4 ≤ s.fuel)
    (hcode : d.code = BSRGen.basicStateReducer_func) (hcls : d.isClassCtor = false) (hmode : d.thisMode = .strict)
    (ha : ∀ o, a ≠ .obj o) :
    WP eng answer n h (callImpl eng (.obj fo) t #[st, a]) s fun v w _ =>
      v = a ∧ w = { bodyState s fo d t #[st, a] with realm := s.realm, script := s.script } := by
  apply wp_call_simple hlt hk (by omega) hcls hmode (by rw [hcode]; rfl) (by rw [hcode]; rfl) (simple d hcode)
    (by rw [hcode]; rfl) (by rw [hcode]; rfl)
  change WP eng answer n h (evalStmts (999970 + 29) _ BSRGen.basicStateReducer_stmts) _ _
  rw [← congrFun (BSRGen.basicStateReducer_eq 999970) _]
  simp only [BSRGen.basicStateReducer]
  have hE : s.envs.size < (bodyState s fo d t #[st, a]).envs.size := by simp [bodyState, entryState]
  have hfuel : (bodyState s fo d t #[st, a]).fuel = s.fuel - 1 := by simp [bodyState, entryState]
  apply wp_stmts (by simp [hfuel]; omega)
  simp only [StmtsWP]
  apply wp_ret (by simp [FDI.fdiCtx, hcode])
  apply wp_cond
  apply wp_binary
  apply wp_lit
  have hrec := record s fo d t st a hcode
  have hlex : (Sem.inner (FDI.fdiCtx fo d s.envs.size)).lex = s.envs.size := rfl
  apply wp_typeof_ident 1 (e := s.envs.size)
    (by rw [hlex]; simp [Scope.resolve, hE, hrec, B_contains_action]) (by simp [hfuel]; omega) hE hrec
    (B_action st a) rfl
  -- (`typeof action` is a primitive's type name, never "function": the conditional's second branch)
  have hlook : Scope.lookup (bodyState s fo d t #[st, a]) 1 (Sem.inner (FDI.fdiCtx fo d s.envs.size)).lex
      (JSStr.ofString "action") = some a := by
    rw [hlex, Scope.lookup_succ]; simp [hE, hrec, B_action]
  cases a with
  | obj o => exact absurd rfl (ha o)
  | _ =>
    refine wp_typeOf_prim ha rfl (wp_seq ?_)
    split
    · next hc => exact absurd hc (by decide)
    · exact wp_ident 1 hlook (by simp [hfuel]; omega) ⟨rfl, rfl⟩

end

end ReactBSR
