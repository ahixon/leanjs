import JSProofs.JsTactic
import JSProofs.MULGen

/-!
# React's `markUpdateLaneFromFiberToRoot` for a component under the host root (zippy docs/react-proofs.md)

The counter's fiber `F` (with its alternate `Fa`) sits directly under a host-root fiber `P` (tag 3, no parent, with
its alternate `Pa`): the lane goes into `F`'s and `Fa`'s `lanes` and `P`'s and `Pa`'s `childLanes`; nothing is hidden;
the root (`P.stateNode`) is returned.
-/

open ES ES.M HostRuns Logic
open Std (HashMap)

namespace ReactMarkLane

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ}

theorem simple (d : FuncData) (hc : d.code = MULGen.markUpdateLaneFromFiberToRoot_func) : FDI.Simple d := by
  constructor <;> rw [hc] <;> try rfl
  simp [MULGen.markUpdateLaneFromFiberToRoot_func, Func.params, Func.info]

/-- What it writes. -/
def fp (F Fa P Pa : ObjId) : Footprint :=
  ⟨[], [(F, .str "lanes"), (Fa, .str "lanes"), (P, .str "childLanes"), (Pa, .str "childLanes")], false⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000 in
/-- **`markUpdateLaneFromFiberToRoot(F, update, lane)`**, `F.return` the host root's fiber `P`: four lane fields;
returns `P.stateNode`. -/
theorem root_spec {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t update : Value} {s : State}
    {F Fa P Pa Rt : ObjId} {lane fl al pc ac : F64}
    {fe fc ae ac' pe pc' qe qc r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 : Bool}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : 30 ≤ s.fuel)
    (hcode : d.code = MULGen.markUpdateLaneFromFiberToRoot_func) (hcls : d.isClassCtor = false)
    (hmode : d.thisMode = .strict)
    (hF : F < s.heap.size) (hFk : (s.objEntry F).kind.isPlain = true)
    (hFa : Fa < s.heap.size) (hFak : (s.objEntry Fa).kind.isPlain = true)
    (hP : P < s.heap.size) (hPk : (s.objEntry P).kind.isPlain = true)
    (hPa : Pa < s.heap.size) (hPak : (s.objEntry Pa).kind.isPlain = true)
    (d1 : F ≠ Fa) (d2 : F ≠ P) (d3 : F ≠ Pa) (d4 : Fa ≠ P) (d5 : Fa ≠ Pa) (d6 : P ≠ Pa)
    (hFl : (s.objEntry F).props.get? (.str "lanes") = some (.data (.num fl) true fe fc))
    (hFal : (s.objEntry F).props.get? (.str "alternate") = some (.data (.obj Fa) r1 r2 r3))
    (hFr : (s.objEntry F).props.get? (.str "return") = some (.data (.obj P) r4 r5 r6))
    (hFal' : (s.objEntry Fa).props.get? (.str "lanes") = some (.data (.num al) true ae ac'))
    (hPc : (s.objEntry P).props.get? (.str "childLanes") = some (.data (.num pc) true pe pc'))
    (hPal : (s.objEntry P).props.get? (.str "alternate") = some (.data (.obj Pa) r7 r8 r9))
    (hPt : (s.objEntry P).props.get? (.str "tag") = some (.data (.num (F64.fin false 6755399441055744 (-51))) r10 r11 r12))
    (hPr : (s.objEntry P).props.get? (.str "return") = some (.data .null r13 r14 r15))
    (hPs : (s.objEntry P).props.get? (.str "stateNode") = some (.data (.obj Rt) r16 r17 r18))
    (hPac : (s.objEntry Pa).props.get? (.str "childLanes") = some (.data (.num ac) true qe qc)) :
    WP eng answer n h (callImpl eng (.obj fo) t #[.obj F, update, .num lane]) s fun v w h' =>
      v = .obj Rt ∧ Frame (fp F Fa P Pa) s w ∧ s.fuel ≤ w.fuel + 30 ∧ h' = h ∧
      (w.objEntry F).props.get? (.str "lanes") = some (.data (.num (numberBinOp .bitOr fl lane)) true fe fc) ∧
      (w.objEntry Fa).props.get? (.str "lanes") = some (.data (.num (numberBinOp .bitOr al lane)) true ae ac') ∧
      (w.objEntry P).props.get? (.str "childLanes") = some (.data (.num (numberBinOp .bitOr pc lane)) true pe pc') ∧
      (w.objEntry Pa).props.get? (.str "childLanes") = some (.data (.num (numberBinOp .bitOr ac lane)) true qe qc) := by
  apply wp_callGen MULGen.markUpdateLaneFromFiberToRoot_eq (by decide) hlt hk (by omega) hcls hmode
    (by rw [hcode]; rfl) (by rw [hcode]; rfl) (simple d hcode) (by rw [hcode]; rfl) (by rw [hcode]; rfl)
  have hpn : d.code.info.fdi.paramNames = #[JSStr.ofString "sourceFiber", JSStr.ofString "update",
    JSStr.ofString "lane"] := by rw [hcode]; rfl
  have hv : d.code.info.fdi.varNames = #[JSStr.ofString "alternate", JSStr.ofString "isHidden",
    JSStr.ofString "parent"] := by rw [hcode]; rfl
  have hl : FDI.lexDecls d = #[] := by
    simp [FDI.lexDecls, hcode, MULGen.markUpdateLaneFromFiberToRoot_func, Func.info]
  have ha : d.code.isAsync = false := by rw [hcode]; rfl
  clear hcode
  simp only [MULGen.markUpdateLaneFromFiberToRoot]
  js [hpn, hv, hl, ha, hF, hFk, hFa, hFak, hP, hPk, hPa, hPak, d1, d2, d3, d4, d5, d6, Ne.symm d1, Ne.symm d2,
    Ne.symm d3, Ne.symm d4, Ne.symm d5, Ne.symm d6, hFl, hFal, hFr, hFal', hPc, hPal, hPt, hPr, hPs, hPac,
    FDI.fdiCtx, Sem.inner]
  all_goals (repeat' apply And.intro)
  all_goals first | omega | (simp only [fp]; frame_go' [*, Ne.symm d1, Ne.symm d2, Ne.symm d3, Ne.symm d4, Ne.symm d5, Ne.symm d6])

end

end ReactMarkLane
