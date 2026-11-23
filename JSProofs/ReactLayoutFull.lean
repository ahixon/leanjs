import JSProofs.ReactLayoutFiber
import JSProofs.ReactLayoutTraverse

/-!
# The click's layout pass, composed (zippy docs/react-proofs.md)

`commitLayoutEffectOnFiber` from each of the counter's fibers down, its traversal discharged by
`recursivelyTraverseLayoutEffects` (`rtl_none` at the text, `rtl_one_eq` above it): nothing written (`Frame {}`) and
the host state, the DOM, unchanged.
-/

open ES ES.M HostRuns Logic
open Std (HashMap)

namespace ReactLayoutFull

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ}

set_option maxRecDepth 40000 in
set_option maxHeartbeats 8000000 in
/-- **The text fiber** `X` (tag 6, no layout flags below it). -/
theorem lay_text {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t : Value} {s : State}
    {rv cv : Value} {X : ObjId} {fl sf : F64} {fw fe fc tw te tc qw qe qc : Bool}
    {bG : HashMap JSStr Binding} {oG : Option EnvId} {bdRT : Binding} {fRT : ObjId} {dRT : FuncData}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : 340 ≤ s.fuel)
    (hcode : d.code = CLEGen.commitLayoutEffectOnFiber_func) (hcls : d.isClassCtor = false)
    (hmode : d.thisMode = .strict)
    (hG : d.env < s.envs.size) (hGe : Scope.declLike? (s.envEntry d.env) = some (bG, oG))
    (hGRT : bG[JSStr.ofString "recursivelyTraverseLayoutEffects"]? = some bdRT) (hGRTv : bdRT.value = some (.obj fRT))
    (hRTo : fRT < s.heap.size) (hRTk : (s.objEntry fRT).kind = .func dRT)
    (hRTcode : dRT.code = RTLGen.recursivelyTraverseLayoutEffects_func) (hRTcls : dRT.isClassCtor = false)
    (hRTmode : dRT.thisMode = .strict)
    (hX : X < s.heap.size) (hXk : (s.objEntry X).kind.isPlain = true)
    (hXf : (s.objEntry X).props.get? (.str (JSStr.ofString "flags")) = some (.data (.num fl) fw fe fc))
    (hXt : (s.objEntry X).props.get? (.str (JSStr.ofString "tag")) =
      some (.data (.num (F64.fin false 6755399441055744 (-50))) tw te tc))
    (hXs : (s.objEntry X).props.get? (.str (JSStr.ofString "subtreeFlags")) = some (.data (.num sf) qw qe qc))
    (hsf : numberBinOp .bitAnd sf (F64.fin false 4822457999425536 (-39)) = F64.fin false 0 (-1074)) :
    WP eng answer (n + 2) h (callImpl eng (.obj fo) t #[rv, cv, .obj X]) s fun v w h' =>
      v = .undefined ∧ s.fuel ≤ w.fuel + 240 ∧ Frame {} s w ∧ h' = h := by
  refine ReactLayoutFiber.cle_text (KR := 40) (hlt := hlt) (hk := hk) (hf := by omega) (hcode := hcode)
    (hcls := hcls) (hmode := hmode) (hB := hX) (hBk := hXk) (hBf := hXf) (hBt := hXt) (hG := hG) (hGe := hGe)
    (hGRT := hGRT) (hGRTv := hGRTv) (hRTo := hRTo) (hRTc := ⟨_, hRTk⟩) (hRT := ?_)
  intro w h1 hw hfw
  have hX' : w.objEntry X = s.objEntry X := objEntry_frame0 hw hX
  refine wp_mono (ReactLayoutTraverse.rtl_none (s := w) (hlt := lt_heap_of_frame hw hRTo)
    (hk := by rw [objEntry_frame0 hw hRTo]; exact hRTk) (hf := hfw) (hcode := hRTcode) (hcls := hRTcls)
    (hmode := hRTmode) (hP := lt_heap_of_frame hw hX) (hPk := by rw [hX']; exact hXk) (hPs := by rw [hX']; exact hXs)
    (hsf := hsf)) ?_
  rintro v w' h' ⟨-, hF, hfu, rfl⟩
  exact ⟨hF, hfu, rfl⟩


set_option maxRecDepth 40000 in
set_option maxHeartbeats 8000000 in
/-- **The button** `B` (tag 5, current `Bc`, no ref) over its text `X`. -/
theorem lay_button {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t : Value} {s : State}
    {rv xv : Value} {B Bc X : ObjId} {bf bs xf xs : F64}
    {bfw bfe bfc btw bte btc bsw bse bsc bcw bce bcc fw fe fc tw te tc qw qe qc aw ae ac sw se sc : Bool}
    {bG : HashMap JSStr Binding} {oG : Option EnvId} {bdRT bdC : Binding} {fRT : ObjId} {dRT : FuncData}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : 840 ≤ s.fuel)
    (hcode : d.code = CLEGen.commitLayoutEffectOnFiber_func) (hcls : d.isClassCtor = false)
    (hmode : d.thisMode = .strict)
    (hG : d.env < s.envs.size) (hGe : Scope.declLike? (s.envEntry d.env) = some (bG, oG))
    (hGRT : bG[JSStr.ofString "recursivelyTraverseLayoutEffects"]? = some bdRT) (hGRTv : bdRT.value = some (.obj fRT))
    (hGC : bG[JSStr.ofString "commitLayoutEffectOnFiber"]? = some bdC) (hGCv : bdC.value = some (.obj fo))
    (hRTo : fRT < s.heap.size) (hRTk : (s.objEntry fRT).kind = .func dRT)
    (hRTcode : dRT.code = RTLGen.recursivelyTraverseLayoutEffects_func) (hRTcls : dRT.isClassCtor = false)
    (hRTmode : dRT.thisMode = .strict) (hRTenv : dRT.env = d.env)
    (hB : B < s.heap.size) (hBk : (s.objEntry B).kind.isPlain = true)
    (hBf : (s.objEntry B).props.get? (.str (JSStr.ofString "flags")) = some (.data (.num bf) bfw bfe bfc))
    (hBt : (s.objEntry B).props.get? (.str (JSStr.ofString "tag")) =
      some (.data (.num (F64.fin false 5629499534213120 (-50))) btw bte btc))
    (h512 : numberBinOp .bitAnd bf (F64.fin false 4503599627370496 (-43)) = F64.fin false 0 (-1074))
    (hBs : (s.objEntry B).props.get? (.str (JSStr.ofString "subtreeFlags")) = some (.data (.num bs) bsw bse bsc))
    (hbs : (!((numberBinOp .bitAnd bs (F64.fin false 4822457999425536 (-39))).isZero ||
      numberBinOp .bitAnd bs (F64.fin false 4822457999425536 (-39)) == F64.nan)) = true)
    (hBc : (s.objEntry B).props.get? (.str (JSStr.ofString "child")) = some (.data (.obj X) bcw bce bcc))
    (hX : X < s.heap.size) (hXk : (s.objEntry X).kind.isPlain = true)
    (hXf : (s.objEntry X).props.get? (.str (JSStr.ofString "flags")) = some (.data (.num xf) fw fe fc))
    (hXt : (s.objEntry X).props.get? (.str (JSStr.ofString "tag")) =
      some (.data (.num (F64.fin false 6755399441055744 (-50))) tw te tc))
    (hXs : (s.objEntry X).props.get? (.str (JSStr.ofString "subtreeFlags")) = some (.data (.num xs) qw qe qc))
    (hxs : numberBinOp .bitAnd xs (F64.fin false 4822457999425536 (-39)) = F64.fin false 0 (-1074))
    (hXa : (s.objEntry X).props.get? (.str (JSStr.ofString "alternate")) = some (.data xv aw ae ac))
    (hXsib : (s.objEntry X).props.get? (.str (JSStr.ofString "sibling")) = some (.data .null sw se sc)) :
    WP eng answer (n + 4) h (callImpl eng (.obj fo) t #[rv, .obj Bc, .obj B]) s fun v w h' =>
      v = .undefined ∧ s.fuel ≤ w.fuel + 740 ∧ Frame {} s w ∧ h' = h := by
  refine ReactLayoutFiber.cle_button (n := n + 2) (KR := 540) (hlt := hlt) (hk := hk) (hf := by omega)
    (hcode := hcode) (hcls := hcls) (hmode := hmode) (hB := hB) (hBk := hBk) (hBf := hBf) (hBt := hBt)
    (h512 := h512) (hG := hG) (hGe := hGe) (hGRT := hGRT) (hGRTv := hGRTv) (hRTo := hRTo) (hRTc := ⟨_, hRTk⟩)
    (hRT := ?_)
  intro w h1 hw hfw
  have hB' : w.objEntry B = s.objEntry B := objEntry_frame0 hw hB
  have hX' : w.objEntry X = s.objEntry X := objEntry_frame0 hw hX
  refine wp_mono (ReactLayoutTraverse.rtl_one_eq (s := w) (d := dRT) (KC := 340) (hlt := lt_heap_of_frame hw hRTo)
    (hk := by rw [objEntry_frame0 hw hRTo]; exact hRTk) (hf := by omega) (hcode := hRTcode) (hcls := hRTcls)
    (hmode := hRTmode) (hG := by rw [hRTenv]; exact lt_envs_of_frame hw hG)
    (hGe := by rw [hRTenv, envEntry_frame0 hw hG]; exact hGe) (hGC := hGC) (hGCv := hGCv)
    (hCo := lt_heap_of_frame hw hlt) (hCc := ⟨_, by rw [objEntry_frame0 hw hlt]; exact hk⟩)
    (hP := lt_heap_of_frame hw hB) (hPk := by rw [hB']; exact hBk) (hPs := by rw [hB']; exact hBs) (hsf := hbs)
    (hPc := by rw [hB']; exact hBc) (hCx := lt_heap_of_frame hw hX) (hCxk := by rw [hX']; exact hXk)
    (hCa := by rw [hX']; exact hXa) (hC := ?_)) ?_
  · intro w2 h2 hw2 hfw2
    have hw0 := frame_empty_trans hw hw2
    refine wp_mono (lay_text (s := w2) (hlt := lt_heap_of_frame hw0 hlt) (hk := by rw [objEntry_frame0 hw0 hlt]; exact hk)
      (hf := hfw2) (hcode := hcode) (hcls := hcls) (hmode := hmode) (hG := lt_envs_of_frame hw0 hG)
      (hGe := by rw [envEntry_frame0 hw0 hG]; exact hGe) (hGRT := hGRT) (hGRTv := hGRTv)
      (hRTo := lt_heap_of_frame hw0 hRTo) (hRTk := by rw [objEntry_frame0 hw0 hRTo]; exact hRTk)
      (hRTcode := hRTcode) (hRTcls := hRTcls) (hRTmode := hRTmode) (hX := lt_heap_of_frame hw0 hX)
      (hXk := by rw [objEntry_frame0 hw0 hX]; exact hXk) (hXf := by rw [objEntry_frame0 hw0 hX]; exact hXf)
      (hXt := by rw [objEntry_frame0 hw0 hX]; exact hXt) (hXs := by rw [objEntry_frame0 hw0 hX]; exact hXs)
      (hsf := hxs)) ?_
    rintro v w' h' ⟨-, hfu, hF, rfl⟩
    have hw1 := frame_empty_trans hw0 hF
    exact ⟨hF, by omega, rfl, lt_heap_of_frame hw1 hX, by rw [objEntry_frame0 hw1 hX]; exact hXk, _, _, _,
      by rw [objEntry_frame0 hw1 hX]; exact hXsib⟩
  · rintro v w' h' ⟨-, hfu, rfl, hF⟩
    exact ⟨hF, by omega, rfl⟩


set_option maxRecDepth 40000 in
set_option maxHeartbeats 8000000 in
/-- **The button as a leaf** `B` (tag 5, current `Bc`, no ref, no layout flags below it: its string child is text
content, not a fiber). -/
theorem lay_button_leaf {n : Nat} {h : σ} {fo : ObjId} {d : FuncData} {t : Value} {s : State}
    {rv : Value} {B Bc : ObjId} {bf bs : F64}
    {bfw bfe bfc btw bte btc bsw bse bsc : Bool}
    {bG : HashMap JSStr Binding} {oG : Option EnvId} {bdRT bdC : Binding} {fRT : ObjId} {dRT : FuncData}
    (hlt : fo < s.heap.size) (hk : (s.objEntry fo).kind = .func d) (hf : 340 ≤ s.fuel)
    (hcode : d.code = CLEGen.commitLayoutEffectOnFiber_func) (hcls : d.isClassCtor = false)
    (hmode : d.thisMode = .strict)
    (hG : d.env < s.envs.size) (hGe : Scope.declLike? (s.envEntry d.env) = some (bG, oG))
    (hGRT : bG[JSStr.ofString "recursivelyTraverseLayoutEffects"]? = some bdRT) (hGRTv : bdRT.value = some (.obj fRT))
    (hGC : bG[JSStr.ofString "commitLayoutEffectOnFiber"]? = some bdC) (hGCv : bdC.value = some (.obj fo))
    (hRTo : fRT < s.heap.size) (hRTk : (s.objEntry fRT).kind = .func dRT)
    (hRTcode : dRT.code = RTLGen.recursivelyTraverseLayoutEffects_func) (hRTcls : dRT.isClassCtor = false)
    (hRTmode : dRT.thisMode = .strict) (hRTenv : dRT.env = d.env)
    (hB : B < s.heap.size) (hBk : (s.objEntry B).kind.isPlain = true)
    (hBf : (s.objEntry B).props.get? (.str (JSStr.ofString "flags")) = some (.data (.num bf) bfw bfe bfc))
    (hBt : (s.objEntry B).props.get? (.str (JSStr.ofString "tag")) =
      some (.data (.num (F64.fin false 5629499534213120 (-50))) btw bte btc))
    (h512 : numberBinOp .bitAnd bf (F64.fin false 4503599627370496 (-43)) = F64.fin false 0 (-1074))
    (hBs : (s.objEntry B).props.get? (.str (JSStr.ofString "subtreeFlags")) = some (.data (.num bs) bsw bse bsc))
    (hbs : numberBinOp .bitAnd bs (F64.fin false 4822457999425536 (-39)) = F64.fin false 0 (-1074)) :
    WP eng answer (n + 2) h (callImpl eng (.obj fo) t #[rv, .obj Bc, .obj B]) s fun v w h' =>
      v = .undefined ∧ s.fuel ≤ w.fuel + 240 ∧ Frame {} s w ∧ h' = h := by
  refine ReactLayoutFiber.cle_button (KR := 40) (hlt := hlt) (hk := hk) (hf := by omega) (hcode := hcode)
    (hcls := hcls) (hmode := hmode) (hB := hB) (hBk := hBk) (hBf := hBf) (hBt := hBt) (h512 := h512) (hG := hG)
    (hGe := hGe) (hGRT := hGRT) (hGRTv := hGRTv) (hRTo := hRTo) (hRTc := ⟨_, hRTk⟩) (hRT := ?_)
  intro w h1 hw hfw
  have hB' : w.objEntry B = s.objEntry B := objEntry_frame0 hw hB
  refine wp_mono (ReactLayoutTraverse.rtl_none (s := w) (hlt := lt_heap_of_frame hw hRTo)
    (hk := by rw [objEntry_frame0 hw hRTo]; exact hRTk) (hf := hfw) (hcode := hRTcode) (hcls := hRTcls)
    (hmode := hRTmode) (hP := lt_heap_of_frame hw hB) (hPk := by rw [hB']; exact hBk) (hPs := by rw [hB']; exact hBs)
    (hsf := hbs)) ?_
  rintro v w' h' ⟨-, hF, hfu, rfl⟩
  exact ⟨hF, hfu, rfl⟩




set_option maxRecDepth 40000 in
set_option maxHeartbeats 8000000 in
/-- **The counter** `K` (tag 0, no layout hook) over the button (a leaf). -/
theorem lay_counter {n : Nat} {h : σ} {s : State}
    {K : ObjId} {kf ks : F64} {kfw kfe kfc ktw kte ktc ksw kse ksc kcw kce kcc kaw kae kac kbw kbe kbc : Bool} {kv : Value}
    {fo : ObjId}
    {d : FuncData}
    {t : Value}
    {rv : Value}
    {B : ObjId}
    {Bc : ObjId}
    {bf : F64}
    {bs : F64}
    {bfw : Bool}
    {bfe : Bool}
    {bfc : Bool}
    {btw : Bool}
    {bte : Bool}
    {btc : Bool}
    {bsw : Bool}
    {bse : Bool}
    {bsc : Bool}
    {bG : HashMap JSStr Binding}
    {oG : Option EnvId}
    {bdRT : Binding}
    {bdC : Binding}
    {fRT : ObjId}
    {dRT : FuncData}
    (hlt : fo < s.heap.size)
    (hk : (s.objEntry fo).kind = .func d)
    (hcode : d.code = CLEGen.commitLayoutEffectOnFiber_func)
    (hcls : d.isClassCtor = false)
    (hmode : d.thisMode = .strict)
    (hG : d.env < s.envs.size)
    (hGe : Scope.declLike? (s.envEntry d.env) = some (bG, oG))
    (hGRT : bG[JSStr.ofString "recursivelyTraverseLayoutEffects"]? = some bdRT)
    (hGRTv : bdRT.value = some (.obj fRT))
    (hGC : bG[JSStr.ofString "commitLayoutEffectOnFiber"]? = some bdC)
    (hGCv : bdC.value = some (.obj fo))
    (hRTo : fRT < s.heap.size)
    (hRTk : (s.objEntry fRT).kind = .func dRT)
    (hRTcode : dRT.code = RTLGen.recursivelyTraverseLayoutEffects_func)
    (hRTcls : dRT.isClassCtor = false)
    (hRTmode : dRT.thisMode = .strict)
    (hRTenv : dRT.env = d.env)
    (hB : B < s.heap.size)
    (hBk : (s.objEntry B).kind.isPlain = true)
    (hBf : (s.objEntry B).props.get? (.str (JSStr.ofString "flags")) = some (.data (.num bf) bfw bfe bfc))
    (hBt : (s.objEntry B).props.get? (.str (JSStr.ofString "tag")) =
      some (.data (.num (F64.fin false 5629499534213120 (-50))) btw bte btc))
    (h512 : numberBinOp .bitAnd bf (F64.fin false 4503599627370496 (-43)) = F64.fin false 0 (-1074))
    (hBs : (s.objEntry B).props.get? (.str (JSStr.ofString "subtreeFlags")) = some (.data (.num bs) bsw bse bsc))
    (hbs : numberBinOp .bitAnd bs (F64.fin false 4822457999425536 (-39)) = F64.fin false 0 (-1074))
    (hK : K < s.heap.size) (hKk : (s.objEntry K).kind.isPlain = true)
    (hKf : (s.objEntry K).props.get? (.str (JSStr.ofString "flags")) = some (.data (.num kf) kfw kfe kfc))
    (hKt : (s.objEntry K).props.get? (.str (JSStr.ofString "tag")) =
      some (.data (.num (F64.fin false 0 (-1074))) ktw kte ktc))
    (h4 : numberBinOp .bitAnd kf (F64.fin false 4503599627370496 (-50)) = F64.fin false 0 (-1074))
    (hKs : (s.objEntry K).props.get? (.str (JSStr.ofString "subtreeFlags")) = some (.data (.num ks) ksw kse ksc))
    (hKsf : (!((numberBinOp .bitAnd ks (F64.fin false 4822457999425536 (-39))).isZero ||
      numberBinOp .bitAnd ks (F64.fin false 4822457999425536 (-39)) == F64.nan)) = true)
    (hKc : (s.objEntry K).props.get? (.str (JSStr.ofString "child")) = some (.data (.obj B) kcw kce kcc))
    (hBa' : (s.objEntry B).props.get? (.str (JSStr.ofString "alternate")) = some (.data (.obj Bc) kaw kae kac))
    (hBsib : (s.objEntry B).props.get? (.str (JSStr.ofString "sibling")) = some (.data .null kbw kbe kbc))
    (hf : 1340 ≤ s.fuel) :
    WP eng answer (n + 6) h (callImpl eng (.obj fo) t #[rv, kv, .obj K]) s fun v w h' =>
      v = .undefined ∧ s.fuel ≤ w.fuel + 1240 ∧ Frame {} s w ∧ h' = h := by
  refine ReactLayoutFiber.cle_counter (n := n + 4) (KR := 1040) (hlt := hlt) (hk := hk) (hf := by omega)
    (hcode := hcode) (hcls := hcls) (hmode := hmode) (hB := hK) (hBk := hKk) (hBf := hKf) (hBt := hKt)
    (h4 := h4) (hG := hG) (hGe := hGe) (hGRT := hGRT) (hGRTv := hGRTv) (hRTo := hRTo)
    (hRTc := ⟨_, hRTk⟩) (hRT := ?_)
  intro w h1 hw hfw
  have hF' : w.objEntry K = s.objEntry K := objEntry_frame0 hw hK
  have hC' : w.objEntry B = s.objEntry B := objEntry_frame0 hw hB
  refine wp_mono (ReactLayoutTraverse.rtl_one_eq (s := w) (d := dRT) (KC := 840) (hlt := lt_heap_of_frame hw hRTo)
    (hk := by rw [objEntry_frame0 hw hRTo]; exact hRTk) (hf := by omega) (hcode := hRTcode) (hcls := hRTcls)
    (hmode := hRTmode) (hG := by rw [hRTenv]; exact lt_envs_of_frame hw hG)
    (hGe := by rw [hRTenv, envEntry_frame0 hw hG]; exact hGe) (hGC := hGC) (hGCv := hGCv)
    (hCo := lt_heap_of_frame hw hlt) (hCc := ⟨_, by rw [objEntry_frame0 hw hlt]; exact hk⟩)
    (hP := lt_heap_of_frame hw hK) (hPk := by rw [hF']; exact hKk) (hPs := by rw [hF']; exact hKs)
    (hsf := hKsf) (hPc := by rw [hF']; exact hKc) (hCx := lt_heap_of_frame hw hB)
    (hCxk := by rw [hC']; exact hBk) (hCa := by rw [hC']; exact hBa') (hC := ?_)) ?_
  · intro w2 h2 hw2 hfw2
    have hw0 := frame_empty_trans hw hw2
    refine wp_mono (Q := fun v w h' => v = .undefined ∧ w2.fuel ≤ w.fuel + 240 ∧ Frame {} w2 w ∧ h' = h2) ?_ ?_
    · apply lay_button_leaf (s := w2) (fo := fo) (d := d) (t := .undefined) (rv := rv) (B := B) (Bc := Bc) (bf := bf) (bs := bs) (bfw := bfw) (bfe := bfe) (bfc := bfc) (btw := btw) (bte := bte) (btc := btc) (bsw := bsw) (bse := bse) (bsc := bsc) (bG := bG) (oG := oG) (bdRT := bdRT) (bdC := bdC) (fRT := fRT) (dRT := dRT) (hf := by omega)
      all_goals rebase_tac hw0
    · rintro v w' h' ⟨-, hfu, hF, rfl⟩
      have hw1 := frame_empty_trans hw0 hF
      exact ⟨hF, by omega, rfl, lt_heap_of_frame hw1 hB, by rw [objEntry_frame0 hw1 hB]; exact hBk, _, _, _,
        by rw [objEntry_frame0 hw1 hB]; exact hBsib⟩
  · rintro v w' h' ⟨-, hfu, rfl, hF⟩
    exact ⟨hF, by omega, rfl⟩


set_option maxRecDepth 40000 in
set_option maxHeartbeats 8000000 in
/-- **The host root** `R` (tag 3, no callbacks) over the counter. -/
theorem lay_root {n : Nat} {h : σ} {s : State}
    {R Kc : ObjId} {rf rs : F64} {rfw rfe rfc rtw rte rtc rsw rse rsc rcw rce rcc raw rae rac rbw rbe rbc : Bool} {rcv : Value}
    {K : ObjId}
    {kf : F64}
    {ks : F64}
    {kfw : Bool}
    {kfe : Bool}
    {kfc : Bool}
    {ktw : Bool}
    {kte : Bool}
    {ktc : Bool}
    {ksw : Bool}
    {kse : Bool}
    {ksc : Bool}
    {kcw : Bool}
    {kce : Bool}
    {kcc : Bool}
    {kaw : Bool}
    {kae : Bool}
    {kac : Bool}
    {kbw : Bool}
    {kbe : Bool}
    {kbc : Bool}
    {fo : ObjId}
    {d : FuncData}
    {t : Value}
    {rv : Value}
    {B : ObjId}
    {Bc : ObjId}
    {bf : F64}
    {bs : F64}
    {bfw : Bool}
    {bfe : Bool}
    {bfc : Bool}
    {btw : Bool}
    {bte : Bool}
    {btc : Bool}
    {bsw : Bool}
    {bse : Bool}
    {bsc : Bool}
    {bG : HashMap JSStr Binding}
    {oG : Option EnvId}
    {bdRT : Binding}
    {bdC : Binding}
    {fRT : ObjId}
    {dRT : FuncData}
    (hlt : fo < s.heap.size)
    (hk : (s.objEntry fo).kind = .func d)
    (hcode : d.code = CLEGen.commitLayoutEffectOnFiber_func)
    (hcls : d.isClassCtor = false)
    (hmode : d.thisMode = .strict)
    (hG : d.env < s.envs.size)
    (hGe : Scope.declLike? (s.envEntry d.env) = some (bG, oG))
    (hGRT : bG[JSStr.ofString "recursivelyTraverseLayoutEffects"]? = some bdRT)
    (hGRTv : bdRT.value = some (.obj fRT))
    (hGC : bG[JSStr.ofString "commitLayoutEffectOnFiber"]? = some bdC)
    (hGCv : bdC.value = some (.obj fo))
    (hRTo : fRT < s.heap.size)
    (hRTk : (s.objEntry fRT).kind = .func dRT)
    (hRTcode : dRT.code = RTLGen.recursivelyTraverseLayoutEffects_func)
    (hRTcls : dRT.isClassCtor = false)
    (hRTmode : dRT.thisMode = .strict)
    (hRTenv : dRT.env = d.env)
    (hB : B < s.heap.size)
    (hBk : (s.objEntry B).kind.isPlain = true)
    (hBf : (s.objEntry B).props.get? (.str (JSStr.ofString "flags")) = some (.data (.num bf) bfw bfe bfc))
    (hBt : (s.objEntry B).props.get? (.str (JSStr.ofString "tag")) =
      some (.data (.num (F64.fin false 5629499534213120 (-50))) btw bte btc))
    (h512 : numberBinOp .bitAnd bf (F64.fin false 4503599627370496 (-43)) = F64.fin false 0 (-1074))
    (hBs : (s.objEntry B).props.get? (.str (JSStr.ofString "subtreeFlags")) = some (.data (.num bs) bsw bse bsc))
    (hbs : numberBinOp .bitAnd bs (F64.fin false 4822457999425536 (-39)) = F64.fin false 0 (-1074))
    (hK : K < s.heap.size)
    (hKk : (s.objEntry K).kind.isPlain = true)
    (hKf : (s.objEntry K).props.get? (.str (JSStr.ofString "flags")) = some (.data (.num kf) kfw kfe kfc))
    (hKt : (s.objEntry K).props.get? (.str (JSStr.ofString "tag")) =
      some (.data (.num (F64.fin false 0 (-1074))) ktw kte ktc))
    (h4 : numberBinOp .bitAnd kf (F64.fin false 4503599627370496 (-50)) = F64.fin false 0 (-1074))
    (hKs : (s.objEntry K).props.get? (.str (JSStr.ofString "subtreeFlags")) = some (.data (.num ks) ksw kse ksc))
    (hKsf : (!((numberBinOp .bitAnd ks (F64.fin false 4822457999425536 (-39))).isZero ||
      numberBinOp .bitAnd ks (F64.fin false 4822457999425536 (-39)) == F64.nan)) = true)
    (hKc : (s.objEntry K).props.get? (.str (JSStr.ofString "child")) = some (.data (.obj B) kcw kce kcc))
    (hBa' : (s.objEntry B).props.get? (.str (JSStr.ofString "alternate")) = some (.data (.obj Bc) kaw kae kac))
    (hBsib : (s.objEntry B).props.get? (.str (JSStr.ofString "sibling")) = some (.data .null kbw kbe kbc))
    (hR : R < s.heap.size) (hRk : (s.objEntry R).kind.isPlain = true)
    (hRf : (s.objEntry R).props.get? (.str (JSStr.ofString "flags")) = some (.data (.num rf) rfw rfe rfc))
    (hRt : (s.objEntry R).props.get? (.str (JSStr.ofString "tag")) =
      some (.data (.num (F64.fin false 6755399441055744 (-51))) rtw rte rtc))
    (h64 : numberBinOp .bitAnd rf (F64.fin false 4503599627370496 (-46)) = F64.fin false 0 (-1074))
    (hRs : (s.objEntry R).props.get? (.str (JSStr.ofString "subtreeFlags")) = some (.data (.num rs) rsw rse rsc))
    (hRsf : (!((numberBinOp .bitAnd rs (F64.fin false 4822457999425536 (-39))).isZero ||
      numberBinOp .bitAnd rs (F64.fin false 4822457999425536 (-39)) == F64.nan)) = true)
    (hRc : (s.objEntry R).props.get? (.str (JSStr.ofString "child")) = some (.data (.obj K) rcw rce rcc))
    (hKa' : (s.objEntry K).props.get? (.str (JSStr.ofString "alternate")) = some (.data (.obj Kc) raw rae rac))
    (hKsib : (s.objEntry K).props.get? (.str (JSStr.ofString "sibling")) = some (.data .null rbw rbe rbc))
    (hf : 1840 ≤ s.fuel) :
    WP eng answer (n + 8) h (callImpl eng (.obj fo) t #[rv, rcv, .obj R]) s fun v w h' =>
      v = .undefined ∧ s.fuel ≤ w.fuel + 1740 ∧ Frame {} s w ∧ h' = h := by
  refine ReactLayoutFiber.cle_root (n := n + 6) (KR := 1540) (hlt := hlt) (hk := hk) (hf := by omega)
    (hcode := hcode) (hcls := hcls) (hmode := hmode) (hB := hR) (hBk := hRk) (hBf := hRf) (hBt := hRt)
    (h64 := h64) (hG := hG) (hGe := hGe) (hGRT := hGRT) (hGRTv := hGRTv) (hRTo := hRTo)
    (hRTc := ⟨_, hRTk⟩) (hRT := ?_)
  intro w h1 hw hfw
  have hF' : w.objEntry R = s.objEntry R := objEntry_frame0 hw hR
  have hC' : w.objEntry K = s.objEntry K := objEntry_frame0 hw hK
  refine wp_mono (ReactLayoutTraverse.rtl_one_eq (s := w) (d := dRT) (KC := 1340) (hlt := lt_heap_of_frame hw hRTo)
    (hk := by rw [objEntry_frame0 hw hRTo]; exact hRTk) (hf := by omega) (hcode := hRTcode) (hcls := hRTcls)
    (hmode := hRTmode) (hG := by rw [hRTenv]; exact lt_envs_of_frame hw hG)
    (hGe := by rw [hRTenv, envEntry_frame0 hw hG]; exact hGe) (hGC := hGC) (hGCv := hGCv)
    (hCo := lt_heap_of_frame hw hlt) (hCc := ⟨_, by rw [objEntry_frame0 hw hlt]; exact hk⟩)
    (hP := lt_heap_of_frame hw hR) (hPk := by rw [hF']; exact hRk) (hPs := by rw [hF']; exact hRs)
    (hsf := hRsf) (hPc := by rw [hF']; exact hRc) (hCx := lt_heap_of_frame hw hK)
    (hCxk := by rw [hC']; exact hKk) (hCa := by rw [hC']; exact hKa') (hC := ?_)) ?_
  · intro w2 h2 hw2 hfw2
    have hw0 := frame_empty_trans hw hw2
    refine wp_mono (Q := fun v w h' => v = .undefined ∧ w2.fuel ≤ w.fuel + 1240 ∧ Frame {} w2 w ∧ h' = h2) ?_ ?_
    · apply lay_counter (s := w2) (K := K) (kf := kf) (ks := ks) (kfw := kfw) (kfe := kfe) (kfc := kfc) (ktw := ktw) (kte := kte) (ktc := ktc) (ksw := ksw) (kse := kse) (ksc := ksc) (kcw := kcw) (kce := kce) (kcc := kcc) (kaw := kaw) (kae := kae) (kac := kac) (kbw := kbw) (kbe := kbe) (kbc := kbc) (kv := .obj Kc) (fo := fo) (d := d) (t := .undefined) (rv := rv) (B := B) (Bc := Bc) (bf := bf) (bs := bs) (bfw := bfw) (bfe := bfe) (bfc := bfc) (btw := btw) (bte := bte) (btc := btc) (bsw := bsw) (bse := bse) (bsc := bsc) (bG := bG) (oG := oG) (bdRT := bdRT) (bdC := bdC) (fRT := fRT) (dRT := dRT) (hf := by omega)
      all_goals rebase_tac hw0
    · rintro v w' h' ⟨-, hfu, hF, rfl⟩
      have hw1 := frame_empty_trans hw0 hF
      exact ⟨hF, by omega, rfl, lt_heap_of_frame hw1 hK, by rw [objEntry_frame0 hw1 hK]; exact hKk, _, _, _,
        by rw [objEntry_frame0 hw1 hK]; exact hKsib⟩
  · rintro v w' h' ⟨-, hfu, rfl, hF⟩
    exact ⟨hF, by omega, rfl⟩

end

end ReactLayoutFull
