import JSProofs.FactsForm
import JSProofs.ReactBeforeMutation
import JSProofs.ReactSelection

/-! `facts_form` on real specs: their property, kind, binding and frame-closed premises as one list of facts;
`facts_apart` deciding which facts a footprint misses. -/

facts_form ReactBeforeMutation.cbm_spec
facts_form ReactBeforeMutation.cbmc_root
facts_form ReactSelection.hsc_spec

open ES Logic in
/-- Facts of `R` and of `d.env`'s binding `current` pass through commitBeforeMutation's frame (`FB d.env`), which
writes other bindings of `d.env`. -/
example (R : ObjId) (d : FuncData) (oG : Option EnvId) (v : Value) (P : Option Binding → Prop) :
    Facts.Apart (ReactBeforeMutation.FB d.env)
      [.prop R (.str (JSStr.ofString "current")) (some (.data v true true true)),
       .bind d.env oG (JSStr.ofString "current") P, .kindP R (fun _ => True)] := by
  facts_apart
  exact ⟨by simp, by simp⟩

#check @ReactSelection.hsc_spec.Pre_frame
#check @ReactSelection.hsc_spec.ofPre

open ES Logic in
/-- **A callee's contract from its spec**: commitBeforeMutationEffects' contract for hasSelectionCapabilities, from
`hsc_spec`'s precondition at every state its frame (`FB d.env`) reaches. (Not from the precondition at its start:
`hsc_spec`'s reads of the DOM hold through frames within `{}` only, and `facts_apart` rightly fails on them; who
holds them through `FB d.env` discharges this premise.) -/
example {eng : Engine} {σ : Type} {answer : HostAnswer σ} {HI : σ → Prop} {n : Nat} {h : σ} {s : State}
    {d : FuncData} {fHS E : ObjId}
    (hS : ∀ w, Frame (ReactBeforeMutation.FB d.env) s w → ∃ (dHS : FuncData) (fTL : ObjId) (bdTL : BuiltinData)
      (nm ce : JSStr), ReactSelection.hsc_spec.Pre (eng := eng) (answer := answer) (HI := HI) (n := n) (h := h)
        (fo := fHS) (d := dHS) (t := .undefined) (s := w) (E := E) (fTL := fTL) (bdTL := bdTL) (nm := nm) (ce := ce)) :
    ∀ w h1, Frame (ReactBeforeMutation.FB d.env) s w → HI h1 → 100 ≤ w.fuel →
      WP eng answer (n + 1) h1 (callImpl eng (.obj fHS) .undefined #[.obj E]) w fun v w' h' =>
        v = .bool false ∧ Frame {} w w' ∧ w.fuel ≤ w'.fuel + 80 ∧ h' = h1 := by
  intro w h1 hw hHI hfu
  obtain ⟨dHS, fTL, bdTL, nm, ce, hp⟩ := hS w hw
  exact ReactSelection.hsc_spec.ofPre (h := h1) hp (by omega) hHI

open ES Logic in
/-- **A precondition through a frame**: `cbmc_root`'s (the fiber's flags, tag, links; the record's bindings) through
a frame writing other properties of the fiber and other objects. -/
example {eng : Engine} {σ : Type} {answer : HostAnswer σ} {n : Nat} {h : σ} {fo : ObjId}
    {d : FuncData} {t : Value} {s w : State} {bG : Std.HashMap JSStr Binding} {oG : Option EnvId} {bdN : Binding}
    {R X : ObjId} {av : Value} {fl : F64} {aw ae ac fw fe fc tw te tc sw se sc rw re rc : Bool} (hRX : R ≠ X)
    (hp : ReactBeforeMutation.cbmc_root.Pre (eng := eng) (answer := answer) (n := n) (h := h) (fo := fo)
      (d := d) (t := t) (s := s) (bG := bG) (oG := oG) (bdN := bdN) (R := R) (av := av) (fl := fl) (aw := aw)
      (ae := ae) (ac := ac) (fw := fw) (fe := fe) (fc := fc) (tw := tw) (te := te) (tc := tc) (sw := sw) (se := se)
      (sc := sc) (rw := rw) (re := re) (rc := rc))
    (hF : Frame ⟨[], [(R, .str (JSStr.ofString "memoizedState")), (X, .str (JSStr.ofString "flags"))], false⟩ s w) :
    ReactBeforeMutation.cbmc_root.Pre (eng := eng) (answer := answer) (n := n) (h := h) (fo := fo)
      (d := d) (t := t) (s := w) (bG := bG) (oG := oG) (bdN := bdN) (R := R) (av := av) (fl := fl) (aw := aw)
      (ae := ae) (ac := ac) (fw := fw) (fe := fe) (fc := fc) (tw := tw) (te := te) (tc := tc) (sw := sw) (se := se)
      (sc := sc) (rw := rw) (re := re) (rc := rc) :=
  ReactBeforeMutation.cbmc_root.Pre_frame w _ hp hF (by facts_apart; exact ⟨by simp [hRX], by simp⟩)
