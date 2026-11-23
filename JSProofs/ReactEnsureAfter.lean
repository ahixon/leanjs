import JSProofs.ReactSpawned
import JSProofs.ReactFlushSync

/-!
# `ensureRootIsScheduled` after the click's commit (zippy docs/react-proofs.md)

`performWorkOnRoot` calls `ensureRootIsScheduled(root)` once the commit returns. The commit's post (`ReactSpawned.Done`)
says the root is scheduled and a microtask already marked (by the commit's own call), so the call only marks sync work
pending (`ReactEnsureRoot.call_flagged`); `ReactFlushSync.After` and the root's finished lanes, which the flush's loop
reads next, hold after it. What the user claims of the page (`Pu`) is left as a fact about the states.
-/

open ES ES.M HostRuns Logic
open Std (HashMap)

namespace ReactEnsureAfter

theorem bind_value {m : HashMap JSStr Binding} {k : JSStr} {v : Value} (h : (m[k]?.bind (·.value)) = some v) :
    ∃ bd, m[k]? = some bd ∧ bd.value = some v := by
  cases e : m[k]? with
  | none => rw [e] at h; simp at h
  | some bd => rw [e] at h; exact ⟨bd, rfl, by simpa using h⟩

theorem binds_ne_of {fp : Footprint} {e g : EnvId} (hall : fp.binds.all (fun q => q.1 == e) = true) (hne : e ≠ g) :
    ∀ p, p ∈ fp.binds → p.1 ≠ g := fun p hp => by
  have := List.all_eq_true.mp hall p hp
  simp only [beq_iff_eq] at this
  rw [this]; exact hne

section
variable {eng : Engine} {σ : Type} {answer : HostAnswer σ}

theorem ensure_call {n : Nat} {h : σ} {fo : ObjId} {x w sW sP : State} {g : EnvId}
    {oG : Option EnvId} {R : ObjId} {bdF bEn : Binding} {fp : Footprint} {Pu : State → σ → Prop}
    (hD : ReactSpawned.Done x g oG R bdF bEn fo) (hF : Frame fp x w)
    (hfpB : ∀ p, p ∈ fp.binds → p.1 ≠ g) (hfpP : ∀ p, p ∈ fp.props → p.1 ≠ R) (hf : 20 ≤ w.fuel)
    (hPu : ∀ w', Frame (ReactEnsureRoot.fpS g) w w' → Pu ((w'.restore sW).restore sP) h) :
    WP eng answer (n + 1) h (callImpl eng (.obj fo) .undefined #[.obj R]) w fun _ w' h' =>
      Frame (ReactEnsureRoot.fpS g) w w' ∧ w.fuel ≤ w'.fuel + 20 ∧
      ReactFlushSync.After ((w'.restore sW).restore sP) g oG R bdF ∧
      (∃ a b c, (((w'.restore sW).restore sP).objEntry R).props.get? (.str "pendingLanes") =
        some (.data (.num (F64.fin false 0 (-1074))) a b c)) ∧
      Pu ((w'.restore sW).restore sP) h' := by
  obtain ⟨⟨bW, hdW, g1, g2, g3, g4, bdm, g5, g5m⟩, ⟨pa, pb, pc, hPL⟩,
    ⟨bW2, bdW, bdL, lv, hd2, hWR, hWRv, hRL, hRLv, hFS, -⟩, ⟨na, nb, nc, hNx⟩, ⟨ca, cb, cc, hCa⟩, ⟨ta, tb, tc, hTo⟩,
    hg, hR, hRk, hfo, dE, hk0, hcode, hcls, hmode, hdenv⟩ := hD
  have hlt : fo < w.heap.size := Nat.lt_of_lt_of_le hfo hF.heap_le
  have hk : (w.objEntry fo).kind = .func dE := by rw [kind_frame hF hfo]; exact hk0
  have hb2 : bW = bW2 := by rw [hdW] at hd2; simp only [Option.some.injEq, Prod.mk.injEq] at hd2; exact hd2.1
  subst hb2
  have hEw : w.envEntry g = x.envEntry g := hF.env_eq g hg fun y hy => hfpB _ hy rfl
  have hOw : w.objEntry R = x.objEntry R := hF.obj_eq R hR fun k hk => hfpP _ hk rfl
  have hgw : g < w.envs.size := Nat.lt_of_lt_of_le hg hF.envs_le
  have hRw : R < w.heap.size := Nat.lt_of_lt_of_le hR hF.heap_le
  obtain ⟨bF, hF1, hF1v⟩ := bind_value g1
  obtain ⟨bL, hL1, hL1v⟩ := bind_value g2
  obtain ⟨bM, hM1, hM1v⟩ := bind_value g3
  obtain ⟨bD, hD1, hD1v⟩ := bind_value g4
  have hMe : bM = bdm := by rw [hM1] at g5; exact Option.some.inj g5
  subst hMe
  refine wp_mono (ReactEnsureRoot.call_flagged (n := n) (d := dE) (t := .undefined) (bG := bW) (oG := oG)
    hlt hk (by omega) hcode hcls hmode (by rw [hdenv]; exact hgw) (by rw [hdenv, hEw]; exact hdW)
    hF1 hF1v hL1 hL1v hM1 g5m (by rw [hM1v]; rfl) hD1 hD1v hRw (by rw [hOw]; exact hRk)) ?_
  rintro v w' h' ⟨-, hS, hfu, rfl, -⟩
  rw [hdenv] at hS
  have hO' : w'.objEntry R = x.objEntry R := by
    rw [hS.obj_eq R hRw (fun k hk => by simp [ReactEnsureRoot.fpS] at hk), hOw]
  obtain ⟨bW', hdW', hxW'⟩ := declLike_frame hS hgw (by rw [hEw]; exact hdW)
  refine ⟨hS, hfu, ⟨⟨bW', bdW, bdL, lv, ?_, ?_, hWRv, ?_, hRLv, ?_⟩, ?_, ?_, ?_⟩, ?_, hPu w' hS⟩
  · simp only [restore_envEntry]; exact hdW'
  · rw [hxW' _ (by simp [ReactEnsureRoot.fpS])]; exact hWR
  · rw [hxW' _ (by simp [ReactEnsureRoot.fpS])]; exact hRL
  · rw [hxW' _ (by simp [ReactEnsureRoot.fpS])]; exact hFS
  · exact ⟨na, nb, nc, by simp only [restore_objEntry, hO']; exact hNx⟩
  · exact ⟨ca, cb, cc, by simp only [restore_objEntry, hO']; exact hCa⟩
  · exact ⟨ta, tb, tc, by simp only [restore_objEntry, hO']; exact hTo⟩
  · exact ⟨pa, pb, pc, by simp only [restore_objEntry, hO']; exact hPL⟩

end

end ReactEnsureAfter
