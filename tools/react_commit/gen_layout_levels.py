import sys, re
sys.path.insert(0, "tools/react_commit")
from compose import binders
P = "JSProofs/ReactLayoutFull.lean"
Z = "F64.fin false 0 (-1074)"; M = "F64.fin false 4822457999425536 (-39)"

def level(name, child, doc, cpost, F, C, Cc, tagF, flag_nm, flag_bit, fuel, post, nn, n_inner, KR, KC, cur_val, cur_bind):
    cb = binders(P, child)
    imp = [(nm, t) for nm, k, t in cb if k == "{" and nm not in ("n", "h", "s")]
    exp = [(nm, t) for nm, k, t in cb if k == "(" and nm != "hf"]
    f = F.lower()
    own_imp = f"{{{F} : ObjId}} {{{f}f {f}s : F64}} {{{f}fw {f}fe {f}fc {f}tw {f}te {f}tc {f}sw {f}se {f}sc {f}cw {f}ce {f}cc {f}aw {f}ae {f}ac {f}bw {f}be {f}bc : Bool}}" + cur_bind
    own = [
      f"(h{F} : {F} < s.heap.size) (h{F}k : (s.objEntry {F}).kind.isPlain = true)",
      f"(h{F}f : (s.objEntry {F}).props.get? (.str (JSStr.ofString \"flags\")) = some (.data (.num {f}f) {f}fw {f}fe {f}fc))",
      f"(h{F}t : (s.objEntry {F}).props.get? (.str (JSStr.ofString \"tag\")) =\n      some (.data (.num ({tagF})) {f}tw {f}te {f}tc))",
      f"({flag_nm} : numberBinOp .bitAnd {f}f ({flag_bit}) = {Z})",
      f"(h{F}s : (s.objEntry {F}).props.get? (.str (JSStr.ofString \"subtreeFlags\")) = some (.data (.num {f}s) {f}sw {f}se {f}sc))",
      f"(h{F}sf : (!((numberBinOp .bitAnd {f}s ({M})).isZero ||\n      numberBinOp .bitAnd {f}s ({M}) == F64.nan)) = true)",
      f"(h{F}c : (s.objEntry {F}).props.get? (.str (JSStr.ofString \"child\")) = some (.data (.obj {C}) {f}cw {f}ce {f}cc))",
      f"(h{C}a' : (s.objEntry {C}).props.get? (.str (JSStr.ofString \"alternate\")) = some (.data (.obj {Cc}) {f}aw {f}ae {f}ac))",
      f"(h{C}sib : (s.objEntry {C}).props.get? (.str (JSStr.ofString \"sibling\")) = some (.data .null {f}bw {f}be {f}bc))"]
    binds = [own_imp] + [f"{{{nm} : {t}}}" for nm, t in imp] + [f"({nm} : {t})" for nm, t in exp] + own + [f"(hf : {fuel} ≤ s.fuel)"]
    impargs = " ".join(f"({nm} := {nm})" for nm, t in imp).replace("(t := t)", "(t := .undefined)")
    cname = {"lay_button": "B", "lay_button_leaf": "B", "lay_counter": "K"}[child]
    hC = {"B": "hB", "K": "hK"}[cname]
    s = f"""
set_option maxRecDepth 40000 in
set_option maxHeartbeats 8000000 in
/-- {doc} -/
theorem {name} {{n : Nat}} {{h : σ}} {{s : State}}
    {chr(10).join("    " + b for b in binds).lstrip()} :
    WP eng answer (n + {nn}) h (callImpl eng (.obj fo) t #[rv, {cur_val}, .obj {F}]) s fun v w h' =>
      v = .undefined ∧ s.fuel ≤ w.fuel + {post} ∧ Frame {{}} s w ∧ h' = h := by
  refine ReactLayoutFiber.{ {'K':'cle_counter','R':'cle_root'}[F] } (n := n + {n_inner}) (KR := {KR}) (hlt := hlt) (hk := hk) (hf := by omega)
    (hcode := hcode) (hcls := hcls) (hmode := hmode) (hB := h{F}) (hBk := h{F}k) (hBf := h{F}f) (hBt := h{F}t)
    ({flag_nm} := {flag_nm}) (hG := hG) (hGe := hGe) (hGRT := hGRT) (hGRTv := hGRTv) (hRTo := hRTo)
    (hRTc := ⟨_, hRTk⟩) (hRT := ?_)
  intro w h1 hw hfw
  have hF' : w.objEntry {F} = s.objEntry {F} := objEntry_frame0 hw h{F}
  have hC' : w.objEntry {C} = s.objEntry {C} := objEntry_frame0 hw h{C}
  refine wp_mono (ReactLayoutTraverse.rtl_one_eq (s := w) (d := dRT) (KC := {KC}) (hlt := lt_heap_of_frame hw hRTo)
    (hk := by rw [objEntry_frame0 hw hRTo]; exact hRTk) (hf := by omega) (hcode := hRTcode) (hcls := hRTcls)
    (hmode := hRTmode) (hG := by rw [hRTenv]; exact lt_envs_of_frame hw hG)
    (hGe := by rw [hRTenv, envEntry_frame0 hw hG]; exact hGe) (hGC := hGC) (hGCv := hGCv)
    (hCo := lt_heap_of_frame hw hlt) (hCc := ⟨_, by rw [objEntry_frame0 hw hlt]; exact hk⟩)
    (hP := lt_heap_of_frame hw h{F}) (hPk := by rw [hF']; exact h{F}k) (hPs := by rw [hF']; exact h{F}s)
    (hsf := h{F}sf) (hPc := by rw [hF']; exact h{F}c) (hCx := lt_heap_of_frame hw h{C})
    (hCxk := by rw [hC']; exact h{C}k) (hCa := by rw [hC']; exact h{C}a') (hC := ?_)) ?_
  · intro w2 h2 hw2 hfw2
    have hw0 := frame_empty_trans hw hw2
    refine wp_mono (Q := fun v w h' => v = .undefined ∧ w2.fuel ≤ w.fuel + {cpost} ∧ Frame {{}} w2 w ∧ h' = h2) ?_ ?_
    · apply {child} (s := w2) {impargs} (hf := by omega)
      all_goals rebase_tac hw0
    · rintro v w' h' ⟨-, hfu, hF, rfl⟩
      have hw1 := frame_empty_trans hw0 hF
      exact ⟨hF, by omega, rfl, lt_heap_of_frame hw1 h{C}, by rw [objEntry_frame0 hw1 h{C}]; exact h{C}k, _, _, _,
        by rw [objEntry_frame0 hw1 h{C}]; exact h{C}sib⟩
  · rintro v w' h' ⟨-, hfu, rfl, hF⟩
    exact ⟨hF, by omega, rfl⟩
"""
    return s

import re as _re
src = open(P).read()
for nm in ("lay_counter", "lay_root"):
    a = src.find("\nset_option maxRecDepth 40000 in\nset_option maxHeartbeats 8000000 in\n/-- **The counter**" if nm == "lay_counter" else
                 "\nset_option maxRecDepth 40000 in\nset_option maxHeartbeats 8000000 in\n/-- **The host root**")
    if a >= 0:
        b = src.find("\nset_option maxRecDepth", a + 10)
        if b < 0: b = src.index("\nend\n\nend ReactLayoutFull")
        src = src[:a] + src[b:]
open(P, "w").write(src)
src = open(P).read(); i = src.index("\nend\n\nend ReactLayoutFull")
c = level("lay_counter", "lay_button_leaf", "**The counter** `K` (tag 0, no layout hook) over the button (a leaf).", 240, "K", "B", "Bc",
    Z, "h4", "F64.fin false 4503599627370496 (-50)", 1340, 1240, 6, 4, 1040, 840, "kv", " {kv : Value}")
src = src[:i] + "\n" + c + src[i:]
open(P, "w").write(src)
src = open(P).read(); i = src.index("\nend\n\nend ReactLayoutFull")
r = level("lay_root", "lay_counter", "**The host root** `R` (tag 3, no callbacks) over the counter.", 1240, "R", "K", "Kc",
    "F64.fin false 6755399441055744 (-51)", "h64", "F64.fin false 4503599627370496 (-46)", 1840, 1740, 8, 6, 1540, 1340,
    "rcv", " {rcv : Value}")
r = r.replace("{R : ObjId}", "{R Kc : ObjId}", 1)
j = r.index("theorem lay_root")
r = r[:j] + r[j:].replace("\n    {kv : Value}", "", 1).replace("(kv := kv)", "(kv := .obj Kc)", 1)
src = src[:i] + "\n" + r + src[i:]
open(P, "w").write(src)
