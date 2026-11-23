import sys; sys.path.insert(0, "tools/react_cuw"); import args as A
CALLER = "JSProofs/ReactCompleteUnit.lean"
bounds = A.caller_bounds(CALLER, "unit_spec")
dl = "dS1 dS2 dS3 dS4 dS5 dS6 dS7 dS8 dS9 dU1 dU2 dU3 dX1 dX2 dX3 dO1 dO2 dO3 dO4 dO5 dO6 hHX hCX hRC hAC hAX hRX".split()
DS = ", ".join(dl + [f"Ne.symm {x}" for x in dl])
ren = {"R": "Rb", "hGCF": "hGCFb", "hGCFv": "hGCFbv", "hRX": "hRbX", "cfw": "true", "cfe": "fe'", "cfc": "fc'",
       "tW": ".undefined"}
a1 = A.transfer("JSProofs/ReactCompleteButton.lean", "button_spec", ren, {"hGe": "(by rw [gG1]; exact hGe)"},
                {"R": "Rb"}, bounds, 1, DS)
s = open(CALLER).read()
F = "hW, hWk, hGCW, hGCWv, hGe, hG, hG1, hne, Ne.symm hne"
block = f"""  refine ⟨by js_norm [CallableC, {F}], ?_⟩
  refine ReactReconcileFibers.wp_gen_state fun St hSt => ?_
  have gZ1 : s.heap.size ≤ St.heap.size := by rw [hSt]; js_norm; try exact Nat.le_refl _
  have gK1 : ∀ o, o < s.heap.size → (St.objEntry o).kind = (s.objEntry o).kind := by intro o ho; rw [hSt]; js_norm
  have gP1 : ∀ o k, (o, k) ∉ ([] : List (ObjId × PropKey)) → o < s.heap.size →
      (St.objEntry o).props.get? k = (s.objEntry o).props.get? k := by intro o k _ ho; rw [hSt]; js_norm
  have gE1 : s.envs.size ≤ St.envs.size := by rw [hSt]; js_norm; omega
  have gF1 : 590 ≤ St.fuel := by rw [hSt]; js_norm; omega
  have gG1 : St.envEntry g = s.envEntry g := by rw [hSt]; js_norm [hG, hG1, hne, Ne.symm hne]
  have gB1 : ∀ x, x ≠ JSStr.ofString "workInProgress" → bG[x]? = bG[x]? := fun _ _ => rfl
  clear hSt
  refine wp_mono (ReactCompleteButton.button_spec {a1}) ?_
  intro v1 w1 h1 ⟨hv1, hF1, hfu1, hh1, hr1, hXf1, hXs1, hXl1⟩
  subst hv1 hh1
  trace_state
  all_goals sorry"""
i = s.index("  js [hpn, hv, hl, ha, hUenv,")
j = s.index("  trace_state\n  all_goals sorry", i)
s = s[:j] + block + s[j + len("  trace_state\n  all_goals sorry"):]
open(CALLER, "w").write(s)
