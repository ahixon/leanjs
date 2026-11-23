import sys; sys.path.insert(0, "tools/react_cuw"); import args as A
CALLER = "JSProofs/ReactCompleteUnit.lean"
bounds = A.caller_bounds(CALLER, "unit_spec")
dl = "dS1 dS2 dS3 dS4 dS5 dS6 dS7 dS8 dS9 dU1 dU2 dU3 dX1 dX2 dX3 dO1 dO2 dO3 dO4 dO5 dO6 hHX hCX hRC hAC hAX hRX".split()
DS = ", ".join(["ReactCompleteButton.fpCW", "ReactCompleteButton.fpCC", "ReactCompleteRoot.fpRC"] + dl + [f"Ne.symm {x}" for x in dl])
bG2 = 'bG.modify (JSStr.ofString "workInProgress") (fun bd => { bd with value := some (.obj C) })'
c = "numberBinOp .bitAnd (numberBinOp .bitOr sf (F64.fin false 0 (-1074))) (F64.fin true 4503599761588224 (-27))"
f = "numberBinOp .bitAnd (numberBinOp .bitOr fl (F64.fin false 4503599627370496 (-50))) (F64.fin true 4503599895805952 (-28))"
ren = {"bG": f"({bG2})", "C0": "A", "Y": "H", "rv": "(.obj C)", "pp": "(.obj pp2)", "cl": "cl2", "b": "(F64.fin false 0 (-1074))",
       "c": f"({c})", "e": "e2", "f": f"({f})", "tW": ".undefined",
       "ppw": "ppw2", "ppe": "ppe2", "ppc": "ppc2", "tgw": "tgw2", "tge": "tge2", "tgc": "tgc2", "aw": "aw2", "ae": "ae2",
       "ac": "ac2", "cw": "cw2", "ce": "ce2", "cc": "cc2", "yw": "yw2", "ye": "ye2", "yc": "yc2", "xcw": "true",
       "xce": "le", "xcc": "lc", "xsw": "true", "xse": "se", "xsc": "sc", "xfw": "true", "xfe": "fe", "xfc": "fc",
       "se": "se2", "sc": "sc2", "le": "le2", "lc": "lc2",
       "hXl": "hXla", "hYX": "hHX"}
ex = {"hGe": "gG2",
      "hXcl": "(by rw [gW2 X]; exact hXl1)", "hXs": "(by rw [gW2 X]; exact hXs1)", "hXf": "(by rw [gW2 X]; exact hXf1)"}
a2 = A.transfer("JSProofs/ReactCompleteButton.lean", "counter_spec", ren, ex, {}, bounds, 2, DS)
s = open(CALLER).read()
F = "hW, hWk, Nat.lt_of_lt_of_le hW z1, k1 fW hW, p1"
block = f"""  have hWk1 := (k1 fW hW).trans hWk
  refine ⟨by js_norm [CallableC, hWk1, Nat.lt_of_lt_of_le hW z1], ?_⟩
  refine ReactReconcileFibers.wp_gen_state fun St hSt => ?_
  have gW2 : ∀ o, St.objEntry o = w1.objEntry o := by intro o; rw [hSt]; js_norm
  have gZ2 : s.heap.size ≤ St.heap.size := by rw [hSt]; js_norm; exact z1
  have gK2 : ∀ o, o < s.heap.size → (St.objEntry o).kind = (s.objEntry o).kind := fun o ho => by rw [gW2]; exact k1 o ho
  have gP2 : ∀ o k, (o, k) ∉ (ReactCompleteButton.fpCW X).props → o < s.heap.size →
      (St.objEntry o).props.get? k = (s.objEntry o).props.get? k := fun o k hk ho => by rw [gW2]; exact p1 o k hk ho
  have gE2 : s.envs.size ≤ St.envs.size := by rw [hSt]; js_norm; omega
  have gF2 : 380 ≤ St.fuel := by rw [hSt]; js_norm; omega
  have gG2 : Scope.declLike? (St.envEntry g) = some ({bG2}, none) := by
    rw [hSt]; js_norm [hw1G, hGe, hG, Nat.lt_of_lt_of_le hG1 E1, hne, Ne.symm hne,
      Nat.ne_of_gt (Nat.lt_of_lt_of_le hG1 E1), Ne.symm (Nat.ne_of_gt (Nat.lt_of_lt_of_le hG1 E1))]
  have gB2 : ∀ x, x ≠ JSStr.ofString "workInProgress" → ({bG2})[x]? = bG[x]? := fun x hx => by
    simp [Std.HashMap.getElem?_modify, Ne.symm hx]
  refine wp_mono (ReactCompleteButton.counter_spec {a2}) ?_
  intro v2 w2 h2 ⟨hv2, hF2, hfu2, hh2, hr2, hCs2, hCl2, hXr2⟩
  subst hv2 hh2
  trace_state
  all_goals sorry"""
j = s.rindex("  trace_state\n  all_goals sorry")
s = s[:j] + block + s[j + len("  trace_state\n  all_goals sorry"):]
open(CALLER, "w").write(s)
