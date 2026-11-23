import sys; sys.path.insert(0, "tools/react_cuw"); import args as A
CALLER = "JSProofs/ReactCompleteUnit.lean"
bounds = A.caller_bounds(CALLER, "unit_spec")
dl = "dS1 dS2 dS3 dS4 dS5 dS6 dS7 dS8 dS9 dU1 dU2 dU3 dX1 dX2 dX3 dO1 dO2 dO3 dO4 dO5 dO6 hHX hCX hRC hAC hAX hRX".split()
DS = ", ".join(["ReactCompleteButton.fpCW", "ReactCompleteButton.fpCC", "ReactCompleteRoot.fpRC"] + dl + [f"Ne.symm {x}" for x in dl])
W = 'fun bd => { bd with value := some (.obj C) }'
bG3 = f'(bG.modify (JSStr.ofString "workInProgress") ({W})).modify (JSStr.ofString "workInProgress") (fun bd => {{ bd with value := some (.obj R) }})'
cb = "numberBinOp .bitAnd (numberBinOp .bitOr sf (F64.fin false 0 (-1074))) (F64.fin true 4503599761588224 (-27))"
fb = "numberBinOp .bitAnd (numberBinOp .bitOr fl (F64.fin false 4503599627370496 (-50))) (F64.fin true 4503599895805952 (-28))"
b = "numberBinOp .bitOr (F64.fin false 0 (-1074)) (numberBinOp .bitOr a (F64.fin false 0 (-1074)))"
c = f"numberBinOp .bitOr e2 (numberBinOp .bitOr (numberBinOp .bitOr (F64.fin false 0 (-1074)) ({cb})) ({fb}))"
ren = {"bG": f"({bG3})", "H": "RH", "Y": "A", "pp": "pp3", "rv": "(.obj R)", "cl": "cl3", "a": "a2", "b": f"({b})",
       "c": f"({c})", "e": "e3", "f": "f2", "tW": ".undefined", "bdCF": "bdCF", "vf": "(.obj Rb)", "fe": "fe'", "fc": "fc'",
       "ppw": "ppw3", "ppe": "ppe3", "ppc": "ppc3", "tgw": "tgw3", "tge": "tge3", "tgc": "tgc3", "snw": "snw3",
       "sne": "sne3", "snc": "snc3", "hcw": "hcw3", "hce": "hce3", "hcc": "hcc3", "aw": "aw3", "ae": "ae3", "ac": "ac3",
       "cw": "cw3", "ce": "ce3", "cc": "cc3", "yw": "false", "ye": "false", "yc": "false", "xlw": "xlw2", "xle": "xle2",
       "xlc": "xlc2", "xcw": "true", "xce": "le2", "xcc": "lc2", "xsw": "true", "xse": "se2", "xsc": "sc2",
       "xfw": "xfw2", "xfe": "xfe2", "xfc": "xfc2", "rwe": "rwe2", "rwc": "rwc2", "sbw": "sbw2", "sbe": "sbe2",
       "sbc": "sbc2", "se": "se3", "sc": "sc3", "le": "le3", "lc": "lc3", "e2": "e2'", "e3": "e3'",
       "hH": "hRH", "hHk": "hRHk", "hHms": "hRHms", "hHc": "hRHc", "hYC": "hAC", "hCl": "hCla",
       "hGCF": "hGCFb", "hGCFv": "hGCFbv"}
ex = {"hGe": "gG3", "hCcl": "(by rw [gW3 C]; exact hCl2)", "hCs": "(by rw [gW3 C]; exact hCs2)",
      "hdF": "(fun Y hY => hdF Y (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hY; rcases hY with h | h | h | h | h | h | h | h <;> subst h <;> simp))"}
a3 = A.transfer("JSProofs/ReactCompleteRoot.lean", "root_spec", ren, ex, {"H": "RH", "Y": "A"}, bounds, 3, DS)
s = open(CALLER).read()
block = f"""  have hw2K := envEntry_frame hF2 (e := s.envs.size) (by rw [hSt]; js_norm [hK1']) (by simp [ReactCompleteButton.fpCC])
  have hw2G := envEntry_frame hF2 (e := g) (Nat.lt_of_lt_of_le hG gE2) (by simp [ReactCompleteButton.fpCC])
  rw [hSt] at hw2K hw2G
  try simp only [js_simp, ↓reduceIte, hne, Ne.symm hne] at hw2K hw2G
  have hw2E : s.envs.size + 1 ≤ w2.envs.size := Nat.le_trans (by rw [hSt]; js_norm; omega) hF2.envs_le
  clear hSt
  have z2 : s.heap.size ≤ w2.heap.size := Nat.le_trans gZ2 hF2.heap_le
  have p2 : ∀ o k, (o, k) ∉ (ReactCompleteButton.fpCW X).props ++ (ReactCompleteButton.fpCC C X).props →
      o < s.heap.size → (w2.objEntry o).props.get? k = (s.objEntry o).props.get? k := fun o k hk ho => by
    simp only [List.mem_append, not_or] at hk
    rw [props_frame hF2 (Nat.lt_of_lt_of_le ho gZ2) (by simpa using hk.2), gP2 o k hk.1 ho]
  have k2 : ∀ o, o < s.heap.size → (w2.objEntry o).kind = (s.objEntry o).kind := fun o ho => by
    rw [kind_frame hF2 (Nat.lt_of_lt_of_le ho gZ2), gK2 o ho]
  try simp only [js_simp] at hfu2
  have f2' : 280 ≤ w2.fuel := by omega
  have hCsb2 := (p2 C (.str "sibling") (by simp [{DS}]) hC).trans hCsb
  have hCk2 : (w2.objEntry C).kind.isPlain = true := by rw [k2 C hC]; exact hCk
  have hRk2 : (w2.objEntry R).kind.isPlain = true := by rw [k2 R hR]; exact hRk
  have hRf2 := (p2 R (.str "flags") (by simp [{DS}]) hR).trans hRf
  have hRr2 := (p2 R (.str "return") (by simp [{DS}]) hR).trans hRr
  have hRa2 := (p2 R (.str "alternate") (by simp [{DS}]) hR).trans hRa
  have hWk2 : (w2.objEntry fW).kind = .func dW := by rw [k2 fW hW]; exact hWk
  js [hw2K, hw2G, hCsb2, hCk2, hRk2, hRf2, hRr2, hRa2, hRi, hWk2, Nat.lt_of_lt_of_le hC z2, Nat.lt_of_lt_of_le hR z2,
    Nat.lt_of_lt_of_le hW z2, f2', Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hw2E,
    Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hw2E), Nat.lt_of_lt_of_le hG1 hw2E,
    Nat.ne_of_gt (Nat.lt_of_lt_of_le hG1 hw2E), hGe, hGWIP, hGWIPm, hGWIPi, hGCW, hGCWv, hGEL, hGELv, hG, hG1, hne,
    Ne.symm hne, hpn, hv, hl, ha, FDI.fdiCtx, Sem.inner]
  refine ⟨by js_norm [CallableC, hWk2, Nat.lt_of_lt_of_le hW z2], ?_⟩
  refine ReactReconcileFibers.wp_gen_state fun St hSt => ?_
  have gW3 : ∀ o, St.objEntry o = w2.objEntry o := by intro o; rw [hSt]; js_norm
  have gZ3 : s.heap.size ≤ St.heap.size := by rw [hSt]; js_norm; exact z2
  have gK3 : ∀ o, o < s.heap.size → (St.objEntry o).kind = (s.objEntry o).kind := fun o ho => by rw [gW3]; exact k2 o ho
  have gP3 : ∀ o k, (o, k) ∉ (ReactCompleteButton.fpCW X).props ++ (ReactCompleteButton.fpCC C X).props →
      o < s.heap.size → (St.objEntry o).props.get? k = (s.objEntry o).props.get? k := fun o k hk ho => by
    rw [gW3]; exact p2 o k hk ho
  have gE3 : s.envs.size ≤ St.envs.size := by rw [hSt]; js_norm; omega
  have gF3 : 260 ≤ St.fuel := by rw [hSt]; js_norm; omega
  have gG3 : Scope.declLike? (St.envEntry g) = some ({bG3}, oG) := by
    rw [hSt]; js_norm [hw2G, hGe, hG, Nat.lt_of_lt_of_le hG1 hw2E, hne, Ne.symm hne,
      Nat.ne_of_gt (Nat.lt_of_lt_of_le hG1 hw2E), Ne.symm (Nat.ne_of_gt (Nat.lt_of_lt_of_le hG1 hw2E))]
  have gB3 : ∀ x, x ≠ JSStr.ofString "workInProgress" → ({bG3})[x]? = bG[x]? := fun x hx => by
    simp [Std.HashMap.getElem?_modify, Ne.symm hx]
  refine wp_mono (ReactCompleteRoot.root_spec {a3}) ?_
  intro v3 w3 h3 ⟨hv3, hF3, hfu3, hh3, hr3, hRs3, hRl3, hCr3⟩
  subst hv3 hh3
  trace_state
  all_goals sorry"""
j = s.rindex("  trace_state\n  all_goals sorry")
s = s[:j] + block + s[j + len("  trace_state\n  all_goals sorry"):]
open(CALLER, "w").write(s)
