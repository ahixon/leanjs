import Proofs.Basic

/-!
# Integer Numbers

Integers of magnitude below 2^53 are exactly representable; `Conv.ofSmallInt` builds them, and the
engine's Number addition and `<` on them are integer addition and `<` (`addF_int`, `ltF_int`).
-/

namespace ES.Conv

/-- The bound below which integers are Numbers exactly (and the engine's small-integer paths apply). -/
abbrev intBound : Nat := 9007199254740992

theorem log2_le_52 (a : Nat) (ha : a ≠ 0) (hb : a < intBound) : Nat.log2 a ≤ 52 := by
  have := (Nat.log2_lt ha).mpr (show a < 2 ^ 53 from hb)
  omega

/-- A nonzero small integer's Number: sign, a nonzero significand, an exponent in [-52, 0]. -/
theorem ofSmallInt_ne_zero (i : Int) (hi : i ≠ 0) (hb : i.natAbs < intBound) :
    ofSmallInt i = .fin (decide (i < 0)) (i.natAbs <<< (52 - Nat.log2 i.natAbs))
      ((Nat.log2 i.natAbs : Int) - 52) := by
  have ha : i.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hi
  have hl := log2_le_52 _ ha hb
  simp [ofSmallInt, hi, hl]

theorem smallInt_ofSmallInt (i : Int) (hi : i ≠ 0) (hb : i.natAbs < intBound) :
    smallInt? (ofSmallInt i) = some i := by
  have ha : i.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hi
  have hl := log2_le_52 _ ha hb
  rw [ofSmallInt_ne_zero i hi hb]
  have hm : i.natAbs <<< (52 - Nat.log2 i.natAbs) ≠ 0 := by
    rw [Nat.shiftLeft_eq]; exact Nat.mul_ne_zero ha (Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos _))
  have hsign : (if i < 0 then -((i.natAbs : Nat) : Int) else ((i.natAbs : Nat) : Int)) = i := by
    split <;> omega
  simp only [smallInt?, hm, beq_iff_eq, ite_false]
  by_cases he : (Nat.log2 i.natAbs : Int) - 52 ≥ 0
  · have h52 : Nat.log2 i.natAbs = 52 := by omega
    simp [he, h52, show ((52 : Nat) : Int) - 52 ≤ 0 by omega, hsign]
  · have hk : (-((Nat.log2 i.natAbs : Int) - 52)).toNat = 52 - Nat.log2 i.natAbs := by omega
    have he' : ¬ (0 ≤ (Nat.log2 i.natAbs : Int) - 52) := he
    simp only [ge_iff_le, he', ite_false, hk, show ¬ (52 - Nat.log2 i.natAbs > 52) by omega]
    simp [Nat.shiftLeft_shiftRight, hsign]

theorem smallInt_zero : smallInt? (ofSmallInt 0) = none := by
  simp [ofSmallInt, smallInt?]

theorem ofSmallInt_zero : ofSmallInt 0 = .fin false 0 (-1074) := by simp [ofSmallInt]

theorem smallInt_fin_zero : smallInt? (.fin false 0 (-1074)) = none := by simp [smallInt?]

/-- `smallInt_ofSmallInt` on the unfolded form. -/
theorem smallInt_fin (i : Int) (hi : i ≠ 0) (hb : i.natAbs < intBound) :
    smallInt? (.fin (decide (i < 0)) (i.natAbs <<< (52 - Nat.log2 i.natAbs)) ((Nat.log2 i.natAbs : Int) - 52)) =
      some i := by
  rw [← ofSmallInt_ne_zero i hi hb]; exact smallInt_ofSmallInt i hi hb

theorem ofSmallInt_m_ne_zero (i : Int) (hi : i ≠ 0) : i.natAbs <<< (52 - Nat.log2 i.natAbs) ≠ 0 := by
  rw [Nat.shiftLeft_eq]
  exact Nat.mul_ne_zero (Int.natAbs_ne_zero.mpr hi) (Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos _))

/-- The engine's Number addition on small integers is integer addition. -/
theorem addF_int (a b : Int) (ha : a.natAbs < intBound) (hb : b.natAbs < intBound)
    (hab : (a + b).natAbs < intBound) : addF (ofSmallInt a) (ofSmallInt b) = ofSmallInt (a + b) := by
  by_cases ha0 : a = 0
  · subst ha0
    by_cases hb0 : b = 0
    · subst hb0; simp [addF, ofSmallInt_zero, smallInt_fin_zero, F64.add]
    · simp [addF, ofSmallInt_zero, smallInt_fin_zero, F64.add, ofSmallInt_ne_zero b hb0 hb,
        ofSmallInt_m_ne_zero b hb0]
  · by_cases hb0 : b = 0
    · subst hb0
      simp [addF, ofSmallInt_zero, smallInt_fin_zero, F64.add, ofSmallInt_ne_zero a ha0 ha,
        smallInt_fin a ha0 ha, ofSmallInt_m_ne_zero a ha0]
    · simp [addF, smallInt_ofSmallInt a ha0 ha, smallInt_ofSmallInt b hb0 hb, Nat.le_of_lt hab]

/-- Zero is less than a nonzero finite Number exactly when that Number is positive. -/
theorem lt_zero_fin (neg : Bool) (m : Nat) (e : Int) (hm : m ≠ 0) (he : -1074 ≤ e) :
    F64.lt (.fin false 0 (-1074)) (.fin neg m e) = !neg := by
  have hg : min (-1074 : Int) e = -1074 := by omega
  have hpos : 0 < m * 2 ^ (e - -1074).toNat := Nat.mul_pos (Nat.pos_of_ne_zero hm) (Nat.two_pow_pos _)
  simp only [F64.lt, hm, hg]
  generalize m * 2 ^ (e - -1074).toNat = X at hpos ⊢
  cases neg <;> simp <;> omega

theorem lt_fin_zero (neg : Bool) (m : Nat) (e : Int) (hm : m ≠ 0) (he : -1074 ≤ e) :
    F64.lt (.fin neg m e) (.fin false 0 (-1074)) = neg := by
  have hg : min e (-1074 : Int) = -1074 := by omega
  have hpos : 0 < m * 2 ^ (e - -1074).toNat := Nat.mul_pos (Nat.pos_of_ne_zero hm) (Nat.two_pow_pos _)
  simp only [F64.lt, hm, hg]
  generalize m * 2 ^ (e - -1074).toNat = X at hpos ⊢
  cases neg <;> simp <;> omega

/-- The engine's Number `<` on small integers is integer `<`. -/
theorem ltF_int (a b : Int) (ha : a.natAbs < intBound) (hb : b.natAbs < intBound) :
    ltF (ofSmallInt a) (ofSmallInt b) = decide (a < b) := by
  by_cases ha0 : a = 0
  · subst ha0
    by_cases hb0 : b = 0
    · subst hb0; simp [ltF, ofSmallInt_zero, smallInt_fin_zero, F64.lt]
    · have hl := log2_le_52 _ (Int.natAbs_ne_zero.mpr hb0) hb
      simp only [ltF, ofSmallInt_zero, smallInt_fin_zero, ofSmallInt_ne_zero b hb0 hb]
      rw [lt_zero_fin _ _ _ (ofSmallInt_m_ne_zero b hb0) (by omega)]
      by_cases hneg : b < 0 <;> simp [hneg] <;> omega
  · by_cases hb0 : b = 0
    · subst hb0
      have hl := log2_le_52 _ (Int.natAbs_ne_zero.mpr ha0) ha
      simp only [ltF, ofSmallInt_zero, smallInt_fin_zero, ofSmallInt_ne_zero a ha0 ha, smallInt_fin a ha0 ha]
      rw [lt_fin_zero _ _ _ (ofSmallInt_m_ne_zero a ha0) (by omega)]
    · simp [ltF, smallInt_ofSmallInt a ha0 ha, smallInt_ofSmallInt b hb0 hb]

end ES.Conv
