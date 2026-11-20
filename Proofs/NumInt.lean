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

/-- The engine's Number subtraction on nonzero small integers is integer subtraction. -/
theorem subF_nz (a b : Int) (ha : a.natAbs < intBound) (hb : b.natAbs < intBound) (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (hab : (a - b).natAbs < intBound) : subF (ofSmallInt a) (ofSmallInt b) = ofSmallInt (a - b) := by
  simp [subF, smallInt_ofSmallInt a ha0 ha, smallInt_ofSmallInt b hb0 hb, Nat.le_of_lt hab]

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

/-- `toNat?` of a small natural's Number. -/
theorem toNat?_ofSmallInt (k : Nat) (hk : k < intBound) : toNat? (ofSmallInt k) = some k := by
  by_cases hk0 : k = 0
  · subst hk0; simp [toNat?, ofSmallInt_zero, isIntegral, truncInt]
  · have hi : (k : Int) ≠ 0 := by omega
    have hb : (k : Int).natAbs < intBound := by simpa using hk
    rw [ofSmallInt_ne_zero _ hi hb]
    have hl := log2_le_52 _ (by simpa using hi) hb
    simp only [Int.natAbs_natCast] at hl ⊢
    have hneg : decide ((k : Int) < 0) = false := by simp
    rw [hneg]
    by_cases h52 : Nat.log2 k = 52
    · simp [toNat?, isIntegral, truncInt, h52]
    · have he : ¬ ((Nat.log2 k : Int) - 52 ≥ 0) := by omega
      have hk' : (-((Nat.log2 k : Int) - 52)).toNat = 52 - Nat.log2 k := by omega
      have he' : ¬ (0 ≤ (Nat.log2 k : Int) - 52) := he
      simp only [toNat?, isIntegral, truncInt, ge_iff_le, he', decide_false, Bool.false_or, hk', Nat.shiftLeft_eq,
        Nat.mul_mod_left, beq_self_eq_true, ↓reduceIte, Nat.mul_div_cancel _ (Nat.two_pow_pos _)]
      simp

/-- `Conv.ofNat` (exact rounding of an integer) on a small natural is `ofSmallInt`. -/
theorem ofNat_eq_ofSmallInt (k : Nat) (hk : k < intBound) : Conv.ofNat k = ofSmallInt k := by
  by_cases hk0 : k = 0
  · subst hk0; simp [Conv.ofNat, F64.ofInt, F64.ofRat, ofSmallInt_zero]
  · have hi : (k : Int) ≠ 0 := by omega
    have hb : (k : Int).natAbs < intBound := by simpa using hk
    rw [ofSmallInt_ne_zero _ hi hb]
    have hl := log2_le_52 _ (by simpa using hi) hb
    simp only [Int.natAbs_natCast] at hl ⊢
    have hlo : 2 ^ Nat.log2 k ≤ k := Nat.log2_self_le hk0
    have hhi : k < 2 ^ (Nat.log2 k + 1) := Nat.lt_log2_self
    obtain ⟨lg, hlg⟩ : ∃ lg, Nat.log2 k = lg := ⟨_, rfl⟩
    rw [hlg] at hl hlo hhi ⊢
    have hpow : ∀ a b, 2 ^ a * 2 ^ b = 2 ^ (a + b) := fun a b => (Nat.pow_add 2 a b).symm
    have q53 : 2 ^ 53 ≤ k * 2 ^ (53 - lg) := by
      have := Nat.mul_le_mul_right (2 ^ (53 - lg)) hlo
      rw [hpow, show lg + (53 - lg) = 53 by omega] at this; exact this
    have q52 : k * 2 ^ (52 - lg) < 2 ^ 53 := by
      have := Nat.mul_lt_mul_of_pos_right hhi (Nat.two_pow_pos (52 - lg))
      rw [hpow, show lg + 1 + (52 - lg) = 53 by omega] at this; exact this
    have hev : k * 2 ^ (53 - lg) = k * 2 ^ (52 - lg) * 2 := by
      rw [show 53 - lg = (52 - lg) + 1 by omega, Nat.pow_succ, Nat.mul_assoc]
    have hneg : decide ((k : Int) < 0) = false := by simp
    have hlog1 : Nat.log2 1 = 0 := by decide
    simp only [Conv.ofNat, F64.ofInt, hneg, Int.natAbs_natCast, F64.ofRat, hlg, hlog1]
    simp only [show (k == 0) = false by simpa using hk0, Bool.false_eq_true, ↓reduceIte]
    have hm0 : max (-1074) ((lg : Int) - ((0 : Nat) : Int) - 52 - 1) = (lg : Int) - 53 := by omega
    have hc0 : ¬ ((lg : Int) - 53 ≥ 0) := by omega
    have ht0 : (-((lg : Int) - 53)).toNat = 53 - lg := by omega
    have hq0 : ¬ (k * 2 ^ (53 - lg) < 2 ^ 53) := by omega
    have hsub : (lg : Int) - 53 + 1 - 1 = (lg : Int) - 53 := by omega
    have hm2 : k * 2 ^ (53 - lg) % 2 = 0 := by rw [hev]; exact Nat.mul_mod_left _ _
    have hd2 : k * 2 ^ (53 - lg) / 2 = k * 2 ^ (52 - lg) := by rw [hev]; exact Nat.mul_div_cancel _ (by decide)
    have hdiv1 : ∀ x : Nat, x / 1 = x := Nat.div_one
    have hmod1 : ∀ x : Nat, (x % 1 != 0) = false := by intro x; simp [Nat.mod_one]
    simp only [hm0, ge_iff_le, show ¬ (0 ≤ (lg : Int) - 53) by omega, ↓reduceIte, ht0, hdiv1, hmod1, hq0, hsub]
    by_cases h52 : lg = 52
    · have hc1 : (0 ≤ (lg : Int) - 53 + 1) := by omega
      have ht1 : ((lg : Int) - 53 + 1).toNat = 0 := by omega
      have hk52 : k < 2 ^ 53 := by omega
      simp only [hc1, ↓reduceIte, ht1, Nat.pow_zero, Nat.one_mul, Nat.div_one, hk52, hsub, ht0, hdiv1, hmod1,
        hm2, beq_self_eq_true, hd2, Bool.false_eq_true]
      subst h52
      have hne : (k * 2 ^ (52 - 52) == 2 ^ 53) = false := by simp; omega
      simp [hne, Nat.shiftLeft_eq, show ¬ k = 9007199254740992 by omega]
    · have hc1 : ¬ (0 ≤ (lg : Int) - 53 + 1) := by omega
      have ht1 : (-((lg : Int) - 53 + 1)).toNat = 52 - lg := by omega
      simp only [hc1, ↓reduceIte, ht1, hdiv1, q52, hsub, ht0, hmod1, hm2, beq_self_eq_true, hd2, Bool.false_eq_true]
      have hne : (k * 2 ^ (52 - lg) == 2 ^ 53) = false := by simp; omega
      simp [hne, Nat.shiftLeft_eq, show ¬ ((53 : Int) ≤ lg) by omega, hm2, hd2, q52, Nat.ne_of_lt q52]
      rw [if_neg (by omega), show (lg : Int) - 53 + 1 = (lg : Int) - 52 by omega]

theorem truncInt_ofSmallInt (k : Nat) (hk : k < intBound) : truncInt (ofSmallInt k) = some k := by
  have h := toNat?_ofSmallInt k hk
  simp only [toNat?] at h
  split at h
  · split at h
    · next i hi =>
      split at h
      · simp at h; rw [hi]; congr 1; omega
      · simp at h
    · simp at h
  · simp at h

theorem toUint32_ofSmallInt (k : Nat) (hk : k < 4294967296) : toUint32 (ofSmallInt k) = k := by
  simp [toUint32, truncInt_ofSmallInt k (by simp only [intBound]; omega)]; omega

end ES.Conv
