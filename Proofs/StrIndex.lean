import ES.Str

/-!
# Array-index keys round-trip

`JSStr.ofNat n` (the digits of `n`, UTF-16 encoded) parses back to `n` as an array index
(`toArrayIndex_ofNat`), and is not `"length"`. Array literals and element writes go through the
array exotic [[DefineOwnProperty]], which parses its key: this is what lets proofs follow them.
-/

namespace ES.JSStr

/-- Pushing a code unit below 256 (one byte, then a zero byte). -/
theorem push_small (s : JSStr) (u : UInt16) (hu : u.toNat < 256) :
    s.push u = ⟨(s.b.push u.toUInt8).push 0⟩ := by
  have : (u >>> 8).toUInt8 = 0 := by
    apply UInt8.toNat_inj.mp
    simp [UInt16.toNat_shiftRight]
    omega
  simp [push, this]

theorem length_push_small (s : JSStr) (u : UInt16) (hu : u.toNat < 256) (he : s.b.size % 2 = 0) :
    (s.push u).length = s.length + 1 ∧ (s.push u).b.size % 2 = 0 := by
  rw [push_small s u hu]
  simp [length, ByteArray.size_push]
  omega

/-- The two bytes of a code unit below 256. -/
def enc (c : Char) : List UInt8 := [c.toNat.toUInt16.toUInt8, 0]

theorem toUInt16_small (c : Char) (hc : c.toNat < 256) : c.toNat.toUInt16.toNat = c.toNat := by
  simp [Nat.toUInt16, UInt16.toNat_ofNat]; omega

/-- The bytes of `ofList cs` (characters below 256): each character's two bytes, in order. -/
theorem bytes_foldl (cs : List Char) (hcs : ∀ c ∈ cs, c.toNat < 256) :
    ∀ acc : JSStr, (cs.foldl (fun acc c => acc.pushCodePoint c.toNat) acc).b.data.toList =
      acc.b.data.toList ++ cs.flatMap enc := by
  induction cs with
  | nil => intro acc; simp
  | cons c cs ih =>
    intro acc
    have hc := hcs c (List.mem_cons_self ..)
    have hrest : ∀ c ∈ cs, c.toNat < 256 := fun c h => hcs c (List.mem_cons_of_mem _ h)
    simp only [List.foldl_cons]
    rw [ih hrest]
    have hcp : acc.pushCodePoint c.toNat = ⟨(acc.b.push c.toNat.toUInt16.toUInt8).push 0⟩ := by
      simp only [pushCodePoint, show c.toNat < 0x10000 by omega, ↓reduceIte]
      exact push_small acc _ (by rw [toUInt16_small c hc]; exact hc)
    rw [hcp]
    simp [ByteArray.data_push, enc]

theorem bytes_ofList (cs : List Char) (hcs : ∀ c ∈ cs, c.toNat < 256) :
    (ofList cs).b.data.toList = cs.flatMap enc := by
  simp only [ofList]
  rw [bytes_foldl cs hcs empty]
  simp [empty, ByteArray.empty, ByteArray.emptyWithCapacity]; rfl

theorem flatMap_enc_get (cs : List Char) :
    ∀ i (hi : i < cs.length), (cs.flatMap enc)[2 * i]? = some cs[i].toNat.toUInt16.toUInt8 ∧
      (cs.flatMap enc)[2 * i + 1]? = some 0 := by
  induction cs with
  | nil => intro i hi; simp at hi
  | cons c cs ih =>
    intro i hi
    cases i with
    | zero => simp [enc]
    | succ j =>
      have := ih j (by simpa using hi)
      have e1 : 2 * (j + 1) = 2 * j + 2 := by omega
      have e2 : 2 * (j + 1) + 1 = 2 * j + 1 + 2 := by omega
      simp only [List.flatMap_cons, e1, e2, enc, List.cons_append, List.nil_append, List.getElem?_cons_succ,
        List.getElem_cons_succ]
      exact this

theorem length_flatMap_enc (cs : List Char) : (cs.flatMap enc).length = 2 * cs.length := by
  induction cs with
  | nil => simp
  | cons c cs ih => rw [List.flatMap_cons, List.length_append, ih]; simp [enc]; omega

theorem length_ofList (cs : List Char) (hcs : ∀ c ∈ cs, c.toNat < 256) : (ofList cs).length = cs.length := by
  have h := congrArg List.length (bytes_ofList cs hcs)
  simp only [Array.length_toList] at h
  simp only [length, ByteArray.size, h, length_flatMap_enc]; omega

theorem get_ofList (cs : List Char) (hcs : ∀ c ∈ cs, c.toNat < 256) (i : Nat) (hi : i < cs.length) :
    (ofList cs).get i = cs[i].toNat.toUInt16 := by
  have hb := bytes_ofList cs hcs
  obtain ⟨h0, h1⟩ := flatMap_enc_get cs i hi
  have g : ∀ k, (ofList cs).b.get! k = ((ofList cs).b.data.toList[k]?).getD 0 := by
    intro k; cases hob : (ofList cs).b with
    | mk bs => simp [ByteArray.get!, getElem!_def, Array.getElem?_toList]; rfl
  have hc := hcs cs[i] (List.getElem_mem hi)
  simp only [get, g, hb, h0, h1, Option.getD_some]
  apply UInt16.toNat_inj.mp
  simp [toUInt16_small _ hc]
  omega

/-- `toIndex?`'s loop over code units that are all digits: no early exit; it computes the decimal value. -/
theorem forIn_digits (s : JSStr) (l : List Nat) (hd : ∀ i ∈ l, 48 ≤ s.get i ∧ s.get i ≤ 57) :
    ∀ v0 : Nat, (forIn (m := Id) l ((none : Option (Option Nat)), v0) fun i (st : Option (Option Nat) × Nat) =>
        if s.get i < 48 ∨ 57 < s.get i then ForInStep.done (some none, st.snd)
        else ForInStep.yield (none, st.snd * 10 + ((s.get i).toNat - 48))) =
      ((none : Option (Option Nat)), l.foldl (fun v i => v * 10 + ((s.get i).toNat - 48)) v0) := by
  induction l with
  | nil => intro v0; rfl
  | cons i l ih =>
    intro v0
    have hi := hd i (List.mem_cons_self ..)
    have hrest : ∀ j ∈ l, 48 ≤ s.get j ∧ s.get j ≤ 57 := fun j h => hd j (List.mem_cons_of_mem _ h)
    have hnot : ¬ (s.get i < 48 ∨ 57 < s.get i) := by
      intro h; rcases h with h | h
      · exact absurd hi.1 (by simpa [UInt16.le_iff_toNat_le, UInt16.lt_iff_toNat_lt] using h)
      · exact absurd hi.2 (by simpa [UInt16.le_iff_toNat_le, UInt16.lt_iff_toNat_lt] using h)
    simp only [List.forIn_cons, hnot, ↓reduceIte, List.foldl_cons]
    exact ih hrest _

theorem digit_range (c : Char) (h : c.isDigit = true) : 48 ≤ c.toNat ∧ c.toNat ≤ 57 := by
  simp only [Char.isDigit, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h
  have e1 : ('0' : Char).val.toNat = 48 := rfl
  have e2 : ('9' : Char).val.toNat = 57 := rfl
  simp only [Char.toNat, UInt32.le_iff_toNat_le] at h1 h2 ⊢
  omega

/-- A positive number's decimal digits do not start with `0`. -/
theorem toDigits_head (n : Nat) (hn : 1 ≤ n) : (Nat.toDigits 10 n).head? ≠ some '0' := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [Nat.toDigits_eq_if (by omega)]
    split
    · next h =>
      have : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 := by omega
      rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    · next h =>
      have := ih (n / 10) (by omega) (by omega)
      cases hd : Nat.toDigits 10 (n / 10) with
      | nil => exact absurd hd Nat.toDigits_ne_nil
      | cons c cs => rw [hd] at this; simpa using this

/-- The fold over positions `pre.length, …` of `pre ++ cs` is the fold over `cs`. -/
theorem foldl_range'_digits (f : Char → Nat) (cs : List Char) :
    ∀ (pre : List Char) (v0 : Nat), (List.range' pre.length cs.length).foldl
        (fun v i => v * 10 + f (((pre ++ cs)[i]?).getD '0')) v0 = cs.foldl (fun v c => v * 10 + f c) v0 := by
  induction cs with
  | nil => intro pre v0; simp
  | cons c cs ih =>
    intro pre v0
    have h := ih (pre ++ [c]) (v0 * 10 + f c)
    simp only [List.length_append, List.length_singleton, List.append_assoc, List.singleton_append] at h
    simp only [List.length_cons, List.range'_succ, List.foldl_cons, List.foldl_cons]
    rw [show (pre ++ c :: cs)[pre.length]? = some c by simp]
    simpa using h

theorem foldl_congr_mem {α β : Type} (f g : β → α → β) :
    ∀ (l : List α) (b : β), (∀ b a, a ∈ l → f b a = g b a) → l.foldl f b = l.foldl g b := by
  intro l
  induction l with
  | nil => intro b _; rfl
  | cons a l ih =>
    intro b h
    simp only [List.foldl_cons]
    rw [h b a (List.mem_cons_self ..)]
    exact ih _ (fun b' a' ha' => h b' a' (List.mem_cons_of_mem _ ha'))

/-- **Array-index keys round-trip**: the digits of `n` parse back to `n`. -/
theorem toIndex_ofNat (n : Nat) (hn : n < 10 ^ 10) : (ofNat n).toIndex? = some n := by
  let cs := Nat.toDigits 10 n
  have hdig : ∀ c ∈ cs, 48 ≤ c.toNat ∧ c.toNat ≤ 57 := fun c h =>
    digit_range c (Nat.isDigit_of_mem_toDigits (by omega) (by omega) h)
  have hsmall : ∀ c ∈ cs, c.toNat < 256 := fun c h => by have := hdig c h; omega
  have hof : ofNat n = ofList cs := by simp only [ofNat, ofString, Nat.toList_repr, cs]
  have hlen : (ofNat n).length = cs.length := by rw [hof]; exact length_ofList cs hsmall
  have hget : ∀ i (hi : i < cs.length), (ofNat n).get i = cs[i].toNat.toUInt16 := by
    intro i hi; rw [hof]; exact get_ofList cs hsmall i hi
  have hpos : 0 < cs.length := List.length_pos_iff.mpr Nat.toDigits_ne_nil
  have hle : cs.length ≤ 10 := (Nat.length_toDigits_le_iff (by omega) (by omega)).mpr hn
  have hd : ∀ i ∈ List.range' 0 cs.length, 48 ≤ (ofNat n).get i ∧ (ofNat n).get i ≤ 57 := by
    intro i hi
    have hi' : i < cs.length := by simp at hi; omega
    have := hdig cs[i] (List.getElem_mem hi')
    rw [hget i hi', UInt16.le_iff_toNat_le, UInt16.le_iff_toNat_le, toUInt16_small _ (hsmall _ (List.getElem_mem hi'))]
    simpa using this
  have hz : ¬ (1 < cs.length ∧ (ofNat n).get 0 = 48) := by
    intro ⟨h1, h2⟩
    have hn1 : 1 ≤ n := by
      rcases Nat.eq_zero_or_pos n with h | h
      · subst h; simp [cs, Nat.toDigits_zero] at h1
      · exact h
    have hh := toDigits_head n hn1
    rw [hget 0 hpos] at h2
    have : cs[0].toNat = 48 := by
      have := congrArg UInt16.toNat h2
      rwa [toUInt16_small _ (hsmall _ (List.getElem_mem hpos))] at this
    apply hh
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hpos]
    congr 1
    rw [← Char.ofNat_toNat cs[0], this]
  have hfold : (List.range' 0 cs.length).foldl (fun v i => v * 10 + (((ofNat n).get i).toNat - 48)) 0 = n := by
    have h := foldl_range'_digits (fun c => c.toNat - 48) cs [] 0
    simp only [List.length_nil, List.nil_append] at h
    have hcong : ∀ i ∈ List.range' 0 cs.length, ((ofNat n).get i).toNat - 48 = (cs[i]?.getD '0').toNat - 48 := by
      intro i hi
      have hi' : i < cs.length := by simp at hi; omega
      rw [hget i hi', toUInt16_small _ (hsmall _ (List.getElem_mem hi')), List.getElem?_eq_getElem hi']
      rfl
    rw [foldl_congr_mem _ (fun v i => v * 10 + ((cs[i]?.getD '0').toNat - 48)) _ _ (fun v i hi => by rw [hcong i hi])]
    rw [h]
    have := Nat.ofDigitChars_ten_toDigits (n := n)
    simp only [Nat.ofDigitChars_eq_foldl] at this
    rw [← this]
    exact foldl_congr_mem _ _ _ _ (fun b a _ => by rw [Nat.mul_comm]; rfl)
  have h0 : cs.length ≠ 0 := by omega
  have h16 : ¬ 16 < cs.length := by omega
  simp only [toIndex?, Id.run]
  simp [hlen, h0, h16]
  rw [ite_eq_right (by simpa [hlen] using hz)]
  simp only [pure, bind]
  rw [forIn_digits (ofNat n) _ (by simpa [hlen] using hd) 0]
  simp [hfold]

theorem toArrayIndex_ofNat (n : Nat) (hn : n < 4294967295) : (ofNat n).toArrayIndex? = some n := by
  simp [toArrayIndex?, toIndex_ofNat n (by omega), hn]

/-- A digit string's first code unit is a digit. -/
theorem get_zero_ofNat (n : Nat) (hn : n < 10 ^ 10) : 48 ≤ (ofNat n).get 0 ∧ (ofNat n).get 0 ≤ 57 := by
  let cs := Nat.toDigits 10 n
  have hdig : ∀ c ∈ cs, 48 ≤ c.toNat ∧ c.toNat ≤ 57 := fun c h =>
    digit_range c (Nat.isDigit_of_mem_toDigits (by omega) (by omega) h)
  have hsmall : ∀ c ∈ cs, c.toNat < 256 := fun c h => by have := hdig c h; omega
  have hof : ofNat n = ofList cs := by simp only [ofNat, ofString, Nat.toList_repr, cs]
  have hpos : 0 < cs.length := List.length_pos_iff.mpr Nat.toDigits_ne_nil
  rw [hof, get_ofList cs hsmall 0 hpos, UInt16.le_iff_toNat_le, UInt16.le_iff_toNat_le,
    toUInt16_small _ (hsmall _ (List.getElem_mem hpos))]
  simpa using hdig _ (List.getElem_mem hpos)

/-- A digit string is not a string whose first code unit is not a digit (e.g. `"length"`). -/
theorem ofNat_ne (n : Nat) (hn : n < 10 ^ 10) (t : JSStr) (ht : ¬ (48 ≤ t.get 0 ∧ t.get 0 ≤ 57)) : ofNat n ≠ t := by
  intro h; rw [← h] at ht; exact ht (get_zero_ofNat n hn)

theorem ofNat_ne_length (n : Nat) (hn : n < 10 ^ 10) : ofNat n ≠ JSStr.ofString "length" :=
  ofNat_ne n hn _ (by decide)

end ES.JSStr
