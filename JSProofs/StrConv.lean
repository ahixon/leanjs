import JSProofs.Basic

/-!
# From Lean strings to String values and back

`toString_ofString`: a Lean string whose characters are below the surrogates (every Basic Multilingual Plane
character before U+D800: ASCII, Latin, most scripts) survives the round trip through UTF-16 code units.
-/

namespace ES.JSStr

/-- Characters below the surrogates: one code unit each, never part of a pair. -/
def Plain (cs : List Char) : Prop := ∀ c ∈ cs, c.toNat < 0xD800

theorem ofList_snoc (cs : List Char) (c : Char) (hc : c.toNat < 0x10000) :
    ofList (cs ++ [c]) = (ofList cs).push c.toNat.toUInt16 := by
  simp [ofList, List.foldl_append, pushCodePoint, hc]

theorem push_size (s : JSStr) (u : UInt16) : (s.push u).b.size = s.b.size + 2 := by
  simp [push, ByteArray.size_push]

theorem bytes_join (u : UInt16) : (u.toUInt8.toUInt16 ||| ((u >>> 8).toUInt8.toUInt16 <<< 8)) = u := by
  apply UInt16.toNat_inj.mp
  simp only [UInt16.toNat_or, UInt16.toNat_shiftLeft, UInt8.toNat_toUInt16, UInt16.toNat_toUInt8, UInt16.toNat_shiftRight]
  have hu := u.toNat_lt
  have h8 : UInt16.toNat 8 % 16 = 8 := rfl
  rw [h8]
  generalize u.toNat = n at hu ⊢
  have hq : n >>> 8 < 2 ^ 8 := by rw [Nat.shiftRight_eq_div_pow]; omega
  rw [Nat.mod_eq_of_lt hq]
  have hs : (n >>> 8) <<< 8 < 2 ^ 16 := by rw [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]; omega
  rw [Nat.mod_eq_of_lt hs, Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt (Nat.mod_lt _ (by decide)),
    Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  omega

theorem get!_push_lt (b : ByteArray) (x : UInt8) (j : Nat) (hj : j < b.size) : (b.push x).get! j = b.get! j := by
  cases b with | mk d =>
  simp only [ByteArray.push, ByteArray.get!, ByteArray.size] at hj ⊢
  rw [getElem!_pos (d.push x) j (by simp; omega), getElem!_pos d j hj, Array.getElem_push_lt hj]

theorem get!_push_eq (b : ByteArray) (x : UInt8) : (b.push x).get! b.size = x := by
  cases b with | mk d =>
  simp only [ByteArray.push, ByteArray.get!, ByteArray.size]
  rw [getElem!_pos (d.push x) d.size (by simp)]; simp

theorem get_push_lt (s : JSStr) (u : UInt16) (i : Nat) (hi : 2 * i + 1 < s.b.size) : (s.push u).get i = s.get i := by
  simp only [get, push]
  rw [get!_push_lt _ _ _ (by simp [ByteArray.size_push]; omega), get!_push_lt _ _ _ (by omega),
    get!_push_lt _ _ _ (by simp [ByteArray.size_push]; omega), get!_push_lt _ _ _ (by omega)]

theorem get_push_eq (s : JSStr) (u : UInt16) (he : s.b.size % 2 = 0) : (s.push u).get s.length = u := by
  simp only [get, push, length]
  have h1 : 2 * (s.b.size / 2) = s.b.size := by omega
  have h2 : s.b.size + 1 = (s.b.push u.toUInt8).size := by simp [ByteArray.size_push]
  rw [h1, get!_push_lt _ _ _ (by simp [ByteArray.size_push]), get!_push_eq, h2, get!_push_eq, bytes_join]

/-- Pushing a plain list's characters onto `acc`: one unit each after `acc`'s. -/
theorem foldl_units (cs : List Char) (hp : Plain cs) : ∀ acc : JSStr, acc.b.size % 2 = 0 →
    (cs.foldl (fun acc c => acc.pushCodePoint c.toNat) acc).b.size = acc.b.size + 2 * cs.length ∧
      ∀ i (hi : i < acc.length + cs.length),
        (cs.foldl (fun acc c => acc.pushCodePoint c.toNat) acc).get i =
          if h : i < acc.length then acc.get i else (cs[i - acc.length]'(by omega)).toNat.toUInt16 := by
  induction cs with
  | nil => intro acc _; exact ⟨by simp, fun i hi => by simp at hi; simp [hi]⟩
  | cons c cs ih =>
    intro acc he
    have hc : c.toNat < 0xD800 := hp c (by simp)
    have hpc : acc.pushCodePoint c.toNat = acc.push c.toNat.toUInt16 := by simp [pushCodePoint]; omega
    obtain ⟨hsz, hget⟩ := ih (fun x hx => hp x (by simp [hx])) (acc.push c.toNat.toUInt16)
      (by rw [push_size]; omega)
    simp only [List.foldl_cons, hpc]
    have hlen : (acc.push c.toNat.toUInt16).length = acc.length + 1 := by
      simp only [length, push_size]; omega
    refine ⟨by rw [hsz, push_size]; simp; omega, fun i hi => ?_⟩
    simp only [List.length_cons] at hi
    rw [hget i (by rw [hlen]; omega)]
    have hle : acc.b.size = 2 * acc.length := by simp only [length]; omega
    by_cases hl : i < acc.length
    · have hl' : i < (acc.push c.toNat.toUInt16).length := by rw [hlen]; omega
      simp only [hl', hl, ↓reduceDIte]; exact get_push_lt _ _ _ (by omega)
    · by_cases hl1 : i = acc.length
      · subst hl1
        have hl' : acc.length < (acc.push c.toNat.toUInt16).length := by rw [hlen]; omega
        simp only [hl', hl, ↓reduceDIte, get_push_eq _ _ he, Nat.sub_self, List.getElem_cons_zero]
      · have hl' : ¬ i < (acc.push c.toNat.toUInt16).length := by rw [hlen]; omega
        simp only [hl', hl, ↓reduceDIte]
        have : i - acc.length = (i - (acc.length + 1)) + 1 := by omega
        simp only [this, List.getElem_cons_succ, hlen]

/-- **The code units of a plain list**: one per character, its code. -/
theorem ofList_units (cs : List Char) (hp : Plain cs) :
    (ofList cs).length = cs.length ∧ ∀ i (hi : i < cs.length), (ofList cs).get i = (cs[i]).toNat.toUInt16 := by
  obtain ⟨hsz, hget⟩ := foldl_units cs hp empty rfl
  have h0 : empty.length = 0 := rfl
  refine ⟨by simp only [ofList, length]; rw [hsz]; simp [empty], fun i hi => ?_⟩
  simp only [ofList]
  rw [hget i (by rw [h0]; omega)]
  simp [h0]

theorem codePointAt_plain (cs : List Char) (hp : Plain cs) (i : Nat) (hi : i < cs.length) :
    (ofList cs).codePointAt i = ((cs[i]).toNat, 1, false) := by
  obtain ⟨-, hget⟩ := ofList_units cs hp
  have hc : (cs[i]).toNat < 0xD800 := hp _ (List.getElem_mem hi)
  have hu : (cs[i]).toNat.toUInt16.toNat = (cs[i]).toNat := by
    simp [Nat.toUInt16, UInt16.toNat_ofNat]; omega
  have hh : isHighSurrogate (cs[i]).toNat.toUInt16 = false := by
    simp only [isHighSurrogate, Bool.and_eq_false_iff, decide_eq_false_iff_not, UInt16.le_iff_toNat_le, hu]
    left; simp; omega
  have hl : isLowSurrogate (cs[i]).toNat.toUInt16 = false := by
    simp only [isLowSurrogate, Bool.and_eq_false_iff, decide_eq_false_iff_not, UInt16.le_iff_toNat_le, hu]
    left; simp; omega
  simp [codePointAt, hget i hi, hh, hl, hu]

theorem toString_ofList (cs : List Char) (hp : Plain cs) : (ofList cs).toString = String.ofList cs := by
  obtain ⟨hlen, -⟩ := ofList_units cs hp
  simp only [toString, Id.run, Std.Legacy.Range.forIn_eq_forIn_range']
  have hsz : [:(ofList cs).length].size = cs.length := by simp [Std.Legacy.Range.size, hlen]
  rw [hsz]
  suffices hgo : ∀ r a j, j + r = cs.length →
      forIn (m := Id) (List.range' a r) (String.ofList (cs.take j), j) (fun x (__s : String × Nat) =>
          if __s.snd ≥ (ofList cs).length then pure (ForInStep.done (__s.fst, __s.snd))
          else pure (ForInStep.yield (__s.fst.push
              (if ((ofList cs).codePointAt __s.snd).2.snd = true then '�'
               else Char.ofNat ((ofList cs).codePointAt __s.snd).fst),
            __s.snd + ((ofList cs).codePointAt __s.snd).2.fst))) = (String.ofList cs, cs.length) by
    have := hgo cs.length 0 0 (by simp)
    simp only [List.take_zero, String.ofList_nil] at this
    rw [this]; rfl
  intro r
  induction r with
  | zero => intro a j hj; simp at hj; subst hj; simp; rfl
  | succ r ih =>
    intro a j hj
    have hjl : j < cs.length := by omega
    rw [List.range'_succ, List.forIn_cons]
    have hcp := codePointAt_plain cs hp j hjl
    have hnot : ¬ (j ≥ (ofList cs).length) := by rw [hlen]; omega
    simp only [hnot, ↓reduceIte, hcp, Bool.false_eq_true, Char.ofNat_toNat]
    have ht : (String.ofList (cs.take j)).push cs[j] = String.ofList (cs.take (j + 1)) := by
      rw [List.take_add_one, List.getElem?_eq_getElem hjl, Option.toList_some]
      simp only [String.ofList_append, String.ofList_cons, String.ofList_nil, String.append_empty,
        String.append_singleton]
    have := ih (a + 1) (j + 1) (by omega)
    simp only [ht]
    exact this

/-- **The round trip**: a Lean string below the surrogates, as a String value and back. -/
theorem toString_ofString (str : String) (hp : Plain str.toList) : (ofString str).toString = str := by
  rw [ofString, toString_ofList _ hp, String.ofList_toList]

theorem bytes_ext (a b : ByteArray) (h : a.data = b.data) : a = b := by
  cases a; cases b; simp only at h; rw [h]

theorem append_push (a t : JSStr) (u : UInt16) : (a ++ t).push u = a ++ t.push u := by
  show JSStr.mk _ = JSStr.mk _
  congr 1
  apply bytes_ext
  simp only [ByteArray.data_push, HAppend.hAppend, Append.append, append]
  simp [ByteArray.data_append, Array.push_append]
  rfl

theorem append_pushCodePoint (a t : JSStr) (c : Nat) : (a ++ t).pushCodePoint c = a ++ t.pushCodePoint c := by
  unfold pushCodePoint; split <;> simp [append_push]

theorem foldl_append_acc (cs : List Char) : ∀ a t : JSStr,
    cs.foldl (fun acc c => acc.pushCodePoint c.toNat) (a ++ t) = a ++ cs.foldl (fun acc c => acc.pushCodePoint c.toNat) t := by
  induction cs with
  | nil => intro a t; rfl
  | cons c cs ih => intro a t; simp only [List.foldl_cons, append_pushCodePoint, ih]

theorem append_empty (a : JSStr) : a ++ empty = a := by
  show JSStr.mk _ = _
  cases a; simp only [empty]; congr 1; exact ByteArray.append_empty

/-- **Appending** encodings: the encoding of the concatenation. -/
theorem ofString_append (a b : String) : ofString a ++ ofString b = ofString (a ++ b) := by
  simp only [ofString, ofList, String.toList_append, List.foldl_append]
  rw [← foldl_append_acc, append_empty]

theorem plain_digits (k : Nat) : Plain (ToString.toString k).toList := by
  intro c hc
  have hd : c.isDigit = true := by
    have : (ToString.toString k).toList = Nat.toDigits 10 k := by
      show (String.ofList (Nat.toDigits 10 k)).toList = _; simp
    rw [this] at hc
    exact Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc
  simp only [Char.isDigit, Bool.and_eq_true, decide_eq_true_eq] at hd
  have h57 : c.val.toNat ≤ 57 := by
    have := hd.2; rw [UInt32.le_iff_toNat_le] at this; simpa using this
  show c.val.toNat < 0xD800
  omega

end ES.JSStr
