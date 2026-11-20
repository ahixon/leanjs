import JSProofs.Basic
import JSProofs.Env
import JSProofs.Object
import JSProofs.StrIndex

/-!
# Strings: concatenation and `length`

`a + b` on two strings is their concatenation (`applyBinaryOp_add_str`); `s.length` on a primitive string is
its number of UTF-16 code units (`getRefValue_str_length`), and lengths add (`length_append`).
-/

namespace ES

@[simp] theorem applyBinaryOp_add_str (a b : JSStr) (s : State) :
    applyBinaryOp .add (.str a) (.str b) s = .ok (.str (a ++ b)) s := by
  have hp : ∀ v : JSStr, toPrim (.str v) none = M.pure (.str v) := by
    intro v; funext t; simp only [toPrim, maxDepth_eq]; rfl
  have hs : ∀ v : JSStr, toStr (.str v) = M.pure v := by
    intro v; funext t; simp only [toStr, maxDepth_eq]; rfl
  have hop : (BinOp.add == BinOp.add) = true := by decide
  simp [applyBinaryOp, hp, hs, hop, M.bind_eq, M.bind_apply, pure, M.pure]

/-- `s.length` for a primitive string `s`. -/
theorem getRefValue_str_length (a : JSStr) (strict : Bool) (s : State) :
    getRefValue (.prop (.str a) (.str "length") strict none) s = .ok (.num (Conv.ofNat a.length)) s := by
  have hk : JSStr.ofString "length" = kLength := rfl
  simp [getRefValue, Value.isNullish, toPropertyKey, hk, M.bind_eq, M.bind_apply, pure, M.pure]

theorem JSStr.size_append (a b : JSStr) : (a ++ b).b.size = a.b.size + b.b.size := by
  show (a.b ++ b.b).size = _; exact ByteArray.size_append ..

theorem JSStr.length_append (a b : JSStr) (ha : a.b.size % 2 = 0) : (a ++ b).length = a.length + b.length := by
  simp only [JSStr.length, JSStr.size_append]; omega

/-! ## Numbers as strings -/

/-- **Number::toString of a natural number below 2^53**: its decimal digits. -/
theorem toStringDec_ofSmallInt (k : Nat) (hk : k < 2 ^ 53) :
    Num.toStringDec (Conv.ofSmallInt (k : Int)) = toString k := by
  by_cases h0 : k = 0
  · subst h0; rfl
  have hb : Nat.log2 k ≤ 52 := by
    have := (Nat.log2_lt h0).2 hk; omega
  have hne : ((k : Int) == 0) = false := by simp [h0]
  have hneg : decide ((k : Int) < 0) = false := by simp
  have ha : (k : Int).natAbs = k := by simp
  simp only [Conv.ofSmallInt, hne, Bool.false_eq_true, ↓reduceIte, ha, hb, hneg]
  have hm0 : k <<< (52 - Nat.log2 k) ≠ 0 := by
    rw [Nat.shiftLeft_eq]; exact Nat.mul_ne_zero h0 (Nat.ne_of_gt (Nat.two_pow_pos _))
  have hshift : (k <<< (52 - Nat.log2 k)) >>> (52 - Nat.log2 k) = k := Nat.shiftLeft_shiftRight _ _
  unfold Num.toStringDec
  split
  · rename_i h; cases h
  · rename_i m e h; injection h with h1 h2; exact absurd h2 hm0
  · rename_i h; cases h
  · rename_i n m e h
    injection h with hn hm he
    subst hn hm he
    by_cases hz : Nat.log2 k = 52
    · have h52 : ((Nat.log2 k : Int) - 52 == 0) = true := by simp [hz]
      simp [h52, hz]
    · have h52 : ((Nat.log2 k : Int) - 52 == 0) = false := by simp; omega
      have hlt : (Nat.log2 k : Int) - 52 < 0 := by omega
      have hgt : (Nat.log2 k : Int) - 52 > -53 := by omega
      have hto : (-((Nat.log2 k : Int) - 52)).toNat = 52 - Nat.log2 k := by omega
      have hint : Num.intMag (k <<< (52 - Nat.log2 k)) ((Nat.log2 k : Int) - 52) = true := by
        simp [Num.intMag, hto, hshift]
      simp [h52, hlt, hgt, hint, hto, hshift]

/-- The string of a natural-number Number value. -/
theorem numberToJSStr_nat (k : Nat) (hk : k < 2 ^ 53) :
    numberToJSStr (Conv.ofSmallInt (k : Int)) = JSStr.ofString (toString k) := by
  simp only [numberToJSStr, Num.toJSStr, Num.toStringRadix, beq_self_eq_true, ↓reduceIte, toStringDec_ofSmallInt k hk]

/-- **A string plus a Number**: the string, then the Number's string. -/
@[simp] theorem applyBinaryOp_add_str_num (a : JSStr) (x : F64) (s : State) :
    applyBinaryOp .add (.str a) (.num x) s = .ok (.str (a ++ numberToJSStr x)) s := by
  have hpa : toPrim (.str a) none = M.pure (.str a) := by funext t; simp only [toPrim, maxDepth_eq]; rfl
  have hpx : toPrim (.num x) none = M.pure (.num x) := by funext t; simp only [toPrim, maxDepth_eq]; rfl
  have hs : ∀ v : JSStr, toStr (.str v) = M.pure v := by
    intro v; funext t; simp only [toStr, maxDepth_eq]; rfl
  have hn : toStr (.num x) = M.pure (numberToJSStr x) := by
    funext t; simp only [toStr, maxDepth_eq]; rfl
  have hop : (BinOp.add == BinOp.add) = true := by decide
  simp [applyBinaryOp, hpa, hpx, hs, hn, hop, M.bind_eq, M.bind_apply, pure, M.pure]

/-! ## Indexing -/

/-- The key of `s[k]` for a natural `k`: its numeral. -/
theorem toPropertyKey_nat (k : Nat) (hk : k < 2 ^ 53) (s : State) :
    toPropertyKey (.num (Conv.ofSmallInt (k : Int))) s = .ok (.str (JSStr.ofNat k)) s := by
  have hpx : toPrim (.num (Conv.ofSmallInt (k : Int))) (some false) = M.pure (.num (Conv.ofSmallInt (k : Int))) := by
    funext t; simp only [toPrim, maxDepth_eq]; rfl
  have hn : toStr (.num (Conv.ofSmallInt (k : Int))) = M.pure (numberToJSStr (Conv.ofSmallInt (k : Int))) := by
    funext t; simp only [toStr, maxDepth_eq]; rfl
  simp [toPropertyKey, hpx, hn, numberToJSStr_nat k hk, M.bind_eq, M.bind_apply, pure, M.pure]; rfl

/-- **`a[k]`** for a primitive string `a` and a natural `k` below its length: the one-unit string at `k`. -/
theorem getRefValue_str_index (a : JSStr) (k : Nat) (hk : k < a.length) (hk10 : k < 10 ^ 10) (strict : Bool)
    (s : State) :
    getRefValue (.prop (.str a) (.num (Conv.ofSmallInt (k : Int))) strict none) s = .ok (.str (a.slice k (k + 1))) s := by
  have hne : JSStr.ofNat k ≠ kLength := JSStr.ofNat_ne_length k hk10
  simp [getRefValue, Value.isNullish, toPropertyKey_nat k (by omega), hne, JSStr.toIndex_ofNat k hk10, hk,
    M.bind_eq, M.bind_apply, pure, M.pure]

/-- One code unit of an encoded list of characters below 256. -/
theorem JSStr.slice_ofList (cs : List Char) (hcs : ∀ c ∈ cs, c.toNat < 256) (i : Nat) (hi : i < cs.length) :
    (JSStr.ofList cs).slice i (i + 1) = JSStr.ofList [cs[i]] := by
  have hl := JSStr.length_ofList cs hcs
  have hb := JSStr.bytes_ofList cs hcs
  have hb1 := JSStr.bytes_ofList [cs[i]] (by intro c hc; simp at hc; subst hc; exact hcs _ (List.getElem_mem _))
  obtain ⟨r, hr⟩ : ∃ r, JSStr.ofList [cs[i]] = r := ⟨_, rfl⟩
  rw [hr] at hb1 ⊢
  obtain ⟨h0, h1⟩ := JSStr.flatMap_enc_get cs i hi
  have hsz : (JSStr.ofList cs).b.data.size = 2 * cs.length := by
    rw [← Array.length_toList, hb, JSStr.length_flatMap_enc]
  unfold JSStr.slice
  simp only [hl, Nat.min_def, show i + 1 ≤ cs.length from hi, show i ≤ i + 1 by omega, ↓reduceIte]
  show JSStr.mk _ = JSStr.mk _
  congr 1; apply ByteArray.ext
  apply Array.toList_inj.mp
  rw [ByteArray.data_extract, Array.toList_extract, hb, hb1]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, JSStr.enc]
  rw [List.extract_eq_take_drop]
  have hlen := JSStr.length_flatMap_enc cs
  apply List.ext_getElem
  · simp only [List.length_take, List.length_drop, hlen, List.length_cons, List.length_nil]; omega
  · intro j hj1 hj2
    simp only [List.length_cons, List.length_nil] at hj2
    simp only [List.getElem_take, List.getElem_drop]
    have e : j = 0 ∨ j = 1 := by omega
    have hi0 : 2 * i < (List.flatMap JSStr.enc cs).length := by rw [hlen]; omega
    have hi1 : 2 * i + 1 < (List.flatMap JSStr.enc cs).length := by rw [hlen]; omega
    rw [List.getElem?_eq_getElem hi0] at h0
    rw [List.getElem?_eq_getElem hi1] at h1
    rcases e with rfl | rfl
    · simpa [JSStr.enc] using h0
    · simpa [JSStr.enc] using h1

end ES
