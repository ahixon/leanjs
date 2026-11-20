import Proofs.Basic
import Proofs.Env
import Proofs.Object

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

end ES
