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

end ES
