/-
  Rv64mc.Proof.Field.U128

  A `u128` and its two words (`Spec.Field.lo128`, `hi128`): the words of a concatenation, of a XOR and of a shift by
  one, as the code computes them a word at a time.
-/

import Rv64mc.Spec.Field.Basic

namespace Rv64mc.Spec.Field

theorem lo128_append (h l : BitVec 64) : lo128 (h ++ l) = l := by
  unfold lo128; ext i hi
  rw [BitVec.getElem_setWidth, BitVec.getLsbD_append]; simp [hi]
theorem hi128_append (h l : BitVec 64) : hi128 (h ++ l) = h := by
  unfold hi128; ext i hi
  rw [BitVec.getElem_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_append]
  simp [BitVec.getLsbD_eq_getElem, hi]
theorem append_hi_lo (x : BitVec 128) : hi128 x ++ lo128 x = x := by
  unfold hi128 lo128; ext i hi
  rw [BitVec.getElem_append]; split
  · have hi' : i < 128 := hi
    simp only [BitVec.getElem_setWidth]; exact BitVec.getLsbD_eq_getElem hi'
  · have hi' : i < 128 := hi
    simp only [BitVec.getElem_setWidth, BitVec.getLsbD_ushiftRight]
    rw [show 64 + (i - 64) = i by omega, BitVec.getLsbD_eq_getElem hi']
theorem lo128_xor (x y : BitVec 128) : lo128 (x ^^^ y) = lo128 x ^^^ lo128 y := by
  unfold lo128; ext i hi; simp
theorem hi128_xor (x y : BitVec 128) : hi128 (x ^^^ y) = hi128 x ^^^ hi128 y := by
  unfold hi128; ext i hi; simp
theorem lo128_shl1 (x : BitVec 128) : lo128 (x <<< 1) = lo128 x <<< 1 := by
  unfold lo128; ext i hi; simp [BitVec.getElem_shiftLeft]
theorem hi128_shl1 (x : BitVec 128) : hi128 (x <<< 1) = (hi128 x <<< 1) ||| (lo128 x >>> 63) := by
  unfold hi128 lo128; ext i hi
  simp only [BitVec.getElem_setWidth, BitVec.getElem_or, BitVec.getElem_shiftLeft, BitVec.getElem_ushiftRight,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
  by_cases h : i = 0
  · subst h; simp
  · simp [h, show ¬ i < 1 by omega, show 64 + i - 1 = 64 + (i - 1) by omega, show 64 + i < 128 by omega,
      show ¬ 63 + i < 64 by omega]
/-- `lo128_append` unfolded, as `Model.reduce` reads a `u128`. -/
theorem setWidth_append (h l : BitVec 64) : (h ++ l).setWidth 64 = l := lo128_append h l

/-- `hi128_append` unfolded, as `Model.reduce` reads a `u128`. -/
theorem setWidth_shift_append (h l : BitVec 64) : ((h ++ l) >>> 64).setWidth 64 = h := hi128_append h l

/-- With `BitVec.xor_assoc` and `BitVec.xor_comm`, `simp` puts a XOR of words in one order: for comparing the code's
    XORs with the Model's. -/
theorem xor_left_comm {w : Nat} (x y z : BitVec w) : x ^^^ (y ^^^ z) = y ^^^ (x ^^^ z) := by
  rw [← BitVec.xor_assoc, BitVec.xor_comm x y, BitVec.xor_assoc]

/-- `xor_left_comm` for `|||` (named apart from `_root_.or_left_comm`). -/
theorem bor_left_comm {w : Nat} (x y z : BitVec w) : x ||| (y ||| z) = y ||| (x ||| z) := by
  rw [← BitVec.or_assoc, BitVec.or_comm x y, BitVec.or_assoc]

/-- The low word of `(h as u128) << 64 | l as u128`, as `Model.clmul` builds it. -/
theorem lo128_join (h l : BitVec 64) : lo128 (h.setWidth 128 <<< 64 ||| l.setWidth 128) = l := by
  unfold lo128; ext i hi; simp

/-- The high word of `(h as u128) << 64 | l as u128`. -/
theorem hi128_join (h l : BitVec 64) : hi128 (h.setWidth 128 <<< 64 ||| l.setWidth 128) = h := by
  unfold hi128; ext i hi
  simp [show 64 + i < 128 by omega, show i < 128 by omega, BitVec.getLsbD_eq_getElem hi]

/-- A word is the bit reversal of another when its bits are the other's read from the top: for a reversal the code
    computes by shifts and masks, checked bit by bit. -/
theorem eq_reverse {x y : BitVec 64} (h : ∀ i, i < 64 → x.getLsbD i = y.getLsbD (63 - i)) : x = y.reverse := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [BitVec.getLsbD_reverse, h i hi, BitVec.getMsbD_eq_getLsbD]; simp [hi]

end Rv64mc.Spec.Field
