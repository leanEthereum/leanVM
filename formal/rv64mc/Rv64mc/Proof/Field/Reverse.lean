/-
  Rv64mc.Proof.Field.Reverse

  `u64::reverse_bits` as the compiler lowers it on RV64IM (no bit-reversal instruction): a byte swap by shifts and
  masks (`bswap`), then swaps of nibbles, pairs and bits (`swapBits`), proved bit by bit to be `BitVec.reverse`
  (`reverse_net`). A function's code is this up to the order of its `|||`s and `&&&`s: `ac_rfl` after
  `simp only [bswap, swapBits]` matches it (`Proof/Field/Clmul.lean`).
-/

import Rv64mc.Spec.Field.Basic
import Mathlib.Tactic.IntervalCases

namespace Rv64mc.Spec.Field

open Lprog

/-- The byte swap, as the code computes it (the middle bytes through a 32-bit shift). -/
def bswap (x : BitVec 64) : BitVec 64 :=
  x <<< 56 ||| (x &&& 0xff00#64) <<< 40 ||| ((x &&& 0xff0000#64) <<< 24 |||
    (UnOp.sext .b4).eval ((UnOp.zext .b4).eval x >>> 24) <<< 32) |||
    (x >>> 8 &&& 0xff000000#64 ||| x >>> 24 &&& 0xff0000#64 ||| (x >>> 40 &&& 0xff00#64 ||| x >>> 56))

/-- A swap of the `k`-bit groups `m` selects. -/
def swapBits (k : Nat) (m x : BitVec 64) : BitVec 64 := x >>> k &&& m ||| (x &&& m) <<< k

set_option maxHeartbeats 1000000 in
-- 64 bits, each through four stages
/-- **The lowered `reverse_bits` reverses the bits.** -/
theorem reverse_net (x : BitVec 64) :
    swapBits 1 0x5555555555555555#64 (swapBits 2 0x3333333333333333#64
      (swapBits 4 0x0f0f0f0f0f0f0f0f#64 (bswap x))) = x.reverse := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [BitVec.getLsbD_reverse, BitVec.getMsbD_eq_getLsbD]
  interval_cases i <;> simp [swapBits, bswap, UnOp.eval, Width.bits,
    BitVec.getElem_signExtend, BitVec.getElem_setWidth]

end Rv64mc.Spec.Field
