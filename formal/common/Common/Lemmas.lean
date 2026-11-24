module

public import Common.Prob
public import Common.Sponge
public import Common.Defs

@[expose] public section

/-!
# The permutation calls of a Keccak-256 hash

A hash of `n` bytes pads to `⌊n / 136⌋ + 1` blocks (`keccakPad_length`), one permutation call
each.
-/

namespace Common

/-- Splitting a list whose length is a multiple of 136 gives a block per 136 bytes. -/
theorem toBlocks_length (bs : List UInt8) (h : bs.length % 136 = 0) :
    (toBlocks bs).length = bs.length / 136 := by
  induction bs using toBlocks.induct with
  | case1 => simp [toBlocks]
  | case2 b bs ih =>
    rw [toBlocks, List.length_cons, ih (by simp only [List.length_drop]; omega)]
    simp only [List.length_drop, List.length_cons] at h ⊢
    have : 0 < bs.length + 1 := by omega
    omega

/-- **A Keccak-256 hash of `n` bytes calls the permutation `⌊n / 136⌋ + 1` times.** -/
theorem keccakPad_length (m : List UInt8) : (keccakPadding.pad m).length = m.length / 136 + 1 := by
  change (toBlocks (keccakPadBytes m)).length = _
  rw [toBlocks_length _ (by rw [keccakPadBytes_length]; omega), keccakPadBytes_length]
  omega

end Common
