module

public import NativeRustc.Xmss.Swar

/-!
# `is_codeword`'s bit counts as rustc computes them on x86-64

On x86-64 rustc counts `(hi & LOW)`'s bits with the nibble form `popLowLo` uses, under the mask
`0x1111…` cut at bit 52 (`popLowHiN`); it is the count when `hi`'s top 12 bits are zero
(`popLowHiN_toNat`). The other three counts are `NativeRustc.Xmss.Swar`'s.
-/

namespace NativeRustc.Xmss.Swar

@[expose] public section

/-- `0x1111…` below bit 52. -/
def m11hi : BitVec 64 := 0x1111111111111#64

/-- `(hi & LOW).count_ones()` as rustc computes it on x86-64. -/
def popLowHiN (hi : BitVec 64) : BitVec 64 :=
  fromNibbles ((hi &&& m11hi) + ((hi >>> 2) &&& m11hi))

end

public section

/-- **`(hi & LOW).count_ones()`**, rustc's x86-64 way, for `hi` below `2 ^ 52`. -/
theorem popLowHiN_toNat (hi : BitVec 64) (h : hi.toNat < 2 ^ 52) :
    (popLowHiN hi).toNat = pop (hi.toNat &&& 0x5555555555555555) 64 := by
  have h2 : (hi >>> 2).toNat < 2 ^ 52 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    omega
  rw [popLowHiN, and_below52 hi h (c' := m11) (by decide +kernel),
    and_below52 (hi >>> 2) h2 (c' := m11) (by decide +kernel)]
  exact popLowLo_toNat hi

/-- **`is_codeword` of a digest whose top 12 bits are zero**, as rustc computes it on x86-64. -/
theorem isCodeword_swarN (lo hi : BitVec 64) (h : hi.toNat < 2 ^ 52) :
    isCodeword (2 ^ 64 * hi.toNat + lo.toNat) =
      ((popLowLo lo).toNat + (popLowHiN hi).toNat +
        2 * ((popHighLo lo).toNat + (popHighHi hi).toNat) == 106) := by
  rw [isCodeword_swar lo hi h, popLowHiN_toNat hi h, popLowHi_toNat hi h]

end

end NativeRustc.Xmss.Swar
