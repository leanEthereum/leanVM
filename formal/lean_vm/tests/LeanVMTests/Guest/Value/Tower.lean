import LeanVM.Guest.Value.Tower

/-!
# Tests: the tower and integers

Compiled checks (`#guard`) of `LeanVM.Guest.Value.Tower` on concrete words, each split or pin
with a mutation the guest's constraint rejects: a wrong hinted limb, a word with a top limb, an
overlapping split.
-/

namespace LeanVMTests.Guest.Value

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Guest.Value

/-! ## The tower -/

#guard y * y⁻¹ = 1
#guard y⁻¹ = E.ofLimbs 1 0 1

/-- A full word. -/
def w : E := E.ofLimbs (K.ofBits 0x1111) (K.ofBits 0x2222) (K.ofBits 0x3333)

/-- A canonical word. -/
def wc : E := E.ofLimbs (K.ofBits 0x1111) (K.ofBits 0x2222) 0

-- `pack64x2`.
#guard eOfNat 5 + y * eOfNat 7 = E.ofLimbs (K.ofBits 5) (K.ofBits 7) 0
-- `assert_canonical`: the honest low limb passes, and the derived high limb is the `y` limb.
#guard IsInK ((wc + ofK (wc.limb 0)) * y⁻¹)
#guard (wc + ofK (wc.limb 0)) * y⁻¹ = ofK (wc.limb 1)
-- Mutations: a wrong low limb, and a word with a top limb.
#guard ¬ IsInK ((wc + ofK (K.ofBits 0x1112)) * y⁻¹)
#guard ¬ IsInK ((w + ofK (w.limb 0)) * y⁻¹)
-- The three-limb split, and a wrong middle limb.
#guard ((w + ofK (w.limb 0)) * y⁻¹ + ofK (w.limb 1)) * y⁻¹ = ofK (w.limb 2)
#guard ¬ IsInK (((w + ofK (w.limb 0)) * y⁻¹ + ofK (K.ofBits 0x2223)) * y⁻¹)
-- `fs_pack`'s top-limb pin, and a wrong top limb.
#guard w + y * y * ofK (w.limb 2) = E.ofLimbs (w.limb 0) (w.limb 1) 0
#guard ¬ IsCanonical128 (w + y * y * ofK (K.ofBits 0x3334))

/-! ## Integers -/

#guard eOfNat 0b1010 + eOfNat 0b0110 = eOfNat 0b1100
#guard eOfNat (2 ^ 11) * eOfNat 5 = eOfNat (2 ^ 11 * 5)
#guard gen ^ 63 = eOfNat (2 ^ 63)
#guard coordBasis 70 = E.ofLimbs 0 (K.ofBits 64) 0
#guard coordBasis 191 = E.ofLimbs 0 0 (K.ofBits (2 ^ 63))
#guard eToNat (eOfNat192 (2 ^ 150 + 7)) = 2 ^ 150 + 7
-- Products by the coordinate basis in each limb.
#guard coordBasis 70 * eOfNat 5 = eOfNat192 (2 ^ 70 * 5)
#guard coordBasis 130 * eOfNat 3 = eOfNat192 (2 ^ 130 * 3)
#guard coordBasis 63 * eOfNat 2 ≠ eOfNat192 (2 ^ 64)
-- A reduction: `x^63 · x` is not the word `2^64`.
#guard gen ^ 64 ≠ eOfNat192 (2 ^ 64)

-- The disjoint-bit split: a multiple of `2^s` plus a value below `2^s` is their sum, an
-- overlapping split an XOR.
#guard eOfNat (2 ^ 11 * 3) + eOfNat 192 = eOfNat (2 ^ 11 * 3 + 192)
#guard eOfNat 64 + eOfNat 64 ≠ eOfNat 128

end LeanVMTests.Guest.Value
