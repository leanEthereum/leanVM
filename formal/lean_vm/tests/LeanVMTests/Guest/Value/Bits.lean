import LeanVM.Guest.Value.All

/-!
# Tests: bits, logs, tables and orders

Compiled checks (`#guard`) of `LeanVM.Guest.Value.Bits`, `Tables` and `Pigeonhole`: bit
reconstructions over the coordinate basis and in the exponent, `verify_log2_ceil`'s bounds on the
honest log and on its neighbours, the `g_squares` words, a certified sorted order; then the axioms
of the main lemmas.
-/

namespace LeanVMTests.Guest.Value

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Guest.Value

/-! ## Bits -/

#guard bitsVal (Nat.testBit 0b1011) 4 = 11
#guard (∑ i ∈ Finset.range 4, bitE (Nat.testBit 11 i) * coordBasis i) = eOfNat 11
#guard (∑ i ∈ Finset.range 4, bitE (Nat.testBit 11 i) * coordBasis (62 + i)) =
  eOfNat192 (2 ^ 62 * 11)
#guard (∏ j ∈ Finset.range 4, (1 + bitE (Nat.testBit 11 j) * (gen ^ 2 ^ j + 1))) = gen ^ 11
-- Without booleanity the bits are not unique: `x·e_0 = e_1`, and `x` fails `b·b = b`.
#guard eOfNat 2 * coordBasis 0 + 0 * coordBasis 1 = 0 * coordBasis 0 + 1 * coordBasis 1
#guard eOfNat 2 * eOfNat 2 ≠ eOfNat 2

/-! ## `verify_log2_ceil` -/

example : max 0 (log2Ceil 5) = 3 ∧ max 4 (log2Ceil 5) = 4 ∧ log2Ceil 8 = 3 ∧ log2Ceil 0 = 0 := by
  decide
-- For `W = 5` the guest's product `(E(W mod 2^L) + E(W))·(E(W) + E(2^L))` vanishes at `L = 3`
-- and not at `L = 2`: so `L = 3` passes the upper bound (G:632) and the minimality (G:639, at
-- `L - 1 = 2`), `L = 2` fails the upper bound, and `L = 4` fails the minimality (at `L - 1 = 3`).
#guard (eOfNat (5 % 2 ^ 3) + eOfNat 5) * (eOfNat 5 + eOfNat (2 ^ 3)) = 0
#guard (eOfNat (5 % 2 ^ 2) + eOfNat 5) * (eOfNat 5 + eOfNat (2 ^ 2)) ≠ 0

/-! ## The exponent tables -/

#guard squares sizeBits g = gSquaresBits.map K.ofBits
#guard gen ^ 2 ^ 33 = eOfNat (gSquaresBits.getD 33 0)
#guard gen ^ 2 ^ 33 ≠ eOfNat (gSquaresBits.getD 32 0)

/-! ## Sorted orders -/

/-- Four blocks' sizes. -/
def sizes : ℕ → ℕ := fun i ↦ [3, 5, 5, 2].getD i 0

#guard (List.range 4).mergeSort (stackLe sizes) = [1, 2, 0, 3]

example : [1, 2, 0, 3] = (List.range 4).mergeSort (stackLe sizes) :=
  eq_mergeSort_of_adjacent sizes (by decide) fun i h ↦ by
    have hi : i < 3 := by simp at h; omega
    interval_cases i <;> simp [sizes]

/-! ## Axioms -/

/-- info: 'LeanVM.Guest.Value.chain_eq_blake2sBytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms chain_eq_blake2sBytes

/-- info: 'LeanVM.Guest.Value.grind_check_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms grind_check_sound

/-- info: 'LeanVM.Guest.Value.ofBits_gSquaresBits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ofBits_gSquaresBits

/-- info: 'LeanVM.Guest.Value.verify_log2_ceil_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms verify_log2_ceil_sound

/-- info: 'LeanVM.Guest.Value.cover_of_writeOnce' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cover_of_writeOnce

end LeanVMTests.Guest.Value
