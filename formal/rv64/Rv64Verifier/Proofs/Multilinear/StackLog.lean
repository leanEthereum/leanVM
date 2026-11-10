import Rv64Verifier.Proofs.Multilinear.Basic
import Rv64Verifier.Blocks.F25
import Rv64Verifier.Model.Multilinear

/-!
# `log2_ceil` as `stack_offsets` computes it

RV64IM has no `clz`: `0x80006354` smears the bits of `y = total.saturating_sub(1)` down
(`smear`), inverts, and counts the ones (`popc`, the SWAR popcount); `0x800063f8` stores
`64 - popc`. `smear y` is `2^b - 1` for `b` the bit length of `y` (`smear_eq`), so the result is
`b`, checked for each of the 65 bit lengths (`popc_not`), which is `log2CeilRust total`.
-/

namespace Rv64Verifier.Proofs.Multilinear.StackOffsets
open RiscvZkvm.Rv64 LeanVM.Protocol.Verifier Rv64Verifier.Blocks.F25
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

def smear (y : Word) : Word :=
  let a := y ||| (y >>> 1)
  let b := a ||| (a >>> 2)
  let c := b ||| (b >>> 4)
  let d := c ||| (c >>> 8)
  let e := d ||| (d >>> 16)
  e ||| (e >>> 32)

def popc (x : Word) : Word :=
  let a := x - ((x >>> 1) &&& 0x5555555555555555)
  let b := (a &&& 0x3333333333333333) + ((a >>> 2) &&& 0x3333333333333333)
  let c := (b + (b >>> 4)) &&& 0x0f0f0f0f0f0f0f0f
  (c * 0x0101010101010101) >>> 56

theorem window_or {y a : Word} {m : Nat}
    (h : ∀ i, a.getLsbD i = true ↔ ∃ j, i ≤ j ∧ j < i + m ∧ y.getLsbD j = true) :
    ∀ i, (a ||| (a >>> m)).getLsbD i = true ↔ ∃ j, i ≤ j ∧ j < i + 2 * m ∧ y.getLsbD j = true := by
  intro i
  rw [BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight, Bool.or_eq_true, h, h]
  constructor
  · rintro (⟨j, h1, h2, h3⟩ | ⟨j, h1, h2, h3⟩)
    · exact ⟨j, h1, by omega, h3⟩
    · exact ⟨j, by omega, by omega, h3⟩
  · rintro ⟨j, h1, h2, h3⟩
    by_cases hj : j < i + m
    · exact Or.inl ⟨j, h1, hj, h3⟩
    · exact Or.inr ⟨j, by omega, by omega, h3⟩

theorem smear_bit (y : Word) (i : Nat) :
    (smear y).getLsbD i = true ↔ ∃ j, i ≤ j ∧ j < i + 64 ∧ y.getLsbD j = true := by
  have h0 : ∀ i, y.getLsbD i = true ↔ ∃ j, i ≤ j ∧ j < i + 1 ∧ y.getLsbD j = true := fun i ↦
    ⟨fun h ↦ ⟨i, le_rfl, by omega, h⟩, fun ⟨j, h1, h2, h3⟩ ↦ by rwa [show i = j by omega]⟩
  have h6 := window_or (window_or (window_or (window_or (window_or (window_or h0)))))
  exact h6 i

theorem smear_eq (y : Word) : smear y = BitVec.ofNat 64 (2 ^ bitLength y.toNat - 1) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one, decide_eq_true hi, Bool.true_and]
  apply Bool.eq_iff_iff.mpr
  rw [smear_bit, decide_eq_true_iff]
  simp only [← BitVec.testBit_toNat]
  constructor
  · rintro ⟨j, h1, -, h3⟩
    have hne : y.toNat ≠ 0 := fun h ↦ by rw [h, Nat.zero_testBit] at h3; cases h3
    have hge := Nat.ge_two_pow_of_testBit h3
    have hlt := Nat.lt_log2_self (n := y.toNat)
    have : j < y.toNat.log2 + 1 := (Nat.pow_lt_pow_iff_right (a := 2) (by norm_num)).mp (by omega)
    simp only [bitLength, hne, ite_false]
    omega
  · intro hb
    have hne : y.toNat ≠ 0 := fun h ↦ by rw [h] at hb; simp [bitLength] at hb
    have hlog : y.toNat.log2 < 64 := (Nat.log2_lt hne).mpr y.isLt
    simp only [bitLength, hne, ite_false] at hb
    exact ⟨y.toNat.log2, by omega, by omega, Nat.testBit_log2 hne⟩

theorem popc_not : ∀ b : Fin 65,
    (64 : Word) - popc (BitVec.ofNat 64 (2 ^ b.val - 1) ^^^ 0xffffffffffffffff) =
      BitVec.ofNat 64 b.val := by
  decide +kernel

theorem bitLength_le (y : Word) : bitLength y.toNat ≤ 64 := by
  by_cases h : y.toNat = 0
  · rw [h]; simp [bitLength]
  · simp only [bitLength, h, ite_false]
    have := (Nat.log2_lt h).mpr y.isLt
    omega

/-- `64 - popc(!smear(y))` is the bit length of `y`. -/
theorem log_eq (y : Word) :
    ((64 : Word) - popc (smear y ^^^ 0xffffffffffffffff)).toNat = bitLength y.toNat := by
  rw [smear_eq, popc_not ⟨bitLength y.toNat, by have := bitLength_le y; omega⟩, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by have := bitLength_le y; omega)]

/-- The popcount block's result. -/
theorem x14_eq {s t : MachineState} (h : b80006354.Holds s t) :
    t.getReg .x14 = popc (smear (s.getReg .x13) ^^^ 0xffffffffffffffff) :=
  h.reg_eq .x14 rfl rfl

end Rv64Verifier.Proofs.Multilinear.StackOffsets
