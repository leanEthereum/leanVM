module

public import NativeRustcX64.Sym.Basic

/-!
# Bit-level lemmas for the digest's bit loop (x86-64)

The loop's leaf is ten bits assembled with `add`s of disjoint bits (`addb %bl, %bl`, `leaq`); the
lemmas turn them into `or`s and shifts (`add_self'`, `mul2`, `mul4`, `add_bit_shl1`, `add_lea4`),
normalize the merges of zero-extended bytes (`extract_setWidth8`, `extract_app`, `setWidth8_app`,
`zero_app`) and `setb`'s values (`ite_one_zero`). `bitsVal`: ten bits, most significant first.
-/

namespace NativeRustcX64.SphincsVerifyProof.Digest

@[expose] public section

/-- Ten bits, most significant first. -/
def bitsVal (b : Nat → BitVec 64) : BitVec 64 := (List.range 10).foldl (fun v j ↦ v <<< 1 ||| b j) 0

end

public section

theorem add_self' {w : Nat} (x : BitVec w) : x + x = x <<< 1 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  congr 1
  omega

theorem mul2 (x : BitVec 64) : x * 2#64 = x <<< 1 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_mul, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  simp [Nat.mul_comm]

theorem mul4 (x : BitVec 64) : x * 4#64 = x <<< 2 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_mul, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  simp [Nat.mul_comm]

theorem add_bit_shl1 (c : Bool) (b : BitVec 64) :
    (BitVec.append 0#56 (BitVec.setWidth 8 (if c = true then 1#64 else 0#64)) : BitVec 64) + b <<< 1 =
      BitVec.append 0#56 (BitVec.setWidth 8 (if c = true then 1#64 else 0#64)) ||| b <<< 1 := by
  apply BitVec.add_eq_or_of_and_eq_zero
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  cases c
  · simp
  · simp
    omega

theorem add_lea4 (v : BitVec 32) (b : BitVec 64) :
    BitVec.setWidth 64 ((v &&& 1#32) <<< 1) + b <<< 2 = BitVec.setWidth 64 ((v &&& 1#32) <<< 1) ||| b <<< 2 := by
  apply BitVec.add_eq_or_of_and_eq_zero
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp
  omega

theorem ite_one_zero (c : Bool) : (if c = true then 1#64 else 0#64) = (BitVec.ofBool c).setWidth 64 := by
  cases c <;> rfl

theorem zero_app (x : BitVec 8) : BitVec.append 0#56 x = x.setWidth 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  show (0#56 ++ x).getLsbD i = _
  rw [BitVec.getLsbD_append, BitVec.getLsbD_setWidth]
  by_cases h : i < 8
  · simp [h]
    omega
  · simp [h, BitVec.getLsbD_of_ge x i (by omega)]

theorem extract_setWidth8 (z : BitVec 8) : (BitVec.setWidth 64 z).extractLsb' 8 (64 - 8) = 0#56 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp

theorem extract_app (a : BitVec 56) (b : BitVec 8) : (a.append b : BitVec 64).extractLsb' 8 (64 - 8) = a :=
  BitVec.extractLsb'_append_eq_left

theorem setWidth8_app (a : BitVec 56) (b : BitVec 8) : (a.append b : BitVec 64).setWidth 8 = b :=
  BitVec.setWidth_append_eq_right

end

end NativeRustcX64.SphincsVerifyProof.Digest
