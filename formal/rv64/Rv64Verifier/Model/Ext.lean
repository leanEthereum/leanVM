import Rv64Verifier.Model.Field
import Statement.Field

/-!
# `E` multiplication as the Rust computes it

`crates/verifier/src/field.rs`, `impl Mul for E`: Karatsuba, six carry-less products into the
coefficients of `y^0..y^4`, then `y^3 = y + 1` folds them into three limbs, each reduced once.
Proved equal to CompPoly's `Ext3` product (`emul_eq`).
-/

namespace Rv64Verifier.Model

open CompPoly.Extension LeanVM.Parameters

/-- The carry-less product as one 128-bit word. -/
def cl (a b : BitVec 64) : BitVec 128 := BinaryField.carryLessMul (w := 128) a b

/-- `E * E`, the Rust's Karatsuba, on limbs. -/
def emul (a0 a1 a2 b0 b1 b2 : BitVec 64) : BitVec 64 × BitVec 64 × BitVec 64 :=
  let p0 := cl a0 b0
  let p1 := cl a1 b1
  let p2 := cl a2 b2
  let e1 := cl (a0 ^^^ a1) (b0 ^^^ b1) ^^^ p0 ^^^ p1
  let e2 := cl (a0 ^^^ a2) (b0 ^^^ b2) ^^^ p0 ^^^ p2 ^^^ p1
  let e3 := cl (a1 ^^^ a2) (b1 ^^^ b2) ^^^ p1 ^^^ p2
  (BF64.reduce (p0 ^^^ e3), BF64.reduce (e1 ^^^ e3 ^^^ p2), BF64.reduce (e2 ^^^ p2))

/-- XOR identities between atoms: AC-normalize, then cancel equal pairs. -/
macro "xor_cancel" : tactic => `(tactic| (
  simp only [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor, BitVec.xor_zero] <;>
  ac_nf <;>
  simp only [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor, BitVec.xor_zero] <;>
  ac_nf))

theorem cl_xor_left (a b c : BitVec 64) : cl (a ^^^ b) c = cl a c ^^^ cl b c := by
  apply BF64.bitVec_toPoly_injective
  simp only [cl, BinaryField.toPoly_xor,
    BinaryField.toPoly_carryLessMul _ _ (show 64 + 64 ≤ 128 by norm_num)]
  ring

theorem cl_xor_right (a b c : BitVec 64) : cl a (b ^^^ c) = cl a b ^^^ cl a c := by
  apply BF64.bitVec_toPoly_injective
  simp only [cl, BinaryField.toPoly_xor,
    BinaryField.toPoly_carryLessMul _ _ (show 64 + 64 ≤ 128 by norm_num)]
  ring

theorem split128 (x : BitVec 128) : x = x.extractLsb' 64 64 ++ x.extractLsb' 0 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_append]
  by_cases h : i < 64
  · simp [h, hi]
  · simp [h, show i - 64 < 64 by omega, show 64 + (i - 64) = i by omega]

theorem reduce_xor (x y : BitVec 128) : BF64.reduce (x ^^^ y) = BF64.reduce x ^^^ BF64.reduce y := by
  have h : ∀ z : BitVec 128, BF64.reduce z = reduceWords (z.extractLsb' 64 64) (z.extractLsb' 0 64) :=
    fun z ↦ by rw [reduceWords_eq, ← split128]
  rw [h, h x, h y]
  simp only [reduceWords, BitVec.extractLsb'_xor, BitVec.ushiftRight_xor_distrib,
    BitVec.shiftLeft_xor_distrib]
  ac_rfl

theorem reduce_cl (a b : BF64) : BF64.reduce (cl a.toBitVec b.toBitVec) = (a * b).toBitVec :=
  (BF64.toBitVec_mul a b).symm

theorem toBitVec_add (a b : BF64) : (a + b).toBitVec = a.toBitVec ^^^ b.toBitVec := rfl

/-- The limbs of an `E` word. -/
def limbs (x : E) : BitVec 64 × BitVec 64 × BitVec 64 :=
  ((Ext.coeffNat x 0).toBitVec, (Ext.coeffNat x 1).toBitVec, (Ext.coeffNat x 2).toBitVec)

theorem monomialMod_three :
    (Ext.coeffNat (Ext.monomialMod 3 : E) 0, Ext.coeffNat (Ext.monomialMod 3 : E) 1,
      Ext.coeffNat (Ext.monomialMod 3 : E) 2) = (1, 1, 0) := by
  decide +kernel

theorem monomialMod_four :
    (Ext.coeffNat (Ext.monomialMod 4 : E) 0, Ext.coeffNat (Ext.monomialMod 4 : E) 1,
      Ext.coeffNat (Ext.monomialMod 4 : E) 2) = (0, 1, 1) := by
  decide +kernel

section
variable (a b c : BF64) (h : #[a, b, c].size = BF64.ext3Params.d)

theorem coeffNat_ofVector0 : Ext.coeffNat (Ext.ofVector (P := BF64.ext3Params) ⟨#[a, b, c], h⟩) 0 = a := by
  simp [Ext.coeffNat, Ext.coeff, Ext.ofVector, BF64.ext3Params]
  rfl

theorem coeffNat_ofVector1 : Ext.coeffNat (Ext.ofVector (P := BF64.ext3Params) ⟨#[a, b, c], h⟩) 1 = b := by
  simp [Ext.coeffNat, Ext.coeff, Ext.ofVector, BF64.ext3Params]
  rfl

theorem coeffNat_ofVector2 : Ext.coeffNat (Ext.ofVector (P := BF64.ext3Params) ⟨#[a, b, c], h⟩) 2 = c := by
  simp [Ext.coeffNat, Ext.coeff, Ext.ofVector, BF64.ext3Params]
  rfl

end

/-- **The Rust's `E` product is `Ext3` multiplication.** -/
theorem emul_eq (x y : E) :
    emul (limbs x).1 (limbs x).2.1 (limbs x).2.2 (limbs y).1 (limbs y).2.1 (limbs y).2.2 =
      limbs (x * y) := by
  have h3 := monomialMod_three
  have h4 := monomialMod_four
  simp only [Prod.mk.injEq] at h3 h4
  obtain ⟨h30, h31, h32⟩ := h3
  obtain ⟨h40, h41, h42⟩ := h4
  have hxy : x * y = Ext.mulCubic rfl x y := Ext.mul_eq_mulCubic rfl x y
  rw [hxy]
  unfold limbs Ext.mulCubic
  simp only [h30, h31, h32, h40, h41, h42, coeffNat_ofVector0, coeffNat_ofVector1,
    coeffNat_ofVector2, mul_one, mul_zero, add_zero]
  generalize Ext.coeffNat x 0 = x0, Ext.coeffNat x 1 = x1, Ext.coeffNat x 2 = x2,
    Ext.coeffNat y 0 = y0, Ext.coeffNat y 1 = y1, Ext.coeffNat y 2 = y2
  simp only [emul, cl_xor_left, cl_xor_right, reduce_xor, reduce_cl, toBitVec_add]
  clear h30 h31 h32 h40 h41 h42 hxy
  simp only [Prod.mk.injEq, BF64.mul_def]
  generalize (BF64.mul x0 y0).toBitVec = p00, (BF64.mul x0 y1).toBitVec = p01,
    (BF64.mul x0 y2).toBitVec = p02, (BF64.mul x1 y0).toBitVec = p10,
    (BF64.mul x1 y1).toBitVec = p11, (BF64.mul x1 y2).toBitVec = p12,
    (BF64.mul x2 y0).toBitVec = p20, (BF64.mul x2 y1).toBitVec = p21,
    (BF64.mul x2 y2).toBitVec = p22
  refine ⟨?_, ?_, ?_⟩ <;> xor_cancel

end Rv64Verifier.Model
