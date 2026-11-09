import Rv64Verifier.Model.Clmul
import Statement.Fast.FieldWords

/-!
# `K` multiplication as the Rust computes it

`crates/verifier/src/field.rs`: `clmul` takes the high half of the carry-less product from the
low half of the bit-reversed operands' product, reversed back; `reduce` folds the high word by
`x^64 = x^4 + x^3 + x + 1` twice; `base_mul` is their composition. Each is proved equal to
CompPoly's definitions, so `baseMul` is `BF64` multiplication.
-/

namespace Rv64Verifier.Model

open Finset

/-- `clmul`, as the high and low words of the Rust's `u128`. -/
def clmul (a b : BitVec 64) : BitVec 64 × BitVec 64 :=
  ((clmulLow a.reverse b.reverse).reverse >>> 1, clmulLow a b)

/-- `reduce`, on the high and low words. -/
def reduceWords (hi lo : BitVec 64) : BitVec 64 :=
  let spill := (hi >>> 63) ^^^ (hi >>> 61) ^^^ (hi >>> 60)
  let v := hi ^^^ spill
  lo ^^^ v ^^^ (v <<< 1) ^^^ (v <<< 3) ^^^ (v <<< 4)

/-- `base_mul`. -/
def baseMul (a b : BitVec 64) : BitVec 64 := reduceWords (clmul a b).1 (clmul a b).2

theorem card_pairs_reverse (a b : BitVec 64) (k : ℕ) (hk : k ≤ 126) :
    (pairs a.reverse b.reverse k).card = (pairs a b (126 - k)).card := by
  apply card_nbij' (fun uv ↦ (63 - uv.1, 63 - uv.2)) (fun uv ↦ (63 - uv.1, 63 - uv.2))
  · intro uv huv
    have huv := mem_coe.1 huv
    simp only [pairs, mem_filter, mem_product, mem_bitSet, BitVec.getLsbD_reverse,
      BitVec.getMsbD_eq_getLsbD, Bool.and_eq_true, decide_eq_true_eq] at huv
    rw [mem_coe]
    simp only [pairs, mem_filter, mem_product, mem_bitSet]
    refine ⟨⟨?_, ?_⟩, by omega⟩
    · rw [show 63 - uv.1 = 64 - 1 - uv.1 by omega]; exact huv.1.1.2
    · rw [show 63 - uv.2 = 64 - 1 - uv.2 by omega]; exact huv.1.2.2
  · intro uv huv
    have huv := mem_coe.1 huv
    simp only [pairs, mem_filter, mem_product, mem_bitSet] at huv
    have := BitVec.lt_of_getLsbD huv.1.1
    have := BitVec.lt_of_getLsbD huv.1.2
    rw [mem_coe]
    simp only [pairs, mem_filter, mem_product, mem_bitSet, BitVec.getLsbD_reverse,
      BitVec.getMsbD_eq_getLsbD, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨⟨by omega, ?_⟩, ⟨by omega, ?_⟩⟩, by omega⟩
    · rw [show 64 - 1 - (63 - uv.1) = uv.1 by omega]; exact huv.1.1
    · rw [show 64 - 1 - (63 - uv.2) = uv.2 by omega]; exact huv.1.2
  · intro uv huv
    have huv := mem_coe.1 huv
    simp only [pairs, mem_filter, mem_product, mem_bitSet, BitVec.getLsbD_reverse,
      BitVec.getMsbD_eq_getLsbD, Bool.and_eq_true, decide_eq_true_eq] at huv
    ext <;> simp <;> omega
  · intro uv huv
    have huv := mem_coe.1 huv
    simp only [pairs, mem_filter, mem_product, mem_bitSet] at huv
    have := BitVec.lt_of_getLsbD huv.1.1
    have := BitVec.lt_of_getLsbD huv.1.2
    ext <;> simp <;> omega

theorem pairs_eq_empty (a b : BitVec 64) (k : ℕ) (hk : 126 < k) : pairs a b k = ∅ := by
  ext uv
  simp only [pairs, mem_filter, mem_product, mem_bitSet, Finset.notMem_empty, iff_false, not_and]
  intro h1 h2
  have := BitVec.lt_of_getLsbD h1.1
  have := BitVec.lt_of_getLsbD h1.2
  omega

/-- **`clmul` is the carry-less product.** -/
theorem clmul_eq (a b : BitVec 64) :
    (clmul a b).1 ++ (clmul a b).2 = BinaryField.carryLessMul (w := 128) a b := by
  apply BitVec.eq_of_getLsbD_eq
  intro p hp
  rw [BitVec.getLsbD_append, getLsbD_carryLessMul]
  by_cases hp64 : p < 64
  · simp only [hp64, ↓reduceIte, clmul]
    exact getLsbD_clmulLow a b p hp64
  · simp only [hp64, ↓reduceIte, clmul, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_reverse,
      BitVec.getMsbD_eq_getLsbD]
    by_cases hp127 : p = 127
    · subst hp127
      simp [pairs_eq_empty a b 127 (by norm_num)]
    · rw [show 1 + (p - 64) = p - 63 by omega, decide_eq_true (show p - 63 < 64 by omega),
        Bool.true_and, getLsbD_clmulLow _ _ _ (by omega), card_pairs_reverse _ _ _ (by omega),
        show 126 - (64 - 1 - (p - 63)) = p by omega]

theorem reduceWords_eq (hi lo : BitVec 64) : reduceWords hi lo = BF64.reduce (hi ++ lo) := by
  have h := BF64.reduceWords_eq ⟨hi⟩ ⟨lo⟩
  simp only [BF64.wordsToBitVec] at h
  rw [← h]
  simp only [reduceWords, BF64.reduceWords, BF64.tailLow, BF64.tailHigh, UInt64.toBitVec_xor,
    UInt64.toBitVec_shiftLeft, UInt64.toBitVec_shiftRight]
  bv_decide

/-- **`base_mul` is `GF(2^64)` multiplication.** -/
theorem baseMul_eq (a b : BF64) : baseMul a.toBitVec b.toBitVec = (a * b).toBitVec := by
  rw [BF64.toBitVec_mul, ← clmul_eq, baseMul, reduceWords_eq]

end Rv64Verifier.Model
