module

public import NativeRustc.Sphincs.Address

/-!
# `codeword` is the statement's `base_2b` test

On the bytes of a digest, `codeword`'s chunks of the big-endian number are
`TargetSum.base2bDigits`' (`getD_digits`), and their sum is the statement's (`codeword_eq`).
-/

@[expose] public section

namespace NativeRustc.Sphincs

open _root_.Sphincs HashSig

/-- Two bits `6 - 2 r` of byte `q` of a number. -/
theorem div_pow_mod4 (d q r : Nat) (hr : r < 4) :
    d / 2 ^ (8 * q + (6 - 2 * r)) % 4 = d / 256 ^ q % 256 / 2 ^ (6 - 2 * r) % 4 := by
  rw [pow_add, pow_mul, ← Nat.div_div_eq_div_mul, show (2 : Nat) ^ 8 = 256 from rfl]
  generalize d / 256 ^ q = y
  interval_cases r <;> simp <;> omega

/-- **Chunk `i` of a digest's big-endian number** is `base2bDigits`' digit `i`. -/
theorem beNat_digit (D : Digest) {i : Nat} (hi : i < 64) :
    beNat (le16 D) / 2 ^ (2 * (63 - i)) % 4 =
      (TargetSum.base2bDigits D ⟨i, hi⟩).val := by
  have hl := length_le16 D
  have hq : i / 4 < 16 := by omega
  rw [TargetSum.base2bDigits, BitVec.val_toFin, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow,
    winternitzBits, ← leNat_le16, show 8 * (i / 4) + 6 - 2 * (i % 4) = 8 * (i / 4) + (6 - 2 * (i % 4))
      by omega, div_pow_mod4 _ _ _ (Nat.mod_lt _ (by omega)),
    leNat_div_mod _ (by omega), beNat, show 2 * (63 - i) = 8 * (15 - i / 4) + (6 - 2 * (i % 4)) by
      omega, div_pow_mod4 _ _ _ (Nat.mod_lt _ (by omega)), leNat_div_mod _ (by simp; omega),
    List.getElem_reverse]
  congr 4
  simp only [hl]
  omega

/-- A sum over `range` as a list's. -/
theorem sum_map_range (g : Nat → Nat) : ∀ n, ((List.range n).map g).sum = ∑ i ∈ Finset.range n, g i
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, sum_map_range g n, Finset.sum_range_succ]
    simp

/-- **Chunk `i` of `codeword`** is `base2bDigits`' digit `i`. -/
theorem getD_digits (D : Digest) {i : Nat} (hi : i < 64) :
    ((digits (beNat (le16 D))).getD i 0).toNat = (TargetSum.base2bDigits D ⟨i, hi⟩).val := by
  rw [← beNat_digit D hi, digits, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hi]
  simp only [Option.map_some, Option.getD_some, UInt8.toNat_ofNat', Nat.shiftRight_eq_div_pow,
    show (3 : Nat) = 2 ^ 2 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega

/-- **`codeword` of a digest's bytes is `TargetSum.decodeDigest`'s test.** -/
theorem codeword_eq (D : Digest) :
    codeword (le16 D) =
      if TargetSum.Valid (TargetSum.base2bDigits D) then some (digits (beNat (le16 D))) else none := by
  have hsum : ((digits (beNat (le16 D))).map UInt8.toNat).sum =
      TargetSum.sum (TargetSum.base2bDigits D) := by
    rw [digits, List.map_map, sum_map_range, TargetSum.sum]
    rw [← Fin.sum_univ_eq_sum_range (fun i ↦ (UInt8.toNat ∘ fun i ↦
      UInt8.ofNat (beNat (le16 D) >>> (2 * (63 - i)) &&& 3)) i) 64]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have h := getD_digits D i.isLt
    rw [digits, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range i.isLt] at h
    simp only [Option.map_some, Option.getD_some] at h
    simp only [Function.comp_apply, UInt8.toNat_ofNat']
    exact h
  rw [codeword, hsum]
  rfl

end NativeRustc.Sphincs
