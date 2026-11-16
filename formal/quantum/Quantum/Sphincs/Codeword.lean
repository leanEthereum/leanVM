module

public import Quantum.Xmss.EncCost
public import Statement.LeanSphincs

@[expose] public section

/-!
# leanSPHINCS's codewords

A WOTS+C trial of leanSPHINCS hashes `PK.seed ‖ ADRS_enc ‖ M ‖ BE32(c)` and reads the 128-bit digest
`Trunc_16` of the output as `v = 64` base-4 digits (`TargetSum.base2bDigits`, FIPS 205's `base_2b`
with `w = 2` bits); the digest is a codeword when its digits sum to `T = 128`
(`TargetSum.decodeDigest`). Unlike leanXMSS's code (58 digits over the low 116 bits), the 64 digits
cover all 128 digest bits, so reading the digits is a bijection of digests and words
(`base2bDigits_bijective`).

* **The codeword fraction** (`cwCount_eq`, `rhoCw_eq`):
  `cwCount = 23195210617839120199658819909693679` of the `2^128` digests are codewords, the number
  of 64-digit base-4 words with digit sum 128,
  counted by leanXMSS's kernel-checked digit recursion (`Quantum.Xmss.card_digitSum`,
  `digitRow_64_128`). So `rhoCw = cwCount / 2^128 = 2^-13.84` and
  `2^-14 ≤ rhoCw ≤ 2^-13.8` (`inv_two_pow_14_le_rhoCw`, `rhoCw_le_two_rpow`), `rhoCw < 2^-13`
  (`rhoCw_lt_inv_two_pow_13`). Every trial rate gives `cwCount * 2^960` codeword values
  (`card_codeword_trunc128`).
* **Decoding** (`Codeword.decode_eq_some_iff`, `Codeword.decode_eq_none_iff`,
  `Codeword.sum_eq_of_decode`, `Codeword.eq_of_decode`): a digest decodes exactly when it is a
  codeword, to its digits, and the digits determine the digest.
* **Incomparability** (`Codeword.eq_of_le`, `Codeword.exists_lt_of_ne`): a codeword pointwise below
  another is equal to it, so of two distinct codewords the second has a digit smaller than the
  first's; every codeword has a chain opened below its end (`Codeword.exists_lt_of_sum`,
  `64 · 3 ≠ 128`).
-/

open Finset Sphincs
open HashSig (Digest chainLength winternitzBits digestBits)
open Quantum.Xmss (X trunc128 card_fiber_trunc128 card_filter_out_add)

namespace Quantum.Sphincs

/-! ## Digests and words -/

/-- **Reading the digits loses nothing**: the 64 base-4 digits cover the 128 digest bits. -/
theorem base2bDigits_injective : Function.Injective TargetSum.base2bDigits := by
  intro d d' h
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  have hb' : b < 128 := hb
  have hi : 4 * (b / 8) + (3 - b % 8 / 2) < chainCount := by
    simp only [chainCount]
    omega
  have hdig := congrArg (fun y : Encoding ↦ (y ⟨4 * (b / 8) + (3 - b % 8 / 2), hi⟩).val) h
  simp only [TargetSum.base2bDigits, BitVec.val_toFin] at hdig
  have hv := congrArg (fun y ↦ y.getLsbD (b % 2)) (BitVec.toNat_inj.1 hdig)
  have key : 8 * ((4 * (b / 8) + (3 - b % 8 / 2)) / 4) + 6 -
      2 * ((4 * (b / 8) + (3 - b % 8 / 2)) % 4) + b % 2 = b := by
    omega
  rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb', key] at hv
  simpa [winternitzBits, Nat.mod_lt b (show 2 > 0 by norm_num)] using hv

theorem card_digest_eq_card_encoding : Fintype.card Digest = Fintype.card Encoding := by
  rw [← FinEnum.card_eq_fintypeCard, FinEnum.card_bitVec, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_fin]
  norm_num [digestBits, chainLength, winternitzBits, chainCount]

theorem base2bDigits_bijective : Function.Bijective TargetSum.base2bDigits :=
  (Fintype.bijective_iff_injective_and_card _).2
    ⟨base2bDigits_injective, card_digest_eq_card_encoding⟩

/-! ## Codewords -/

/-- A codeword digest: its 64 base-4 digits sum to `T = 128`. -/
abbrev Codeword.Valid (d : Digest) : Prop := TargetSum.Valid (TargetSum.base2bDigits d)

theorem Codeword.decode_eq_some_iff {d : Digest} {x : Encoding} :
    TargetSum.decodeDigest d = some x ↔ Codeword.Valid d ∧ TargetSum.base2bDigits d = x := by
  unfold TargetSum.decodeDigest
  split_ifs with hv
  · exact ⟨fun h ↦ ⟨hv, Option.some.inj h⟩, fun h ↦ congrArg some h.2⟩
  · exact ⟨fun h ↦ h.elim, fun h ↦ absurd h.1 hv⟩

theorem Codeword.decode_eq_none_iff {d : Digest} :
    TargetSum.decodeDigest d = none ↔ ¬ Codeword.Valid d := by
  unfold TargetSum.decodeDigest
  split_ifs with hv
  · exact ⟨fun h ↦ h.elim, fun h ↦ absurd hv h⟩
  · exact ⟨fun _ ↦ hv, fun _ ↦ rfl⟩

theorem Codeword.valid_of_decode {d : Digest} {x : Encoding}
    (h : TargetSum.decodeDigest d = some x) : Codeword.Valid d :=
  (Codeword.decode_eq_some_iff.1 h).1

theorem Codeword.sum_eq_of_decode {d : Digest} {x : Encoding}
    (h : TargetSum.decodeDigest d = some x) : TargetSum.Valid x := by
  obtain ⟨hv, rfl⟩ := Codeword.decode_eq_some_iff.1 h
  exact hv

/-- A codeword is determined by its word. -/
theorem Codeword.eq_of_decode {d d' : Digest} {x : Encoding}
    (h : TargetSum.decodeDigest d = some x) (h' : TargetSum.decodeDigest d' = some x) : d = d' :=
  base2bDigits_injective ((Codeword.decode_eq_some_iff.1 h).2.trans
    (Codeword.decode_eq_some_iff.1 h').2.symm)

/-- A codeword has a chain opened below its end (`64 · 3 ≠ 128`). -/
theorem Codeword.exists_lt_of_sum {x : Encoding} (hx : TargetSum.Valid x) :
    ∃ i, (x i).val < chainLength - 1 := by
  by_contra h
  push Not at h
  have hc : chainLength = 4 := rfl
  have hs : TargetSum.sum x = ∑ _i : ChainIndex, 3 :=
    Finset.sum_congr rfl fun i _ ↦ by have := (x i).isLt; have := h i; omega
  rw [hx] at hs
  simp [targetSum, chainCount] at hs

/-- **Incomparability**: a codeword pointwise below another is equal to it. -/
theorem Codeword.eq_of_le {x y : Encoding} (hx : TargetSum.Valid x) (hy : TargetSum.Valid y)
    (hle : ∀ i, x i ≤ y i) : x = y := by
  by_contra hne
  have hlt : ∃ i ∈ Finset.univ, (x i).val < (y i).val := by
    by_contra h
    push Not at h
    exact hne (funext fun i ↦ Fin.ext (Nat.le_antisymm (hle i) (h i (Finset.mem_univ i))))
  have hsum : TargetSum.sum x < TargetSum.sum y :=
    Finset.sum_lt_sum (fun i _ ↦ hle i) hlt
  exact Nat.ne_of_lt hsum (hx.trans hy.symm)

/-- **Two distinct codewords**: the second has a digit smaller than the first's. -/
theorem Codeword.exists_lt_of_ne {x y : Encoding} (hx : TargetSum.Valid x)
    (hy : TargetSum.Valid y) (hne : x ≠ y) : ∃ i, y i < x i := by
  by_contra h
  push Not at h
  exact hne (Codeword.eq_of_le hx hy h)

/-! ## The codeword count -/

theorem digitRow_64_128 :
    (Quantum.Xmss.digitRow 64).getD 128 0 = 23195210617839120199658819909693679 := by
  decide +kernel

/-- The codeword digests. -/
def cwCount : ℕ := (Finset.univ.filter fun d : Digest ↦ Codeword.Valid d).card

/-- The codewords are the words of 64 base-4 digits with digit sum 128. -/
theorem cwCount_eq_card_words :
    cwCount = (Finset.univ.filter fun w : Fin 64 → Fin 4 ↦ ∑ i, (w i).val = 128).card := by
  have h : cwCount = (Finset.univ.filter fun x : Encoding ↦ TargetSum.Valid x).card :=
    Finset.card_equiv (Equiv.ofBijective _ base2bDigits_bijective) fun d ↦ by simp
  rw [h]
  rfl

/-- **The number of codewords** among the `2^128` digests. -/
theorem cwCount_eq : cwCount = 23195210617839120199658819909693679 := by
  rw [cwCount_eq_card_words, Quantum.Xmss.card_digitSum, digitRow_64_128]

/-- **The codeword fraction** `ρ_c`: the probability that a uniform digest is a codeword. -/
noncomputable def rhoCw : ℝ := cwCount / 2 ^ 128

theorem rhoCw_eq : rhoCw = 23195210617839120199658819909693679 / 2 ^ 128 := by
  rw [rhoCw, cwCount_eq]
  norm_num

/-- **`ρ_c ≥ 2^-14`**, the best power of two below it (`rhoCw_lt_inv_two_pow_13`). -/
theorem inv_two_pow_14_le_rhoCw : (2 ^ 14 : ℝ)⁻¹ ≤ rhoCw := by
  rw [rhoCw_eq]
  norm_num

theorem rhoCw_lt_inv_two_pow_13 : rhoCw < (2 ^ 13 : ℝ)⁻¹ := by
  rw [rhoCw_eq]
  norm_num

theorem rhoCw_pos : 0 < rhoCw :=
  lt_of_lt_of_le (by norm_num) inv_two_pow_14_le_rhoCw

theorem inv_rhoCw_le : rhoCw⁻¹ ≤ 2 ^ 14 := by
  rw [inv_le_comm₀ rhoCw_pos (by norm_num)]
  exact inv_two_pow_14_le_rhoCw

/-- **`ρ_c ≤ 2^-13.8`**: `ρ_c^5 ≤ 2^-69`. -/
theorem rhoCw_le_two_rpow : rhoCw ≤ (2 : ℝ) ^ (-13.8 : ℝ) := by
  have h5 : rhoCw ^ 5 ≤ ((2 : ℝ) ^ (-13.8 : ℝ)) ^ 5 := by
    rw [← Real.rpow_natCast ((2 : ℝ) ^ (-13.8 : ℝ)) 5, ← Real.rpow_mul (by norm_num),
      show (-13.8 : ℝ) * ((5 : ℕ) : ℝ) = -((69 : ℕ) : ℝ) by norm_num, Real.rpow_neg (by norm_num),
      Real.rpow_natCast, rhoCw_eq]
    norm_num
  exact le_of_pow_le_pow_left₀ (by norm_num) (by positivity) h5

/-- **Each trial rate gives `cwCount * 2^960` codeword values** of the read cell. -/
theorem card_codeword_trunc128 (xi : X) :
    (Finset.univ.filter fun v : X ↦ Codeword.Valid (trunc128 (xi + v))).card =
      cwCount * 2 ^ 960 := by
  -- `cwCount` is unfolded by `rw`: a kernel check of `cwCount * _` against the count would try to
  -- evaluate both to literals.
  rw [cwCount]
  exact card_filter_out_add (out := trunc128) (F := 2 ^ 960) (fun d ↦ card_fiber_trunc128 d)
    (fun d ↦ Codeword.Valid d) xi

end Quantum.Sphincs

end
