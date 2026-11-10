/-
  LeanVM.Guest.B1.Sig.SpWotsCompleteStmt

  `sp_wots` is complete against the statement (`sp_wots_complete : sp_wots_complete_Spec`): for a
  digest whose `base_2b` digits reach the target sum and any chain values, its body holds of a
  valuation whose arguments are `PK.seed`'s cell, the key's address cells and the digest's cell,
  returning the cell of the leaf the values recover.
-/

module

public import LeanVM.Guest.B1.Sig.SpWotsCompleteR
public import LeanVM.Guest.B1.Sig.SphincsSoundWots

/-!
# `sp_wots`, complete, against the statement

The digest's digits as numbers (`spDigitsOf`, `TargetSum.base2bDigits`) and the chain values as
cells (`spValsOf`) are what the cells' completeness takes (`sp_wots_complete_cells`); its encoding
`spX` of those digits is the digest's own number (`spX_digest`: both have the same base-4 digits,
digit `k` being the `base_2b` digit `4 (k / 4) + 3 - k % 4`), and its leaf over cells is the
statement's (`wotsLeafOf_cells`).
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open HashSig

@[expose] public section

/-- **The digest's `base_2b` digits**, as numbers (`0` past the 64 chains). -/
def spDigitsOf (digest : Digest) (i : Nat) : Nat :=
  if h : i < 64 then (Sphincs.TargetSum.base2bDigits digest ⟨i, h⟩).val else 0

/-- **The chain values as cells** (`0` past the 64 chains). -/
def spValsOf (values : Sphincs.ChainIndex → Digest) (i : Nat) : E :=
  if h : i < 64 then cellOf128 (values ⟨i, h⟩) else 0

theorem spDigitsOf_lt (digest : Digest) (i : Nat) : spDigitsOf digest i < 4 := by
  unfold spDigitsOf
  split
  · exact (Sphincs.TargetSum.base2bDigits digest _).isLt
  · norm_num

theorem spDigitsOf_eq (digest : Digest) (i : Sphincs.ChainIndex) :
    (Sphincs.TargetSum.base2bDigits digest i).val = spDigitsOf digest i.val := by
  have hi : i.val < 64 := i.isLt
  simp only [spDigitsOf, hi, ↓reduceDIte]

theorem spDigitsOf_sum {digest : Digest}
    (hT : Sphincs.TargetSum.Valid (Sphincs.TargetSum.base2bDigits digest)) :
    ∑ i ∈ Finset.range 64, spDigitsOf digest i = 128 := by
  unfold Sphincs.TargetSum.Valid Sphincs.TargetSum.sum at hT
  simp only [spDigitsOf_eq] at hT
  rw [Fin.sum_univ_eq_sum_range (fun i => spDigitsOf digest i)] at hT
  exact hT

theorem spValsOf_canon (values : Sphincs.ChainIndex → Digest) (i : Nat) :
    IsCanonical128 (spValsOf values i) := by
  unfold spValsOf
  split
  · exact isCanonical128_cellOf128 _
  · exact canon_zero

theorem sum_base4 (x : Nat) : ∀ m, ∑ i ∈ Finset.range m, x / 4 ^ i % 4 * 4 ^ i = x % 4 ^ m
  | 0 => by simp [Nat.mod_one]
  | m + 1 => by
      rw [Finset.sum_range_succ, sum_base4 x m, Nat.mod_pow_succ]
      ring

/-- The `base_2b` digit holding base-4 digit `k` of the digest's number. -/
def spDigitOfQuad (k : Nat) : Nat := 4 * (k / 4) + 3 - k % 4

theorem spDigitPos_quad (k : Nat) : spDigitPos (spDigitOfQuad k) = 2 * k := by
  unfold spDigitPos spDigitOfQuad; omega

/-- **Base-4 digit `k` of the digest's number** is its `base_2b` digit `spDigitOfQuad k`. -/
theorem digest_quad (digest : Digest) {k : Nat} (hk : k < 64) :
    digest.toNat / 4 ^ k % 4 = spDigitsOf digest (spDigitOfQuad k) := by
  have hi : spDigitOfQuad k < 64 := by unfold spDigitOfQuad; omega
  simp only [spDigitsOf, hi, ↓reduceDIte, Sphincs.TargetSum.base2bDigits, winternitzBits]
  rw [show 8 * (spDigitOfQuad k / 4) + 6 - 2 * (spDigitOfQuad k % 4) = 2 * k by
    unfold spDigitOfQuad; omega]
  show _ = (BitVec.extractLsb' (2 * k) 2 digest).toNat
  rw [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, pow_mul]
  norm_num

/-- **The digits' encoding is the digest's number.** -/
theorem spX_digest (digest : Digest) : spX (spDigitsOf digest) 64 = digest.toNat := by
  have hd := spDigitsOf_lt digest
  have hX := spX_lt hd (m := 64) le_rfl
  have hY : digest.toNat < 2 ^ 128 := digest.isLt
  rw [← Nat.mod_eq_of_lt (show spX (spDigitsOf digest) 64 < 4 ^ 64 by simpa using hX),
    ← Nat.mod_eq_of_lt (show digest.toNat < 4 ^ 64 by simpa using hY), ← sum_base4, ← sum_base4]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k < 64 := Finset.mem_range.mp hk
  have hi : spDigitOfQuad k < 64 := by unfold spDigitOfQuad; omega
  rw [digest_quad digest hk', show (4 : Nat) ^ k = 2 ^ spDigitPos (spDigitOfQuad k) by
    rw [spDigitPos_quad, pow_mul]; norm_num, spX_digit hd hi]

theorem cellOf128_eq_eOfNat128' (v : BitVec 128) : cellOf128 v = eOfNat128 v.toNat := by
  rw [← cellOf128_eq_eOfNat128 v.isLt, BitVec.ofNat_toNat, BitVec.setWidth_eq]

variable {C : CallRel} {rd : Reader}

/-- **`sp_wots` is complete.** -/
theorem sp_wots_complete : sp_wots_complete_Spec := by
  intro C rd publicSeed layer tree leaf digest values hm hT
  have hpk : keyAdrsCells layer.val tree.val leaf.val =
      (adrsCell0 layer.val tree.val, adrsCell1 0 leaf.val 0 0) := rfl
  obtain ⟨σ, h0, h1, h2, h3, hh⟩ := sp_wots_complete_cells (C := C) (rd := rd)
    (pp := cellOf128 publicSeed) (a0 := adrsCell0 layer.val tree.val) (a1 := adrsCell1 0 leaf.val 0 0)
    (isCanonical128_cellOf128 _) (isCanonical128_cellOf128 _) (isCanonical128_cellOf128 _)
    (spDigitsOf_lt digest) (spDigitsOf_sum hT) (spValsOf_canon values) hm
  have hleaf : spLeafCell (cellOf128 publicSeed) (adrsCell0 layer.val tree.val)
      (adrsCell1 0 leaf.val 0 0) (spDigitsOf digest) (spValsOf values) =
      cellOf128 (wotsLeafOf publicSeed layer tree leaf digest values) := by
    have e := wotsLeafOf_cells (cellOf128 publicSeed) layer tree leaf digest (spDigitsOf digest)
      (spValsOf values) (spDigitsOf_eq digest)
    have ev : (fun i : Sphincs.ChainIndex => cellVal (spValsOf values i.val)) = values := by
      funext i
      have hi : i.val < 64 := i.isLt
      simp only [spValsOf, hi, ↓reduceDIte]
      exact cellVal_cellOf128 _
    rw [ev, cellVal_cellOf128] at e
    rw [e]
    exact (cellOf128_cellVal (canon_hcell _)).symm
  refine ⟨σ, h0, by rw [hpk, h1, h2], by rw [h3, spX_digest]; exact (cellOf128_eq_eOfNat128' digest).symm, ?_⟩
  rw [← hleaf]
  exact hh

end
end LeanVM.Guest.B1.Sig
