import SphincsSecurity.Scheme

/-!
# How many digests the target-sum code accepts

The signer accepts a digest when its 64 two-bit digits sum to `T = 123`. The count is the coefficient of `z^123` in `(1 + z + z^2 + z^3)^64`. Packing the polynomial in base `2^129`, above every coefficient, makes the coefficient one digit of an ordinary natural power.
-/

open Finset

set_option maxRecDepth 100000

namespace SphincsSecurity.Completeness

open TargetSum

/-- A base above every coefficient, so the coefficients are the digits. -/
def base : Nat := 2 ^ 129

theorem digit_of_sum (B : Nat) (hB : 0 < B) (c : Nat → Nat) (hc : ∀ s, c s < B) :
    ∀ (n k : Nat), k < n → (∑ s ∈ range n, c s * B ^ s) / B ^ k % B = c k := by
  intro n
  induction n generalizing c with
  | zero => intro k hk; exact absurd hk (Nat.not_lt_zero k)
  | succ n ih =>
      intro k hk
      have hsplit : ∑ s ∈ range (n + 1), c s * B ^ s
          = c 0 + B * ∑ s ∈ range n, c (s + 1) * B ^ s := by
        rw [Finset.sum_range_succ', Finset.mul_sum]
        simp only [pow_zero, mul_one, pow_succ]
        rw [Nat.add_comm]
        congr 1
        apply Finset.sum_congr rfl
        intro s _
        ring
      cases k with
      | zero =>
          rw [hsplit, pow_zero, Nat.div_one, Nat.add_mul_mod_self_left,
            Nat.mod_eq_of_lt (hc 0)]
      | succ k =>
          rw [hsplit, pow_succ']
          rw [← Nat.div_div_eq_div_mul]
          rw [Nat.add_mul_div_left _ _ hB, Nat.div_eq_of_lt (hc 0), Nat.zero_add]
          exact ih (fun s => c (s + 1)) (fun s => hc (s + 1)) k (Nat.lt_of_succ_lt_succ hk)

theorem weight_pow (B : Nat) :
    (∑ d : Digit, B ^ d.val) ^ numChains = ∑ x : Encoding, B ^ (TargetSum.sum x) := by
  have hcard : (Finset.univ : Finset ChainIndex).card = numChains := by
    simp [Finset.card_univ]
  have h1 : (∑ d : Digit, B ^ d.val) ^ numChains
      = ∏ _i : ChainIndex, ∑ d : Digit, B ^ d.val := by
    rw [Finset.prod_const, hcard]
  rw [h1, Finset.prod_univ_sum, Fintype.piFinset_univ]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.prod_pow_eq_pow_sum]
  rfl

/-- The number of codewords of digit sum `s`. -/
def codeCount (s : Nat) : Nat := (Finset.univ.filter (fun x : Encoding => TargetSum.sum x = s)).card

theorem sum_lt_193 (x : Encoding) : TargetSum.sum x < 193 := by
  have h : TargetSum.sum x ≤ ∑ _i : ChainIndex, 3 :=
    Finset.sum_le_sum (fun i _ => Nat.le_of_lt_succ (x i).isLt)
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at h
  have hcard : Fintype.card ChainIndex = 64 := by simp [numChains]
  rw [hcard] at h
  omega

theorem sum_encoding_pow (B : Nat) :
    ∑ x : Encoding, B ^ (TargetSum.sum x) = ∑ s ∈ range 193, codeCount s * B ^ s := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := TargetSum.sum) (t := range 193)
    (fun x _ => Finset.mem_range.mpr (sum_lt_193 x)) (fun x => B ^ (TargetSum.sum x))]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.sum_congr rfl (fun x hx => by rw [(Finset.mem_filter.mp hx).2]),
    Finset.sum_const, codeCount, smul_eq_mul]

theorem codeCount_lt_base (s : Nat) : codeCount s < base := by
  have h : codeCount s ≤ Fintype.card Encoding := Finset.card_filter_le _ _
  have hcard : Fintype.card Encoding = 4 ^ 64 := by
    simp [numChains, chainLength, winternitzBits]
  rw [hcard] at h
  exact Nat.lt_of_le_of_lt h (by decide)

theorem weight_eq : (∑ d : Digit, base ^ d.val) = (base ^ 4 - 1) / (base - 1) := by decide

theorem codeCount_target :
    codeCount targetSum = (∑ d : Digit, base ^ d.val) ^ numChains / base ^ targetSum % base := by
  rw [weight_pow, sum_encoding_pow]
  exact (digit_of_sum base (by decide) codeCount codeCount_lt_base 193 targetSum (by decide)).symm

theorem two_pow_le_codeCount : 2 ^ 114 ≤ codeCount targetSum := by
  rw [codeCount_target, weight_eq]
  decide

/-- A bounded-digit sum stays below the next power. -/
theorem sum_digits_lt (B : Nat) (hB : 0 < B) (v : Nat → Nat) (hv : ∀ j, v j < B) :
    ∀ n, ∑ j ∈ range n, v j * B ^ j < B ^ n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, pow_succ]
      have hle : v n * B ^ n ≤ (B - 1) * B ^ n :=
        Nat.mul_le_mul_right _ (by have := hv n; omega)
      have : B ^ n * B = (B - 1) * B ^ n + B ^ n := by
        cases B with
        | zero => omega
        | succ b => simp; ring
      omega

def encodingDigit (x : Encoding) (j : Nat) : Nat :=
  if h : j < numChains then (x ⟨j, h⟩).val else 0

theorem encodingDigit_lt (x : Encoding) (j : Nat) : encodingDigit x j < 4 := by
  unfold encodingDigit
  split
  · exact (x _).isLt
  · decide

def packNat (x : Encoding) : Nat := ∑ j ∈ range numChains, encodingDigit x j * 4 ^ j

def pack (x : Encoding) : Digest := BitVec.ofNat digestBits (packNat x)

theorem packNat_lt (x : Encoding) : packNat x < 2 ^ 128 := by
  have h := sum_digits_lt 4 (by decide) (encodingDigit x) (encodingDigit_lt x) numChains
  simpa [packNat, numChains, show (4 : Nat) ^ 64 = 2 ^ 128 by norm_num] using h

theorem toNat_pack (x : Encoding) : (pack x).toNat = packNat x := by
  rw [pack, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by simpa [digestBits] using packNat_lt x)]

theorem encoding_val (d : Digest) (i : ChainIndex) :
    (digestEncoding d i).val = d.toNat / 2 ^ (digitOffset i) % 4 := by
  simp [digestEncoding, BitVec.extractLsb', winternitzBits, Nat.shiftRight_eq_div_pow]

theorem digestEncoding_pack (x : Encoding) : digestEncoding (pack x) = x := by
  funext i
  apply Fin.ext
  rw [encoding_val, toNat_pack]
  have hpow : (2 : Nat) ^ digitOffset i = 4 ^ i.val := by
    rw [digitOffset, winternitzBits, pow_mul]
    norm_num
  rw [hpow]
  have h := digit_of_sum 4 (by decide) (encodingDigit x) (encodingDigit_lt x)
    numChains i.val i.isLt
  change packNat x / 4 ^ i.val % 4 = encodingDigit x i.val at h
  simpa [encodingDigit, i.isLt] using h

theorem decodeDigest_pack (x : Encoding) (hx : Valid x) : decodeDigest (pack x) = some x := by
  rw [decodeDigest, if_pos (by rw [digestEncoding_pack]; exact hx), digestEncoding_pack]

/-- The signer's counter search accepts at least `2^114` of the `2^128` digests. -/
theorem two_pow_le_card_accepting :
    2 ^ 114 ≤ (Finset.univ.filter fun d : Digest => (decodeDigest d).isSome).card := by
  refine le_trans two_pow_le_codeCount ?_
  rw [codeCount]
  apply Finset.card_le_card_of_injOn pack
  · intro x hx
    have hvalid : Valid x := (Finset.mem_filter.mp hx).2
    simp [decodeDigest_pack x hvalid]
  · intro left hleft right hright heq
    have hl : Valid left := (Finset.mem_filter.mp hleft).2
    have hr : Valid right := (Finset.mem_filter.mp hright).2
    have := decodeDigest_pack left hl
    rw [heq, decodeDigest_pack right hr] at this
    exact (Option.some.inj this).symm

end SphincsSecurity.Completeness
