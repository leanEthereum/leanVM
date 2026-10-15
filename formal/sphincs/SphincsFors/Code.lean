import SphincsFors.Scheme

/-!
# How many digests the target-sum code accepts

The signer's counter search succeeds on a digest whose 64 two-bit digits sum to `T = 120` with no padding bits, so the search's failure probability is governed by how many of
the `2^128` digests that is. The count is the coefficient of `z^120` in `(1 + z + z^2 + z^3)^64`.

Counting it is one identity and one division. Packing the polynomial into a single natural number
in base `2^129`, which is above every coefficient, turns the product of the `64` factors into a
`Nat` power and the coefficient into one of its digits, so the kernel evaluates the whole count as
ordinary arithmetic on one large numeral.
-/

open Finset

set_option maxRecDepth 100000

namespace SphincsFors.Completeness

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
  have : TargetSum.sum x ≤ ∑ _i : ChainIndex, 3 :=
    Finset.sum_le_sum (fun i _ => Nat.le_of_lt_succ (x i).isLt)
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at this
  have hcard : Fintype.card ChainIndex = 64 := by simp [numChains]
  rw [hcard] at this
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

theorem two_pow_le_codeCount : 2 ^ 118 ≤ codeCount targetSum := by
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

def digit (x : Encoding) (j : Nat) : Nat :=
  if h : j < numChains then (x ⟨j, h⟩).val else 0

theorem digit_lt (x : Encoding) (j : Nat) : digit x j < 4 := by
  unfold digit
  split
  · exact (x _).isLt
  · decide

def packNat (x : Encoding) : Nat := ∑ j ∈ range numChains, digit x j * 4 ^ j

def pack (x : Encoding) : Digest := BitVec.ofNat digestBits (packNat x)

theorem packNat_lt (x : Encoding) : packNat x < 2 ^ 128 := by
  exact (sum_digits_lt 4 (by decide) (digit x) (digit_lt x) numChains)

theorem toNat_pack (x : Encoding) : (pack x).toNat = packNat x := by
  rw [pack, BitVec.toNat_ofNat, digestBits, Nat.mod_eq_of_lt (packNat_lt x)]

theorem encoding_val (d : Digest) (i : ChainIndex) :
    (digestEncoding d i).val = d.toNat / 2 ^ (digitOffset i) % 4 := by
  simp [digestEncoding, BitVec.extractLsb', winternitzBits, Nat.shiftRight_eq_div_pow]

theorem digestEncoding_pack (x : Encoding) : digestEncoding (pack x) = x := by
  funext i
  apply Fin.ext
  rw [encoding_val, toNat_pack]
  have hp : (2 : Nat) ^ digitOffset i = 4 ^ i.val := by
    simp [digitOffset, winternitzBits, pow_mul]
  rw [hp, packNat, digit_of_sum 4 (by decide) (digit x) (digit_lt x) numChains i.val i.isLt,
    digit, dif_pos i.isLt]

theorem decodeDigest_pack (x : Encoding) (hx : Valid x) : decodeDigest (pack x) = some x := by
  rw [decodeDigest, digestEncoding_pack, if_pos hx]

/-- At least one in 1024 uniformly sampled 128-bit digests is an admissible WOTS+C codeword. -/
theorem two_pow_le_card_accepting :
    2 ^ 118 ≤ (Finset.univ.filter fun d : Digest => (decodeDigest d).isSome).card := by
  refine le_trans two_pow_le_codeCount ?_
  rw [codeCount]
  apply Finset.card_le_card_of_injOn pack
  · intro x hx
    have hvalid : Valid x := (Finset.mem_filter.mp hx).2
    simp [decodeDigest_pack x hvalid]
  · intro left _ right _ heq
    have h := congrArg digestEncoding heq
    simpa only [digestEncoding_pack] using h

/-- Forward chain walks cannot turn a disclosed valid encoding into a different valid encoding. -/
theorem encoding_antichain {x y : Encoding} (hx : Valid x) (hy : Valid y)
    (hle : ∀ i, (x i).val ≤ (y i).val) : x = y := by
  have hsum : TargetSum.sum x = TargetSum.sum y := hx.trans hy.symm
  funext i
  refine Fin.ext (le_antisymm (hle i) ?_)
  by_contra hnot
  have hstrict : (x i).val < (y i).val := by omega
  have : TargetSum.sum x < TargetSum.sum y :=
    Finset.sum_lt_sum (fun j _ => hle j) ⟨i, Finset.mem_univ i, hstrict⟩
  omega

/-- Every admissible WOTS+C encoding leaves exactly 72 hash steps for its verifier. -/
theorem verification_chain_steps (word : Encoding) (hword : Valid word) :
    (∑ i : ChainIndex, (chainLength - 1 - (word i).val)) = 72 := by
  have hle : ∀ i ∈ (Finset.univ : Finset ChainIndex), (word i).val ≤ chainLength - 1 :=
    fun i _ => Nat.le_of_lt_succ (word i).isLt
  rw [Finset.sum_tsub_distrib Finset.univ hle,
    show (∑ i : ChainIndex, (word i).val) = targetSum from hword]
  simp [chainLength, winternitzBits, numChains, targetSum]

end SphincsFors.Completeness
