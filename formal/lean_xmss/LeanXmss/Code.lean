module

public import LeanXmss.Scheme

@[expose] public section

/-!
# The codewords

A digest is a codeword when its top `128 - 2v = 12` bits are zero and its first `v = 58` base-4
digits sum to `T = 106`. Its digits determine it, so codewords and digit words of sum `T` are in
bijection, and there are `[z^106](1 + z + z^2 + z^3)^58` of them.

The count packs the polynomial into one natural number in base `2^117`, above every coefficient, so
the kernel evaluates the coefficient as a digit of a power.
-/

open Finset

set_option maxRecDepth 100000

namespace LeanXmss.Codeword

open HashSig

/-- A base above every coefficient, so the coefficients are the digits. -/
def base : Nat := 2 ^ 117

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

/-- A number below `B^k` is the sum of its `k` base-`B` digits. -/
theorem sum_digits_eq (B : Nat) (hB : 0 < B) :
    ∀ (k n : Nat), n < B ^ k → ∑ j ∈ range k, (n / B ^ j % B) * B ^ j = n := by
  intro k
  induction k with
  | zero => intro n hn; simp at hn; simp [hn]
  | succ k ih =>
      intro n hn
      rw [Finset.sum_range_succ']
      have hdiv : n / B < B ^ k := by
        rw [Nat.div_lt_iff_lt_mul hB]; rwa [pow_succ] at hn
      have hrest : ∑ j ∈ range k, (n / B ^ (j + 1) % B) * B ^ (j + 1) = B * (n / B) := by
        rw [← ih (n / B) hdiv, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        rw [pow_succ, ← Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, mul_comm (B ^ j) B,
          ← Nat.div_div_eq_div_mul]
        ring
      rw [hrest]
      simp only [pow_zero, Nat.div_one, mul_one]
      have := Nat.div_add_mod n B
      omega

theorem weight_pow (B : Nat) :
    (∑ d : WinternitzDigit, B ^ d.val) ^ chainCount = ∑ x : Encoding, B ^ (sum x) := by
  have hcard : (Finset.univ : Finset ChainIndex).card = chainCount := by
    simp [Finset.card_univ]
  have h1 : (∑ d : WinternitzDigit, B ^ d.val) ^ chainCount
      = ∏ _i : ChainIndex, ∑ d : WinternitzDigit, B ^ d.val := by
    rw [Finset.prod_const, hcard]
  rw [h1, Finset.prod_univ_sum, Fintype.piFinset_univ]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.prod_pow_eq_pow_sum]
  rfl

/-- The number of digit words of sum `s`. -/
def codeCount (s : Nat) : Nat := (Finset.univ.filter (fun x : Encoding => sum x = s)).card

theorem sum_lt_175 (x : Encoding) : sum x < 175 := by
  have : sum x ≤ ∑ _i : ChainIndex, 3 :=
    Finset.sum_le_sum (fun i _ => Nat.le_of_lt_succ (x i).isLt)
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at this
  have hcard : Fintype.card ChainIndex = 58 := by simp [chainCount]
  rw [hcard] at this
  omega

theorem sum_encoding_pow (B : Nat) :
    ∑ x : Encoding, B ^ (sum x) = ∑ s ∈ range 175, codeCount s * B ^ s := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := sum) (t := range 175)
    (fun x _ => Finset.mem_range.mpr (sum_lt_175 x)) (fun x => B ^ (sum x))]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.sum_congr rfl (fun x hx => by rw [(Finset.mem_filter.mp hx).2]),
    Finset.sum_const, codeCount, smul_eq_mul]

theorem codeCount_lt_base (s : Nat) : codeCount s < base := by
  have h : codeCount s ≤ Fintype.card Encoding := Finset.card_filter_le _ _
  have hcard : Fintype.card Encoding = 4 ^ 58 := by
    simp [chainCount, chainLength, winternitzBits]
  rw [hcard] at h
  exact Nat.lt_of_le_of_lt h (by decide)

theorem weight_eq : (∑ d : WinternitzDigit, base ^ d.val) = (base ^ 4 - 1) / (base - 1) := by decide

theorem codeCount_target_eq_digit :
    codeCount targetSum = (∑ d : WinternitzDigit, base ^ d.val) ^ chainCount / base ^ targetSum %
        base := by
  rw [weight_pow, sum_encoding_pow]
  exact (digit_of_sum base (by decide) codeCount codeCount_lt_base 175 targetSum (by decide)).symm

/-- `[z^106](1 + z + z^2 + z^3)^58`. -/
theorem codeCount_target : codeCount targetSum = 323504418562481994618807509487594 := by
  rw [codeCount_target_eq_digit, weight_eq]
  decide

/-! ### Codewords are digit words -/

/-- The value of digit `j` of a word, `0` past `v`. -/
def wordDigit (x : Encoding) (j : Nat) : Nat :=
  if h : j < chainCount then (x ⟨j, h⟩).val else 0

theorem wordDigit_lt (x : Encoding) (j : Nat) : wordDigit x j < 4 := by
  unfold wordDigit
  split
  · exact (x _).isLt
  · decide

/-- `Σ_j x_j 4^j`. -/
def packNat (x : Encoding) : Nat := ∑ j ∈ range chainCount, wordDigit x j * 4 ^ j

theorem packNat_lt (x : Encoding) : packNat x < 2 ^ 116 := by
  have hlt : ∀ n, ∑ j ∈ range n, wordDigit x j * 4 ^ j < 4 ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Finset.sum_range_succ, pow_succ]
        have h3 : wordDigit x n * 4 ^ n ≤ 3 * 4 ^ n :=
          Nat.mul_le_mul_right _ (by have := wordDigit_lt x n; omega)
        omega
  have := hlt chainCount
  simpa [packNat, chainCount, show (4 : Nat) ^ 58 = 2 ^ 116 by norm_num] using this

/-- The digest of a word. -/
def pack (x : Encoding) : Digest := BitVec.ofNat digestBits (packNat x)

theorem toNat_pack (x : Encoding) : (pack x).toNat = packNat x := by
  rw [pack, BitVec.toNat_ofNat, digestBits,
    Nat.mod_eq_of_lt (lt_trans (packNat_lt x) (by norm_num))]

theorem digit_val {n : Nat} (d : Digest) (i : Fin n) :
    (digestDigits d i).val = d.toNat / 4 ^ i.val % 4 := by
  simp [digestDigits, BitVec.extractLsb', winternitzBits, Nat.shiftRight_eq_div_pow, pow_mul]

theorem encoding_pack (x : Encoding) : (digestDigits (pack x) : Encoding) = x := by
  funext i
  apply Fin.ext
  rw [digit_val, toNat_pack, packNat,
    digit_of_sum 4 (by decide) (wordDigit x) (wordDigit_lt x) chainCount i.val i.isLt,
    wordDigit, dite_eq_left i.isLt]

theorem valid_pack {x : Encoding} (hx : sum x = targetSum) : Valid (pack x) := by
  refine ⟨?_, by rw [encoding_pack]; exact hx⟩
  rw [toNat_pack]
  exact Nat.div_eq_of_lt (by simpa [winternitzBits, chainCount] using packNat_lt x)

/-- A codeword is the digest of its digits. -/
theorem pack_encoding {d : Digest} (hd : Valid d) : pack (digestDigits d) = d := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_pack]
  have hlt : d.toNat < 4 ^ chainCount := by
    have h0 := hd.1
    simp only [winternitzBits, chainCount] at h0
    have := (Nat.div_eq_zero_iff_lt (by positivity)).mp h0
    simpa [chainCount, show (4 : Nat) ^ 58 = 2 ^ 116 by norm_num] using this
  rw [← sum_digits_eq 4 (by decide) chainCount d.toNat hlt, packNat]
  apply Finset.sum_congr rfl
  intro j hj
  rw [wordDigit, dite_eq_left (Finset.mem_range.mp hj), digit_val]

/-- Two codewords with the same digits are the same digest. -/
theorem eq_of_encoding_eq {d d' : Digest} (hd : Valid d) (hd' : Valid d')
    (h : (digestDigits d : Encoding) = digestDigits d') : d = d' := by
  rw [← pack_encoding hd, ← pack_encoding hd', h]

end LeanXmss.Codeword
