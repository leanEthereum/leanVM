/-
  LeanVM.Guest.Value.Bits

  Bits, counts and logs as the guest certifies them: bit decompositions pinned by booleanity and
  reconstruction, products of g-powers, the injectivity of `g`'s powers, the range check in the
  exponent, and `log2Ceil` certified by its two bounds.
-/

module

public import LeanVM.Guest.Value.Tower
public import LeanVM.Parameters.Generator
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Bits, counts and logs

A count `n` is the g-power `gen ^ n` (TRIAGE's convention; `Spec/Verifier.lean`'s `gpow`), an
integer word its bit pattern `eOfNat n`. The guest moves between the two with hinted bits
(`hint_decompose_bits`, `hint_decompose_bits_exponent`, `zkDSL.md` §Hints), which it pins by
booleanity (`b * b == b`, or the write-once `bits[i] = b * b`) and a reconstruction:

* `sum_bitE_coordBasis` and `bits_of_reconstruct`: booleanity and `Σ b_i · COORD_BASIS[s + i] = x`
  make the `b_i` the bits of `x` from bit `s` on, and `x` zero elsewhere (`decode_query_bits`,
  G:654-698; `grind_check`, G:723-730; `scaled_log`, G:2706-2723; the start offset of G:2555);
* `prod_bitE_gen_pow`: `Π (1 + b_j·(g^(2^j) + 1))` is `g` to the bits' integer
  (`g_power_of_word`, G:590-603; `verify_log2_ceil`, G:606-640; `column_selector`, G:2002-2017),
  and `gen_pow_inj` (the order of `g`, `Parameters.Generator`) makes that integer the exponent
  (`bits_of_exponent`, for `hint_decompose_bits_exponent`); together, `g_power_of_word_spec`
  and `scaled_log_spec` (G:2706-2723);
* `rangeCheck_sound`: the ISA's range check in the exponent (`zkDSL.md` §Range checks) means
  `x = g^e` with `e < k` (`LogLt`), and `gen_pow_div_eq` reads a range-checked quotient
  `log(a / b) < k` as `a = b + c`;
* `log2Ceil_certified` and `verify_log2_ceil_sound`: `verify_log2_ceil`'s two bounds
  (G:606-640) pin its hinted log to `max floor (log2Ceil W)` (`Spec/Verifier.lean:695`).
-/

namespace LeanVM.Guest.Value

open LeanVM.Parameters LeanVM.Protocol.Verifier

@[expose] public section

/-! ## Bits as integers -/

/-- The integer of the bits `f 0, …, f (n - 1)`, least significant first. -/
def bitsVal (f : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | n + 1 => bitsVal f n + 2 ^ n * (f n).toNat

theorem bitsVal_lt (f : ℕ → Bool) (n : ℕ) : bitsVal f n < 2 ^ n := by
  induction n with
  | zero => simp [bitsVal]
  | succ n ih =>
    rw [bitsVal, pow_succ]
    have : (f n).toNat ≤ 1 := Bool.toNat_le _
    have : 2 ^ n * (f n).toNat ≤ 2 ^ n := by nlinarith
    omega

theorem testBit_bitsVal (f : ℕ → Bool) (n i : ℕ) :
    (bitsVal f n).testBit i = (decide (i < n) && f i) := by
  induction n with
  | zero => simp [bitsVal]
  | succ n ih =>
    rw [bitsVal, Nat.add_comm, Nat.testBit_two_pow_mul_add _ (bitsVal_lt f n), ih]
    by_cases h : i < n
    · simp [h, show i < n + 1 by omega]
    · by_cases h' : i = n
      · subst h'
        cases f i <;> simp
      · have hlt : 1 < 2 ^ (i - n) := Nat.one_lt_two_pow (by omega)
        cases hf : f n <;> simp [h, show ¬ i < n + 1 by omega, Nat.testBit_lt_two_pow hlt]

/-- The low `j` bits of the integer of `n ≥ j` bits are the integer of the first `j`. -/
theorem bitsVal_mod (f : ℕ → Bool) {n j : ℕ} (h : j ≤ n) : bitsVal f n % 2 ^ j = bitsVal f j := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_mod_two_pow, testBit_bitsVal, testBit_bitsVal]
  by_cases hi : i < j
  · simp [hi, show i < n by omega]
  · simp [hi]

/-- The integer of a number's own bits. -/
theorem bitsVal_testBit {N n : ℕ} (hN : N < 2 ^ n) : bitsVal N.testBit n = N := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_bitsVal]
  by_cases hi : i < n
  · simp [hi]
  · simp [hi, Nat.testBit_lt_two_pow (lt_of_lt_of_le hN (Nat.pow_le_pow_right (by decide)
      (Nat.le_of_not_lt hi)))]

/-- Bits that agree below `n` have the same integer. -/
theorem bitsVal_congr {f f' : ℕ → Bool} {n : ℕ} (h : ∀ i < n, f i = f' i) :
    bitsVal f n = bitsVal f' n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [bitsVal, bitsVal, ih fun i hi ↦ h i (by omega), h n (by omega)]

/-! ## Field bits -/

/-- A bit as a field element, `0` or `1`. -/
def bitE (b : Bool) : E := if b then 1 else 0

/-- **Booleanity**: `b · b = b` makes `b` a bit. -/
theorem bitE_of_mul_self {b : E} (h : b * b = b) : b = bitE (decide (b = 1)) := by
  have h' : b * (b - 1) = 0 := by rw [mul_sub, h, mul_one, sub_self]
  rcases mul_eq_zero.mp h' with h0 | h1
  · subst h0
    simp [bitE]
  · have : b = 1 := sub_eq_zero.mp h1
    simp [bitE, this]

theorem bitE_mul_self (c : Bool) : bitE c * bitE c = bitE c := by cases c <;> simp [bitE]

theorem bitE_injective : Function.Injective bitE := by
  intro a b h
  cases a <;> cases b <;> simp_all [bitE]

/-- A bit times the coordinate basis vector `i` is the bit pattern `2^i` or zero. -/
theorem bitE_mul_coordBasis (c : Bool) (i : ℕ) :
    bitE c * coordBasis i = eOfNat192 (2 ^ i * c.toNat) := by
  cases c
  · simp [bitE, eOfNat192_zero]
  · simp [bitE, coordBasis]

/-- **A bit run reconstructed** over the coordinate basis from position `s`: the bit pattern of
`2^s` times the bits' integer. -/
theorem sum_bitE_coordBasis (f : ℕ → Bool) (s n : ℕ) :
    ∑ i ∈ Finset.range n, bitE (f i) * coordBasis (s + i) = eOfNat192 (2 ^ s * bitsVal f n) := by
  induction n with
  | zero => simp [bitsVal, eOfNat192_zero]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, bitE_mul_coordBasis, ← eOfNat192_xor, bitsVal, Nat.mul_add,
      ← Nat.mul_assoc, ← Nat.pow_add, Nat.xor_comm, two_pow_mul_xor, Nat.add_comm]
    rw [Nat.pow_add]
    exact Nat.mul_lt_mul_of_pos_left (bitsVal_lt f n) (Nat.two_pow_pos s)

/-- **Booleanity and reconstruction give the bits of a word** (`hint_decompose_bits(bits, x, n,
s)` and the checks after it): if every `b_i` satisfies `b_i · b_i = b_i` and
`Σ_{i < n} b_i · COORD_BASIS[s + i] = x` with `s + n ≤ 192`, then `x` is `2^s` times an integer
`N < 2^n` and `b_i` is bit `i` of `N`. -/
theorem bits_of_reconstruct {s n : ℕ} {b : ℕ → E} (hb : ∀ i < n, b i * b i = b i) {x : E}
    (hx : ∑ i ∈ Finset.range n, b i * coordBasis (s + i) = x) :
    ∃ N < 2 ^ n, x = eOfNat192 (2 ^ s * N) ∧ ∀ i < n, b i = bitE (N.testBit i) := by
  let f : ℕ → Bool := fun i ↦ decide (b i = 1)
  have hbf : ∀ i < n, b i = bitE (f i) := fun i hi ↦ bitE_of_mul_self (hb i hi)
  have hsum : ∑ i ∈ Finset.range n, b i * coordBasis (s + i) =
      ∑ i ∈ Finset.range n, bitE (f i) * coordBasis (s + i) :=
    Finset.sum_congr rfl fun i hi ↦ by rw [hbf i (Finset.mem_range.mp hi)]
  refine ⟨bitsVal f n, bitsVal_lt f n, ?_, fun i hi ↦ ?_⟩
  · rw [← hx, hsum, sum_bitE_coordBasis]
  · rw [hbf i hi, testBit_bitsVal]
    simp [hi]

/-- The same, read off the word (`s = 0`, `n ≤ 192`): `x`'s integer is below `2^n` and `b_i` is
its bit `i`. -/
theorem bits_of_reconstruct_zero {n : ℕ} (hn : n ≤ 192) {b : ℕ → E}
    (hb : ∀ i < n, b i * b i = b i) {x : E}
    (hx : ∑ i ∈ Finset.range n, b i * coordBasis i = x) :
    eToNat x < 2 ^ n ∧ ∀ i < n, b i = bitE ((eToNat x).testBit i) := by
  obtain ⟨N, hN, rfl, hbits⟩ := bits_of_reconstruct (s := 0) hb (by simpa using hx)
  have hN' : N < 2 ^ 192 := lt_of_lt_of_le hN (Nat.pow_le_pow_right (by decide) hn)
  rw [Nat.pow_zero, Nat.one_mul, eToNat_eOfNat192, Nat.mod_eq_of_lt hN']
  exact ⟨hN, hbits⟩

/-- **Completeness**: the bits of an integer below `2^n` are Boolean and reconstruct it. -/
theorem reconstruct_bits (s : ℕ) {N n : ℕ} (hN : N < 2 ^ n) :
    ∑ i ∈ Finset.range n, bitE (N.testBit i) * coordBasis (s + i) = eOfNat192 (2 ^ s * N) := by
  rw [sum_bitE_coordBasis, bitsVal_testBit hN]

/-! ## Products of g-powers -/

theorem e_add_self (a : E) : a + a = 0 := CharTwo.add_self_eq_zero a

/-- **The exponent of a bit run** (`g_power_of_word`, `verify_log2_ceil`, `column_selector`,
`scaled_log`): `Π_{j < n} (1 + b_j·(g^(2^j) + 1))` over bits is `g` to their integer. -/
theorem prod_bitE_gen_pow (f : ℕ → Bool) (n : ℕ) :
    ∏ j ∈ Finset.range n, (1 + bitE (f j) * (gen ^ 2 ^ j + 1)) = gen ^ bitsVal f n := by
  induction n with
  | zero => simp [bitsVal]
  | succ n ih =>
    rw [Finset.prod_range_succ, ih, bitsVal, pow_add, pow_mul]
    cases f n
    · simp [bitE]
    · simp only [bitE, ↓reduceIte, one_mul, Bool.toNat_true, pow_one]
      rw [add_comm, add_assoc, e_add_self, add_zero]

/-- The same over hinted bits pinned by booleanity. -/
theorem prod_gen_pow_of_bool {n : ℕ} {b : ℕ → E} (hb : ∀ j < n, b j * b j = b j) :
    ∏ j ∈ Finset.range n, (1 + b j * (gen ^ 2 ^ j + 1)) =
      gen ^ bitsVal (fun j ↦ decide (b j = 1)) n := by
  rw [← prod_bitE_gen_pow]
  exact Finset.prod_congr rfl fun j hj ↦ by
    rw [← bitE_of_mul_self (hb j (Finset.mem_range.mp hj))]

/-! ## Powers of `g` -/

theorem gen_eq_ofK : gen = ofK g := rfl

theorem gen_pow_eq_ofK (a : ℕ) : gen ^ a = ofK (Parameters.gpow a) := by
  rw [gen_eq_ofK, ← ofK_pow]

theorem gen_ne_zero : gen ≠ 0 := by
  rw [gen_eq_ofK, ← ofK_zero]
  exact fun h ↦ g_ne_zero (ofK_injective h)

theorem gen_pow_ne_zero (a : ℕ) : gen ^ a ≠ 0 := pow_ne_zero a gen_ne_zero

/-- **Distinct exponents below the order of `g` give distinct powers** (`orderOf_g`). -/
theorem gen_pow_inj {a b : ℕ} (ha : a < 2 ^ 64 - 1) (hb : b < 2 ^ 64 - 1)
    (h : gen ^ a = gen ^ b) : a = b := by
  rw [gen_pow_eq_ofK, gen_pow_eq_ofK] at h
  exact gpow_injOn ha hb (ofK_injective h)

theorem gen_pow_eq_one_iff {a : ℕ} (ha : a < 2 ^ 64 - 1) : gen ^ a = 1 ↔ a = 0 := by
  constructor
  · intro h
    exact gen_pow_inj ha (by decide) (h.trans (pow_zero gen).symm)
  · rintro rfl
    exact pow_zero gen

/-- **A range-checked quotient** (`assert log(a / b) < k`): if `g^a / g^b = g^c` with all three
exponents below `2^63`, then `a = b + c`, so `b ≤ a` (G:628, G:1513, G:1985, G:2115). -/
theorem gen_pow_div_eq {a b c : ℕ} (ha : a < 2 ^ 63) (hb : b < 2 ^ 63) (hc : c < 2 ^ 63)
    (h : gen ^ a / gen ^ b = gen ^ c) : a = b + c := by
  have : gen ^ a = gen ^ (b + c) := by
    rw [pow_add, ← h, mul_div_cancel₀ _ (gen_pow_ne_zero b)]
  exact gen_pow_inj (by omega) (by omega) this

/-- **Bits pinned in the exponent** (`hint_decompose_bits_exponent(bits, x, n)` and the checks
after it, `scaled_log`, G:2706-2723, `column_selector`, G:2002-2017,
`log2_ceil_in_the_exponent`, G:643-651): Boolean `b_j` whose product
`Π_{j < n} (1 + b_j·(g^(2^j) + 1))` is `x = g^N`, with `n ≤ 63` and `N` below the order of `g`,
are the bits of `N`, and `N < 2^n`. -/
theorem bits_of_exponent {n N : ℕ} (hn : n ≤ 63) (hN : N < 2 ^ 64 - 1) {b : ℕ → E}
    (hb : ∀ j < n, b j * b j = b j)
    (hx : ∏ j ∈ Finset.range n, (1 + b j * (gen ^ 2 ^ j + 1)) = gen ^ N) :
    N < 2 ^ n ∧ ∀ j < n, b j = bitE (N.testBit j) := by
  rw [prod_gen_pow_of_bool hb] at hx
  have hlt := bitsVal_lt (fun j ↦ decide (b j = 1)) n
  have h2n : 2 ^ n ≤ 2 ^ 63 := Nat.pow_le_pow_right (by decide) hn
  have hv := gen_pow_inj (by omega) hN hx
  subst hv
  refine ⟨hlt, fun j hj ↦ ?_⟩
  rw [bitE_of_mul_self (hb j hj), testBit_bitsVal]
  simp [hj]

/-- **`g_power_of_word(value, g_squares, n)`** (G:590-603; TRIAGE #14): Boolean bits with
`Σ_{j < n} b_j · E(2^j) = value`, `n ≤ 63`, make `value` a word in `K` below `2^n`, and the
product over `g_squares` (`Tables.squares_eq`) its g-power, `gpow (kToNat value.limb0)`. -/
theorem g_power_of_word_spec {n : ℕ} (hn : n ≤ 63) {b : ℕ → E} (hb : ∀ j < n, b j * b j = b j)
    {value : E} (hword : ∑ j ∈ Finset.range n, b j * eOfNat (2 ^ j) = value) :
    IsInK value ∧ kToNat (value.limb 0) < 2 ^ n ∧
      ∏ j ∈ Finset.range n, (1 + b j * (gen ^ 2 ^ j + 1)) = gen ^ kToNat (value.limb 0) := by
  have hsum : ∑ j ∈ Finset.range n, b j * coordBasis (0 + j) = value := by
    rw [← hword]
    exact Finset.sum_congr rfl fun j hj ↦ by
      rw [Nat.zero_add, coordBasis_of_lt (by have := Finset.mem_range.mp hj; omega)]
  obtain ⟨N, hN, hv, hbits⟩ := bits_of_reconstruct hb hsum
  have hN64 : N < 2 ^ 64 := lt_of_lt_of_le hN (Nat.pow_le_pow_right (by decide) (by omega))
  rw [Nat.pow_zero, Nat.one_mul, eOfNat192_of_lt hN64] at hv
  subst hv
  have hk : kToNat ((eOfNat N).limb 0) = N := by
    rw [eOfNat_eq_ofLimbs, ofLimbs_limb0, kToNat_ofBits, Nat.mod_eq_of_lt hN64]
  rw [hk, prod_gen_pow_of_bool hb]
  refine ⟨eOfNat_isInK N, hN, ?_⟩
  rw [bitsVal_congr (f' := N.testBit) fun j hj ↦ ?_, bitsVal_testBit hN]
  rw [hbits j hj]
  cases N.testBit j <;> simp [bitE]

/-- **`scaled_log(x, g_squares, shift)`** (G:2706-2723; TRIAGE #59): Boolean bits whose g-power
product is `x = g^N`, `N` below the order of `g`, weigh to `E(N)`, and the final product by
`COORD_BASIS[shift]` is `E(2^shift · N)` when it does not reduce. -/
theorem scaled_log_spec {n N shift : ℕ} (hn : n ≤ 63) (hN : N < 2 ^ 64 - 1) (hs : shift < 64)
    (hfit : 2 ^ shift * 2 ^ n ≤ 2 ^ 64) {b : ℕ → E} (hb : ∀ j < n, b j * b j = b j)
    (hx : ∏ j ∈ Finset.range n, (1 + b j * (gen ^ 2 ^ j + 1)) = gen ^ N) :
    N < 2 ^ n ∧
      (∑ j ∈ Finset.range n, b j * coordBasis j) * coordBasis shift = eOfNat (2 ^ shift * N) := by
  obtain ⟨hNn, hbits⟩ := bits_of_exponent hn hN hb hx
  refine ⟨hNn, ?_⟩
  have hsum : ∑ j ∈ Finset.range n, b j * coordBasis j =
      ∑ j ∈ Finset.range n, bitE (N.testBit j) * coordBasis (0 + j) :=
    Finset.sum_congr rfl fun j hj ↦ by rw [hbits j (Finset.mem_range.mp hj), Nat.zero_add]
  have hfit' : 2 ^ shift * N < 2 ^ 64 :=
    lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_left hNn (Nat.two_pow_pos shift)) hfit
  have hNlt : N < 2 ^ 64 := lt_of_le_of_lt (Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)) hfit'
  rw [hsum, reconstruct_bits 0 hNn, Nat.pow_zero, Nat.one_mul, eOfNat192_of_lt hNlt, mul_comm,
    coordBasis_of_lt hs, eOfNat_two_pow_mul hfit']

/-! ## The range check in the exponent -/

/-- `assert log(x) < k` (`zkDSL.md` §Range checks): `x` is `g^e` with `e < k`. -/
def LogLt (x : E) (k : ℕ) : Prop := ∃ e < k, x = gen ^ e

/-- **The range check in the exponent is sound** (`zkDSL.md` §Range checks): the gadget's two
`DEREF`s make `x` and the back-solved complement `z` addresses `g^e`, `g^e'` of a memory of at
most `2^32` words (`Spec/Isa.lean`, `MemImage.read`), and its `MUL` pins `x·z = g^(k-1)`; for
`1 ≤ k ≤ 2^32` that is `e < k`. -/
theorem rangeCheck_sound {e e' k : ℕ} (he : e < 2 ^ 32) (he' : e' < 2 ^ 32) (hk : 1 ≤ k)
    (hk' : k ≤ 2 ^ 32) (h : Parameters.gpow e * Parameters.gpow e' = Parameters.gpow (k - 1)) :
    e < k := by
  have : Parameters.gpow (e + e') = Parameters.gpow (k - 1) := by
    rw [← h, Parameters.gpow, Parameters.gpow, pow_add]
  have := gpow_injOn (show e + e' ∈ Set.Iio (2 ^ 64 - 1) by simp only [Set.mem_Iio]; omega)
    (show k - 1 ∈ Set.Iio (2 ^ 64 - 1) by simp only [Set.mem_Iio]; omega) this
  omega

/-- **The range check is complete**: for `e < k` the complement `g^(k-1-e)` balances it. -/
theorem rangeCheck_complete {e k : ℕ} (h : e < k) :
    Parameters.gpow e * Parameters.gpow (k - 1 - e) = Parameters.gpow (k - 1) := by
  rw [Parameters.gpow, Parameters.gpow, Parameters.gpow, ← pow_add]
  congr 1
  omega

/-- The range check, as a cell in `K`: `x = ofK (g^e)` with `e < k`. -/
theorem logLt_of_rangeCheck {x : E} {e e' k : ℕ} (hx : x = ofK (Parameters.gpow e))
    (he : e < 2 ^ 32) (he' : e' < 2 ^ 32) (hk : 1 ≤ k) (hk' : k ≤ 2 ^ 32)
    (h : Parameters.gpow e * Parameters.gpow e' = Parameters.gpow (k - 1)) : LogLt x k :=
  ⟨e, rangeCheck_sound he he' hk hk' h, by rw [hx, gen_pow_eq_ofK]⟩

/-! ## `log2Ceil`, certified by its two bounds (`verify_log2_ceil`, G:606-640) -/

theorem log2Ceil_le_iff {W L : ℕ} : log2Ceil W ≤ L ↔ W ≤ 2 ^ L := by
  unfold log2Ceil bitLength
  by_cases h : W - 1 = 0
  · simp only [h, ↓reduceIte, Nat.zero_le, true_iff]
    have := Nat.one_le_two_pow (n := L)
    omega
  · simp only [h, ↓reduceIte]
    rw [Nat.add_one_le_iff, Nat.log2_lt h]
    omega

theorem lt_log2Ceil_iff {W L : ℕ} : L < log2Ceil W ↔ 2 ^ L < W := by
  rw [← not_le, log2Ceil_le_iff, not_le]

/-- **`log2Ceil` certified**: `L ≥ floor` with `W ≤ 2^L`, and `2^(L-1) < W` unless `L` is the
floor, is `max floor (log2Ceil W)` (`verifier.py:247-248`, floored). -/
theorem log2Ceil_certified {W L floor : ℕ} (hfl : floor ≤ L) (hW : W ≤ 2 ^ L)
    (hmin : L ≠ floor → 2 ^ (L - 1) < W) : L = max floor (log2Ceil W) := by
  have hle := log2Ceil_le_iff.mpr hW
  by_cases hL : L = floor
  · subst hL
    omega
  · have hlt := lt_log2Ceil_iff.mpr (hmin hL)
    omega

/-- The value of bits `[L, 64)`, `E(W mod 2^L) + E(W)`, vanishes exactly when `W < 2^L`. -/
theorem high_eq_zero_iff {W L : ℕ} (hW : W < 2 ^ 64) :
    eOfNat (W % 2 ^ L) + eOfNat W = 0 ↔ W < 2 ^ L := by
  rw [eOfNat_add_eq_zero_iff (lt_of_le_of_lt (Nat.mod_le _ _) hW) hW]
  constructor
  · intro h
    rw [← h]
    exact Nat.mod_lt _ (Nat.two_pow_pos L)
  · exact Nat.mod_eq_of_lt

/-- **`verify_log2_ceil` is sound** (G:606-640): with `W = Σ b_j 2^j` below `2^64` and the hinted
log `L < 64` range-checked above `floor` (G:627-628), the guest's two products
`high · low = 0` and `high · (W + 2^L) = 0` (G:631-632), and, unless `L` is the floor (or zero),
`(low' + W)·(W + 2^(L-1)) ≠ 0` (G:633-639), pin `L` to `max floor (log2Ceil W)`. Here
`low = E(W mod 2^L)` and `low' = E(W mod 2^(L-1))` are the guest's prefix sums `psum_buf[g^L]`,
`psum_buf[g^(L-1)]` (`bitsVal_mod`), and `high = low + E(W)`. -/
theorem verify_log2_ceil_sound {W L floor : ℕ} (hW : W < 2 ^ 64) (hL : L < 64) (hfl : floor ≤ L)
    (h2 : (eOfNat (W % 2 ^ L) + eOfNat W) * (eOfNat W + eOfNat (2 ^ L)) = 0)
    (h3 : L ≠ floor → L ≠ 0 →
      (eOfNat (W % 2 ^ (L - 1)) + eOfNat W) * (eOfNat W + eOfNat (2 ^ (L - 1))) ≠ 0) :
    L = max floor (log2Ceil W) := by
  have hpow : ∀ j, j < 64 → 2 ^ j < 2 ^ 64 := fun j hj ↦ Nat.pow_lt_pow_right (by decide) hj
  refine log2Ceil_certified hfl ?_ ?_
  · rcases mul_eq_zero.mp h2 with h | h
    · exact le_of_lt ((high_eq_zero_iff hW).mp h)
    · exact le_of_eq ((eOfNat_add_eq_zero_iff hW (hpow L hL)).mp h)
  · intro hne
    have hne0 : L ≠ 0 := by omega
    have h3 := h3 hne hne0
    have ha : eOfNat (W % 2 ^ (L - 1)) + eOfNat W ≠ 0 := left_ne_zero_of_mul h3
    have hb : eOfNat W + eOfNat (2 ^ (L - 1)) ≠ 0 := right_ne_zero_of_mul h3
    rw [Ne, high_eq_zero_iff hW] at ha
    rw [Ne, eOfNat_add_eq_zero_iff hW (hpow (L - 1) (by omega))] at hb
    omega

/-- **`verify_log2_ceil` is complete**: the honest `L = max floor (log2Ceil W)` satisfies the
products the guest asserts. -/
theorem verify_log2_ceil_complete {W floor : ℕ} (hW : W < 2 ^ 64)
    (hL : max floor (log2Ceil W) < 64) :
    let L := max floor (log2Ceil W)
    (eOfNat (W % 2 ^ L) + eOfNat W) * eOfNat (W % 2 ^ L) = 0 ∧
      (eOfNat (W % 2 ^ L) + eOfNat W) * (eOfNat W + eOfNat (2 ^ L)) = 0 ∧
      (L ≠ floor → L ≠ 0 →
        (eOfNat (W % 2 ^ (L - 1)) + eOfNat W) * (eOfNat W + eOfNat (2 ^ (L - 1))) ≠ 0) := by
  intro L
  have hpow : ∀ j, j < 64 → 2 ^ j < 2 ^ 64 := fun j hj ↦ Nat.pow_lt_pow_right (by decide) hj
  have hle : W ≤ 2 ^ L := log2Ceil_le_iff.mp (le_max_right _ _)
  have hboth : (eOfNat (W % 2 ^ L) + eOfNat W) * eOfNat (W % 2 ^ L) = 0 ∧
      (eOfNat (W % 2 ^ L) + eOfNat W) * (eOfNat W + eOfNat (2 ^ L)) = 0 := by
    rcases lt_or_eq_of_le hle with h | h
    · rw [(high_eq_zero_iff hW).mpr h, zero_mul, zero_mul]
      exact ⟨rfl, rfl⟩
    · rw [h, Nat.mod_self, eOfNat_zero, mul_zero, (eOfNat_add_eq_zero_iff (hpow L hL)
        (hpow L hL)).mpr rfl, mul_zero]
      exact ⟨rfl, rfl⟩
  refine ⟨hboth.1, hboth.2, fun hne hne0 ↦ ?_⟩
  have hlog : L = log2Ceil W := by
    rcases le_total floor (log2Ceil W) with h | h
    · exact max_eq_right h
    · exact absurd (max_eq_left h) hne
  have hgt : 2 ^ (L - 1) < W := lt_log2Ceil_iff.mp (by omega)
  refine mul_ne_zero ?_ ?_
  · rw [Ne, high_eq_zero_iff hW]
    omega
  · rw [Ne, eOfNat_add_eq_zero_iff hW (hpow (L - 1) (by omega))]
    omega

end
end LeanVM.Guest.Value
