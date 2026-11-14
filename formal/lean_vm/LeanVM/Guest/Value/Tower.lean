/-
  LeanVM.Guest.Value.Tower

  The tower `E = K[y]/(y² + x·y + 1)` as the aggregation guest reads it: `y` and `y⁻¹`, packing two
  limbs into a cell and splitting a word into its limbs, integers as bit patterns, and products by
  powers of `x` that do not reduce.
-/

module

public import LeanVM.Parameters.Field
public import LeanVM.Guest.Value.FieldBits
public import Statement.LeanVmVerifier
public import Statement.Fast.Keccak
public import Statement.Fast.QuadExt
public import Statement.Fast.FieldWords
import CompPoly.Fields.Binary.BF64.Impl

/-!
# The tower, as the guest reads it

A word is one memory cell of two `K` limbs, `c0 + c1·y`. The guest
(`crates/rec_aggregation/guests/lean_ethereum.py`, G below) never reads a limb directly: it hints
the low one, derives the high one by `y⁻¹` and proves both lie in `K` with `assert_in_k` (one
untaken `JUMP` whose operands must be in `K`). The representation `c0 + c1·y` is unique, so those
constraints pin the hint, for every word:

* `pack64x2` is `E.ofLimbs a b` (`pack64x2_eq`);
* `split_limbs` splits a word as `lo + y·hi` (`split_iff`, `split_hi`), and `grind_check` the
  word less its rebuilt low limb.

The guest's constants are `Y_TOWER = y` and `Y_INV = y⁻¹ = x + y` (`y_inv`; `placeholder_map`,
`crates/rec_aggregation/src/aggregation/placeholders.rs`). A zkDSL integer literal is a bit
pattern: `n < 2^64` is `E::new(n, 0)`, `eOfNat n`, and a wider one, up to `u128`, is
`eOfNat128 n`. `COORD_BASIS[i]` (`placeholder_map`) is `eOfNat128 (2^i)`. Sums of integers are XORs
(`eOfNat_xor`), so they add when their bits are disjoint (`two_pow_mul_xor`); and the product of
`x^s` with a word of degree below `64 - s` does not reduce (`ofBits_two_pow_mul`).
-/

namespace LeanVM.Guest.Value

open LeanVM.Parameters LeanVM.Protocol.Verifier

@[expose] public section

/-! ## Characteristic two -/

/-- In `K`, `a + b = 0` exactly when `a = b`. -/
theorem k_add_eq_zero_iff {a b : K} : a + b = 0 ↔ a = b := by
  rw [add_eq_zero_iff_eq_neg, CharTwo.neg_eq]

/-- `2 = 0` in `K`. -/
theorem k_two : (2 : K) = 0 := CharTwo.two_eq_zero

/-- In `K`, `a + a = 0`. -/
theorem k_add_self (a : K) : a + a = 0 := CharTwo.add_self_eq_zero a

/-! ## `ofK` and the limb view -/

theorem ofK_zero : ofK 0 = 0 := map_zero (algebraMap K E)

theorem ofK_one : ofK 1 = 1 := map_one (algebraMap K E)

theorem ofK_pow (a : K) (n : ℕ) : ofK (a ^ n) = ofK a ^ n := map_pow (algebraMap K E) a n

@[simp] theorem ofLimbs_limb0 (a b : K) : (E.ofLimbs a b).limb 0 = a := by simp

@[simp] theorem ofLimbs_limb1 (a b : K) : (E.ofLimbs a b).limb 1 = b := by simp

theorem zero_eq_ofLimbs : (0 : E) = E.ofLimbs 0 0 := by rw [← ofK_eq_ofLimbs, ofK_zero]

theorem one_eq_ofLimbs : (1 : E) = E.ofLimbs 1 0 := by rw [← ofK_eq_ofLimbs, ofK_one]

/-- A word in limb form. -/
theorem eq_ofLimbs (x : E) : x = E.ofLimbs (x.limb 0) (x.limb 1) := (ofLimbs_limb x).symm

theorem ofLimbs_inj {a b a' b' : K} : E.ofLimbs a b = E.ofLimbs a' b' ↔ a = a' ∧ b = b' := by
  constructor
  · intro h
    exact ⟨by simpa using congrArg (·.limb 0) h, by simpa using congrArg (·.limb 1) h⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem isInK_ofLimbs_iff (a b : K) : IsInK (E.ofLimbs a b) ↔ b = 0 := by
  show (E.ofLimbs a b).limb 1 = 0 ↔ b = 0
  simp

theorem ofK_isInK (a : K) : IsInK (ofK a) := (isInK_iff _).mpr ⟨a, rfl⟩

theorem ofLimbs_add (a0 a1 b0 b1 : K) :
    E.ofLimbs a0 a1 + E.ofLimbs b0 b1 = E.ofLimbs (a0 + b0) (a1 + b1) :=
  add_limbs a0 a1 b0 b1

/-! ## `y` and `y⁻¹` -/

/-- `y` is the limb vector `(0, 1)`. -/
theorem y_eq : y = E.ofLimbs 0 1 := by
  rw [ofLimbs_eq, ofK_zero, ofK_one]
  ring

/-- Multiplying by `y` shifts the limbs and folds `y² = x·y + 1`. -/
theorem ofLimbs_mul_y (a0 a1 : K) : E.ofLimbs a0 a1 * y = E.ofLimbs a1 (a0 + g * a1) := by
  rw [y_eq, mul_limbs, ofLimbs_inj]
  exact ⟨by ring, by ring⟩

/-- `y⁻¹ = x + y`, the limb vector `(g, 1)` (the guest's `Y_INV`). -/
theorem y_inv : y⁻¹ = E.ofLimbs g 1 := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [y_eq, mul_limbs, one_eq_ofLimbs, ofLimbs_inj]
  exact ⟨by ring, by linear_combination g * k_two⟩

/-- Multiplying by `y⁻¹`. -/
theorem ofLimbs_mul_y_inv (a0 a1 : K) :
    E.ofLimbs a0 a1 * y⁻¹ = E.ofLimbs (a0 * g + a1) a0 := by
  rw [y_inv, mul_limbs, ofLimbs_inj]
  exact ⟨by ring, by linear_combination (g * a1) * k_two⟩

/-! ## Packing two limbs (`pack64x2`) -/

/-- **`pack64x2(a, b)`**: after `assert_in_k(a, b)`, `a + y·b` is the cell with limbs `a`, `b`. -/
theorem pack64x2_eq {a b : E} (ha : IsInK a) (hb : IsInK b) :
    a + y * b = E.ofLimbs (a.limb 0) (b.limb 0) := by
  obtain ⟨a0, rfl⟩ := (isInK_iff a).mp ha
  obtain ⟨b0, rfl⟩ := (isInK_iff b).mp hb
  rw [ofK_eq_ofLimbs, ofK_eq_ofLimbs, mul_comm, ofLimbs_mul_y, ofLimbs_add, ofLimbs_inj]
  simp

/-- `a + y·b` for `a`, `b` in `K`: the cell of the two limbs. -/
theorem ofK_add_y_mul_ofK (a b : K) : ofK a + y * ofK b = E.ofLimbs a b := by
  rw [pack64x2_eq (ofK_isInK a) (ofK_isInK b)]
  simp

/-- `y · E(t)`: the word whose `y` limb is `t` (`Y_TOWER * tag`, a rate cell's tag). -/
theorem y_mul_ofK (t : K) : y * ofK t = E.ofLimbs 0 t := by
  rw [← ofK_add_y_mul_ofK, ofK_zero, zero_add]

/-! ## Splitting a word (`split_limbs`) -/

/-- The derived limb `(x + c)·y⁻¹`, in limbs. -/
theorem add_ofK_mul_y_inv (x : E) (c : K) :
    (x + ofK c) * y⁻¹ = E.ofLimbs ((x.limb 0 + c) * g + x.limb 1) (x.limb 0 + c) := by
  rw [eq_ofLimbs x, ofK_eq_ofLimbs, ofLimbs_add, ofLimbs_mul_y_inv]
  simp

/-- **The split of a word** (`split_limbs`; the same constraints in `grind_check`): the hinted
`lo` and the derived `(x + lo)·y⁻¹` both lie in `K` exactly when `lo` is `x`'s low limb: the
representation `c0 + c1·y` is unique. -/
theorem split_iff (x lo : E) : IsInK lo ∧ IsInK ((x + lo) * y⁻¹) ↔ lo = ofK (x.limb 0) := by
  constructor
  · rintro ⟨hlo, hhi⟩
    obtain ⟨c, rfl⟩ := (isInK_iff lo).mp hlo
    rw [add_ofK_mul_y_inv, isInK_ofLimbs_iff] at hhi
    rw [k_add_eq_zero_iff.mp hhi]
  · rintro rfl
    refine ⟨ofK_isInK _, ?_⟩
    rw [add_ofK_mul_y_inv, isInK_ofLimbs_iff]
    exact k_add_self _

/-- The derived high limb is the word's `y` limb. -/
theorem split_hi (x : E) : (x + ofK (x.limb 0)) * y⁻¹ = ofK (x.limb 1) := by
  rw [add_ofK_mul_y_inv, k_add_self, zero_mul, zero_add, ofK_eq_ofLimbs]

/-! ## Integers as bit patterns -/

/-- A `u128` bit pattern: limb `i` holds bits `64·i .. 64·i + 63` of `n` (a zkDSL integer
literal, and `COORD_BASIS[i] = eOfNat128 (2^i)`). -/
def eOfNat128 (n : ℕ) : E := E.ofLimbs (K.ofBits n) (K.ofBits (n / 2 ^ 64))

/-- `COORD_BASIS[i]` (`placeholder_map`): the `i`-th coordinate basis vector. -/
def coordBasis (i : ℕ) : E := eOfNat128 (2 ^ i)

theorem ofBits_xor (a b : ℕ) : K.ofBits (a ^^^ b) = K.ofBits a + K.ofBits b := by
  simp only [K.ofBits, BitVec.ofNat_xor]
  rfl

theorem ofBits_one : K.ofBits 1 = 1 := rfl

theorem ofBits_inj {a b : ℕ} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (h : K.ofBits a = K.ofBits b) :
    a = b := by
  have := congrArg (fun z : K ↦ z.toBitVec.toNat) h
  simp only [K.ofBits, BF64.toBitVec_ofBitVec, BitVec.toNat_ofNat] at this
  rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this

theorem kToNat_ofBits (n : ℕ) : kToNat (K.ofBits n) = n % 2 ^ 64 := by
  simp [kToNat, K.ofBits]

theorem ofBits_kToNat (a : K) : K.ofBits (kToNat a) = a := by
  apply BF64.toBitVec_injective
  simp [K.ofBits, kToNat]

theorem kToNat_lt (a : K) : kToNat a < 2 ^ 64 := a.toBitVec.isLt

theorem eOfNat_eq_ofLimbs (n : ℕ) : eOfNat n = E.ofLimbs (K.ofBits n) 0 := ofK_eq_ofLimbs _

theorem eOfNat_zero : eOfNat 0 = 0 := by rw [eOfNat, ofBits_zero, ofK_zero]

theorem eOfNat_one : eOfNat 1 = 1 := by rw [eOfNat, ofBits_one, ofK_one]

/-- Integer XOR is field addition. -/
theorem eOfNat_xor (a b : ℕ) : eOfNat (a ^^^ b) = eOfNat a + eOfNat b := by
  rw [eOfNat, ofBits_xor, ofK_add]
  rfl

theorem eOfNat_isInK (n : ℕ) : IsInK (eOfNat n) := ofK_isInK _

theorem eOfNat_inj {a b : ℕ} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (h : eOfNat a = eOfNat b) :
    a = b :=
  ofBits_inj ha hb (ofK_injective h)

theorem ofBits_mod (n : ℕ) : K.ofBits (n % 2 ^ 64) = K.ofBits n := by
  apply BF64.toBitVec_injective
  apply BitVec.eq_of_toNat_eq
  simp [K.ofBits]

/-- Two integers below `2^64` add to zero exactly when they are equal. -/
theorem eOfNat_add_eq_zero_iff {a b : ℕ} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    eOfNat a + eOfNat b = 0 ↔ a = b := by
  rw [e_add_eq_zero_iff]
  exact ⟨eOfNat_inj ha hb, fun h ↦ h ▸ rfl⟩

theorem eOfNat128_xor (a b : ℕ) : eOfNat128 (a ^^^ b) = eOfNat128 a + eOfNat128 b := by
  simp only [eOfNat128, Nat.xor_div_two_pow, ofBits_xor, ofLimbs_add]

theorem eOfNat128_of_lt {n : ℕ} (h : n < 2 ^ 64) : eOfNat128 n = eOfNat n := by
  rw [eOfNat128, eOfNat_eq_ofLimbs, Nat.div_eq_of_lt h]
  rfl

theorem eOfNat128_zero : eOfNat128 0 = 0 := by rw [eOfNat128_of_lt (by decide), eOfNat_zero]

/-- `eToNat` reads the bit pattern back, modulo `2^128`. -/
theorem eToNat_eOfNat128 (n : ℕ) : eToNat (eOfNat128 n) = n % 2 ^ 128 := by
  simp only [eToNat, eOfNat128, ofLimbs_limb0, ofLimbs_limb1, kToNat_ofBits]
  have h1 : n % 2 ^ 128 = n % 2 ^ 64 + 2 ^ 64 * (n / 2 ^ 64 % 2 ^ 64) := by
    rw [show (2 : ℕ) ^ 128 = 2 ^ 64 * 2 ^ 64 by norm_num, Nat.mod_mul]
  omega

/-- `eOfNat128` of the integer of a word is the word. -/
theorem eOfNat128_eToNat (x : E) : eOfNat128 (eToNat x) = x := by
  have h0 := kToNat_lt (x.limb 0)
  have h1 := kToNat_lt (x.limb 1)
  have e0 : eToNat x % 2 ^ 64 = kToNat (x.limb 0) := by unfold eToNat; omega
  have e1 : eToNat x / 2 ^ 64 % 2 ^ 64 = kToNat (x.limb 1) := by unfold eToNat; omega
  rw [eOfNat128, ← ofBits_mod (eToNat x), e0, ← ofBits_mod (eToNat x / 2 ^ 64), e1,
    ofBits_kToNat, ofBits_kToNat, ← eq_ofLimbs]

/-- Below the first limb, a coordinate basis vector is `E(2^i)`. -/
theorem coordBasis_of_lt {i : ℕ} (h : i < 64) : coordBasis i = eOfNat (2 ^ i) :=
  eOfNat128_of_lt (Nat.pow_lt_pow_right (by decide) h)

/-- Disjoint bits: a multiple of `2^s` and a value below `2^s` XOR to their sum. -/
theorem two_pow_mul_xor {s q r : ℕ} (hr : r < 2 ^ s) : 2 ^ s * q ^^^ r = 2 ^ s * q + r := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_xor, Nat.testBit_two_pow_mul_add q hr, Nat.testBit_two_pow_mul]
  by_cases hj : j < s
  · have : ¬ s ≤ j := by omega
    simp [hj, this]
  · simp [hj, Nat.testBit_lt_two_pow (lt_of_lt_of_le hr (Nat.pow_le_pow_right (by decide)
      (Nat.le_of_not_lt hj)))]
    omega

/-- Disjoint bits: a multiple of `2^s` and a value below `2^s` OR to their sum. -/
theorem two_pow_mul_or {s q r : ℕ} (hr : r < 2 ^ s) : 2 ^ s * q ||| r = 2 ^ s * q + r := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_or, Nat.testBit_two_pow_mul_add q hr, Nat.testBit_two_pow_mul]
  by_cases hj : j < s
  · have : ¬ s ≤ j := by omega
    simp [hj, this]
  · simp [hj, Nat.testBit_lt_two_pow (lt_of_lt_of_le hr (Nat.pow_le_pow_right (by decide)
      (Nat.le_of_not_lt hj)))]
    omega

/-- The disjoint-bit split (`doc/leanvm` §sec:prog-byte-counter): a multiple of `2^s` plus a
value below `2^s` is their sum. -/
theorem eOfNat_add_of_lt {s q r : ℕ} (hr : r < 2 ^ s) :
    eOfNat (2 ^ s * q) + eOfNat r = eOfNat (2 ^ s * q + r) := by
  rw [← eOfNat_xor, two_pow_mul_xor hr]

/-! ## Products by powers of `x` -/

/-- `E(2^s) · E(v) = E(2^s · v)` without reduction. -/
theorem eOfNat_two_pow_mul {s v : ℕ} (h : 2 ^ s * v < 2 ^ 64) :
    eOfNat (2 ^ s) * eOfNat v = eOfNat (2 ^ s * v) := by
  rw [eOfNat, eOfNat, ← ofK_mul, ofBits_two_pow_mul h]
  rfl

/-- A product by a `K` word, limb by limb. -/
theorem ofLimbs_mul_ofK (a b v : K) : E.ofLimbs a b * ofK v = E.ofLimbs (a * v) (b * v) := by
  rw [ofK_eq_ofLimbs, mul_limbs, ofLimbs_inj]
  exact ⟨by ring, by ring⟩

/-- A word in the `y` limb. -/
theorem eOfNat128_two_pow_64_mul (X : ℕ) :
    eOfNat128 (2 ^ 64 * X) = E.ofLimbs 0 (K.ofBits X) := by
  rw [eOfNat128, ofLimbs_inj, ← ofBits_mod (2 ^ 64 * X), Nat.mul_mod_right,
    Nat.mul_div_cancel_left _ (Nat.two_pow_pos 64)]
  exact ⟨rfl, rfl⟩

/-- **A coordinate basis vector times a word** (`decode_query_windows`): `e_i · E(v)` with `v` of
degree below `64 - i mod 64` is the bit pattern `2^i · v`, in limb `i / 64`. -/
theorem coordBasis_mul_eOfNat {i v : ℕ} (hi : i < 128) (h : 2 ^ (i % 64) * v < 2 ^ 64) :
    coordBasis i * eOfNat v = eOfNat128 (2 ^ i * v) := by
  rcases (show i < 64 ∨ 64 ≤ i by omega) with h0 | h1
  · rw [Nat.mod_eq_of_lt h0] at h
    rw [coordBasis_of_lt h0, eOfNat_two_pow_mul h, eOfNat128_of_lt h]
  · obtain ⟨a, rfl⟩ : ∃ a, i = 64 + a := ⟨i - 64, by omega⟩
    rw [show (64 + a) % 64 = a by omega] at h
    rw [coordBasis, pow_add, eOfNat128_two_pow_64_mul, eOfNat, ofLimbs_mul_ofK, Nat.mul_assoc,
      eOfNat128_two_pow_64_mul, ofBits_two_pow_mul h]
    simp

/-- `gen^a = E(2^a)` below the first reduction (a compile-time `GEN ** a`). -/
theorem gen_pow_eq_eOfNat {a : ℕ} (h : a < 64) : gen ^ a = eOfNat (2 ^ a) := by
  rw [gen, eOfNat, ← ofK_pow, show K.ofBits 2 = g from rfl, g_pow_eq_ofBits h]
  rfl

/-- `GEN · v = E(2v)` without reduction: one Horner step of a little-endian reconstruction. -/
theorem gen_mul_eOfNat {v : ℕ} (h : 2 * v < 2 ^ 64) : gen * eOfNat v = eOfNat (2 * v) := by
  rw [gen]
  exact eOfNat_two_pow_mul (s := 1) h

end
end LeanVM.Guest.Value
