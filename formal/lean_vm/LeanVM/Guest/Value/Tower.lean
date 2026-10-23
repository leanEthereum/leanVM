/-
  LeanVM.Guest.Value.Tower

  The tower `E = K[y]/(y³ + y + 1)` as the aggregation guest reads it: `y` and `y⁻¹`, packing two
  limbs into a cell and splitting a word into its limbs, integers as bit patterns, and products by
  powers of `x` that do not reduce.
-/

module

public import LeanVM.Parameters.Field
public import LeanVM.Spec.Verifier
import CompPoly.Fields.Binary.BF64.Impl

/-!
# The tower, as the guest reads it

The guest (`crates/rec_aggregation/guests/lean_ethereum.py`, G below) never reads a limb directly:
it hints one, derives the next by `y⁻¹` and proves every piece lies in `K` with `assert_in_k`
(one untaken `JUMP` whose operands must be in `K`). The tower representation `c0 + c1·y + c2·y²`
is unique, so those constraints pin the hint. This module states what they pin, at the level of
values:

* `pack64x2` (G:446-449) is `E.ofLimbs a b 0` (`pack64x2_eq`);
* `assert_canonical`, `canonical_limbs` (G:451-468) and `challenge_from_state` (G:472-484)
  split a canonical word as `lo + y·hi` (`split_iff`, `split_hi`);
* `fs_compress` (G:488-497) pins a scalar's top limb by the canonicity of the cell it lands in
  (`top_pin_iff`);
* `statement_digest` (G:2661-2703) and `da_vector_cell` (G:3045-3085) split a full word into its
  three limbs (`split3_iff`, `split3_top`).

The guest's constants are `Y_TOWER = y` and `Y_INV = y⁻¹ = 1 + y²` (`y_inv`;
`crates/rec_aggregation/src/aggregation.rs:2519-2522`). A zkDSL integer literal is a bit pattern
(`crates/lean_compiler/zkDSL.md`, "a substituted literal is a bit-pattern element"): `n < 2^64`
is the Python verifier's `E(n)`, `eOfNat n`, and a wider one, up to the `u128` literals the host
substitutes, is `eOfNat192 n`. `COORD_BASIS[i]` (`aggregation.rs:2526-2534`) is
`eOfNat192 (2^i)`. Sums of integers are XORs (`eOfNat_xor`), so they add when their bits are
disjoint (`two_pow_mul_xor`); and the product of `x^s` with a word of degree below `64 - s` does
not reduce (`ofBits_two_pow_mul`).
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

/-- In `E`, `a + b = 0` exactly when `a = b`. -/
theorem e_add_eq_zero_iff {a b : E} : a + b = 0 ↔ a = b := by
  rw [add_eq_zero_iff_eq_neg, CharTwo.neg_eq]

/-! ## `ofK` and the limb view -/

theorem ofK_zero : ofK 0 = 0 := map_zero (algebraMap K E)

theorem ofK_one : ofK 1 = 1 := map_one (algebraMap K E)

theorem ofK_pow (a : K) (n : ℕ) : ofK (a ^ n) = ofK a ^ n := map_pow (algebraMap K E) a n

theorem zero_eq_ofLimbs : (0 : E) = E.ofLimbs 0 0 0 := by rw [← ofK_eq_ofLimbs, ofK_zero]

theorem one_eq_ofLimbs : (1 : E) = E.ofLimbs 1 0 0 := by rw [← ofK_eq_ofLimbs, ofK_one]

/-- A word in limb form. -/
theorem eq_ofLimbs (x : E) : x = E.ofLimbs (x.limb 0) (x.limb 1) (x.limb 2) := (ofLimbs_limb x).symm

@[simp] theorem ofLimbs_limb0 (a b c : K) : (E.ofLimbs a b c).limb 0 = a := rfl

@[simp] theorem ofLimbs_limb1 (a b c : K) : (E.ofLimbs a b c).limb 1 = b := rfl

@[simp] theorem ofLimbs_limb2 (a b c : K) : (E.ofLimbs a b c).limb 2 = c := rfl

theorem ofLimbs_inj {a b c a' b' c' : K} :
    E.ofLimbs a b c = E.ofLimbs a' b' c' ↔ a = a' ∧ b = b' ∧ c = c' := by
  constructor
  · intro h
    exact ⟨congrArg (·.limb 0) h, congrArg (·.limb 1) h, congrArg (·.limb 2) h⟩
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

theorem isInK_ofLimbs_iff (a b c : K) : IsInK (E.ofLimbs a b c) ↔ b = 0 ∧ c = 0 := Iff.rfl

theorem isCanonical128_ofLimbs_iff (a b c : K) : IsCanonical128 (E.ofLimbs a b c) ↔ c = 0 :=
  Iff.rfl

/-- A canonical word is its two low limbs. -/
theorem eq_ofLimbs_of_canonical {x : E} (h : IsCanonical128 x) :
    x = E.ofLimbs (x.limb 0) (x.limb 1) 0 := by
  conv_lhs => rw [eq_ofLimbs x]
  rw [h]

theorem ofK_isInK (a : K) : IsInK (ofK a) := (isInK_iff _).mpr ⟨a, rfl⟩

/-! ## `y` and `y⁻¹` -/

/-- `y` is the limb vector `(0, 1, 0)`. -/
theorem y_eq : y = E.ofLimbs 0 1 0 := by
  rw [ofLimbs_eq, ofK_zero, ofK_one]
  ring

/-- Multiplying by `y` shifts the limbs and folds `y³ = y + 1`. -/
theorem ofLimbs_mul_y (a0 a1 a2 : K) : E.ofLimbs a0 a1 a2 * y = E.ofLimbs a2 (a0 + a2) a1 := by
  rw [y_eq, mul_limbs, ofLimbs_inj]
  refine ⟨?_, ?_, ?_⟩ <;> ring

/-- `y⁻¹ = 1 + y²`, the limb vector `(1, 0, 1)` (the guest's `Y_INV`). -/
theorem y_inv : y⁻¹ = E.ofLimbs 1 0 1 := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [y_eq, mul_limbs, one_eq_ofLimbs, ofLimbs_inj]
  exact ⟨by ring, by linear_combination k_two, by ring⟩

/-- Multiplying by `y⁻¹`. -/
theorem ofLimbs_mul_y_inv (a0 a1 a2 : K) :
    E.ofLimbs a0 a1 a2 * y⁻¹ = E.ofLimbs (a0 + a1) a2 a0 := by
  rw [y_inv, mul_limbs, ofLimbs_inj]
  exact ⟨by ring, by linear_combination a1 * k_two,
    by linear_combination a2 * k_two⟩

theorem ofLimbs_add (a0 a1 a2 b0 b1 b2 : K) :
    E.ofLimbs a0 a1 a2 + E.ofLimbs b0 b1 b2 = E.ofLimbs (a0 + b0) (a1 + b1) (a2 + b2) :=
  add_limbs a0 a1 a2 b0 b1 b2

/-! ## Packing two limbs (`pack64x2`, G:446-449) -/

/-- **`pack64x2(a, b)`** (G:446-449): after `assert_in_k(a, b)`, `a + y·b` is the canonical cell
with limbs `a`, `b` (TRIAGE #1: `E.ofLimbs a b 0`). -/
theorem pack64x2_eq {a b : E} (ha : IsInK a) (hb : IsInK b) :
    a + y * b = E.ofLimbs (a.limb 0) (b.limb 0) 0 := by
  obtain ⟨a0, rfl⟩ := (isInK_iff a).mp ha
  obtain ⟨b0, rfl⟩ := (isInK_iff b).mp hb
  rw [ofK_eq_ofLimbs, ofK_eq_ofLimbs, mul_comm, ofLimbs_mul_y, ofLimbs_add, ofLimbs_inj]
  simp

/-! ## Splitting a canonical word (`assert_canonical`, `canonical_limbs`, G:451-468) -/

/-- The derived limb `(x + c)·y⁻¹`, in limbs. -/
theorem add_ofK_mul_y_inv (x : E) (c : K) :
    (x + ofK c) * y⁻¹ =
      E.ofLimbs (x.limb 0 + c + x.limb 1) (x.limb 2) (x.limb 0 + c) := by
  rw [eq_ofLimbs x, ofK_eq_ofLimbs, ofLimbs_add, ofLimbs_mul_y_inv]
  simp

/-- **The split of a word** (`assert_canonical`, `canonical_limbs`, G:451-468; the same
constraints in `challenge_from_state`, G:472-484, and `grind_check`, G:717-720): the hinted
`lo` and the derived `(x + lo)·y⁻¹` both lie in `K` exactly when `x` is canonical
(`IsCanonical128`) and `lo` is its low limb. TRIAGE #2, #3: the tower representation is unique. -/
theorem split_iff (x lo : E) :
    IsInK lo ∧ IsInK ((x + lo) * y⁻¹) ↔ IsCanonical128 x ∧ lo = ofK (x.limb 0) := by
  constructor
  · rintro ⟨hlo, hhi⟩
    obtain ⟨c, rfl⟩ := (isInK_iff lo).mp hlo
    rw [add_ofK_mul_y_inv, isInK_ofLimbs_iff] at hhi
    exact ⟨hhi.1, by rw [k_add_eq_zero_iff.mp hhi.2]⟩
  · rintro ⟨hx, rfl⟩
    refine ⟨ofK_isInK _, ?_⟩
    rw [add_ofK_mul_y_inv, isInK_ofLimbs_iff]
    exact ⟨hx, k_add_self _⟩

/-- The derived high limb of a canonical word is its `y` limb. -/
theorem split_hi {x : E} (hx : IsCanonical128 x) : (x + ofK (x.limb 0)) * y⁻¹ = ofK (x.limb 1) := by
  rw [add_ofK_mul_y_inv, k_add_self, zero_add, hx, ofK_eq_ofLimbs]

/-! ## The top limb, pinned by a canonical cell (`fs_compress`, G:488-497) -/

/-- `x + y²·c`, in limbs. -/
theorem add_y_mul_y_mul_ofK (x : E) (c : K) :
    x + y * y * ofK c = E.ofLimbs (x.limb 0) (x.limb 1) (x.limb 2 + c) := by
  have hyy : y * y = E.ofLimbs 0 0 1 := by
    rw [y_eq, mul_limbs, ofLimbs_inj]
    refine ⟨by ring, by ring, by ring⟩
  rw [hyy, ofK_eq_ofLimbs, mul_limbs, eq_ofLimbs x, ofLimbs_add]
  simp

/-- **The top limb is pinned** (`fs_compress`, G:488-497): a hinted `l` in `K` makes
`x + y²·l` canonical exactly when it is `x`'s top limb. TRIAGE #5. -/
theorem top_pin_iff (x l : E) : IsInK l ∧ IsCanonical128 (x + y * y * l) ↔ l = ofK (x.limb 2) := by
  constructor
  · rintro ⟨hl, hc⟩
    obtain ⟨c, rfl⟩ := (isInK_iff l).mp hl
    rw [add_y_mul_y_mul_ofK, isCanonical128_ofLimbs_iff] at hc
    rw [k_add_eq_zero_iff.mp hc]
  · rintro rfl
    refine ⟨ofK_isInK _, ?_⟩
    rw [add_y_mul_y_mul_ofK, isCanonical128_ofLimbs_iff]
    exact k_add_self _

/-- With its top limb pinned, `x + y²·x₂` is the cell of `x`'s two low limbs. -/
theorem top_pin_eq (x : E) : x + y * y * ofK (x.limb 2) = E.ofLimbs (x.limb 0) (x.limb 1) 0 := by
  rw [add_y_mul_y_mul_ofK, k_add_self]

/-- `t + y·tag` for a tag in `K`, the block's second cell in `fs_compress`. -/
theorem ofK_add_y_mul_ofK (a b : K) : ofK a + y * ofK b = E.ofLimbs a b 0 := by
  rw [pack64x2_eq (ofK_isInK a) (ofK_isInK b)]
  simp

/-! ## Splitting a full word into three limbs (`statement_digest`, `da_vector_cell`) -/

/-- **The three-limb split** (`statement_digest`, G:2690-2694; `da_vector_cell`, G:3055-3059):
two hinted limbs `a`, `b` and the derived top `((x + a)·y⁻¹ + b)·y⁻¹` all lie in `K` (the three
`pack64x2` calls assert it) exactly when `a`, `b` are `x`'s low limbs. -/
theorem split3_iff (x a b : E) :
    IsInK a ∧ IsInK b ∧ IsInK (((x + a) * y⁻¹ + b) * y⁻¹) ↔
      a = ofK (x.limb 0) ∧ b = ofK (x.limb 1) := by
  constructor
  · rintro ⟨ha, hb, htop⟩
    obtain ⟨a0, rfl⟩ := (isInK_iff a).mp ha
    obtain ⟨b0, rfl⟩ := (isInK_iff b).mp hb
    rw [add_ofK_mul_y_inv x a0, ofK_eq_ofLimbs b0, ofLimbs_add, ofLimbs_mul_y_inv,
      isInK_ofLimbs_iff] at htop
    simp only [add_zero] at htop
    have h0 : x.limb 0 = a0 := k_add_eq_zero_iff.mp htop.1
    subst h0
    rw [k_add_self, zero_add] at htop
    exact ⟨rfl, by rw [k_add_eq_zero_iff.mp htop.2]⟩
  · rintro ⟨rfl, rfl⟩
    refine ⟨ofK_isInK _, ofK_isInK _, ?_⟩
    rw [add_ofK_mul_y_inv x (x.limb 0), ofK_eq_ofLimbs (x.limb 1), ofLimbs_add,
      ofLimbs_mul_y_inv, isInK_ofLimbs_iff]
    simp [k_add_self]

/-- The derived top limb of the three-limb split is `x`'s `y²` limb. -/
theorem split3_top (x : E) :
    ((x + ofK (x.limb 0)) * y⁻¹ + ofK (x.limb 1)) * y⁻¹ = ofK (x.limb 2) := by
  rw [add_ofK_mul_y_inv x (x.limb 0), ofK_eq_ofLimbs (x.limb 1), ofLimbs_add,
    ofLimbs_mul_y_inv, ofK_eq_ofLimbs]
  simp [k_add_self]

/-! ## Integers as bit patterns -/

/-- A `u192` bit pattern: limb `i` holds bits `64·i .. 64·i + 63` of `n` (a zkDSL integer
literal, and `COORD_BASIS[i] = eOfNat192 (2^i)`). -/
def eOfNat192 (n : ℕ) : E :=
  E.ofLimbs (K.ofBits n) (K.ofBits (n / 2 ^ 64)) (K.ofBits (n / 2 ^ 128))

/-- `COORD_BASIS[i]` (`aggregation.rs:2526-2534`): the `i`-th coordinate basis vector. -/
def coordBasis (i : ℕ) : E := eOfNat192 (2 ^ i)

theorem ofBits_xor (a b : ℕ) : K.ofBits (a ^^^ b) = K.ofBits a + K.ofBits b := by
  simp only [K.ofBits, BitVec.ofNat_xor]
  rfl

theorem ofBits_zero : K.ofBits 0 = 0 := rfl

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

theorem eOfNat_eq_ofLimbs (n : ℕ) : eOfNat n = E.ofLimbs (K.ofBits n) 0 0 := ofK_eq_ofLimbs _

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

theorem eOfNat_mod (n : ℕ) : eOfNat (n % 2 ^ 64) = eOfNat n := by
  rw [eOfNat, ofBits_mod]
  rfl

/-- Two integers below `2^64` add to zero exactly when they are equal. -/
theorem eOfNat_add_eq_zero_iff {a b : ℕ} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    eOfNat a + eOfNat b = 0 ↔ a = b := by
  rw [e_add_eq_zero_iff]
  exact ⟨eOfNat_inj ha hb, fun h ↦ h ▸ rfl⟩

theorem eOfNat192_xor (a b : ℕ) : eOfNat192 (a ^^^ b) = eOfNat192 a + eOfNat192 b := by
  simp only [eOfNat192, Nat.xor_div_two_pow, ofBits_xor, ofLimbs_add]

theorem eOfNat192_of_lt {n : ℕ} (h : n < 2 ^ 64) : eOfNat192 n = eOfNat n := by
  rw [eOfNat192, eOfNat_eq_ofLimbs, Nat.div_eq_of_lt h,
    Nat.div_eq_of_lt (lt_of_lt_of_le h (Nat.pow_le_pow_right (by decide) (by decide)))]
  rfl

theorem eOfNat192_zero : eOfNat192 0 = 0 := by rw [eOfNat192_of_lt (by decide), eOfNat_zero]

/-- `eToNat` reads the bit pattern back, modulo `2^192`. -/
theorem eToNat_eOfNat192 (n : ℕ) : eToNat (eOfNat192 n) = n % 2 ^ 192 := by
  simp only [eToNat, eOfNat192, ofLimbs_limb0, ofLimbs_limb1, ofLimbs_limb2, kToNat_ofBits]
  have h1 : n % 2 ^ 128 = n % 2 ^ 64 + 2 ^ 64 * (n / 2 ^ 64 % 2 ^ 64) := by
    rw [show (2 : ℕ) ^ 128 = 2 ^ 64 * 2 ^ 64 by norm_num, Nat.mod_mul]
  have h2 : n % 2 ^ 192 = n % 2 ^ 128 + 2 ^ 128 * (n / 2 ^ 128 % 2 ^ 64) := by
    rw [show (2 : ℕ) ^ 192 = 2 ^ 128 * 2 ^ 64 by norm_num, Nat.mod_mul]
  omega

/-- `eOfNat192` of the integer of a word is the word. -/
theorem eOfNat192_eToNat (x : E) : eOfNat192 (eToNat x) = x := by
  have h0 := (x.limb 0).toBitVec.isLt
  have h1 := (x.limb 1).toBitVec.isLt
  have h2 := (x.limb 2).toBitVec.isLt
  have e0 : eToNat x % 2 ^ 64 = kToNat (x.limb 0) := by unfold eToNat kToNat; omega
  have e1 : eToNat x / 2 ^ 64 % 2 ^ 64 = kToNat (x.limb 1) := by unfold eToNat kToNat; omega
  have e2 : eToNat x / 2 ^ 128 % 2 ^ 64 = kToNat (x.limb 2) := by unfold eToNat kToNat; omega
  rw [eOfNat192, ← ofBits_mod (eToNat x), e0, ← ofBits_mod (eToNat x / 2 ^ 64), e1,
    ← ofBits_mod (eToNat x / 2 ^ 128), e2, ofBits_kToNat, ofBits_kToNat, ofBits_kToNat,
    ← eq_ofLimbs]

/-- Distinct bit patterns below `2^192` are distinct words. -/
theorem eOfNat192_inj {a b : ℕ} (ha : a < 2 ^ 192) (hb : b < 2 ^ 192)
    (h : eOfNat192 a = eOfNat192 b) : a = b := by
  have := congrArg eToNat h
  rwa [eToNat_eOfNat192, eToNat_eOfNat192, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this

/-- Below the first limb, a coordinate basis vector is `E(2^i)`. -/
theorem coordBasis_of_lt {i : ℕ} (h : i < 64) : coordBasis i = eOfNat (2 ^ i) :=
  eOfNat192_of_lt (Nat.pow_lt_pow_right (by decide) h)

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

/-- The word `2^s` is `1 <<< s`. -/
private theorem ofNat_two_pow_mul {s v : ℕ} :
    BitVec.ofNat 64 (2 ^ s * v) = BitVec.ofNat 64 v <<< s := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    Nat.mod_mul_mod, Nat.mul_comm]

/-- **No reduction**: `x^s · v` for `v` of degree below `64 - s` is the shifted word, the
product the guest's byte counters (`scaled_log`, G:2704-2723) and query positions
(`decode_query_bits`, G:654-698) rely on. -/
theorem ofBits_two_pow_mul {s v : ℕ} (h : 2 ^ s * v < 2 ^ 64) :
    K.ofBits (2 ^ s) * K.ofBits v = K.ofBits (2 ^ s * v) := by
  rcases Nat.eq_zero_or_pos v with rfl | hv
  · rw [ofBits_zero, mul_zero, Nat.mul_zero, ofBits_zero]
  have hs : s < 64 := by
    by_contra hs
    have : 2 ^ 64 ≤ 2 ^ s * v :=
      le_trans (Nat.pow_le_pow_right (by decide) (Nat.le_of_not_lt hs)) (Nat.le_mul_of_pos_right _ hv)
    omega
  apply BF64.toQuot_injective
  rw [BF64.toQuot_mul]
  simp only [BF64.toQuot, BF64.toPolyBF64, K.ofBits, BF64.toBitVec_ofBitVec, ofNat_two_pow_mul]
  have hx : BinaryField.toPoly (BitVec.ofNat 64 (2 ^ s)) = Polynomial.X ^ s := by
    have := BinaryField.toPoly_one_shiftLeft (w := 64) s hs
    rw [Nat.one_shiftLeft] at this
    exact this
  rw [hx, ← map_mul,
    BinaryField.toPoly_shiftLeft_no_overflow (d := 64 - s) (BitVec.ofNat 64 v) ?_ (by omega),
    mul_comm]
  rw [BitVec.toNat_ofNat]
  have : v < 2 ^ (64 - s) := by
    have h2 : 2 ^ 64 = 2 ^ s * 2 ^ (64 - s) := by rw [← Nat.pow_add]; congr 1; omega
    rw [h2] at h
    exact Nat.lt_of_mul_lt_mul_left h
  exact lt_of_le_of_lt (Nat.mod_le _ _) this

/-- `E(2^s) · E(v) = E(2^s · v)` without reduction. -/
theorem eOfNat_two_pow_mul {s v : ℕ} (h : 2 ^ s * v < 2 ^ 64) :
    eOfNat (2 ^ s) * eOfNat v = eOfNat (2 ^ s * v) := by
  rw [eOfNat, eOfNat, ← ofK_mul, ofBits_two_pow_mul h]
  rfl

/-- A product by a `K` word, limb by limb. -/
theorem ofLimbs_mul_ofK (a b c v : K) : E.ofLimbs a b c * ofK v = E.ofLimbs (a * v) (b * v) (c * v) := by
  rw [ofK_eq_ofLimbs, mul_limbs, ofLimbs_inj]
  exact ⟨by ring, by ring, by ring⟩

/-- A word in the `y` limb. -/
theorem eOfNat192_two_pow_64_mul {X : ℕ} (hX : X < 2 ^ 64) :
    eOfNat192 (2 ^ 64 * X) = E.ofLimbs 0 (K.ofBits X) 0 := by
  rw [eOfNat192, ofLimbs_inj, ← ofBits_mod (2 ^ 64 * X), Nat.mul_mod_right,
    Nat.mul_div_cancel_left _ (Nat.two_pow_pos 64), show (2 : ℕ) ^ 128 = 2 ^ 64 * 2 ^ 64 by norm_num,
    ← Nat.div_div_eq_div_mul, Nat.mul_div_cancel_left _ (Nat.two_pow_pos 64), Nat.div_eq_of_lt hX]
  exact ⟨rfl, rfl, rfl⟩

/-- A word in the `y²` limb. -/
theorem eOfNat192_two_pow_128_mul (X : ℕ) :
    eOfNat192 (2 ^ 128 * X) = E.ofLimbs 0 0 (K.ofBits X) := by
  have h1 : 2 ^ 128 * X / 2 ^ 64 = 2 ^ 64 * X := by
    rw [show (2 : ℕ) ^ 128 = 2 ^ 64 * 2 ^ 64 by norm_num, Nat.mul_assoc,
      Nat.mul_div_cancel_left _ (Nat.two_pow_pos 64)]
  have h2 : 2 ^ 128 * X / 2 ^ 128 = X := Nat.mul_div_cancel_left _ (Nat.two_pow_pos 128)
  have h3 : 2 ^ 128 * X % 2 ^ 64 = 0 := by
    rw [show (2 : ℕ) ^ 128 * X = 2 ^ 64 * (2 ^ 64 * X) by ring]
    exact Nat.mul_mod_right _ _
  have h4 : 2 ^ 64 * X % 2 ^ 64 = 0 := Nat.mul_mod_right _ _
  rw [eOfNat192, ofLimbs_inj, h1, h2, ← ofBits_mod (2 ^ 128 * X), h3, ← ofBits_mod (2 ^ 64 * X), h4]
  exact ⟨rfl, rfl, rfl⟩

/-- **A coordinate basis vector times a word** (`decode_query_bits`, G:654-698): `e_i · E(v)` with
`v` of degree below `64 - i mod 64` is the bit pattern `2^i · v`, in limb `i / 64`. -/
theorem coordBasis_mul_eOfNat {i v : ℕ} (hi : i < 192) (h : 2 ^ (i % 64) * v < 2 ^ 64) :
    coordBasis i * eOfNat v = eOfNat192 (2 ^ i * v) := by
  rcases (show i < 64 ∨ (64 ≤ i ∧ i < 128) ∨ 128 ≤ i by omega) with h0 | h1 | h2
  · rw [Nat.mod_eq_of_lt h0] at h
    rw [coordBasis_of_lt h0, eOfNat_two_pow_mul h, eOfNat192_of_lt h]
  · obtain ⟨a, rfl⟩ : ∃ a, i = 64 + a := ⟨i - 64, by omega⟩
    rw [show (64 + a) % 64 = a by omega] at h
    rcases Nat.eq_zero_or_pos v with hv | hv
    · subst hv
      rw [Nat.mul_zero, eOfNat_zero, mul_zero, eOfNat192_zero]
    have ha : 2 ^ a < 2 ^ 64 := lt_of_le_of_lt (Nat.le_mul_of_pos_right _ hv) h
    rw [coordBasis, pow_add, eOfNat192_two_pow_64_mul ha, eOfNat, ofLimbs_mul_ofK, Nat.mul_assoc,
      eOfNat192_two_pow_64_mul h, ofBits_two_pow_mul h]
    simp
  · obtain ⟨a, rfl⟩ : ∃ a, i = 128 + a := ⟨i - 128, by omega⟩
    rw [show (128 + a) % 64 = a by omega] at h
    rcases Nat.eq_zero_or_pos v with hv | hv
    · subst hv
      rw [Nat.mul_zero, eOfNat_zero, mul_zero, eOfNat192_zero]
    rw [coordBasis, pow_add, eOfNat192_two_pow_128_mul, eOfNat, ofLimbs_mul_ofK, Nat.mul_assoc,
      eOfNat192_two_pow_128_mul, ofBits_two_pow_mul h]
    simp

/-- `g^a` is the word `2^a` below the first reduction. -/
theorem g_pow_eq_ofBits {a : ℕ} (h : a < 64) : g ^ a = K.ofBits (2 ^ a) := by
  induction a with
  | zero => rfl
  | succ a ih =>
    rw [pow_succ', ih (by omega), g, show K.ofBits 0x2 = K.ofBits (2 ^ 1) from rfl,
      ofBits_two_pow_mul (by rw [← pow_add]; exact Nat.pow_lt_pow_right (by decide) (by omega)),
      ← pow_add, add_comm]

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
