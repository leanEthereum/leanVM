module

public import Quantum.Sponge.PermTail
public import Quantum.Sponge.Bound
public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Data.Fintype.BigOperators

@[expose] public section

/-!
# The sponge bounds at Keccak-256 sizes

Keccak-256 is the sponge with rate `1088` bits, capacity `512` bits and output the first `256`
bits of the rate part. This file instantiates the generic bounds at these sizes, for any rate type
`X` with `|X| = 2^1088`, any capacity type `Z` with `|Z| = 2^512`, and any output map whose fibers
have at most `2^832` points.

* `prob_not_permGood_keccak`: with `s = 6`, a uniform permutation is `PermGood π 18` except with
  probability at most `2^-777`.
* `collisionRateBound_le_cube`, `preimageRateBound_le_cube`: the per-port fractions are at most
  `max (T F / |X|) (3 G (T + 1)^3 / |Z|)`, resp. `max (F / |X|) (3 G (T + 1)^3 / |Z|)`.
* `keccak_collision_weight_le`: for `T ≤ 2^k`, `k ≤ 123`, the collision event weight
  `6 T² ε` is at most `2^(3k) / 2^253`; `T ≤ 2^63` gives `2^-64`.
* `keccak_preimage_weight_le`: for `T ≤ 2^k`, `k ≤ 82`, the preimage event weight is at most
  `2^(2k) / 2^253`; `T ≤ 2^64` gives `2^-125`.
* `KeccakRate`, `KeccakCapacity`, `keccakOut`: concrete types, and the end-to-end event bounds
  `keccak256_eventWeight_collisionBad_le`, `keccak256_eventWeight_preimageBad_le`.
-/

namespace Quantum.Sponge

open Finset Quantum
open scoped ENNReal Kronecker

universe u v w

/-! ## Arithmetic helpers -/

theorem natCast_div_le_natCast_div {n m p q : ℕ} (hq : q ≠ 0) (h : n * q ≤ m * p) :
    (n : ℝ≥0∞) / m ≤ p / q := by
  apply ENNReal.div_le_of_le_mul
  rw [mul_comm, ← mul_div_assoc, ENNReal.le_div_iff_mul_le (Or.inl (by exact_mod_cast hq))
    (Or.inl (ENNReal.natCast_ne_top q))]
  exact_mod_cast h

theorem natCast_mul_div_le_natCast_div {c n m p q : ℕ} (hq : q ≠ 0) (h : c * n * q ≤ m * p) :
    (c : ℝ≥0∞) * ((n : ℝ≥0∞) / m) ≤ p / q := by
  rw [← mul_div_assoc, ← Nat.cast_mul]
  exact natCast_div_le_natCast_div hq h

/-! ## The permutation is good -/

section PermGood

variable {X Z : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] [AddCommGroup Z]

set_option exponentiation.threshold 4096 in
/-- At Keccak-256 sizes, a uniform permutation of `X × Z` fails `PermGood π 18` (`s = 6`) with
probability at most `2^-777`. -/
theorem prob_not_permGood_keccak (hX : Fintype.card X = 2 ^ 1088)
    (hZ : Fintype.card Z = 2 ^ 512) :
    (#(univ.filter fun π : Equiv.Perm (X × Z) ↦ ¬PermGood π 18) : ℝ) /
        Fintype.card (Equiv.Perm (X × Z)) ≤ 1 / 2 ^ 777 := by
  have h := prob_not_permGood_le (X := X) (Z := Z) (s := 6) (by rw [hX, hZ]; norm_num)
  rw [hX, hZ] at h
  refine h.trans ?_
  have hc : (((2 ^ 512 : ℕ).choose 6 : ℕ) : ℝ) ≤ (2 : ℝ) ^ 3072 / 720 :=
    (Nat.choose_le_pow_div (α := ℝ) 6 (2 ^ 512)).trans_eq
      (by rw [show Nat.factorial 6 = 720 from rfl]; push_cast; ring)
  set c : ℝ := (((2 ^ 512 : ℕ).choose 6 : ℕ) : ℝ)
  push_cast
  calc _ = c * ((2 : ℝ) ^ 1088) ^ 2 * ((2 ^ 512 / (2 ^ 1088 * 2 ^ 512)) ^ 6 +
          2 ^ 512 * (2 ^ 512 / (2 ^ 1088 * 2 ^ 512 - 2 * 6)) ^ 6) := by ring
    _ ≤ (2 : ℝ) ^ 3072 / 720 * ((2 : ℝ) ^ 1088) ^ 2 * ((2 ^ 512 / (2 ^ 1088 * 2 ^ 512)) ^ 6 +
          2 ^ 512 * (2 ^ 512 / (2 ^ 1088 * 2 ^ 512 - 2 * 6)) ^ 6) := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (by positivity)) ?_
        norm_num
    _ ≤ 1 / 2 ^ 777 := by norm_num

end PermGood

/-! ## The per-port fractions -/

section Rates

variable {X Z : Type} [Fintype X] [Fintype Z]

theorem rateK_le (T G : ℕ) : (T + 1) * ((T + 1) * T + 2 * T) * G ≤ 3 * G * (T + 1) ^ 3 := by
  have : (T + 1) * ((T + 1) * T + 2 * T) ≤ 3 * (T + 1) ^ 3 := by
    nlinarith [Nat.zero_le (T * T * T), Nat.zero_le (T * T)]
  calc _ = G * ((T + 1) * ((T + 1) * T + 2 * T)) := by ring
    _ ≤ G * (3 * (T + 1) ^ 3) := by gcongr
    _ = _ := by ring

theorem rateK'_le {G : ℕ} (hG : 2 ≤ G) (T : ℕ) :
    (T + 1) + T * ((T + 1) * T + T + 1) * G + T * T * G + T ≤ 3 * G * (T + 1) ^ 3 := by
  nlinarith [Nat.zero_le (G * T * T * T), Nat.zero_le (G * T * T), Nat.mul_le_mul hG (le_refl T)]

/-- For `G ≥ 2`, the collision per-port fraction is at most `max (T F / |X|) (3 G (T+1)³ / |Z|)`. -/
theorem collisionRateBound_le_cube {G : ℕ} (hG : 2 ≤ G) (T F : ℕ) :
    collisionRateBound (X := X) (Z := Z) T G F ≤
      max ((T * F : ℕ) / Fintype.card X : ℝ≥0∞) ((3 * G * (T + 1) ^ 3 : ℕ) / Fintype.card Z) :=
  max_le_max le_rfl (max_le (ENNReal.div_le_div_right (by exact_mod_cast rateK_le T G) _)
    (ENNReal.div_le_div_right (by exact_mod_cast rateK'_le hG T) _))

/-- For `G ≥ 2`, the preimage per-port fraction is at most `max (F / |X|) (3 G (T+1)³ / |Z|)`. -/
theorem preimageRateBound_le_cube {G : ℕ} (hG : 2 ≤ G) (T F : ℕ) :
    preimageRateBound (X := X) (Z := Z) T G F ≤
      max ((F : ℕ) / Fintype.card X : ℝ≥0∞) ((3 * G * (T + 1) ^ 3 : ℕ) / Fintype.card Z) :=
  max_le_max le_rfl (max_le (ENNReal.div_le_div_right (by exact_mod_cast rateK_le T G) _)
    (ENNReal.div_le_div_right (by exact_mod_cast rateK'_le hG T) _))

/-! ## Event weights at Keccak-256 sizes -/

/-- The rate term: `6 T² (T 2^a) 2^b ≤ 2^n 2^(3k)` for `T ≤ 2^k` and `a + b + 3 = n`. -/
theorem rate_term_le {k T a b n : ℕ} (hT : T ≤ 2 ^ k) (hn : a + b + 3 = n) :
    6 * T ^ 2 * (T * 2 ^ a) * 2 ^ b ≤ 2 ^ n * 2 ^ (3 * k) := by
  subst hn
  calc 6 * T ^ 2 * (T * 2 ^ a) * 2 ^ b = 6 * T ^ 3 * (2 ^ a * 2 ^ b) := by ring
    _ ≤ 2 ^ 3 * (2 ^ k) ^ 3 * (2 ^ a * 2 ^ b) := by gcongr; norm_num
    _ = 2 ^ (a + b + 3) * 2 ^ (3 * k) := by rw [pow_add, pow_add, pow_mul']; ring

/-- The output term: `6 T² 2^a 2^b ≤ 2^n 2^(2k)` for `T ≤ 2^k` and `a + b + 3 = n`. -/
theorem output_term_le {k T a b n : ℕ} (hT : T ≤ 2 ^ k) (hn : a + b + 3 = n) :
    6 * T ^ 2 * 2 ^ a * 2 ^ b ≤ 2 ^ n * 2 ^ (2 * k) := by
  subst hn
  calc 6 * T ^ 2 * 2 ^ a * 2 ^ b ≤ 2 ^ 3 * (2 ^ k) ^ 2 * 2 ^ a * 2 ^ b := by gcongr; norm_num
    _ = 2 ^ (a + b + 3) * 2 ^ (2 * k) := by rw [pow_add, pow_add, pow_mul']; ring

/-- The capacity term with `G = 18`: `6 T² · 3 G (T+1)³ · 2^b ≤ 2^m 2^e` for `T ≤ 2^k` and
`5 k + 12 + b ≤ m + e`. -/
theorem capacity_term_le {k T b m e : ℕ} (hT : T ≤ 2 ^ k) (he : 5 * k + 12 + b ≤ m + e) :
    6 * T ^ 2 * (3 * 18 * (T + 1) ^ 3) * 2 ^ b ≤ 2 ^ m * 2 ^ e := by
  have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have h2 : T + 1 ≤ 2 * 2 ^ k := by linarith
  calc 6 * T ^ 2 * (3 * 18 * (T + 1) ^ 3) * 2 ^ b
      ≤ 6 * (2 ^ k) ^ 2 * (3 * 18 * (2 * 2 ^ k) ^ 3) * 2 ^ b := by gcongr
    _ = 2592 * (2 ^ k) ^ 5 * 2 ^ b := by ring
    _ ≤ 2 ^ 12 * (2 ^ k) ^ 5 * 2 ^ b := by gcongr; norm_num
    _ = 2 ^ (12 + k * 5 + b) := by rw [← pow_mul, ← pow_add, ← pow_add]
    _ ≤ 2 ^ (m + e) := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ = 2 ^ m * 2 ^ e := pow_add _ _ _

/-- **Collision weight at Keccak-256 sizes.** For `T ≤ 2^k` with `k ≤ 123`, the event weight
`6 T² ε` of `CollisionBad` with `G = 18` and fibers of `2^832` points is at most `2^(3k) / 2^253`:
the truncated-output term `6 T³ / 2^256` dominates. -/
theorem keccak_collision_weight_le (hX : Fintype.card X = 2 ^ 1088)
    (hZ : Fintype.card Z = 2 ^ 512) {k T : ℕ} (hk : k ≤ 123) (hT : T ≤ 2 ^ k) :
    6 * (T : ℝ≥0∞) ^ 2 * collisionRateBound (X := X) (Z := Z) T 18 (2 ^ 832) ≤
      2 ^ (3 * k) / 2 ^ 253 := by
  calc 6 * (T : ℝ≥0∞) ^ 2 * collisionRateBound (X := X) (Z := Z) T 18 (2 ^ 832)
      ≤ ((6 * T ^ 2 : ℕ) : ℝ≥0∞) * max ((T * 2 ^ 832 : ℕ) / Fintype.card X : ℝ≥0∞)
          ((3 * 18 * (T + 1) ^ 3 : ℕ) / Fintype.card Z) := by
        rw [show (6 : ℝ≥0∞) * T ^ 2 = ((6 * T ^ 2 : ℕ) : ℝ≥0∞) by norm_cast]
        gcongr
        exact collisionRateBound_le_cube (by norm_num) T _
    _ ≤ _ := by
        rw [mul_max_of_nonneg _ _ (by positivity), hX, hZ]
        have hp : (2 : ℝ≥0∞) ^ (3 * k) / 2 ^ 253 = ((2 ^ (3 * k) : ℕ) : ℝ≥0∞) / (2 ^ 253 : ℕ) := by
          norm_cast
        rw [hp]
        exact max_le (natCast_mul_div_le_natCast_div (by positivity) (rate_term_le hT rfl))
          (natCast_mul_div_le_natCast_div (by positivity) (capacity_term_le hT (by omega)))

/-- **Preimage weight at Keccak-256 sizes.** For `T ≤ 2^k` with `k ≤ 82`, the event weight
`6 T² ε` of `PreimageBad` with `G = 18` and fibers of `2^832` points is at most `2^(2k) / 2^253`:
the output term `6 T² / 2^256` dominates. -/
theorem keccak_preimage_weight_le (hX : Fintype.card X = 2 ^ 1088)
    (hZ : Fintype.card Z = 2 ^ 512) {k T : ℕ} (hk : k ≤ 82) (hT : T ≤ 2 ^ k) :
    6 * (T : ℝ≥0∞) ^ 2 * preimageRateBound (X := X) (Z := Z) T 18 (2 ^ 832) ≤
      2 ^ (2 * k) / 2 ^ 253 := by
  calc 6 * (T : ℝ≥0∞) ^ 2 * preimageRateBound (X := X) (Z := Z) T 18 (2 ^ 832)
      ≤ ((6 * T ^ 2 : ℕ) : ℝ≥0∞) * max ((2 ^ 832 : ℕ) / Fintype.card X : ℝ≥0∞)
          ((3 * 18 * (T + 1) ^ 3 : ℕ) / Fintype.card Z) := by
        rw [show (6 : ℝ≥0∞) * T ^ 2 = ((6 * T ^ 2 : ℕ) : ℝ≥0∞) by norm_cast]
        gcongr
        exact preimageRateBound_le_cube (by norm_num) T (2 ^ 832)
    _ ≤ _ := by
        rw [mul_max_of_nonneg _ _ (by positivity), hX, hZ]
        have hp : (2 : ℝ≥0∞) ^ (2 * k) / 2 ^ 253 = ((2 ^ (2 * k) : ℕ) : ℝ≥0∞) / (2 ^ 253 : ℕ) := by
          norm_cast
        rw [hp]
        exact max_le (natCast_mul_div_le_natCast_div (by positivity) (output_term_le hT rfl))
          (natCast_mul_div_le_natCast_div (by positivity) (capacity_term_le hT (by omega)))

/-- `T ≤ 2^63` calls find a Keccak-256 collision (or a bad database) with weight at most
`2^-64`. -/
theorem keccak_collision_weight_le_two_pow_63 (hX : Fintype.card X = 2 ^ 1088)
    (hZ : Fintype.card Z = 2 ^ 512) {T : ℕ} (hT : T ≤ 2 ^ 63) :
    6 * (T : ℝ≥0∞) ^ 2 * collisionRateBound (X := X) (Z := Z) T 18 (2 ^ 832) ≤ (2 ^ 64)⁻¹ := by
  refine (keccak_collision_weight_le hX hZ (by norm_num) hT).trans ?_
  have := natCast_div_le_natCast_div (n := 2 ^ (3 * 63)) (m := 2 ^ 253) (p := 1) (q := 2 ^ 64)
    (by positivity) (by norm_num)
  rw [Nat.cast_pow, Nat.cast_pow, Nat.cast_pow, Nat.cast_one, Nat.cast_ofNat, one_div] at this
  exact this

/-- `T ≤ 2^64` calls find a Keccak-256 preimage (or a bad database) with weight at most
`2^-125`. -/
theorem keccak_preimage_weight_le_two_pow_64 (hX : Fintype.card X = 2 ^ 1088)
    (hZ : Fintype.card Z = 2 ^ 512) {T : ℕ} (hT : T ≤ 2 ^ 64) :
    6 * (T : ℝ≥0∞) ^ 2 * preimageRateBound (X := X) (Z := Z) T 18 (2 ^ 832) ≤ (2 ^ 125)⁻¹ := by
  refine (keccak_preimage_weight_le hX hZ (by norm_num) hT).trans ?_
  have := natCast_div_le_natCast_div (n := 2 ^ (2 * 64)) (m := 2 ^ 253) (p := 1) (q := 2 ^ 125)
    (by positivity) (by norm_num)
  rw [Nat.cast_pow, Nat.cast_pow, Nat.cast_pow, Nat.cast_one, Nat.cast_ofNat, one_div] at this
  exact this

end Rates

/-! ## End-to-end event bounds -/

section Event

variable {X Z Y : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
  [AddCommGroup X] [AddCommGroup Z] {L : LocalSig.{u, v}} {W : QReg → Type w} {A : QReg}

open scoped Classical in
/-- A program of `T ≤ 2^k` calls (`k ≤ 123`) to the compressed `h`, `k`, `k'` of Keccak-256 sizes,
for a permutation `π` with `PermGood π 18`, ends with its database bad or holding a collision of
`out` with weight at most `2^(3k) / 2^253`. -/
theorem keccak_eventWeight_collisionBad_le [DecidableEq Y] (hX : Fintype.card X = 2 ^ 1088)
    (hZ : Fintype.card Z = 2 ^ 512) {π : Equiv.Perm (X × Z)} (hπ : PermGood π 18) {out : X → Y}
    (hF : ∀ y, #(univ.filter fun x ↦ out x = y) ≤ 2 ^ 832) {k T : ℕ} (hk : k ≤ 123)
    (hT : T ≤ 2 ^ k) (I : L.Interp) (x : QuantumComp L (spongeSpec X Z) W A)
    (hx : x.IsTotalQueryBound T) (ρ : SubState A) :
    (spongeCompressedRuntime X Z).eventWeight I (dbsProjector (CollisionBad π out)) x
        (ρ.matrix ⊗ₖ (spongeCompressedRuntime X Z).init.matrix) ≤ 2 ^ (3 * k) / 2 ^ 253 :=
  (eventWeight_spongeCompressedRuntime_le _ upClosed_collisionBad not_mem_collisionBad_emptyDbs
    (freshBound_collisionBad hπ hF T) I x hx ρ).trans (keccak_collision_weight_le hX hZ hk hT)

open scoped Classical in
/-- A program of `T ≤ 2^k` calls (`k ≤ 82`) to the compressed `h`, `k`, `k'` of Keccak-256 sizes,
for a permutation `π` with `PermGood π 18`, ends with its database bad or holding a path to `y0`
with weight at most `2^(2k) / 2^253`. -/
theorem keccak_eventWeight_preimageBad_le (hX : Fintype.card X = 2 ^ 1088)
    (hZ : Fintype.card Z = 2 ^ 512) {π : Equiv.Perm (X × Z)} (hπ : PermGood π 18) {out : X → Y}
    (hF : ∀ y, #(univ.filter fun x ↦ out x = y) ≤ 2 ^ 832) (y0 : Y) {k T : ℕ} (hk : k ≤ 82)
    (hT : T ≤ 2 ^ k) (I : L.Interp) (x : QuantumComp L (spongeSpec X Z) W A)
    (hx : x.IsTotalQueryBound T) (ρ : SubState A) :
    (spongeCompressedRuntime X Z).eventWeight I (dbsProjector (PreimageBad π out y0)) x
        (ρ.matrix ⊗ₖ (spongeCompressedRuntime X Z).init.matrix) ≤ 2 ^ (2 * k) / 2 ^ 253 :=
  (eventWeight_spongeCompressedRuntime_le _ (upClosed_preimageBad y0)
    (not_mem_preimageBad_emptyDbs y0) (freshBound_preimageBad hπ hF y0 T) I x hx ρ).trans
    (keccak_preimage_weight_le hX hZ hk hT)

end Event

/-! ## Concrete Keccak-256 types -/

/-- The 1088-bit rate part of Keccak-256. -/
abbrev KeccakRate : Type := Fin 1088 → ZMod 2

/-- The 512-bit capacity part of Keccak-256. -/
abbrev KeccakCapacity : Type := Fin 512 → ZMod 2

/-- The Keccak-256 output: the first 256 bits of the rate part. -/
def keccakOut (x : KeccakRate) : Fin 256 → ZMod 2 := fun i ↦ x (Fin.castAdd 832 i)

theorem card_keccakRate : Fintype.card KeccakRate = 2 ^ 1088 := by
  simp only [Fintype.card_fun, ZMod.card, Fintype.card_fin]

theorem card_keccakCapacity : Fintype.card KeccakCapacity = 2 ^ 512 := by
  simp only [Fintype.card_fun, ZMod.card, Fintype.card_fin]

/-- Each output has `2^832` preimages: split the rate into its first 256 and last 832 bits. -/
theorem card_keccakOut_fiber (y : Fin 256 → ZMod 2) :
    #(univ.filter fun x : KeccakRate ↦ keccakOut x = y) = 2 ^ 832 := by
  calc #(univ.filter fun x : KeccakRate ↦ keccakOut x = y)
      = #(univ.filter fun p : (Fin 256 → ZMod 2) × (Fin 832 → ZMod 2) ↦ p.1 = y) :=
        card_equiv (Fin.appendEquiv (α := ZMod 2) 256 832).symm fun x ↦ by
          simp only [mem_filter, mem_univ, true_and]
          rfl
    _ = Fintype.card (Fin 832 → ZMod 2) := card_filter_fst_eq y
    _ = 2 ^ 832 := by simp only [Fintype.card_fun, ZMod.card, Fintype.card_fin]

/-- At the concrete types, a uniform permutation fails `PermGood π 18` with probability at most
`2^-777`. -/
theorem keccak256_prob_not_permGood :
    (#(univ.filter fun π : Equiv.Perm (KeccakRate × KeccakCapacity) ↦ ¬PermGood π 18) : ℝ) /
        Fintype.card (Equiv.Perm (KeccakRate × KeccakCapacity)) ≤ 1 / 2 ^ 777 :=
  prob_not_permGood_keccak card_keccakRate card_keccakCapacity

section Concrete

variable {L : LocalSig.{u, v}} {W : QReg → Type w} {A : QReg}

open scoped Classical in
/-- **Keccak-256 collisions.** A program of `T ≤ 2^63` calls, for `π` with `PermGood π 18`, ends
with its compressed database bad or holding a collision of the 256-bit output with weight at most
`2^-64`. -/
theorem keccak256_eventWeight_collisionBad_le {π : Equiv.Perm (KeccakRate × KeccakCapacity)}
    (hπ : PermGood π 18) {T : ℕ} (hT : T ≤ 2 ^ 63) (I : L.Interp)
    (x : QuantumComp L (spongeSpec KeccakRate KeccakCapacity) W A) (hx : x.IsTotalQueryBound T)
    (ρ : SubState A) :
    (spongeCompressedRuntime KeccakRate KeccakCapacity).eventWeight I
        (dbsProjector (CollisionBad π keccakOut)) x
        (ρ.matrix ⊗ₖ (spongeCompressedRuntime KeccakRate KeccakCapacity).init.matrix) ≤
      (2 ^ 64)⁻¹ :=
  (eventWeight_spongeCompressedRuntime_le _ upClosed_collisionBad not_mem_collisionBad_emptyDbs
    (freshBound_collisionBad hπ (fun y ↦ (card_keccakOut_fiber y).le) T) I x hx ρ).trans
    (keccak_collision_weight_le_two_pow_63 card_keccakRate card_keccakCapacity hT)

open scoped Classical in
/-- **Keccak-256 preimages.** A program of `T ≤ 2^64` calls, for `π` with `PermGood π 18`, ends
with its compressed database bad or holding a path to `y0` with weight at most `2^-125`. -/
theorem keccak256_eventWeight_preimageBad_le {π : Equiv.Perm (KeccakRate × KeccakCapacity)}
    (hπ : PermGood π 18) (y0 : Fin 256 → ZMod 2) {T : ℕ} (hT : T ≤ 2 ^ 64) (I : L.Interp)
    (x : QuantumComp L (spongeSpec KeccakRate KeccakCapacity) W A) (hx : x.IsTotalQueryBound T)
    (ρ : SubState A) :
    (spongeCompressedRuntime KeccakRate KeccakCapacity).eventWeight I
        (dbsProjector (PreimageBad π keccakOut y0)) x
        (ρ.matrix ⊗ₖ (spongeCompressedRuntime KeccakRate KeccakCapacity).init.matrix) ≤
      (2 ^ 125)⁻¹ :=
  (eventWeight_spongeCompressedRuntime_le _ (upClosed_preimageBad y0)
    (not_mem_preimageBad_emptyDbs y0)
    (freshBound_preimageBad hπ (fun y ↦ by convert (card_keccakOut_fiber y).le) y0 T) I x hx
    ρ).trans
    (keccak_preimage_weight_le_two_pow_64 card_keccakRate card_keccakCapacity hT)

end Concrete

end Quantum.Sponge

end
