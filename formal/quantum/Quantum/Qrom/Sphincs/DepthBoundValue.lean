module

public import Quantum.Qrom.Sphincs.DepthBound
public import Quantum.Qrom.Sphincs.BoundValue
public import Quantum.Qrom.Xmss.DepthBoundValue

@[expose] public section

/-!
# The size of the depth-aware leanSPHINCS QROM bound

DepthBound's `sphincsQromDepthBound q d` in closed form for every `q` (`sphincsQromDepthBound_le`),
with `d' = min d q`:
`((5.86 √(q d') + 2^-55 q + 257.3 √q + 1.818 · 2^32) / 2^64)²`.

* the averaged adversary term `advBarQD q d ≤ 3.852 √(q d') 2^-64` (`advBarQD_le`,
  `√(6 · 2.4726) < 3.852`) and the hybrid `hybTermQD q d ≤ 2 √(q d') 2^-64 + 0.9087 · 2^32 · 2^-64`
  (`hybTermQD_le`);
* the prefix's classical costs for every `q` (`clsBoundQ_le_quad`): beyond `q = 2^64` the Enc
  weight times the recorded mass, `2^-127 · 2^15 · 4 q · q 2^-128 = 2^-238 q²` in `aCap`, is no
  longer absorbed (`aRS_one_le_quad`: `aCap ≤ (1.001 · 2^-56)² q + (2^-119 q)² + 2^-178`), which
  gives the term `2^-55 q` (in units of `2^-64`); every other part of `aCap` and `pCap` only needs
  the classical calls `clsCapQ ≤ 0.826 · 2^64`, so no bound on `q` is needed;
* the verification terms and the read error as in BoundValue.

At `q ≤ 2^64` calls in `d ≤ 2^40` rounds the bound is at most `2^-18`
(`sphincsQromDepthBound_two_pow_64_40_le`), at `q ≤ 2^80` calls in `d ≤ 2^28` rounds at most
`2^-14` (`sphincsQromDepthBound_two_pow_80_28_le`).
-/

open scoped ENNReal
open Sphincs (signatureLimit)

namespace Quantum.Qrom.Sphincs

open Quantum QuantumRuntime Quantum.Xmss.Hybrid
open Quantum.Qrom.Xmss (rpow_inv_two_le_ofRealQ sq_add_rpow_inv_two_leQ inv_two_pow_eq_ofRealQ
  sqrt_le_of_le_two_pow)

/-! ## The classical costs beyond `2^64` calls -/

section costs

set_option exponentiation.threshold 2048 in
/-- **The linear charge, numerically, for every `q`**: with `K ≤ 0.826 · 2^64` classical calls,
`aRS 1 q K ≤ (1.001 · 2^-56)² q + (2^-119 q)² + (2^-89)²`. -/
theorem aRS_one_le_quad {q K : ℕ} (hK : (K : ℝ) ≤ 0.826 * 2 ^ 64) :
    aRS 1 q K ≤ (1.001 * (2 ^ 56)⁻¹) ^ 2 * q + ((2 ^ 119)⁻¹ * q) ^ 2 + ((2 ^ 89)⁻¹) ^ 2 := by
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have hKq : (K : ℝ) * q ≤ (0.826 * 2 ^ 64) * q := mul_le_mul_of_nonneg_right hK hq0
  have hKK : (K : ℝ) * K ≤ 2 ^ 64 * 2 ^ 64 :=
    mul_le_mul (by linarith) (by linarith) hK0 (by positivity)
  have hc : (2 : ℝ) / Fintype.card PairOut = 2 * (2 ^ 512)⁻¹ := by
    rw [card_pairOut_real, div_eq_mul_inv]
    norm_num
  have e : aRS 1 q K = (2 ^ 112)⁻¹ * q + (2 ^ 238)⁻¹ * (q * q) +
      ((2 ^ 238)⁻¹ + (2 ^ 310)⁻¹ + (2 ^ 622)⁻¹) * (K * q) +
      ((2 ^ 310)⁻¹ + (2 ^ 622)⁻¹) * (K * K) + ((2 ^ 255)⁻¹ + (2 ^ 511)⁻¹) * K := by
    unfold aRS
    rw [hc]
    push_cast
    ring
  rw [e]
  nlinarith

/-- **The closed form from square bounds, with a quadratic term**: `aCap ≤ c₁² q + (e q)² + a₀²`
and `pCap ≤ c₂² q + p₀²` give `twBoundQ ≤ ((c₁ + c₂) √q + e q + a₀ + p₀)²`. -/
theorem twBoundQ_le_of_quad {cE εE τ : ℝ≥0∞} {q K Sl R : ℕ} {c₁ c₂ e a₀ p₀ : ℝ} (hc₁ : 0 ≤ c₁)
    (hc₂ : 0 ≤ c₂) (he : 0 ≤ e) (ha₀ : 0 ≤ a₀) (hp₀ : 0 ≤ p₀)
    (ha : aCap cE εE q K τ Sl ≤ ENNReal.ofReal (c₁ ^ 2 * q + (e * q) ^ 2 + a₀ ^ 2))
    (hp : pCap τ R ≤ ENNReal.ofReal (c₂ ^ 2 * q + p₀ ^ 2)) :
    twBoundQ cE εE q K τ Sl R ≤ ENNReal.ofReal (((c₁ + c₂) * √q + e * q + a₀ + p₀) ^ 2) := by
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hs0 := Real.sqrt_nonneg (q : ℝ)
  have hsq := Real.sq_sqrt hq0
  have hquad : c₁ ^ 2 * q + (e * q) ^ 2 + a₀ ^ 2 ≤ (c₁ * √q + e * q + a₀) ^ 2 := by
    have h1 : 0 ≤ c₁ * √q * (e * q) := by positivity
    have h2 : 0 ≤ c₁ * √q * a₀ := by positivity
    have h3 : 0 ≤ e * q * a₀ := by positivity
    have e1 : (c₁ * √q + e * q + a₀) ^ 2 = c₁ ^ 2 * √q ^ 2 + (e * q) ^ 2 + a₀ ^ 2 +
        2 * (c₁ * √q * (e * q)) + 2 * (c₁ * √q * a₀) + 2 * (e * q * a₀) := by
      ring
    rw [e1, hsq]
    linarith
  have ha' : aCap cE εE q K τ Sl ^ (2⁻¹ : ℝ) ≤ ENNReal.ofReal (c₁ * √q + e * q + a₀) :=
    rpow_inv_two_le_ofRealQ (by positivity) ha hquad
  have hp' : pCap τ R ^ (2⁻¹ : ℝ) ≤ ENNReal.ofReal (c₂ * √q + p₀) := by
    refine (ENNReal.rpow_le_rpow hp (by norm_num)).trans ?_
    rw [ENNReal.ofReal_rpow_inv_two]
    exact ENNReal.ofReal_le_ofReal (sqrt_sq_mul_add_sq_le' hc₂ hp₀ hq0)
  unfold twBoundQ
  refine (pow_le_pow_left₀ zero_le (add_le_add ha' hp') 2).trans ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_pow (by positivity)]
  exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (by positivity) (le_of_eq (by ring)) 2)

set_option exponentiation.threshold 2048 in
/-- **The prefix's classical costs for every `q`**:
`clsBoundQ q ≤ ((257.3 √q + 2^-55 q + 0.909 · 2^32) / 2^64)²`. -/
theorem clsBoundQ_le_quad (q : ℕ) :
    clsBoundQ q ≤ ENNReal.ofReal
      (((257.3 * √(q : ℝ) + (2 ^ 55)⁻¹ * q + 0.909 * 2 ^ 32) / 2 ^ 64) ^ 2) := by
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hs0 := Real.sqrt_nonneg (q : ℝ)
  have hτ : tauU q clsCapQ ≤ tauS 1 q clsCapQ := tauU_le q clsCapQ
  have hmono : clsBoundQ q ≤
      twBoundQ encC encEps q clsCapQ (tauS 1 q clsCapQ) clsCapQ clsCapQ := by
    unfold clsBoundQ twBoundQ aCap encCap pCap
    gcongr
  refine hmono.trans ((twBoundQ_le_of_quad (c₁ := 1.001 * (2 ^ 56)⁻¹) (c₂ := (2 ^ 64)⁻¹)
    (e := (2 ^ 119)⁻¹) (a₀ := (2 ^ 89)⁻¹) (p₀ := 0.9089 * (2 ^ 32)⁻¹) (by positivity)
    (by positivity) (by positivity) (by positivity) (by positivity) ?_ ?_).trans ?_)
  · rw [aCap_tauS_eq]
    exact ENNReal.ofReal_le_ofReal (aRS_one_le_quad clsCapQ_le)
  · rw [pCap_tauS_eq]
    refine ENNReal.ofReal_le_ofReal ((pRS_le (cU := 1) (q := q) clsCapQ_le).trans_eq ?_)
    rw [Nat.cast_one, Real.sqrt_one, one_mul]
  · refine ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (by positivity) ?_ 2)
    rw [le_div_iff₀ (by positivity)]
    nlinarith

end costs

/-! ## The terms with rounds -/

section terms

set_option exponentiation.threshold 1100

/-- **The averaged adversary term with rounds**: `advBarQD q d ≤ 3.852 √(q · min d q) 2^-64`. -/
theorem advBarQD_le (q d : ℕ) :
    advBarQD q d ≤ ENNReal.ofReal (3.852 * √((q : ℝ) * (min d q : ℕ)) / 2 ^ 64) := by
  have hX : (0 : ℝ) ≤ (q : ℝ) * (min d q : ℕ) := by positivity
  unfold advBarQD
  refine rpow_inv_two_le_ofRealQ (r := 6 * (2.4726 / 2 ^ 128) * ((q : ℝ) * (min d q : ℕ)))
    (by positivity) ?_ ?_
  · refine (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left epsBarQ_le zero_le) zero_le) zero_le).trans_eq ?_
    simp (disch := positivity) only [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_ofNat,
      ← ENNReal.ofReal_mul]
    exact congrArg ENNReal.ofReal (by ring)
  · have h : (6 : ℝ) * (2.4726 / 2 ^ 128) ≤ 3.852 ^ 2 / (2 ^ 64) ^ 2 := by norm_num
    calc 6 * (2.4726 / 2 ^ 128) * ((q : ℝ) * (min d q : ℕ))
        ≤ 3.852 ^ 2 / (2 ^ 64) ^ 2 * ((q : ℝ) * (min d q : ℕ)) :=
          mul_le_mul_of_nonneg_right h hX
      _ = (3.852 * √((q : ℝ) * (min d q : ℕ)) / 2 ^ 64) ^ 2 := by
        rw [div_pow, mul_pow, Real.sq_sqrt hX]
        ring

/-- **The hybrid term with rounds**:
`hybTermQD q d ≤ 2 √(q · min d q) 2^-64 + 0.9087 · 2^32 · 2^-64`. -/
theorem hybTermQD_le (q d : ℕ) :
    hybTermQD q d ≤ ENNReal.ofReal
      (2 * √((q : ℝ) * (min d q : ℕ)) / 2 ^ 64 + 0.9087 * 2 ^ 32 / 2 ^ 64) := by
  have hX : (0 : ℝ) ≤ (q : ℝ) * (min d q : ℕ) := by positivity
  have hs : 4 * (((min d q : ℕ) : ℝ≥0∞) * ((q : ℝ≥0∞) * kappaQ)) ≤
      ENNReal.ofReal (4 * ((q : ℝ) * (min d q : ℕ)) / 2 ^ 128) := by
    unfold kappaQ
    simp (disch := positivity) only [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_ofNat,
      ← ENNReal.ofReal_pow, ← ENNReal.ofReal_inv_of_pos, ← ENNReal.ofReal_mul]
    exact ENNReal.ofReal_le_ofReal (le_of_eq (by ring))
  have hc : (clsCapQ : ℝ≥0∞) * kappaQ ≤ ENNReal.ofReal ((clsCapQ : ℝ) / 2 ^ 128) := by
    unfold kappaQ
    simp (disch := positivity) only [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_ofNat,
      ← ENNReal.ofReal_pow, ← ENNReal.ofReal_inv_of_pos, ← ENNReal.ofReal_mul]
    exact ENNReal.ofReal_le_ofReal (le_of_eq (by ring))
  have hcap : (clsCapQ : ℝ) / 2 ^ 128 ≤ (0.9087 * 2 ^ 32 / 2 ^ 64) ^ 2 := by
    rw [clsCapQ_eq]
    simp only [signatureLimit]
    norm_num
  unfold hybTermQD
  rw [ENNReal.ofReal_add (by positivity) (by positivity)]
  refine add_le_add (rpow_inv_two_le_ofRealQ (by positivity) hs (le_of_eq ?_))
    (rpow_inv_two_le_ofRealQ (by positivity) hc hcap)
  rw [div_pow, mul_pow, Real.sq_sqrt hX]
  ring

/-- **The square-rooted event term with rounds**: `√eventTermQD q d ≤ 3.852 √(q · min d q) 2^-64 +
1383 · 2^-64 + ((257.3 √q + 2^-55 q + 0.909 · 2^32) / 2^64 + 47 · 2^-64) + 2^-120`. -/
theorem eventTermQD_rpow_le (q d : ℕ) :
    eventTermQD q d ^ (2⁻¹ : ℝ) ≤ ENNReal.ofReal (3.852 * √((q : ℝ) * (min d q : ℕ)) / 2 ^ 64 +
      1383 / 2 ^ 64 + ((257.3 * √(q : ℝ) + (2 ^ 55)⁻¹ * q + 0.909 * 2 ^ 32) / 2 ^ 64 +
        47 / 2 ^ 64) + 1 / 2 ^ 120) := by
  have hr := rpow_inv_two_le_ofRealQ (a := 1 / 2 ^ 120) (by positivity) readErrQ_le
    (by norm_num)
  have hc := rpow_inv_two_le_ofRealQ (by positivity) (clsBoundQ_le_quad q) le_rfl
  have hv := rpow_inv_two_le_ofRealQ (a := 47 / 2 ^ 64) (by positivity) verLinBarQ_le
    (by norm_num)
  have hcv : (clsBoundQ q + verLinBarQ) ^ (2⁻¹ : ℝ) ≤
      ENNReal.ofReal ((257.3 * √(q : ℝ) + (2 ^ 55)⁻¹ * q + 0.909 * 2 ^ 32) / 2 ^ 64 +
        47 / 2 ^ 64) := by
    rw [ENNReal.ofReal_add (by positivity) (by positivity)]
    exact (ENNReal.rpow_add_le_add_rpow _ _ (by norm_num) (by norm_num)).trans
      (add_le_add hc hv)
  unfold eventTermQD
  refine (sq_add_rpow_inv_two_leQ _ _).trans ((add_le_add (add_le_add (add_le_add
    (advBarQD_le q d) verBarQ_le) hcv) hr).trans_eq ?_)
  rw [← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]

end terms

/-! ## The closed form -/

section closed

/-- The arithmetic of the closed form. -/
theorem root_le_closedQD (q d : ℕ) :
    3.852 * √((q : ℝ) * (min d q : ℕ)) / 2 ^ 64 + 1383 / 2 ^ 64 +
      ((257.3 * √(q : ℝ) + (2 ^ 55)⁻¹ * q + 0.909 * 2 ^ 32) / 2 ^ 64 + 47 / 2 ^ 64) +
        1 / 2 ^ 120 +
      (2 * √((q : ℝ) * (min d q : ℕ)) / 2 ^ 64 + 0.9087 * 2 ^ 32 / 2 ^ 64) ≤
      (5.86 * √((q : ℝ) * (min d q : ℕ)) + (2 ^ 55)⁻¹ * q + 257.3 * √(q : ℝ) +
        1.818 * 2 ^ 32) / 2 ^ 64 := by
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hs0 := Real.sqrt_nonneg (q : ℝ)
  have hd0 := Real.sqrt_nonneg ((q : ℝ) * (min d q : ℕ))
  linarith

/-- **The depth-aware leanSPHINCS QROM bound in closed form**: for `q` calls of `H` in `d`
rounds, `sphincsQromDepthBound q d ≤
((5.86 √(q · min d q) + 2^-55 q + 257.3 √q + 1.818 · 2^32) / 2^64)²`. -/
theorem sphincsQromDepthBound_le (q d : ℕ) :
    sphincsQromDepthBound q d ≤ ENNReal.ofReal (((5.86 * √((q : ℝ) * (min d q : ℕ)) +
      (2 ^ 55)⁻¹ * q + 257.3 * √(q : ℝ) + 1.818 * 2 ^ 32) / 2 ^ 64) ^ 2) := by
  have h1 := eventTermQD_rpow_le q d
  have h2 := hybTermQD_le q d
  rw [ENNReal.ofReal_pow (by positivity)]
  unfold sphincsQromDepthBound
  refine pow_le_pow_left₀ zero_le ((add_le_add h1 h2).trans ?_) 2
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  exact ENNReal.ofReal_le_ofReal (root_le_closedQD q d)

set_option exponentiation.threshold 1100 in
/-- **At most `2^64` calls in at most `2^40` rounds** (NIST's MAXDEPTH `2^40`):
`sphincsQromDepthBound q d ≤ 2^-18`. -/
theorem sphincsQromDepthBound_two_pow_64_40_le {q d : ℕ} (hq : q ≤ 2 ^ 64) (hd : d ≤ 2 ^ 40) :
    sphincsQromDepthBound q d ≤ (2 ^ 18 : ℝ≥0∞)⁻¹ := by
  have hq' : (q : ℝ) ≤ 2 ^ 64 := by exact_mod_cast hq
  have hd' : ((min d q : ℕ) : ℝ) ≤ 2 ^ 40 := by exact_mod_cast (min_le_left d q).trans hd
  have hX : (q : ℝ) * (min d q : ℕ) ≤ 2 ^ (2 * 52) :=
    (mul_le_mul hq' hd' (Nat.cast_nonneg _) (by positivity)).trans_eq (by norm_num)
  have hs : √(q : ℝ) ≤ 2 ^ 32 := sqrt_le_of_le_two_pow (hq'.trans_eq (by norm_num))
  have hsX : √((q : ℝ) * (min d q : ℕ)) ≤ 2 ^ 52 := sqrt_le_of_le_two_pow hX
  refine (sphincsQromDepthBound_le q d).trans ?_
  rw [inv_two_pow_eq_ofRealQ]
  refine ENNReal.ofReal_le_ofReal ?_
  calc ((5.86 * √((q : ℝ) * (min d q : ℕ)) + (2 ^ 55)⁻¹ * q + 257.3 * √(q : ℝ) +
        1.818 * 2 ^ 32) / 2 ^ 64) ^ 2
      ≤ ((5.86 * 2 ^ 52 + (2 ^ 55)⁻¹ * 2 ^ 64 + 257.3 * 2 ^ 32 + 1.818 * 2 ^ 32) / 2 ^ 64) ^ 2 := by
        gcongr
    _ ≤ 1 / 2 ^ 18 := by norm_num

set_option exponentiation.threshold 1100 in
/-- **At most `2^80` calls in at most `2^28` rounds** (MAXDEPTH `2^40` at a Keccak depth of
`2^12`): `sphincsQromDepthBound q d ≤ 2^-14`. -/
theorem sphincsQromDepthBound_two_pow_80_28_le {q d : ℕ} (hq : q ≤ 2 ^ 80) (hd : d ≤ 2 ^ 28) :
    sphincsQromDepthBound q d ≤ (2 ^ 14 : ℝ≥0∞)⁻¹ := by
  have hq' : (q : ℝ) ≤ 2 ^ 80 := by exact_mod_cast hq
  have hd' : ((min d q : ℕ) : ℝ) ≤ 2 ^ 28 := by exact_mod_cast (min_le_left d q).trans hd
  have hX : (q : ℝ) * (min d q : ℕ) ≤ 2 ^ (2 * 54) :=
    (mul_le_mul hq' hd' (Nat.cast_nonneg _) (by positivity)).trans_eq (by norm_num)
  have hs : √(q : ℝ) ≤ 2 ^ 40 := sqrt_le_of_le_two_pow (hq'.trans_eq (by norm_num))
  have hsX : √((q : ℝ) * (min d q : ℕ)) ≤ 2 ^ 54 := sqrt_le_of_le_two_pow hX
  refine (sphincsQromDepthBound_le q d).trans ?_
  rw [inv_two_pow_eq_ofRealQ]
  refine ENNReal.ofReal_le_ofReal ?_
  calc ((5.86 * √((q : ℝ) * (min d q : ℕ)) + (2 ^ 55)⁻¹ * q + 257.3 * √(q : ℝ) +
        1.818 * 2 ^ 32) / 2 ^ 64) ^ 2
      ≤ ((5.86 * 2 ^ 54 + (2 ^ 55)⁻¹ * 2 ^ 80 + 257.3 * 2 ^ 40 + 1.818 * 2 ^ 32) / 2 ^ 64) ^ 2 := by
        gcongr
    _ ≤ 1 / 2 ^ 14 := by norm_num

end closed

end Quantum.Qrom.Sphincs

end
