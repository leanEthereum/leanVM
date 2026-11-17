module

public import Quantum.Qrom.Xmss.DepthSecurity
public import Quantum.Qrom.Xmss.BoundValue

@[expose] public section

/-!
# The size of the depth-aware leanXMSS QROM bound

DepthSecurity's `xmssQromDepthBound q d` in closed form for `q ≤ 2^100`
(`xmssQromDepthBound_le`), with `d' = min d q`:
`((4.45 √(q d') + 0.7072 · 2^-35 q + 0.523 · 2^17 √q + 0.709 · 2^33) / 2^64)²`.

* the adversary term `advTermQD q d ≤ 2.45 √(q d') 2^-64` (`advTermQD_le`, `√6 < 2.45`) and the
  hybrid `hybTermQD q d ≤ 2 √(q d') 2^-64 + 20 · 2^-64` (`hybTermQD_le`);
* the prefix's classical costs for `q ≤ 2^100` (`clsBoundQ_le_of_le_two_pow_100`): beyond
  `q = 2^64` the Enc weight times the recorded mass, `2^-199 q²` in `aR`, is no longer absorbed
  (`aR_le_of_le_two_pow_100`: `aR ≤ (0.7072 · 2^-52)² q + (0.7072 · 2^-99 q)² + 2^-255 S +
  2^-187`), which gives the term `0.7072 · 2^-35 q` (in units of `2^-64`);
* the verification terms as in BoundValue.

At `q ≤ 2^64` calls in `d ≤ 2^40` rounds the bound is at most `2^-19`
(`xmssQromDepthBound_two_pow_64_40_le`), at `q ≤ 2^80` calls in `d ≤ 2^28` rounds at most
`2^-13` (`xmssQromDepthBound_two_pow_80_28_le`); the sequential closed form exceeds `1` at
`q = 2^62`.
-/

open scoped ENNReal

namespace Quantum.Qrom.Xmss

open Quantum QuantumRuntime Quantum.Xmss.Hybrid
open LeanXmss HashSig

/-! ## The classical costs beyond `2^64` calls -/

section costs

set_option exponentiation.threshold 2048 in
/-- **The linear charge, numerically, for `q ≤ 2^100`**: `K ≤ 2^65 + 2^41` gives
`aR ≤ (0.7072 · 2^-52)² q + (0.7072 · 2^-99 q)² + 2^-255 S + 2^-187`. -/
theorem aR_le_of_le_two_pow_100 {q K S : ℕ} (hq : q ≤ 2 ^ 100) (hK : K ≤ 2 ^ 65 + 2 ^ 41) :
    aR q K S ≤ (0.7072 * (2 ^ 52)⁻¹) ^ 2 * q + (0.7072 * (2 ^ 99)⁻¹ * q) ^ 2 +
      ((2 ^ 255)⁻¹ * S + (2 ^ 187)⁻¹) := by
  have hqR : (q : ℝ) ≤ 2 ^ 100 := by exact_mod_cast hq
  have hKR : (K : ℝ) ≤ 2 ^ 65 + 2 ^ 41 := by exact_mod_cast hK
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have hqq : (0 : ℝ) ≤ q * q := mul_nonneg hq0 hq0
  have hqK : ((q + K : ℕ) : ℝ) = q + K := by push_cast; ring
  have hKq : (K : ℝ) * q ≤ (2 ^ 65 + 2 ^ 41) * q := mul_le_mul_of_nonneg_right hKR hq0
  have hKK : (K : ℝ) * K ≤ 2 ^ 66 * 2 ^ 66 :=
    mul_le_mul (by linarith) (by linarith) hK0 (by positivity)
  have hqK2 : (q : ℝ) * K ≤ 2 ^ 100 * 2 ^ 66 :=
    mul_le_mul hqR (by linarith) hK0 (by positivity)
  have hτ : ((q + K : ℕ) : ℝ) * tauR q K ≤ (2 ^ 96)⁻¹ * (q * q) + (2 ^ 30)⁻¹ * q + (2 ^ 833)⁻¹ := by
    have e : ((q + K : ℕ) : ℝ) * tauR q K = (2 ^ 96)⁻¹ * (q * q) + (2 ^ 96)⁻¹ * (K * q) +
        (2 ^ 1000)⁻¹ * (q * K) + (2 ^ 1000)⁻¹ * (K * K) := by
      rw [hqK]
      unfold tauR
      ring
    rw [e]
    linarith
  have hP : ((q + K : ℕ) : ℝ) * K ≤ 2 ^ 167 := by
    rw [hqK, add_mul]
    linarith
  have hc : (2 : ℝ) / Fintype.card HashOutput = 2 * (2 ^ 256)⁻¹ := by
    rw [card_hashOutput, Nat.cast_pow, Nat.cast_ofNat, div_eq_mul_inv]
  unfold aR
  rw [hc]
  linarith

/-- **The closed form from square bounds, with a quadratic term**: `aR ≤ c₁² q + (e q)² + a₀²`
and `pR ≤ c₂² q + p₀²` give `twBoundQ ≤ ((c₁ + c₂) √q + e q + a₀ + p₀)²`. -/
theorem twBoundQ_le_of_quad {q K S R : ℕ} {c₁ c₂ e a₀ p₀ : ℝ} (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (he : 0 ≤ e) (ha₀ : 0 ≤ a₀) (hp₀ : 0 ≤ p₀)
    (ha : aR q K S ≤ c₁ ^ 2 * q + (e * q) ^ 2 + a₀ ^ 2)
    (hp : pR q K R ≤ c₂ ^ 2 * q + p₀ ^ 2) :
    twBoundQ q K S R ≤ ENNReal.ofReal (((c₁ + c₂) * √q + e * q + a₀ + p₀) ^ 2) := by
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
  have ha' : √(aR q K S) ≤ c₁ * √q + e * q + a₀ :=
    (Real.sqrt_le_sqrt (ha.trans hquad)).trans_eq (Real.sqrt_sq (by positivity))
  have hp' := (Real.sqrt_le_sqrt hp).trans (sqrt_sq_mul_add_sq_le hc₂ hp₀ hq0)
  have hsum : √(aR q K S) + √(pR q K R) ≤ (c₁ + c₂) * √q + e * q + a₀ + p₀ := by linarith
  unfold twBoundQ
  rw [aCap_eq, pCap_eq, ENNReal.ofReal_rpow_inv_two, ENNReal.ofReal_rpow_inv_two,
    ← ENNReal.ofReal_add (Real.sqrt_nonneg _) (Real.sqrt_nonneg _),
    ← ENNReal.ofReal_pow (by positivity)]
  exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (by positivity) hsum 2)

set_option exponentiation.threshold 2048 in
/-- **The prefix's classical costs for `q ≤ 2^100`**:
`clsBoundQ q ≤ ((0.523 · 2^17 √q + 0.7072 · 2^-35 q + 0.708 · 2^33) / 2^64)²`. -/
theorem clsBoundQ_le_of_le_two_pow_100 {q : ℕ} (hq : q ≤ 2 ^ 100) :
    clsBoundQ q ≤ ENNReal.ofReal
      (((0.523 * 2 ^ 17 * √(q : ℝ) + 0.7072 * (2 ^ 35)⁻¹ * q + 0.708 * 2 ^ 33) / 2 ^ 64) ^ 2) := by
  have hSR : (clsCapQ : ℝ) ≤ 2 ^ 65 + 2 ^ 41 := by exact_mod_cast clsCapQ_le
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hs0 := Real.sqrt_nonneg (q : ℝ)
  refine (twBoundQ_le_of_quad (c₁ := 0.7072 * (2 ^ 52)⁻¹) (c₂ := (2 ^ 48)⁻¹)
    (e := 0.7072 * (2 ^ 99)⁻¹) (a₀ := (2 ^ 93)⁻¹) (p₀ := 0.7072 * (2 ^ 31)⁻¹) (by positivity)
    (by positivity) (by positivity) (by positivity) (by positivity)
    ((aR_le_of_le_two_pow_100 hq clsCapQ_le).trans ?_) ((pR_le clsCapQ_le).trans ?_)).trans ?_
  · linarith
  · linarith
  · refine ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (by positivity) ?_ 2)
    rw [le_div_iff₀ (by positivity)]
    nlinarith

end costs

/-! ## The terms with rounds -/

section terms

set_option exponentiation.threshold 1100

/-- **The adversary term with rounds**: `advTermQD q d ≤ 2.45 √(q · min d q) 2^-64`. -/
theorem advTermQD_le (q d : ℕ) :
    advTermQD q d ≤ ENNReal.ofReal (2.45 * √((q : ℝ) * (min d q : ℕ)) / 2 ^ 64) := by
  have hX : (0 : ℝ) ≤ (q : ℝ) * (min d q : ℕ) := by positivity
  refine rpow_inv_two_le_ofRealQ (r := 6 * ((q : ℝ) * (min d q : ℕ)) / 2 ^ 128) (by positivity)
    ?_ ?_
  · simp (disch := positivity) only [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_ofNat,
      ← ENNReal.ofReal_pow, ← ENNReal.ofReal_inv_of_pos, ← ENNReal.ofReal_mul]
    exact ENNReal.ofReal_le_ofReal (le_of_eq (by ring))
  · calc 6 * ((q : ℝ) * (min d q : ℕ)) / 2 ^ 128
        ≤ 2.45 ^ 2 * ((q : ℝ) * (min d q : ℕ)) / 2 ^ 128 := by gcongr; norm_num
      _ = (2.45 * √((q : ℝ) * (min d q : ℕ)) / 2 ^ 64) ^ 2 := by
        rw [div_pow, mul_pow, Real.sq_sqrt hX]
        ring

/-- **The hybrid term with rounds**: `hybTermQD q d ≤ 2 √(q · min d q) 2^-64 + 20 · 2^-64`. -/
theorem hybTermQD_le (q d : ℕ) :
    hybTermQD q d ≤
      ENNReal.ofReal (2 * √((q : ℝ) * (min d q : ℕ)) / 2 ^ 64 + 20 / 2 ^ 64) := by
  have hX : (0 : ℝ) ≤ (q : ℝ) * (min d q : ℕ) := by positivity
  have hs : 4 * (((min d q : ℕ) : ℝ≥0∞) * ((q : ℝ≥0∞) * kappaQ)) ≤
      ENNReal.ofReal (4 * ((q : ℝ) * (min d q : ℕ)) / 2 ^ 128) := by
    unfold kappaQ
    simp (disch := positivity) only [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_ofNat,
      ← ENNReal.ofReal_pow, ← ENNReal.ofReal_inv_of_pos, ← ENNReal.ofReal_mul]
    exact ENNReal.ofReal_le_ofReal (le_of_eq (by ring))
  have hv : (verifyCalls : ℝ≥0∞) * kappaQ ≤ ENNReal.ofReal (384 / 2 ^ 128) := by
    unfold kappaQ
    rw [verifyCalls_eq]
    simp (disch := positivity) only [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_ofNat,
      ← ENNReal.ofReal_pow, ← ENNReal.ofReal_inv_of_pos, ← ENNReal.ofReal_mul]
    exact ENNReal.ofReal_le_ofReal (by norm_num)
  unfold hybTermQD
  rw [ENNReal.ofReal_add (by positivity) (by positivity)]
  refine add_le_add (rpow_inv_two_le_ofRealQ (by positivity) hs (le_of_eq ?_))
    (rpow_inv_two_le_ofRealQ (by positivity) hv (by norm_num))
  rw [div_pow, mul_pow, Real.sq_sqrt hX]
  ring

/-- **The square-rooted event term with rounds**: for `q ≤ 2^100`. -/
theorem eventTermQD_rpow_le {q d : ℕ} (hq : q ≤ 2 ^ 100) :
    eventTermQD q d ^ (2⁻¹ : ℝ) ≤ ENNReal.ofReal (2.45 * √((q : ℝ) * (min d q : ℕ)) / 2 ^ 64 +
      384 / 2 ^ 64 + ((0.523 * 2 ^ 17 * √(q : ℝ) + 0.7072 * (2 ^ 35)⁻¹ * q + 0.708 * 2 ^ 33) /
        2 ^ 64 + 20 / 2 ^ 64) + 1 / 2 ^ 120) := by
  have hr := rpow_inv_two_le_ofRealQ (a := 1 / 2 ^ 120) (by positivity) readErrQ_le
    (by norm_num)
  have hc := rpow_inv_two_le_ofRealQ (by positivity) (clsBoundQ_le_of_le_two_pow_100 hq) le_rfl
  have hv := rpow_inv_two_le_ofRealQ (a := 20 / 2 ^ 64) (by positivity) verLinQ_le
    (by norm_num)
  have hcv : (clsBoundQ q + verLinQ) ^ (2⁻¹ : ℝ) ≤
      ENNReal.ofReal ((0.523 * 2 ^ 17 * √(q : ℝ) + 0.7072 * (2 ^ 35)⁻¹ * q + 0.708 * 2 ^ 33) /
        2 ^ 64 + 20 / 2 ^ 64) := by
    rw [ENNReal.ofReal_add (by positivity) (by positivity)]
    exact (ENNReal.rpow_add_le_add_rpow _ _ (by norm_num) (by norm_num)).trans
      (add_le_add hc hv)
  unfold eventTermQD
  refine (sq_add_rpow_inv_two_leQ _ _).trans ((add_le_add (add_le_add (add_le_add
    (advTermQD_le q d) verTermQ_le) hcv) hr).trans_eq ?_)
  rw [← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]

end terms

/-! ## The closed form -/

section closed

/-- The arithmetic of the closed form. -/
theorem root_le_closedQD (q d : ℕ) :
    2.45 * √((q : ℝ) * (min d q : ℕ)) / 2 ^ 64 + 384 / 2 ^ 64 +
      ((0.523 * 2 ^ 17 * √(q : ℝ) + 0.7072 * (2 ^ 35)⁻¹ * q + 0.708 * 2 ^ 33) / 2 ^ 64 +
        20 / 2 ^ 64) + 1 / 2 ^ 120 +
      (2 * √((q : ℝ) * (min d q : ℕ)) / 2 ^ 64 + 20 / 2 ^ 64) ≤
      (4.45 * √((q : ℝ) * (min d q : ℕ)) + 0.7072 * (2 ^ 35)⁻¹ * q +
        0.523 * 2 ^ 17 * √(q : ℝ) + 0.709 * 2 ^ 33) / 2 ^ 64 := by
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hs0 := Real.sqrt_nonneg (q : ℝ)
  have hd0 := Real.sqrt_nonneg ((q : ℝ) * (min d q : ℕ))
  linarith

/-- **The depth-aware leanXMSS QROM bound in closed form**: for `q ≤ 2^100` calls of `H` in `d`
rounds, `xmssQromDepthBound q d ≤
((4.45 √(q · min d q) + 0.7072 · 2^-35 q + 0.523 · 2^17 √q + 0.709 · 2^33) / 2^64)²`. -/
theorem xmssQromDepthBound_le {q d : ℕ} (hq : q ≤ 2 ^ 100) :
    xmssQromDepthBound q d ≤ ENNReal.ofReal (((4.45 * √((q : ℝ) * (min d q : ℕ)) +
      0.7072 * (2 ^ 35)⁻¹ * q + 0.523 * 2 ^ 17 * √(q : ℝ) + 0.709 * 2 ^ 33) / 2 ^ 64) ^ 2) := by
  have h1 := eventTermQD_rpow_le (d := d) hq
  have h2 := hybTermQD_le q d
  rw [ENNReal.ofReal_pow (by positivity)]
  unfold xmssQromDepthBound
  refine pow_le_pow_left₀ zero_le ((add_le_add h1 h2).trans ?_) 2
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  exact ENNReal.ofReal_le_ofReal (root_le_closedQD q d)

/-- The square roots of the closed form under bounds on `q` and the rounds. -/
theorem sqrt_le_of_le_two_pow {x : ℝ} {k : ℕ} (hx : x ≤ 2 ^ (2 * k)) : √x ≤ 2 ^ k :=
  (Real.sqrt_le_sqrt hx).trans_eq (by rw [pow_mul', Real.sqrt_sq (by positivity)])

set_option exponentiation.threshold 1100 in
/-- **At most `2^64` calls in at most `2^40` rounds** (NIST's MAXDEPTH `2^40`):
`xmssQromDepthBound q d ≤ 2^-19`. -/
theorem xmssQromDepthBound_two_pow_64_40_le {q d : ℕ} (hq : q ≤ 2 ^ 64) (hd : d ≤ 2 ^ 40) :
    xmssQromDepthBound q d ≤ (2 ^ 19 : ℝ≥0∞)⁻¹ := by
  have hq' : (q : ℝ) ≤ 2 ^ 64 := by exact_mod_cast hq
  have hd' : ((min d q : ℕ) : ℝ) ≤ 2 ^ 40 := by exact_mod_cast (min_le_left d q).trans hd
  have hX : (q : ℝ) * (min d q : ℕ) ≤ 2 ^ (2 * 52) :=
    (mul_le_mul hq' hd' (Nat.cast_nonneg _) (by positivity)).trans_eq (by norm_num)
  have hs : √(q : ℝ) ≤ 2 ^ 32 := sqrt_le_of_le_two_pow (hq'.trans_eq (by norm_num))
  have hsX : √((q : ℝ) * (min d q : ℕ)) ≤ 2 ^ 52 := sqrt_le_of_le_two_pow hX
  refine (xmssQromDepthBound_le (hq.trans (by norm_num))).trans ?_
  rw [inv_two_pow_eq_ofRealQ]
  refine ENNReal.ofReal_le_ofReal ?_
  calc ((4.45 * √((q : ℝ) * (min d q : ℕ)) + 0.7072 * (2 ^ 35)⁻¹ * q +
        0.523 * 2 ^ 17 * √(q : ℝ) + 0.709 * 2 ^ 33) / 2 ^ 64) ^ 2
      ≤ ((4.45 * 2 ^ 52 + 0.7072 * (2 ^ 35)⁻¹ * 2 ^ 64 + 0.523 * 2 ^ 17 * 2 ^ 32 +
          0.709 * 2 ^ 33) / 2 ^ 64) ^ 2 := by gcongr
    _ ≤ 1 / 2 ^ 19 := by norm_num

set_option exponentiation.threshold 1100 in
/-- **At most `2^80` calls in at most `2^28` rounds** (MAXDEPTH `2^40` at a Keccak depth of
`2^12`): `xmssQromDepthBound q d ≤ 2^-13`. -/
theorem xmssQromDepthBound_two_pow_80_28_le {q d : ℕ} (hq : q ≤ 2 ^ 80) (hd : d ≤ 2 ^ 28) :
    xmssQromDepthBound q d ≤ (2 ^ 13 : ℝ≥0∞)⁻¹ := by
  have hq' : (q : ℝ) ≤ 2 ^ 80 := by exact_mod_cast hq
  have hd' : ((min d q : ℕ) : ℝ) ≤ 2 ^ 28 := by exact_mod_cast (min_le_left d q).trans hd
  have hX : (q : ℝ) * (min d q : ℕ) ≤ 2 ^ (2 * 54) :=
    (mul_le_mul hq' hd' (Nat.cast_nonneg _) (by positivity)).trans_eq (by norm_num)
  have hs : √(q : ℝ) ≤ 2 ^ 40 := sqrt_le_of_le_two_pow (hq'.trans_eq (by norm_num))
  have hsX : √((q : ℝ) * (min d q : ℕ)) ≤ 2 ^ 54 := sqrt_le_of_le_two_pow hX
  refine (xmssQromDepthBound_le (hq.trans (by norm_num))).trans ?_
  rw [inv_two_pow_eq_ofRealQ]
  refine ENNReal.ofReal_le_ofReal ?_
  calc ((4.45 * √((q : ℝ) * (min d q : ℕ)) + 0.7072 * (2 ^ 35)⁻¹ * q +
        0.523 * 2 ^ 17 * √(q : ℝ) + 0.709 * 2 ^ 33) / 2 ^ 64) ^ 2
      ≤ ((4.45 * 2 ^ 54 + 0.7072 * (2 ^ 35)⁻¹ * 2 ^ 80 + 0.523 * 2 ^ 17 * 2 ^ 40 +
          0.709 * 2 ^ 33) / 2 ^ 64) ^ 2 := by gcongr
    _ ≤ 1 / 2 ^ 13 := by norm_num

end closed

end Quantum.Qrom.Xmss

end
