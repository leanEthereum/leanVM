import SphincsSecurity.Scheme

/-!
# A search that beats its own odds

The signer's searches are long: `2 ^ 32` trials, each accepted with probability at least `2 ^ -14`.
What that buys is stated here, in the elementary form the bound needs. A trial rejected with
probability at most `1 - 1/m` leaves at most `1/2` after `m` trials, because `(1-a)(1+a) ≤ 1` caps
the product while Bernoulli's inequality puts `(1+a)^m` above `1 + m a = 2`.

Repeating the halving is what turns a per-trial edge into the exponentially small failure the
specification's `2 ^ -256` needs.
-/

namespace SphincsSecurity.Completeness

/-- `m` trials, each rejected with probability at most `1 - 1/m`, all reject with probability at most `1/2`. -/
theorem pow_le_half (m : Nat) (hm : 0 < m) (x : ℝ) (hx0 : 0 ≤ x) (hx : x ≤ 1 - (m : ℝ)⁻¹) :
    x ^ m ≤ 1 / 2 := by
  have hmpos : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have ha0 : (0 : ℝ) ≤ (m : ℝ)⁻¹ := by positivity
  have ha1 : (m : ℝ)⁻¹ ≤ 1 := by
    rw [inv_le_one_iff₀]
    right
    exact_mod_cast hm
  set a := (m : ℝ)⁻¹ with hadef
  have hmono : x ^ m ≤ (1 - a) ^ m := by
    apply pow_le_pow_left₀ hx0 hx
  refine le_trans hmono ?_
  set X := (1 - a) ^ m with hXdef
  set Y := (1 + a) ^ m with hYdef
  have hnonneg : (0 : ℝ) ≤ X := by
    rw [hXdef]
    apply pow_nonneg
    linarith
  have hprod : X * Y ≤ 1 := by
    rw [hXdef, hYdef, ← mul_pow]
    have hle : (1 - a) * (1 + a) ≤ 1 := by nlinarith
    have hnn : (0 : ℝ) ≤ (1 - a) * (1 + a) := by nlinarith
    exact pow_le_one₀ hnn hle
  have h2 : (2 : ℝ) ≤ Y := by
    have hbern : 1 + (m : ℝ) * a ≤ (1 + a) ^ m := one_add_mul_le_pow (by linarith) m
    have hma : (m : ℝ) * a = 1 := by
      rw [hadef]
      field_simp
    rw [hma] at hbern
    rw [hYdef]
    linarith
  have hstep : X * 2 ≤ X * Y := mul_le_mul_of_nonneg_left h2 hnonneg
  have hhalf : X * 2 ≤ 1 := le_trans hstep hprod
  linarith

/-- The same statement for probabilities: a rejection share with room for `1/m` leaves at most `1/2` after `m` trials. -/
theorem pow_le_half_ennreal (m : Nat) (hm : 0 < m) (x : ENNReal)
    (hx : x + (m : ENNReal)⁻¹ ≤ 1) : x ^ m ≤ 2⁻¹ := by
  have hx1 : x ≤ 1 := le_trans le_self_add hx
  have hxtop : x ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hx1
  have hminv : (m : ENNReal)⁻¹ ≠ ⊤ := by
    simpa using (Nat.pos_iff_ne_zero.mp hm)
  have hreal : x.toReal ≤ 1 - (m : ℝ)⁻¹ := by
    have h := ENNReal.toReal_mono ENNReal.one_ne_top hx
    rw [ENNReal.toReal_add hxtop hminv, ENNReal.toReal_inv, ENNReal.toReal_natCast,
      ENNReal.toReal_one] at h
    linarith
  have hhalf := pow_le_half m hm x.toReal ENNReal.toReal_nonneg hreal
  rw [← ENNReal.ofReal_toReal (ENNReal.pow_ne_top hxtop), ENNReal.toReal_pow]
  calc ENNReal.ofReal (x.toReal ^ m) ≤ ENNReal.ofReal (1 / 2) := ENNReal.ofReal_le_ofReal hhalf
    _ = 2⁻¹ := by rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num)]; simp

/-! ## The closing numbers

Every quantity below is a power of `2⁻¹`, so the comparisons are monotonicity in the exponent and the
identity `2⁻¹ + 2⁻¹ = 1`, never an evaluation of `2 ^ (2 ^ 21)`. -/

theorem inv_two_pow_succ_add (k : Nat) :
    (2⁻¹ : ENNReal) ^ (k + 1) + (2⁻¹ : ENNReal) ^ (k + 1) = (2⁻¹ : ENNReal) ^ k := by
  rw [pow_succ, ← mul_add, ENNReal.inv_two_add_inv_two, mul_one]

theorem inv_two_pow_anti {j k : Nat} (h : j ≤ k) :
    (2⁻¹ : ENNReal) ^ k ≤ (2⁻¹ : ENNReal) ^ j :=
  pow_le_pow_right_of_le_one' (by norm_num) h

theorem two_pow_div_two_pow (j k : Nat) :
    (2 : ENNReal) ^ j / (2 : ENNReal) ^ (j + k) = (2⁻¹ : ENNReal) ^ k := by
  rw [pow_add, ENNReal.div_eq_inv_mul, ENNReal.mul_inv (Or.inl (by simp)) (Or.inl (by simp)),
    mul_comm ((2 : ENNReal) ^ j)⁻¹, mul_assoc, ENNReal.inv_mul_cancel (by simp) (by simp), mul_one,
    ENNReal.inv_pow]

/-- A per-trial rejection share of `1 - 2⁻¹⁰` plus a `2 ^ 32 / 2 ^ 128` collision share still leaves room for `2⁻¹¹`. -/
theorem digest_room (x : ENNReal) (hx : x + (1024 : ENNReal)⁻¹ = 1) :
    x + (2 : ENNReal) ^ 32 / (2 : ENNReal) ^ 128 + ((2 ^ 11 : Nat) : ENNReal)⁻¹ ≤ 1 := by
  have hcoll : (2 : ENNReal) ^ 32 / (2 : ENNReal) ^ 128 = (2⁻¹ : ENNReal) ^ 96 := by
    rw [show (128 : Nat) = 32 + 96 from rfl, two_pow_div_two_pow]
  have h11 : ((2 ^ 11 : Nat) : ENNReal)⁻¹ = (2⁻¹ : ENNReal) ^ 11 := by
    rw [Nat.cast_pow, Nat.cast_ofNat, ENNReal.inv_pow]
  have h10 : (1024 : ENNReal)⁻¹ = (2⁻¹ : ENNReal) ^ 10 := by
    rw [show (1024 : ENNReal) = 2 ^ 10 by norm_num, ENNReal.inv_pow]
  rw [hcoll, h11, add_assoc, ← hx, h10]
  refine add_le_add le_rfl ?_
  calc (2⁻¹ : ENNReal) ^ 96 + (2⁻¹ : ENNReal) ^ 11
      ≤ (2⁻¹ : ENNReal) ^ 11 + (2⁻¹ : ENNReal) ^ 11 := add_le_add (inv_two_pow_anti (by norm_num)) le_rfl
    _ = (2⁻¹ : ENNReal) ^ 10 := inv_two_pow_succ_add 10

/-- After a union bound over all `2²⁵⁶` messages, the six search failures stay below `2⁻²⁵⁶`. -/
theorem closing_sum :
    (2 : ENNReal) ^ 256 *
      ((2⁻¹ : ENNReal) ^ (2 ^ 21) + 5 * (2⁻¹ : ENNReal) ^ (2 ^ 18))
      ≤ ((2 ^ 256 : Nat) : ENNReal)⁻¹ := by
  have hcast : ((2 ^ 256 : Nat) : ENNReal)⁻¹ = (2⁻¹ : ENNReal) ^ 256 := by
    rw [Nat.cast_pow, Nat.cast_ofNat, ENNReal.inv_pow]
  have ha : (2⁻¹ : ENNReal) ^ (2 ^ 21) ≤ (2⁻¹ : ENNReal) ^ 515 := inv_two_pow_anti (by norm_num)
  have hb : (2⁻¹ : ENNReal) ^ (2 ^ 18) ≤ (2⁻¹ : ENNReal) ^ 515 := inv_two_pow_anti (by norm_num)
  have height : (2⁻¹ : ENNReal) ^ 515 + 7 * (2⁻¹ : ENNReal) ^ 515 = (2⁻¹ : ENNReal) ^ 512 := by
    have h1 := inv_two_pow_succ_add 514
    have h2 := inv_two_pow_succ_add 513
    have h3 := inv_two_pow_succ_add 512
    calc
      _ = (((2⁻¹ : ENNReal) ^ 515 + (2⁻¹ : ENNReal) ^ 515) +
          ((2⁻¹ : ENNReal) ^ 515 + (2⁻¹ : ENNReal) ^ 515)) +
          (((2⁻¹ : ENNReal) ^ 515 + (2⁻¹ : ENNReal) ^ 515) +
          ((2⁻¹ : ENNReal) ^ 515 + (2⁻¹ : ENNReal) ^ 515)) := by ring
      _ = _ := by simp only [h1, h2, h3]
  have hbound : (2⁻¹ : ENNReal) ^ (2 ^ 21) + 5 * (2⁻¹ : ENNReal) ^ (2 ^ 18) ≤
      (2⁻¹ : ENNReal) ^ 515 + 7 * (2⁻¹ : ENNReal) ^ 515 := by
    apply add_le_add ha
    exact (mul_le_mul' le_rfl hb).trans (mul_le_mul' (by norm_num) le_rfl)
  rw [hcast]
  calc
    (2 : ENNReal) ^ 256 *
          ((2⁻¹ : ENNReal) ^ (2 ^ 21) + 5 * (2⁻¹ : ENNReal) ^ (2 ^ 18))
        ≤ (2 : ENNReal) ^ 256 * (2⁻¹ : ENNReal) ^ 512 :=
          mul_le_mul_right (hbound.trans_eq height) _
    _ = (2⁻¹ : ENNReal) ^ 256 := by
      rw [← ENNReal.inv_pow, mul_comm, ← ENNReal.div_eq_inv_mul,
        show (512 : Nat) = 256 + 256 by norm_num, two_pow_div_two_pow]

end SphincsSecurity.Completeness
