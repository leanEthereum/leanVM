/-
The algebraic core of the descent step: note 37 Proposition 3.3, in the form of steps 1 to 4 of
section 1.2 of the referee report (note 46).

Over a field `K`, with `q = X² + a X`:

* `exists_decomp`, `decomp_unique`, `decomp`, `parts_eq`: every polynomial is uniquely
  `u₀(q) + X u₁(q)` (`part0`, `part1`).

In characteristic two:

* `comp_shift`, `invariant_iff_part1`, `invariant_iff_exists`: `P(X + a) = P + a u₁(q)`, so for
  `a ≠ 0` the polynomials unchanged by `X ↦ X + a` are those with `u₁ = 0`, the polynomials in `q`.
* `Periodic a u v`: the rational function `v / u` is unchanged by `X ↦ X + a`, cross-multiplied:
  `v(X) u(X + a) = v(X + a) u(X)`. `periodic_iff_parts`: this is `v₀ u₁ = v₁ u₀`.
* `rho a u = u / e_u(q)` with `e_u = gcd(u₀, u₁)` (`eGcd`, `rho_mul_eGcd`). It is a function of
  `a` and `u` only.
* `periodic_iff_exists`: for `a ≠ 0` and `u ≠ 0`, `v / u` has the period `a` if and only if
  `v = ϱ Q(q)` for some polynomial `Q`. `periodic_triple_iff`: the members `c` whose function
  `(c - c₀) / (c₁ - c₀)` has the period `a` are exactly `c₀ + ϱ Q(q)`, `ϱ = rho a (c₁ - c₀)`.
* `natDegree_mul_comp_qPoly`, `natDegree_rho_le`, `natDegree_le_of_descent`: the degrees,
  `deg ϱ + 2 deg Q = deg (c - c₀)`.
* `eval_descent`, `agree_iff_of_ne_zero`, `eval_eq_of_eval_rho_eq_zero`: where `ϱ(y) ≠ 0`, `c`
  takes the value `w` at `y` if and only if `Q` takes the value `(w - c₀(y)) / ϱ(y)` at `q(y)`;
  where `ϱ(y) = 0`, `c(y) = c₀(y)`.
* `Periodic.swap`, `Periodic.base_swap`, `periodic_of_const`: the property depends on the
  unordered triple only, and collinear triples have every period.
-/
import Mathlib

open Polynomial
open scoped Classical

namespace PeriodDescent

variable {K : Type*} [Field K]

/-! ### The polynomial `q = X² + a X` -/

/-- `q_a = X² + a X`. -/
noncomputable def qPoly (a : K) : K[X] := X ^ 2 + C a * X

private theorem degree_C_mul_X_lt_two (a : K) : (C a * X : K[X]).degree < ((2 : ℕ) : WithBot ℕ) :=
  lt_of_le_of_lt (degree_C_mul_X_le a) (by exact_mod_cast (by norm_num : (1 : ℕ) < 2))

theorem qPoly_monic (a : K) : (qPoly a).Monic :=
  Polynomial.monic_X_pow_add (degree_C_mul_X_lt_two a)

theorem qPoly_natDegree (a : K) : (qPoly a).natDegree = 2 := by
  unfold qPoly
  have h1 : (C a * X : K[X]).natDegree ≤ 1 := (natDegree_C_mul_le a X).trans natDegree_X_le
  rw [natDegree_add_eq_left_of_natDegree_lt (by rw [natDegree_X_pow]; omega), natDegree_X_pow]

theorem qPoly_ne_one (a : K) : qPoly a ≠ 1 := by
  intro h
  have h1 := qPoly_natDegree a
  rw [h, natDegree_one] at h1
  omega

theorem eval_qPoly (a y : K) : (qPoly a).eval y = y ^ 2 + a * y := by
  simp [qPoly]

theorem comp_qPoly_eq_zero {a : K} {P : K[X]} : P.comp (qPoly a) = 0 ↔ P = 0 := by
  constructor
  · intro h
    have h1 : (P.comp (qPoly a)).natDegree = P.natDegree * (qPoly a).natDegree := natDegree_comp
    rw [h, natDegree_zero, qPoly_natDegree] at h1
    have h2 : P.natDegree = 0 := by omega
    have h3 : P = C (P.coeff 0) := eq_C_of_natDegree_eq_zero h2
    rw [h3, C_comp] at h
    rw [h3, h]
  · rintro rfl
    simp

theorem comp_qPoly_injective {a : K} {P Q : K[X]} (h : P.comp (qPoly a) = Q.comp (qPoly a)) :
    P = Q := by
  have h1 : (P - Q).comp (qPoly a) = 0 := by rw [sub_comp, h, sub_self]
  exact sub_eq_zero.mp (comp_qPoly_eq_zero.mp h1)

/-! ### The decomposition `P = u₀(q) + X u₁(q)` -/

private theorem exists_decomp_aux (a : K) : ∀ n : ℕ, ∀ P : K[X], P.natDegree < n →
    ∃ u0 u1 : K[X], P = u0.comp (qPoly a) + X * u1.comp (qPoly a) := by
  intro n
  induction n with
  | zero =>
    intro P h
    omega
  | succ n ih =>
    intro P hP
    by_cases h2 : P.natDegree < 2
    · have hdeg : P.degree ≤ 1 := by
        have h := degree_le_of_natDegree_le (show P.natDegree ≤ 1 by omega)
        exact_mod_cast h
      refine ⟨C (P.coeff 0), C (P.coeff 1), ?_⟩
      rw [C_comp, C_comp]
      calc P = C (P.coeff 1) * X + C (P.coeff 0) := eq_X_add_C_of_degree_le_one hdeg
        _ = C (P.coeff 0) + X * C (P.coeff 1) := by ring
    · have hq := qPoly_monic a
      have hlt : (P /ₘ qPoly a).natDegree < n := by
        rw [natDegree_divByMonic P hq, qPoly_natDegree]
        omega
      obtain ⟨v0, v1, hv⟩ := ih _ hlt
      have hr : (P %ₘ qPoly a).degree ≤ 1 := by
        have h1 := natDegree_modByMonic_lt P hq (qPoly_ne_one a)
        rw [qPoly_natDegree] at h1
        have h := degree_le_of_natDegree_le (show (P %ₘ qPoly a).natDegree ≤ 1 by omega)
        exact_mod_cast h
      have e : P = (C ((P %ₘ qPoly a).coeff 1) * X + C ((P %ₘ qPoly a).coeff 0))
          + qPoly a * (v0.comp (qPoly a) + X * v1.comp (qPoly a)) := by
        rw [← hv, ← eq_X_add_C_of_degree_le_one hr]
        exact (modByMonic_add_div P (qPoly a)).symm
      refine ⟨C ((P %ₘ qPoly a).coeff 0) + X * v0, C ((P %ₘ qPoly a).coeff 1) + X * v1,
        e.trans ?_⟩
      simp only [add_comp, mul_comp, C_comp, X_comp]
      ring

/-- Existence: every polynomial is `u₀(q) + X u₁(q)`. -/
theorem exists_decomp (a : K) (P : K[X]) :
    ∃ u0 u1 : K[X], P = u0.comp (qPoly a) + X * u1.comp (qPoly a) :=
  exists_decomp_aux a (P.natDegree + 1) P (Nat.lt_succ_self _)

/-- Uniqueness: the degrees of `u₀(q)` and `X u₁(q)` have different parities. -/
theorem decomp_unique (a : K) {u0 u1 : K[X]}
    (h : u0.comp (qPoly a) + X * u1.comp (qPoly a) = 0) : u0 = 0 ∧ u1 = 0 := by
  have h1 : u1 = 0 := by
    by_contra hu1
    have hc : u1.comp (qPoly a) ≠ 0 := fun hc => hu1 (comp_qPoly_eq_zero.mp hc)
    have h2 : u0.comp (qPoly a) = -(X * u1.comp (qPoly a)) := eq_neg_of_add_eq_zero_left h
    have h3 := congrArg natDegree h2
    rw [natDegree_neg, natDegree_X_mul hc, natDegree_comp, natDegree_comp, qPoly_natDegree] at h3
    omega
  subst h1
  simp only [zero_comp, mul_zero, add_zero] at h
  exact ⟨comp_qPoly_eq_zero.mp h, rfl⟩

/-- The part `u₀` of `P = u₀(q) + X u₁(q)`. -/
noncomputable def part0 (a : K) (P : K[X]) : K[X] := (exists_decomp a P).choose

/-- The part `u₁` of `P = u₀(q) + X u₁(q)`. -/
noncomputable def part1 (a : K) (P : K[X]) : K[X] := (exists_decomp a P).choose_spec.choose

theorem decomp (a : K) (P : K[X]) :
    P = (part0 a P).comp (qPoly a) + X * (part1 a P).comp (qPoly a) :=
  (exists_decomp a P).choose_spec.choose_spec

theorem parts_eq (a : K) {P u0 u1 : K[X]} (h : P = u0.comp (qPoly a) + X * u1.comp (qPoly a)) :
    part0 a P = u0 ∧ part1 a P = u1 := by
  have h1 := decomp a P
  have h2 : (part0 a P - u0).comp (qPoly a) + X * (part1 a P - u1).comp (qPoly a) = 0 := by
    rw [sub_comp, sub_comp]
    linear_combination h - h1
  obtain ⟨e0, e1⟩ := decomp_unique a h2
  exact ⟨sub_eq_zero.mp e0, sub_eq_zero.mp e1⟩

/-! ### Degrees -/

theorem natDegree_mul_comp_qPoly (a : K) {ϱ Q : K[X]} (hϱ : ϱ ≠ 0) (hQ : Q ≠ 0) :
    (ϱ * Q.comp (qPoly a)).natDegree = ϱ.natDegree + 2 * Q.natDegree := by
  rw [natDegree_mul hϱ (fun h => hQ (comp_qPoly_eq_zero.mp h)), natDegree_comp, qPoly_natDegree,
    mul_comm]

/-- `deg Q ≤ ⌊(κ - deg ϱ) / 2⌋` when `deg (ϱ Q(q)) ≤ κ`. -/
theorem natDegree_le_of_descent (a : K) {ϱ Q : K[X]} (hϱ : ϱ ≠ 0) {κ : ℕ}
    (h : (ϱ * Q.comp (qPoly a)).natDegree ≤ κ) : Q.natDegree ≤ (κ - ϱ.natDegree) / 2 := by
  rcases eq_or_ne Q 0 with rfl | hQ
  · simp
  · rw [natDegree_mul_comp_qPoly a hϱ hQ] at h
    omega

/-- The polynomial `Q` of `c = c₀ + ϱ Q(q)` is unique: the map `c ↦ Q` is injective, and so is
`Q ↦ c`. -/
theorem descent_unique (a : K) {ϱ Q Q' : K[X]} (hϱ : ϱ ≠ 0)
    (h : ϱ * Q.comp (qPoly a) = ϱ * Q'.comp (qPoly a)) : Q = Q' :=
  comp_qPoly_injective (mul_left_cancel₀ hϱ h)

/-! ### The evaluation of `c = c₀ + ϱ Q(q)` -/

theorem eval_descent {a : K} {P P0 ϱ Q : K[X]} (h : P - P0 = ϱ * Q.comp (qPoly a)) (y : K) :
    P.eval y = P0.eval y + ϱ.eval y * Q.eval ((qPoly a).eval y) := by
  have h1 := congrArg (eval y) h
  rw [eval_sub, eval_mul, eval_comp] at h1
  linear_combination h1

/-- Off the zeros of `ϱ`: `c` takes the value `w` at `y` iff `Q` takes the value
`(w - c₀(y)) / ϱ(y)` at `q(y)`. -/
theorem agree_iff_of_ne_zero {a : K} {P P0 ϱ Q : K[X]} (h : P - P0 = ϱ * Q.comp (qPoly a))
    (y w : K) (hy : ϱ.eval y ≠ 0) :
    w = P.eval y ↔ (w - P0.eval y) / ϱ.eval y = Q.eval ((qPoly a).eval y) := by
  rw [eval_descent h y, div_eq_iff hy]
  constructor
  · intro h1
    linear_combination h1
  · intro h1
    linear_combination h1

/-- On the zeros of `ϱ` every `c₀ + ϱ Q(q)` takes the value of `c₀`. -/
theorem eval_eq_of_eval_rho_eq_zero {a : K} {P P0 ϱ Q : K[X]}
    (h : P - P0 = ϱ * Q.comp (qPoly a)) (y : K) (hy : ϱ.eval y = 0) : P.eval y = P0.eval y := by
  rw [eval_descent h y, hy, zero_mul, add_zero]

/-! ### Periodic rational functions -/

/-- The rational function `v / u` is unchanged by `X ↦ X + a`, cross-multiplied:
`v(X) u(X + a) = v(X + a) u(X)`. -/
def Periodic (a : K) (u v : K[X]) : Prop := v * u.comp (X + C a) = v.comp (X + C a) * u

/-- `v / u` and `u / v` have the same periods: the pair may be swapped. -/
theorem Periodic.swap {a : K} {u v : K[X]} (h : Periodic a u v) : Periodic a v u := by
  unfold Periodic at h ⊢
  linear_combination -h

/-- `(c - c₀) / (c₁ - c₀)` and `(c - c₁) / (c₀ - c₁)` have the same periods: the base point may be
exchanged with the second member. -/
theorem Periodic.base_swap {a : K} {c0 c1 c : K[X]} (h : Periodic a (c1 - c0) (c - c0)) :
    Periodic a (c0 - c1) (c - c1) := by
  unfold Periodic at h ⊢
  simp only [sub_comp] at h ⊢
  linear_combination -h

/-- A constant function has every period: collinear members are periodic for every `a`. -/
theorem periodic_of_const (a : K) (u : K[X]) (t : K) : Periodic a u (C t * u) := by
  unfold Periodic
  rw [mul_comp, C_comp]
  ring

/-! ### Characteristic two -/

section CharTwo

variable [CharP K 2]

/-- `q` is unchanged by `X ↦ X + a`. -/
theorem qPoly_comp_shift (a : K) : (qPoly a).comp (X + C a) = qPoly a := by
  unfold qPoly
  simp only [add_comp, pow_comp, mul_comp, X_comp, C_comp]
  linear_combination (C a * X + C a ^ 2) * (CharTwo.two_eq_zero : (2 : K[X]) = 0)

/-- `P(X + a) = P + a u₁(q)`. -/
theorem comp_shift (a : K) (P : K[X]) :
    P.comp (X + C a) = P + C a * (part1 a P).comp (qPoly a) := by
  calc P.comp (X + C a)
      = ((part0 a P).comp (qPoly a) + X * (part1 a P).comp (qPoly a)).comp (X + C a) := by
        rw [← decomp a P]
    _ = (part0 a P).comp (qPoly a) + (X + C a) * (part1 a P).comp (qPoly a) := by
        rw [add_comp, mul_comp, X_comp, comp_assoc, comp_assoc, qPoly_comp_shift]
    _ = ((part0 a P).comp (qPoly a) + X * (part1 a P).comp (qPoly a))
          + C a * (part1 a P).comp (qPoly a) := by ring
    _ = P + C a * (part1 a P).comp (qPoly a) := by rw [← decomp a P]

/-- Invariance under `X ↦ X + a` is `u₁ = 0`. -/
theorem invariant_iff_part1 {a : K} (ha : a ≠ 0) (P : K[X]) :
    P.comp (X + C a) = P ↔ part1 a P = 0 := by
  rw [comp_shift]
  constructor
  · intro h
    have h1 : C a * (part1 a P).comp (qPoly a) = 0 := by linear_combination h
    rcases mul_eq_zero.mp h1 with h2 | h2
    · exact absurd (C_eq_zero.mp h2) ha
    · exact comp_qPoly_eq_zero.mp h2
  · intro h
    rw [h]
    simp

/-- The polynomials unchanged by `X ↦ X + a` are the polynomials in `q`. -/
theorem invariant_iff_exists {a : K} (ha : a ≠ 0) (P : K[X]) :
    P.comp (X + C a) = P ↔ ∃ Q : K[X], P = Q.comp (qPoly a) := by
  constructor
  · intro h
    have h1 := (invariant_iff_part1 ha P).mp h
    have h2 := decomp a P
    rw [h1, zero_comp, mul_zero, add_zero] at h2
    exact ⟨_, h2⟩
  · rintro ⟨Q, hQ⟩
    rw [hQ, comp_assoc, qPoly_comp_shift]

/-- `v / u` has the period `a` if and only if `v₀ u₁ = v₁ u₀`. -/
theorem periodic_iff_parts {a : K} (ha : a ≠ 0) (u v : K[X]) :
    Periodic a u v ↔ part0 a v * part1 a u = part1 a v * part0 a u := by
  unfold Periodic
  rw [comp_shift a u, comp_shift a v]
  have hCa : (C a : K[X]) ≠ 0 := fun h => ha (C_eq_zero.mp h)
  have hu := decomp a u
  have hv := decomp a v
  constructor
  · intro h
    have h1 : C a * (v * (part1 a u).comp (qPoly a) - (part1 a v).comp (qPoly a) * u) = 0 := by
      linear_combination h
    have h2 := (mul_eq_zero.mp h1).resolve_left hCa
    have h3 : (part0 a v * part1 a u - part1 a v * part0 a u).comp (qPoly a) = 0 := by
      rw [sub_comp, mul_comp, mul_comp]
      linear_combination h2 - (part1 a u).comp (qPoly a) * hv + (part1 a v).comp (qPoly a) * hu
    exact sub_eq_zero.mp (comp_qPoly_eq_zero.mp h3)
  · intro h
    have h3 : (part0 a v).comp (qPoly a) * (part1 a u).comp (qPoly a)
        = (part1 a v).comp (qPoly a) * (part0 a u).comp (qPoly a) := by
      rw [← mul_comp, ← mul_comp, h]
    linear_combination C a * h3 + (C a * (part1 a u).comp (qPoly a)) * hv
      - (C a * (part1 a v).comp (qPoly a)) * hu

/-! ### The polynomial `ϱ` -/

/-- `e_u = gcd(u₀, u₁)`: the largest `e` with `e(q) ∣ u`. -/
noncomputable def eGcd (a : K) (u : K[X]) : K[X] := EuclideanDomain.gcd (part0 a u) (part1 a u)

/-- `ϱ = u / e_u(q)`. It is a function of `a` and `u` only. -/
noncomputable def rho (a : K) (u : K[X]) : K[X] :=
  (part0 a u / eGcd a u).comp (qPoly a) + X * (part1 a u / eGcd a u).comp (qPoly a)

omit [CharP K 2] in
theorem eGcd_ne_zero (a : K) {u : K[X]} (hu : u ≠ 0) : eGcd a u ≠ 0 := by
  intro h
  obtain ⟨h0, h1⟩ := EuclideanDomain.gcd_eq_zero_iff.mp h
  apply hu
  rw [decomp a u, h0, h1]
  simp

omit [CharP K 2] in
private theorem eGcd_mul_div0 (a : K) {u : K[X]} (hu : u ≠ 0) :
    eGcd a u * (part0 a u / eGcd a u) = part0 a u :=
  EuclideanDomain.mul_div_cancel' (eGcd_ne_zero a hu) (EuclideanDomain.gcd_dvd_left _ _)

omit [CharP K 2] in
private theorem eGcd_mul_div1 (a : K) {u : K[X]} (hu : u ≠ 0) :
    eGcd a u * (part1 a u / eGcd a u) = part1 a u :=
  EuclideanDomain.mul_div_cancel' (eGcd_ne_zero a hu) (EuclideanDomain.gcd_dvd_right _ _)

omit [CharP K 2] in
/-- `u = ϱ e_u(q)`. -/
theorem rho_mul_eGcd (a : K) {u : K[X]} (hu : u ≠ 0) :
    rho a u * (eGcd a u).comp (qPoly a) = u := by
  have h0' := congrArg (fun p => p.comp (qPoly a)) (eGcd_mul_div0 a hu)
  have h1' := congrArg (fun p => p.comp (qPoly a)) (eGcd_mul_div1 a hu)
  simp only [mul_comp] at h0' h1'
  have hd := decomp a u
  unfold rho
  linear_combination X * h1' + h0' - hd

omit [CharP K 2] in
theorem rho_ne_zero (a : K) {u : K[X]} (hu : u ≠ 0) : rho a u ≠ 0 := by
  intro h
  have h1 := rho_mul_eGcd a hu
  rw [h, zero_mul] at h1
  exact hu h1.symm

omit [CharP K 2] in
theorem natDegree_rho_le (a : K) {u : K[X]} (hu : u ≠ 0) : (rho a u).natDegree ≤ u.natDegree := by
  have h1 := congrArg natDegree (rho_mul_eGcd a hu)
  rw [natDegree_mul_comp_qPoly a (rho_ne_zero a hu) (eGcd_ne_zero a hu)] at h1
  omega

/-- **Note 37 Proposition 3.3, the algebraic part.** For `a ≠ 0` and `u ≠ 0`, the function `v / u`
is unchanged by `X ↦ X + a` if and only if `v = ϱ Q(q)` for a polynomial `Q`, with `ϱ = rho a u`
depending on `a` and `u` only. -/
theorem periodic_iff_exists {a : K} (ha : a ≠ 0) {u : K[X]} (hu : u ≠ 0) (v : K[X]) :
    Periodic a u v ↔ ∃ Q : K[X], v = rho a u * Q.comp (qPoly a) := by
  have he := eGcd_ne_zero a hu
  have h0 := eGcd_mul_div0 a hu
  have h1 := eGcd_mul_div1 a hu
  have hb : eGcd a u = part0 a u * EuclideanDomain.gcdA (part0 a u) (part1 a u)
      + part1 a u * EuclideanDomain.gcdB (part0 a u) (part1 a u) :=
    EuclideanDomain.gcd_eq_gcd_ab _ _
  rw [periodic_iff_parts ha]
  unfold rho
  generalize part0 a u / eGcd a u = s0 at h0 ⊢
  generalize part1 a u / eGcd a u = s1 at h1 ⊢
  generalize EuclideanDomain.gcdA (part0 a u) (part1 a u) = A at hb
  generalize EuclideanDomain.gcdB (part0 a u) (part1 a u) = B at hb
  generalize eGcd a u = e at he h0 h1 hb
  have hb1 : s0 * A + s1 * B = 1 := by
    apply mul_left_cancel₀ he
    linear_combination -hb + A * h0 + B * h1
  constructor
  · intro h
    have h' : part0 a v * s1 = part1 a v * s0 := by
      apply mul_left_cancel₀ he
      linear_combination h + part0 a v * h1 - part1 a v * h0
    refine ⟨A * part0 a v + B * part1 a v, ?_⟩
    have e0 : s0 * (A * part0 a v + B * part1 a v) = part0 a v := by
      linear_combination part0 a v * hb1 - B * h'
    have e1 : s1 * (A * part0 a v + B * part1 a v) = part1 a v := by
      linear_combination part1 a v * hb1 + A * h'
    have e0' := congrArg (fun p => p.comp (qPoly a)) e0
    have e1' := congrArg (fun p => p.comp (qPoly a)) e1
    simp only [mul_comp] at e0' e1'
    have hv := decomp a v
    linear_combination hv - e0' - X * e1'
  · rintro ⟨Q, hQ⟩
    have hparts : part0 a v = s0 * Q ∧ part1 a v = s1 * Q := by
      apply parts_eq
      rw [hQ]
      simp only [mul_comp]
      ring
    rw [hparts.1, hparts.2]
    linear_combination (-(s0 * Q)) * h1 + (s1 * Q) * h0

/-- **The members periodic for a pair.** For two distinct polynomials `c₀, c₁` and `a ≠ 0`, the
polynomials `c` whose function `(c - c₀) / (c₁ - c₀)` is unchanged by `X ↦ X + a` are exactly
`c₀ + ϱ Q(X² + a X)`, with `ϱ = rho a (c₁ - c₀)`. -/
theorem periodic_triple_iff {a : K} (ha : a ≠ 0) {c0 c1 : K[X]} (h01 : c0 ≠ c1) (c : K[X]) :
    Periodic a (c1 - c0) (c - c0) ↔ ∃ Q : K[X], c = c0 + rho a (c1 - c0) * Q.comp (qPoly a) := by
  rw [periodic_iff_exists ha (sub_ne_zero.mpr (Ne.symm h01))]
  constructor
  · rintro ⟨Q, hQ⟩
    exact ⟨Q, by linear_combination hQ⟩
  · rintro ⟨Q, hQ⟩
    exact ⟨Q, by linear_combination hQ⟩

end CharTwo

end PeriodDescent
