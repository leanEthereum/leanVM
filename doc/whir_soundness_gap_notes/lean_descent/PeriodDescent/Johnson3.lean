/-
The three-wise Johnson bound: Lemma 5.2 of note 44 (`44-period-conjecture-divisors.md`).

`M` sets `S_i` of at least `a` points each, inside a set `Ω` of `n` points, such that every three of
them satisfy `|S_i ∩ S_j| + |S_i ∩ S_l| + |S_j ∩ S_l| ≤ c + |S_i ∩ S_j ∩ S_l|`.

* `threewise_identity`: the sum of the left sides minus the triple intersections over all ordered
  triples of distinct indices is `∑_x 6 h_M(d_x)`, `d_x` the number of sets through `x` and
  `6 h_M(d) = d (d - 1) (3 M - 4 - d)` (`H3`, `H3_eq_choose`). This is inclusion-exclusion truncated
  at triples.
* `H3_tangent`: `h_M` is convex at the integers of `[0, M]`, in the form of the supporting lines
  through two consecutive integers.
* `threewise_jensen`: inequality (3) of the note, `n ĥ_M(M a / n) ≤ C(M, 3) c`, in the division-free
  form "for every integer `e < M`, the value at `M a / n` of the line through `(e, h_M(e))` and
  `(e + 1, h_M(e + 1))`, times `6 n`, is at most `M (M - 1) (M - 2) c`". The piecewise linear
  interpolation `ĥ_M` is the upper envelope of these lines, and `e = ⌊M a / n⌋` gives (3) itself.
* `threewise_johnson`: the closed form, cross-multiplied in `ℤ`: if `a² (3 n - a) > c n²` then
  `M (n - a) < n` or `M (a² (3 n - a) - c n²) ≤ 3 n (a² + n a - c n)`.
* `threewise_johnson_rat`: the same with `α = a / n`, `ϱ = c / (2 n)`:
  `M ≤ max (1 / (1 - α)) (3 (α + α² - 2 ϱ) / (α² (3 - α) - 2 ϱ))` when `α² (3 - α) > 2 ϱ`.

The hypothesis `α ≥ ϱ` of the note is not needed: it follows from `α² (3 - α) > 2 ϱ` and `α ≤ 1`.
Nor is `M ≥ 3`, nor that the sets have exactly `a` points.
-/
import Mathlib

open Finset

namespace PeriodDescent

/-! ### The function `6 h_M` -/

/-- `6 h_M(d) = 6 ((M - 2) C(d, 2) - C(d, 3)) = d (d - 1) (3 M - 4 - d)`. -/
def H3 (M d : ℤ) : ℤ := d * (d - 1) * (3 * M - 4 - d)

theorem two_mul_choose_two (d : ℕ) : 2 * (d.choose 2 : ℤ) = d * (d - 1) := by
  induction d with
  | zero => simp
  | succ d ih =>
    have h : (d + 1).choose 2 = d.choose 1 + d.choose 2 := Nat.choose_succ_succ' d 1
    rw [h, Nat.choose_one_right]
    push_cast
    linear_combination ih

theorem six_mul_choose_three (d : ℕ) : 6 * (d.choose 3 : ℤ) = d * (d - 1) * (d - 2) := by
  induction d with
  | zero => simp
  | succ d ih =>
    have h : (d + 1).choose 3 = d.choose 2 + d.choose 3 := Nat.choose_succ_succ' d 2
    rw [h]
    push_cast
    linear_combination 3 * two_mul_choose_two d + ih

/-- `H3` is six times the function `h_M(d) = (M - 2) C(d, 2) - C(d, 3)` of the note. -/
theorem H3_eq_choose (M : ℤ) (d : ℕ) :
    H3 M d = 6 * ((M - 2) * (d.choose 2 : ℤ) - (d.choose 3 : ℤ)) := by
  unfold H3
  linear_combination (-3 * (M - 2)) * two_mul_choose_two d + six_mul_choose_three d

/-- The supporting line of `h_M` through `e` and `e + 1` lies below `h_M` at every integer `d ≤ M`,
for `e ≤ M - 1`: the second differences of `h_M` are `M - 1 - d ≥ 0`. -/
theorem H3_tangent (M d e : ℤ) (hd : d ≤ M) (he : e ≤ M - 1) :
    H3 M e + (H3 M (e + 1) - H3 M e) * (d - e) ≤ H3 M d := by
  have key : H3 M d - (H3 M e + (H3 M (e + 1) - H3 M e) * (d - e))
      = (d - e) * (d - e - 1) * (3 * M - 4 - 2 * e - d) := by
    unfold H3
    ring
  have h0 : 0 ≤ (d - e) * (d - e - 1) * (3 * M - 4 - 2 * e - d) := by
    rcases lt_trichotomy d e with h | h | h
    · have h1 : 0 ≤ e - d := by linarith
      have h2 : 0 ≤ e - d + 1 := by linarith
      have h3 : 0 ≤ 3 * M - 4 - 2 * e - d := by omega
      have e2 : (d - e) * (d - e - 1) * (3 * M - 4 - 2 * e - d)
          = (e - d) * (e - d + 1) * (3 * M - 4 - 2 * e - d) := by ring
      rw [e2]
      exact mul_nonneg (mul_nonneg h1 h2) h3
    · rw [h]
      simp
    · rcases (by omega : d = e + 1 ∨ e + 2 ≤ d) with h' | h'
      · have h1 : d - e - 1 = 0 := by omega
        rw [h1]
        simp
      · have h1 : 0 ≤ d - e := by linarith
        have h2 : 0 ≤ d - e - 1 := by linarith
        have h3 : 0 ≤ 3 * M - 4 - 2 * e - d := by omega
        exact mul_nonneg (mul_nonneg h1 h2) h3
  linarith

theorem H3_slope (M e : ℤ) : H3 M (e + 1) - H3 M e = 3 * e * (2 * M - 3 - e) := by
  unfold H3
  ring

theorem H3_slope_nonneg (M e : ℤ) (he0 : 0 ≤ e) (he : e ≤ M - 1) :
    0 ≤ H3 M (e + 1) - H3 M e := by
  rw [H3_slope]
  rcases (by omega : e = 0 ∨ 1 ≤ e) with h | h
  · rw [h]
    simp
  · exact mul_nonneg (by linarith) (by linarith)

/-! ### Sums over ordered triples of distinct indices -/

variable {ι α : Type*}

section

variable [DecidableEq ι]

/-- The sum of `g i j l` over the ordered triples of pairwise distinct elements of `I`. -/
def tripleSum (I : Finset ι) (g : ι → ι → ι → ℤ) : ℤ :=
  ∑ i ∈ I, ∑ j ∈ I.erase i, ∑ l ∈ (I.erase i).erase j, g i j l

private theorem card_erase_int (I : Finset ι) {i : ι} (hi : i ∈ I) :
    ((I.erase i).card : ℤ) = I.card - 1 := by
  have h := Finset.card_erase_add_one hi
  omega

private theorem card_erase_erase_int (I : Finset ι) {i j : ι} (hi : i ∈ I) (hj : j ∈ I.erase i) :
    (((I.erase i).erase j).card : ℤ) = I.card - 2 := by
  have h1 := Finset.card_erase_add_one hj
  have h2 := Finset.card_erase_add_one hi
  omega

private theorem sum_erase_erase (I : Finset ι) (u : ι → ℤ) {i j : ι} (hi : i ∈ I)
    (hj : j ∈ I.erase i) :
    ∑ l ∈ (I.erase i).erase j, u l = ∑ l ∈ I, u l - u i - u j := by
  rw [Finset.sum_erase_eq_sub hj, Finset.sum_erase_eq_sub hi]

/-- There are `M (M - 1) (M - 2)` ordered triples of distinct indices. -/
theorem tripleSum_const (I : Finset ι) (c : ℤ) :
    tripleSum I (fun _ _ _ => c) = (I.card : ℤ) * (I.card - 1) * (I.card - 2) * c := by
  unfold tripleSum
  have h2 : ∀ i ∈ I, ∑ j ∈ I.erase i, ∑ _l ∈ (I.erase i).erase j, c
      = ((I.card : ℤ) - 1) * (((I.card : ℤ) - 2) * c) := by
    intro i hi
    have h1 : ∀ j ∈ I.erase i, ∑ _l ∈ (I.erase i).erase j, c = ((I.card : ℤ) - 2) * c := by
      intro j hj
      rw [Finset.sum_const, nsmul_eq_mul, card_erase_erase_int I hi hj]
    rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul, card_erase_int I hi]
  rw [Finset.sum_congr rfl h2, Finset.sum_const, nsmul_eq_mul]
  ring

theorem tripleSum_le (I : Finset ι) (g g' : ι → ι → ι → ℤ)
    (h : ∀ i ∈ I, ∀ j ∈ I, ∀ l ∈ I, i ≠ j → i ≠ l → j ≠ l → g i j l ≤ g' i j l) :
    tripleSum I g ≤ tripleSum I g' := by
  unfold tripleSum
  refine Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj =>
    Finset.sum_le_sum fun l hl => ?_
  have hj' := Finset.mem_erase.mp hj
  have hl' := Finset.mem_erase.mp hl
  have hl'' := Finset.mem_erase.mp hl'.2
  exact h i hi j hj'.2 l hl''.2 (Ne.symm hj'.1) (Ne.symm hl''.1) (Ne.symm hl'.1)

theorem tripleSum_sum (I : Finset ι) (Ω : Finset α) (G : α → ι → ι → ι → ℤ) :
    tripleSum I (fun i j l => ∑ x ∈ Ω, G x i j l) = ∑ x ∈ Ω, tripleSum I (G x) := by
  unfold tripleSum
  calc ∑ i ∈ I, ∑ j ∈ I.erase i, ∑ l ∈ (I.erase i).erase j, ∑ x ∈ Ω, G x i j l
      = ∑ i ∈ I, ∑ j ∈ I.erase i, ∑ x ∈ Ω, ∑ l ∈ (I.erase i).erase j, G x i j l :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_comm
    _ = ∑ i ∈ I, ∑ x ∈ Ω, ∑ j ∈ I.erase i, ∑ l ∈ (I.erase i).erase j, G x i j l :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ x ∈ Ω, ∑ i ∈ I, ∑ j ∈ I.erase i, ∑ l ∈ (I.erase i).erase j, G x i j l :=
        Finset.sum_comm

/-- The count at one point. For a `0/1` vector `u` with `d` ones among the `M` indices of `I`, the
sum over ordered triples of distinct indices of `u_i u_j + u_i u_l + u_j u_l - u_i u_j u_l` is
`3 (M - 2) d (d - 1) - d (d - 1) (d - 2) = 6 h_M(d)`. -/
theorem tripleSum_indicator (I : Finset ι) (u : ι → ℤ) (hu : ∀ i ∈ I, u i * u i = u i) :
    tripleSum I (fun i j l => u i * u j + u i * u l + u j * u l - u i * u j * u l)
      = H3 I.card (∑ i ∈ I, u i) := by
  have inner : ∀ i ∈ I, ∀ j ∈ I.erase i,
      ∑ l ∈ (I.erase i).erase j, (u i * u j + u i * u l + u j * u l - u i * u j * u l)
        = (u i * (∑ l ∈ I, u l) - u i)
          + (((I.card : ℤ) - 2) * u i + (1 - u i) * (∑ l ∈ I, u l) - 1) * u j := by
    intro i hi j hj
    have hj' : j ∈ I := Finset.mem_of_mem_erase hj
    have e : ∀ l, u i * u j + u i * u l + u j * u l - u i * u j * u l
        = u i * u j + (u i + u j - u i * u j) * u l := fun l => by ring
    simp only [e]
    rw [Finset.sum_add_distrib, Finset.sum_const, ← Finset.mul_sum, sum_erase_erase I u hi hj,
      nsmul_eq_mul, card_erase_erase_int I hi hj]
    linear_combination (u j - 1) * hu i hi + (u i - 1) * hu j hj'
  have middle : ∀ i ∈ I,
      ∑ j ∈ I.erase i, ∑ l ∈ (I.erase i).erase j,
        (u i * u j + u i * u l + u j * u l - u i * u j * u l)
        = ((∑ l ∈ I, u l) * (∑ l ∈ I, u l) - (∑ l ∈ I, u l))
          + ((∑ l ∈ I, u l) - 1) * (2 * (I.card : ℤ) - 4 - (∑ l ∈ I, u l)) * u i := by
    intro i hi
    rw [Finset.sum_congr rfl (inner i hi), Finset.sum_add_distrib, Finset.sum_const,
      ← Finset.mul_sum, Finset.sum_erase_eq_sub hi, nsmul_eq_mul, card_erase_int I hi]
    linear_combination ((∑ l ∈ I, u l) - (I.card : ℤ) + 2) * hu i hi
  unfold tripleSum
  rw [Finset.sum_congr rfl middle, Finset.sum_add_distrib, Finset.sum_const, ← Finset.mul_sum,
    nsmul_eq_mul]
  unfold H3
  ring

end

/-! ### Intersections as sums of indicators -/

section

variable [DecidableEq α]

private theorem card_inter_eq_sum (Ω A B : Finset α) (hA : A ⊆ Ω) :
    ((A ∩ B).card : ℤ)
      = ∑ x ∈ Ω, (if x ∈ A then (1 : ℤ) else 0) * (if x ∈ B then (1 : ℤ) else 0) := by
  have h : A ∩ B = Ω.filter (fun x => x ∈ A ∧ x ∈ B) := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_filter]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨hA h1, h1, h2⟩
    · rintro ⟨_, h1, h2⟩
      exact ⟨h1, h2⟩
  rw [h, Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases h1 : x ∈ A <;> by_cases h2 : x ∈ B <;> simp [h1, h2]

private theorem card_inter3_eq_sum (Ω A B C : Finset α) (hA : A ⊆ Ω) :
    ((A ∩ B ∩ C).card : ℤ)
      = ∑ x ∈ Ω, (if x ∈ A then (1 : ℤ) else 0) * (if x ∈ B then (1 : ℤ) else 0)
          * (if x ∈ C then (1 : ℤ) else 0) := by
  have h : A ∩ B ∩ C = Ω.filter (fun x => x ∈ A ∧ x ∈ B ∧ x ∈ C) := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_filter]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨hA h1, h1, h2, h3⟩
    · rintro ⟨_, h1, h2, h3⟩
      exact ⟨⟨h1, h2⟩, h3⟩
  rw [h, Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases h1 : x ∈ A <;> by_cases h2 : x ∈ B <;> by_cases h3 : x ∈ C <;> simp [h1, h2, h3]

private theorem card_eq_sum_indicator (Ω A : Finset α) (hA : A ⊆ Ω) :
    (A.card : ℤ) = ∑ x ∈ Ω, (if x ∈ A then (1 : ℤ) else 0) := by
  have h : A = Ω.filter (fun x => x ∈ A) := by
    ext x
    simp only [Finset.mem_filter]
    exact ⟨fun h1 => ⟨hA h1, h1⟩, fun h1 => h1.2⟩
  conv_lhs => rw [h]
  rw [Finset.card_filter]
  push_cast
  rfl

/-- The number of sets `S i`, `i ∈ I`, through the point `x`. -/
def deg (I : Finset ι) (S : ι → Finset α) (x : α) : ℕ := (I.filter (fun i => x ∈ S i)).card

theorem deg_le (I : Finset ι) (S : ι → Finset α) (x : α) : deg I S x ≤ I.card :=
  Finset.card_filter_le _ _

private theorem deg_eq_sum (I : Finset ι) (S : ι → Finset α) (x : α) :
    (deg I S x : ℤ) = ∑ i ∈ I, (if x ∈ S i then (1 : ℤ) else 0) := by
  unfold deg
  rw [Finset.card_filter]
  push_cast
  rfl

/-- Double counting: the degrees add up to the sizes. -/
theorem sum_deg (I : Finset ι) (Ω : Finset α) (S : ι → Finset α) (hS : ∀ i ∈ I, S i ⊆ Ω) :
    ∑ x ∈ Ω, (deg I S x : ℤ) = ∑ i ∈ I, ((S i).card : ℤ) := by
  simp only [deg_eq_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i hi => (card_eq_sum_indicator Ω (S i) (hS i hi)).symm

end

variable [DecidableEq ι] [DecidableEq α]

/-- **Inclusion-exclusion truncated at triples.** The sum over ordered triples of distinct indices
of `|S_i ∩ S_j| + |S_i ∩ S_l| + |S_j ∩ S_l| - |S_i ∩ S_j ∩ S_l|` is `∑_x 6 h_M(d_x)`. -/
theorem threewise_identity (I : Finset ι) (Ω : Finset α) (S : ι → Finset α)
    (hS : ∀ i ∈ I, S i ⊆ Ω) :
    tripleSum I (fun i j l => ((S i ∩ S j).card : ℤ) + (S i ∩ S l).card + (S j ∩ S l).card
        - (S i ∩ S j ∩ S l).card)
      = ∑ x ∈ Ω, H3 I.card (deg I S x) := by
  have h1 : tripleSum I (fun i j l => ((S i ∩ S j).card : ℤ) + (S i ∩ S l).card
        + (S j ∩ S l).card - (S i ∩ S j ∩ S l).card)
      = tripleSum I (fun i j l => ∑ x ∈ Ω,
          ((if x ∈ S i then (1 : ℤ) else 0) * (if x ∈ S j then (1 : ℤ) else 0)
          + (if x ∈ S i then (1 : ℤ) else 0) * (if x ∈ S l then (1 : ℤ) else 0)
          + (if x ∈ S j then (1 : ℤ) else 0) * (if x ∈ S l then (1 : ℤ) else 0)
          - (if x ∈ S i then (1 : ℤ) else 0) * (if x ∈ S j then (1 : ℤ) else 0)
            * (if x ∈ S l then (1 : ℤ) else 0))) := by
    unfold tripleSum
    refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj =>
      Finset.sum_congr rfl fun l _ => ?_
    have hj' : j ∈ I := Finset.mem_of_mem_erase hj
    dsimp only
    rw [card_inter_eq_sum Ω (S i) (S j) (hS i hi), card_inter_eq_sum Ω (S i) (S l) (hS i hi),
      card_inter_eq_sum Ω (S j) (S l) (hS j hj'),
      card_inter3_eq_sum Ω (S i) (S j) (S l) (hS i hi),
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  rw [h1, tripleSum_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [tripleSum_indicator I (fun i => if x ∈ S i then (1 : ℤ) else 0), deg_eq_sum]
  intro i _
  by_cases h : x ∈ S i <;> simp [h]

/-! ### Inequality (3) of the note -/

/-- **Lemma 5.2 of note 44, inequality (3).** For every integer `e < M`, the supporting line of
`6 h_M` through `e` and `e + 1`, evaluated at the mean degree `M a / n` and multiplied by `n`, is
at most `M (M - 1) (M - 2) c = 6 C(M, 3) c`. With `e = ⌊M a / n⌋` the left side is
`6 n ĥ_M(M a / n)`. -/
theorem threewise_jensen (I : Finset ι) (Ω : Finset α) (S : ι → Finset α) (a c : ℕ)
    (hS : ∀ i ∈ I, S i ⊆ Ω) (ha : ∀ i ∈ I, a ≤ (S i).card)
    (hc : ∀ i ∈ I, ∀ j ∈ I, ∀ l ∈ I, i ≠ j → i ≠ l → j ≠ l →
      (S i ∩ S j).card + (S i ∩ S l).card + (S j ∩ S l).card ≤ c + (S i ∩ S j ∩ S l).card)
    (e : ℕ) (he : e + 1 ≤ I.card) :
    (Ω.card : ℤ) * H3 I.card e
        + (H3 I.card (e + 1) - H3 I.card e) * ((I.card : ℤ) * a - Ω.card * e)
      ≤ (I.card : ℤ) * (I.card - 1) * (I.card - 2) * c := by
  have he' : (e : ℤ) ≤ (I.card : ℤ) - 1 := by omega
  have hslope := H3_slope_nonneg (I.card : ℤ) e (by positivity) he'
  -- the sum of the degrees is at least `M a`
  have hsum : (I.card : ℤ) * a ≤ ∑ x ∈ Ω, (deg I S x : ℤ) := by
    rw [sum_deg I Ω S hS]
    calc (I.card : ℤ) * a = ∑ _i ∈ I, (a : ℤ) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ i ∈ I, ((S i).card : ℤ) := Finset.sum_le_sum fun i hi => by exact_mod_cast ha i hi
  -- the supporting line, summed over the points
  have hline : (Ω.card : ℤ) * H3 I.card e
        + (H3 I.card (e + 1) - H3 I.card e) * (∑ x ∈ Ω, (deg I S x : ℤ) - Ω.card * e)
      ≤ ∑ x ∈ Ω, H3 I.card (deg I S x) := by
    have h1 : ∑ x ∈ Ω, (H3 I.card e + (H3 I.card (e + 1) - H3 I.card e) * ((deg I S x : ℤ) - e))
        = (Ω.card : ℤ) * H3 I.card e
          + (H3 I.card (e + 1) - H3 I.card e) * (∑ x ∈ Ω, (deg I S x : ℤ) - Ω.card * e) := by
      rw [Finset.sum_add_distrib, Finset.sum_const, ← Finset.mul_sum, Finset.sum_sub_distrib,
        Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
    rw [← h1]
    refine Finset.sum_le_sum fun x _ => ?_
    exact H3_tangent _ _ _ (by exact_mod_cast deg_le I S x) he'
  -- the hypothesis, summed over the triples
  have htriple : ∑ x ∈ Ω, H3 I.card (deg I S x)
      ≤ (I.card : ℤ) * (I.card - 1) * (I.card - 2) * c := by
    rw [← threewise_identity I Ω S hS, ← tripleSum_const]
    refine tripleSum_le I _ _ fun i hi j hj l hl hij hil hjl => ?_
    have := hc i hi j hj l hl hij hil hjl
    have h' : ((S i ∩ S j).card : ℤ) + (S i ∩ S l).card + (S j ∩ S l).card
        ≤ c + (S i ∩ S j ∩ S l).card := by exact_mod_cast this
    linarith
  have hmono : (H3 I.card (e + 1) - H3 I.card e) * ((I.card : ℤ) * a - Ω.card * e)
      ≤ (H3 I.card (e + 1) - H3 I.card e) * (∑ x ∈ Ω, (deg I S x : ℤ) - Ω.card * e) :=
    mul_le_mul_of_nonneg_left (by linarith) hslope
  linarith

/-! ### The closed form -/

/-- The arithmetic behind the closed form: from (3) at `e = ⌊M a / n⌋` to the quadratic inequality
`𝒜 M² - ℬ M + 4 (α - ϱ) ≤ 0` of the note, by convexity of the cubic on `[e, e + 1]`. -/
theorem threewise_closed_form_arith (M n a c e : ℤ) (hM : 1 ≤ M) (hn : 0 < n) (ha0 : 0 ≤ a)
    (han : a ≤ n) (hfloor1 : n * e ≤ M * a) (hfloor2 : M * a < n * (e + 1))
    (h3 : e ≤ M - 1 → n * H3 M e + (H3 M (e + 1) - H3 M e) * (M * a - n * e)
      ≤ M * (M - 1) * (M - 2) * c)
    (hA : c * n ^ 2 < a ^ 2 * (3 * n - a)) :
    M * (n - a) < n ∨
      M * (a ^ 2 * (3 * n - a) - c * n ^ 2) ≤ 3 * n * (a ^ 2 + n * a - c * n) := by
  by_cases hcase : M * (n - a) < n
  · exact Or.inl hcase
  right
  have hcase := not_lt.mp hcase
  have hMa : M * a ≤ n * (M - 1) := by linarith
  have he : e ≤ M - 1 := by
    by_contra hcon
    have hcon := not_le.mp hcon
    have h1 : n * M ≤ n * e := mul_le_mul_of_nonneg_left (by omega) hn.le
    linarith
  have h3' := h3 he
  have hthird : 0 ≤ (M * a - n * e) * (n * (3 * M - 4 - 2 * e) - M * a) := by
    rcases (by omega : e ≤ M - 2 ∨ e = M - 1) with h | h
    · refine mul_nonneg (by linarith) ?_
      have h1 : n * M ≤ n * (3 * M - 4 - 2 * e) := mul_le_mul_of_nonneg_left (by omega) hn.le
      have h2 : M * a ≤ M * n := mul_le_mul_of_nonneg_left han (by linarith)
      linarith
    · subst h
      have h1 : M * a - n * (M - 1) = 0 := by linarith
      rw [h1, zero_mul]
  have hchord : 0 ≤ (M * a - n * e) * (n * (e + 1) - M * a)
      * (n * (3 * M - 4 - 2 * e) - M * a) := by
    have h2 : 0 ≤ n * (e + 1) - M * a := by linarith
    have e2 : (M * a - n * e) * (n * (e + 1) - M * a) * (n * (3 * M - 4 - 2 * e) - M * a)
        = ((M * a - n * e) * (n * (3 * M - 4 - 2 * e) - M * a)) * (n * (e + 1) - M * a) := by
      ring
    rw [e2]
    exact mul_nonneg hthird h2
  have hid : n ^ 2 * (n * H3 M e + (H3 M (e + 1) - H3 M e) * (M * a - n * e))
        - M * a * (M * a - n) * (3 * M * n - 4 * n - M * a)
      = (M * a - n * e) * (n * (e + 1) - M * a) * (n * (3 * M - 4 - 2 * e) - M * a) := by
    unfold H3
    ring
  have h4 : M * a * (M * a - n) * (3 * M * n - 4 * n - M * a)
      ≤ n ^ 2 * (M * (M - 1) * (M - 2) * c) := by
    have h5 := mul_le_mul_of_nonneg_left h3' (sq_nonneg n)
    linarith
  have h5 : a * (M * a - n) * (3 * M * n - 4 * n - M * a)
      ≤ n ^ 2 * ((M - 1) * (M - 2) * c) := by
    have h6 : M * (a * (M * a - n) * (3 * M * n - 4 * n - M * a))
        ≤ M * (n ^ 2 * ((M - 1) * (M - 2) * c)) := by linarith
    exact le_of_mul_le_mul_left h6 (by linarith)
  have h6 : 0 < 2 * a - c := by
    have h7 : a ^ 2 * (3 * n - a) ≤ 2 * a * n ^ 2 := by
      have h8 : 0 ≤ a * ((2 * n - a) * (n - a)) :=
        mul_nonneg ha0 (mul_nonneg (by linarith) (by linarith))
      linarith
    have hn2 : 0 < n ^ 2 := by positivity
    by_contra hcon
    have hcon := not_lt.mp hcon
    have h9 : 2 * a * n ^ 2 ≤ c * n ^ 2 := mul_le_mul_of_nonneg_right (by linarith) hn2.le
    linarith
  have h9 : M * (M * (a ^ 2 * (3 * n - a) - c * n ^ 2) - 3 * n * (a ^ 2 + n * a - c * n))
      + 2 * n ^ 2 * (2 * a - c) ≤ 0 := by
    have e9 : M * (M * (a ^ 2 * (3 * n - a) - c * n ^ 2) - 3 * n * (a ^ 2 + n * a - c * n))
        + 2 * n ^ 2 * (2 * a - c)
        = a * (M * a - n) * (3 * M * n - 4 * n - M * a) - n ^ 2 * ((M - 1) * (M - 2) * c) := by
      ring
    linarith
  have h10 : 0 < 2 * n ^ 2 * (2 * a - c) := mul_pos (by positivity) h6
  by_contra hcon
  have hcon := not_le.mp hcon
  have h11 : 0 ≤ M * (M * (a ^ 2 * (3 * n - a) - c * n ^ 2)
      - 3 * n * (a ^ 2 + n * a - c * n)) := mul_nonneg (by linarith) (by linarith)
  linarith

/-- **Lemma 5.2 of note 44, the closed form, cross-multiplied.** Let `M` sets of at least `a`
points each, in a set of `n` points, satisfy
`|S_i ∩ S_j| + |S_i ∩ S_l| + |S_j ∩ S_l| ≤ c + |S_i ∩ S_j ∩ S_l|` three by three. If
`a² (3 n - a) > c n²` (that is `α² (3 - α) > 2 ϱ` with `α = a / n`, `ϱ = c / (2 n)`), then
`M (n - a) < n` (that is `M < 1 / (1 - α)`) or
`M (a² (3 n - a) - c n²) ≤ 3 n (a² + n a - c n)` (that is `M ≤ ℬ / 𝒜`). -/
theorem threewise_johnson (I : Finset ι) (Ω : Finset α) (S : ι → Finset α) (a c : ℕ)
    (hS : ∀ i ∈ I, S i ⊆ Ω) (ha : ∀ i ∈ I, a ≤ (S i).card)
    (hc : ∀ i ∈ I, ∀ j ∈ I, ∀ l ∈ I, i ≠ j → i ≠ l → j ≠ l →
      (S i ∩ S j).card + (S i ∩ S l).card + (S j ∩ S l).card ≤ c + (S i ∩ S j ∩ S l).card)
    (hA : (c : ℤ) * (Ω.card : ℤ) ^ 2 < (a : ℤ) ^ 2 * (3 * (Ω.card : ℤ) - a)) :
    (I.card : ℤ) * ((Ω.card : ℤ) - a) < Ω.card ∨
      (I.card : ℤ) * ((a : ℤ) ^ 2 * (3 * (Ω.card : ℤ) - a) - c * (Ω.card : ℤ) ^ 2)
        ≤ 3 * Ω.card * ((a : ℤ) ^ 2 + Ω.card * a - c * Ω.card) := by
  have hn : 0 < (Ω.card : ℤ) := by
    rcases Nat.eq_zero_or_pos Ω.card with h | h
    · exfalso
      rw [h] at hA
      have h1 : (0 : ℤ) ≤ (a : ℤ) ^ 2 * (a : ℤ) := by positivity
      simp only [Nat.cast_zero] at hA
      nlinarith
    · exact_mod_cast h
  rcases Nat.eq_zero_or_pos I.card with hM | hM
  · left
    rw [hM]
    simpa using hn
  have han : (a : ℤ) ≤ Ω.card := by
    obtain ⟨i, hi⟩ := Finset.card_pos.mp hM
    exact_mod_cast (ha i hi).trans (Finset.card_le_card (hS i hi))
  refine threewise_closed_form_arith (I.card : ℤ) (Ω.card : ℤ) a c ((I.card * a / Ω.card : ℕ) : ℤ)
    (by exact_mod_cast hM) hn (by positivity) han ?_ ?_ ?_ hA
  · exact_mod_cast Nat.mul_div_le (I.card * a) Ω.card
  · have h := Nat.lt_mul_div_succ (I.card * a) (by exact_mod_cast hn : 0 < Ω.card)
    exact_mod_cast h
  · intro he
    have he' : I.card * a / Ω.card + 1 ≤ I.card := by omega
    have h := threewise_jensen I Ω S a c hS ha hc (I.card * a / Ω.card) he'
    push_cast at h ⊢
    linarith

/-- **Lemma 5.2 of note 44, the closed form as stated.** With `α = a / n` and `ϱ = c / (2 n)`:
if `α² (3 - α) > 2 ϱ` then `M ≤ max (1 / (1 - α)) (3 (α + α² - 2 ϱ) / (α² (3 - α) - 2 ϱ))`. The
sets are proper (`a < n`), so that `1 / (1 - α)` is defined. -/
theorem threewise_johnson_rat (I : Finset ι) (Ω : Finset α) (S : ι → Finset α) (a c : ℕ)
    (hS : ∀ i ∈ I, S i ⊆ Ω) (ha : ∀ i ∈ I, a ≤ (S i).card)
    (hc : ∀ i ∈ I, ∀ j ∈ I, ∀ l ∈ I, i ≠ j → i ≠ l → j ≠ l →
      (S i ∩ S j).card + (S i ∩ S l).card + (S j ∩ S l).card ≤ c + (S i ∩ S j ∩ S l).card)
    (han : a < Ω.card)
    (hA : 2 * ((c : ℚ) / (2 * Ω.card))
      < ((a : ℚ) / Ω.card) ^ 2 * (3 - (a : ℚ) / Ω.card)) :
    (I.card : ℚ) ≤ max (1 / (1 - (a : ℚ) / Ω.card))
      (3 * ((a : ℚ) / Ω.card + ((a : ℚ) / Ω.card) ^ 2 - 2 * ((c : ℚ) / (2 * Ω.card)))
        / (((a : ℚ) / Ω.card) ^ 2 * (3 - (a : ℚ) / Ω.card) - 2 * ((c : ℚ) / (2 * Ω.card)))) := by
  have hn : (0 : ℚ) < Ω.card := by exact_mod_cast (Nat.zero_le a).trans_lt han
  have hna : (0 : ℚ) < (Ω.card : ℚ) - a := by
    have : (a : ℚ) < Ω.card := by exact_mod_cast han
    linarith
  have hn3 : (0 : ℚ) < (Ω.card : ℚ) ^ 3 := by positivity
  -- the two quantities of the note, times `n ^ 3`
  have eA : ((a : ℚ) / Ω.card) ^ 2 * (3 - (a : ℚ) / Ω.card) - 2 * ((c : ℚ) / (2 * Ω.card))
      = ((a : ℚ) ^ 2 * (3 * (Ω.card : ℚ) - a) - c * (Ω.card : ℚ) ^ 2) / (Ω.card : ℚ) ^ 3 := by
    field_simp
  have eB : 3 * ((a : ℚ) / Ω.card + ((a : ℚ) / Ω.card) ^ 2 - 2 * ((c : ℚ) / (2 * Ω.card)))
      = (3 * Ω.card * ((a : ℚ) ^ 2 + Ω.card * a - c * Ω.card)) / (Ω.card : ℚ) ^ 3 := by
    field_simp
    ring
  have hApos : (0 : ℚ) < (a : ℚ) ^ 2 * (3 * (Ω.card : ℚ) - a) - c * (Ω.card : ℚ) ^ 2 := by
    have h1 : (0 : ℚ) < ((a : ℚ) / Ω.card) ^ 2 * (3 - (a : ℚ) / Ω.card)
        - 2 * ((c : ℚ) / (2 * Ω.card)) := by linarith
    rw [eA] at h1
    exact (div_pos_iff_of_pos_right hn3).mp h1
  have hAint : (c : ℤ) * (Ω.card : ℤ) ^ 2 < (a : ℤ) ^ 2 * (3 * (Ω.card : ℤ) - a) := by
    have h1 : ((c : ℤ) * (Ω.card : ℤ) ^ 2 : ℚ) < ((a : ℤ) ^ 2 * (3 * (Ω.card : ℤ) - a) : ℚ) := by
      push_cast
      linarith
    exact_mod_cast h1
  rcases threewise_johnson I Ω S a c hS ha hc hAint with h | h
  · refine le_max_of_le_left ?_
    have h1 : (I.card : ℚ) * ((Ω.card : ℚ) - a) < Ω.card := by exact_mod_cast h
    have e1 : (1 : ℚ) - (a : ℚ) / Ω.card = ((Ω.card : ℚ) - a) / Ω.card := by
      field_simp
    rw [e1, one_div_div, le_div_iff₀ hna]
    exact h1.le
  · refine le_max_of_le_right ?_
    have h1 : (I.card : ℚ) * ((a : ℚ) ^ 2 * (3 * (Ω.card : ℚ) - a) - c * (Ω.card : ℚ) ^ 2)
        ≤ 3 * Ω.card * ((a : ℚ) ^ 2 + Ω.card * a - c * Ω.card) := by exact_mod_cast h
    rw [eA, eB, div_div_div_cancel_right₀ hn3.ne', le_div_iff₀ hApos]
    exact h1

end PeriodDescent
