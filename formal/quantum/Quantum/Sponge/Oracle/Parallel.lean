module

public import Quantum.Sponge.Oracle.Hardwired.Potential

@[expose] public section

/-!
# The parallel transition lemma

A round of width `w` makes `w` calls of the compressed oracle at once, on disjoint query
registers. For an event that is a union of one-cell events (some recorded cell has its value in a
target), one round raises the square root of the event weight by at most `√(6 w ε)`, against
`w √(6 ε)` for `w` sequential calls.

* **Union bound over cells** (`l2_opNorm_commutator_mul_le_of_cover`): let `Q` be the projector of
  an event covered by projectors `G c` (`G c ≤ Q`), in the sense that every transition of `U`
  into or out of the event lands in, or leaves, some `G c` with `H c`, a projector commuting with
  `U`. If `‖[G c, U] H c Λ‖ ≤ a c` for every `c`, and every basis state lies in `H c` for a set of
  `c` with `∑ (a c)² ≤ R`, then `‖[Q, U] Λ‖ ≤ √R`. The proof: the two directions of `[Q, U]` have
  orthogonal ranges, and the squared amplitude entering the event splits over the cells.
-/

open Matrix
open scoped Kronecker ENNReal ComplexOrder Matrix.Norms.L2Operator

namespace Quantum.Par

/-! ## Diagonal projectors on vectors -/

section diag

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem labelProjector_mulVec (β : n → Bool) (b : Bool) (v : n → ℂ) (a : n) :
    (labelProjector β b *ᵥ v) a = if β a = b then v a else 0 := by
  simp [labelProjector, mulVec_diagonal]

omit [Fintype n] in
/-- The label projector of the constant label `true` is the identity. -/
theorem labelProjector_const_true :
    labelProjector (fun _ : n ↦ true) true = (1 : Matrix n n ℂ) := by
  simp [labelProjector]

theorem labelProjector_mul_self (β : n → Bool) (b : Bool) :
    (labelProjector β b * labelProjector β b : Matrix n n ℂ) = labelProjector β b :=
  (isStarProjection_labelProjector β b).isIdempotentElem

theorem labelProjector_true_mul_false (β : n → Bool) :
    (labelProjector β true * labelProjector β false : Matrix n n ℂ) = 0 :=
  labelProjector_mul_labelProjector_of_ne β (by decide)

theorem labelProjector_mul_mul_self (β γ : n → Bool) (b c : Bool) :
    (labelProjector β b * (labelProjector γ c * labelProjector β b) : Matrix n n ℂ) =
      labelProjector β b * labelProjector γ c := by
  simp only [labelProjector, diagonal_mul_diagonal]
  congr 1
  funext a
  split_ifs <;> simp

omit [Fintype n] in
theorem conjTranspose_labelProjector' (β : n → Bool) (b : Bool) :
    (labelProjector β b : Matrix n n ℂ)ᴴ = labelProjector β b :=
  conjTranspose_labelProjector β b

/-- A projector of a label preserved by `U` commutes with `U`. -/
theorem labelProjector_mul_comm_of_preserves (U : Matrix n n ℂ) (β : n → Bool) (b : Bool)
    (h : ∀ x x', U x' x ≠ 0 → β x' = β x) :
    labelProjector β b * U = U * labelProjector β b := by
  ext x' x
  simp only [labelProjector, diagonal_mul, mul_diagonal]
  by_cases hU : U x' x = 0
  · simp [hU]
  · rw [h x x' hU, mul_comm]

/-- The squared length of a vector. -/
noncomputable def nsq (v : n → ℂ) : ℝ :=
  ∑ a, ‖v a‖ ^ 2

omit [DecidableEq n] in
theorem nsq_nonneg (v : n → ℂ) : 0 ≤ nsq v :=
  Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

omit [DecidableEq n] in
/-- Squared lengths of vectors with disjoint supports add. -/
theorem nsq_sub_of_disjoint {v v' : n → ℂ} (h : ∀ a, v a = 0 ∨ v' a = 0) :
    nsq (v - v') = nsq v + nsq v' := by
  simp only [nsq, ← Finset.sum_add_distrib, Pi.sub_apply]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rcases h a with h | h <;> simp [h]

/-- A vector splits into its parts on and off a label. -/
theorem nsq_labelProjector_add (β : n → Bool) (v : n → ℂ) :
    nsq (labelProjector β true *ᵥ v) + nsq (labelProjector β false *ᵥ v) = nsq v := by
  simp only [nsq, ← Finset.sum_add_distrib, labelProjector_mulVec]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  cases β a <;> simp

theorem nsq_labelProjector_le (β : n → Bool) (b : Bool) (v : n → ℂ) :
    nsq (labelProjector β b *ᵥ v) ≤ nsq v := by
  refine Finset.sum_le_sum fun a _ ↦ ?_
  rw [labelProjector_mulVec]
  split_ifs <;> simp

theorem nsq_mulVec_le {m : Type*} [Fintype m] (K : Matrix m n ℂ) (v : n → ℂ) :
    nsq (K *ᵥ v) ≤ ‖K‖ ^ 2 * nsq v :=
  Matrix.sum_norm_mulVec_sq_le K v

theorem l2_opNorm_le_of_nsq_le {m : Type*} [Fintype m] {K : Matrix m n ℂ} {R : ℝ} (hR : 0 ≤ R)
    (h : ∀ v, nsq (K *ᵥ v) ≤ R * nsq v) : ‖K‖ ≤ √R := by
  refine Matrix.l2_opNorm_le_of_sum_norm_mulVec_sq_le (Real.sqrt_nonneg R) fun v ↦ ?_
  rw [Real.sq_sqrt hR]
  exact h v

/-- Multiplying by contractions on both sides does not increase the norm. -/
theorem l2_opNorm_sandwich_le {A B C : Matrix n n ℂ} (hA : ‖A‖ ≤ 1) (hC : ‖C‖ ≤ 1) :
    ‖A * B * C‖ ≤ ‖B‖ :=
  (l2_opNorm_mul _ _).trans ((mul_le_of_le_one_right (norm_nonneg _) hC).trans
    ((l2_opNorm_mul _ _).trans (mul_le_of_le_one_left (norm_nonneg _) hA)))

end diag

/-! ## Certificates and norms -/

section cert

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- A Gram certificate `r • 1 - Kᴴ K ⪰ 0` bounds the squared norm of `K`. -/
theorem l2_opNorm_sq_le_of_posSemidef {K : Matrix m n ℂ} {r : ℝ} (hr : 0 ≤ r)
    (h : (r • (1 : Matrix n n ℂ) - Kᴴ * K).PosSemidef) : ‖K‖ ^ 2 ≤ r := by
  have hv : ∀ v : n → ℂ, nsq (K *ᵥ v) ≤ r * nsq v := fun v ↦ by
    have h0 := h.dotProduct_mulVec_nonneg v
    rw [sub_mulVec, dotProduct_sub, star_dotProduct_conjTranspose_mul_self_mulVec, smul_mulVec,
      one_mulVec, dotProduct_smul, sub_nonneg, Complex.real_smul] at h0
    simp only [star_dotProduct_self_eq_sum_norm_sq] at h0
    have h1 : ((nsq (K *ᵥ v) : ℝ) : ℂ) ≤ ((r * nsq v : ℝ) : ℂ) := by
      rw [Complex.ofReal_mul]
      exact h0
    exact Complex.real_le_real.mp h1
  have := l2_opNorm_le_of_nsq_le hr hv
  calc ‖K‖ ^ 2 ≤ (√r) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) this 2
    _ = r := Real.sq_sqrt hr

end cert

/-! ## The union bound over cells -/

section union

variable {n : Type*} [Fintype n] [DecidableEq n] {ι : Type*} [Fintype ι]

local notation "Π[" β "," b "]" => (labelProjector β b : Matrix n n ℂ)

/-- **Entering the event, cell by cell.** The amplitude that `U` carries from outside the event
`q` (inputs restricted to `lam`, outputs to `o`) into it is bounded through the cells. -/
theorem l2_opNorm_enter_le (U : Matrix n n ℂ) (o q lam : n → Bool) (g h : ι → n → Bool)
    (a : ι → ℝ) {R : ℝ} (hR : 0 ≤ R)
    (hsub : ∀ c x, g c x = true → q x = true)
    (hh : ∀ c x x', U x' x ≠ 0 → h c x' = h c x)
    (hcover : ∀ x x', U x' x ≠ 0 → q x = false → q x' = true → o x' = true →
      ∃ c, g c x' = true ∧ h c x' = true)
    (hcell : ∀ c, ‖Π[o, true] * Π[g c, true] * U * Π[g c, false] * Π[h c, true] * Π[lam, true]‖ ≤
      a c)
    (hmult : ∀ x, lam x = true → ∑ c, (if h c x = true then a c ^ 2 else 0) ≤ R) :
    ‖Π[o, true] * Π[q, true] * U * Π[q, false] * Π[lam, true]‖ ≤ √R := by
  refine l2_opNorm_le_of_nsq_le hR fun v ↦ ?_
  set x := Π[q, false] *ᵥ (Π[lam, true] *ᵥ v) with hx
  set y := U *ᵥ x with hy
  have hlhs : (Π[o, true] * Π[q, true] * U * Π[q, false] * Π[lam, true]) *ᵥ v =
      Π[o, true] *ᵥ (Π[q, true] *ᵥ y) := by
    simp only [hy, hx, ← mulVec_mulVec]
  -- The cell pieces of the output.
  have hpiece : ∀ c, Π[o, true] *ᵥ (Π[g c, true] *ᵥ (Π[h c, true] *ᵥ y)) =
      (Π[o, true] * Π[g c, true] * U * Π[g c, false] * Π[h c, true] * Π[lam, true]) *ᵥ
        (Π[q, false] *ᵥ v) := fun c ↦ by
    have hm : Π[o, true] * Π[g c, true] * U * Π[g c, false] * Π[h c, true] * Π[lam, true] *
        Π[q, false] = Π[o, true] * Π[g c, true] * Π[h c, true] * U * Π[q, false] *
          Π[lam, true] := by
      ext x' x
      simp only [labelProjector, Matrix.mul_assoc, diagonal_mul_diagonal, diagonal_mul,
        mul_diagonal]
      by_cases hU : U x' x = 0
      · simp [hU]
      · rw [hh c x x' hU]
        by_cases hq : q x = false
        · have hg : g c x = false := by
            by_contra hg
            simp only [Bool.not_eq_false] at hg
            simp [hsub c x hg] at hq
          by_cases h1 : o x' = true <;> by_cases h2 : g c x' = true <;>
            by_cases h3 : h c x = true <;> by_cases h4 : lam x = true <;>
            simp [hq, hg, h1, h2, h3, h4]
        · simp [hq]
    rw [mulVec_mulVec v, hm]
    simp only [hy, hx, ← mulVec_mulVec]
  -- Pointwise: the event output is covered by the cell outputs.
  have hpt : ∀ x', ‖(Π[o, true] *ᵥ (Π[q, true] *ᵥ y)) x'‖ ^ 2 ≤
      ∑ c, ‖(Π[o, true] *ᵥ (Π[g c, true] *ᵥ (Π[h c, true] *ᵥ y))) x'‖ ^ 2 := fun x' ↦ by
    simp only [labelProjector_mulVec]
    by_cases hox : o x' = true
    · by_cases hqx : q x' = true
      · by_cases hyx : y x' = 0
        · simp [hyx]
        · obtain ⟨x₀, -, hx₀⟩ := Finset.exists_ne_zero_of_sum_ne_zero hyx
          have hU : U x' x₀ ≠ 0 := left_ne_zero_of_mul hx₀
          have hxx : x x₀ ≠ 0 := right_ne_zero_of_mul hx₀
          have hq0 : q x₀ = false := by
            by_contra hq0
            apply hxx
            simp only [hx, labelProjector_mulVec]
            simp [hq0]
          obtain ⟨c, hgc, hhc⟩ := hcover x₀ x' hU hq0 hqx hox
          refine le_trans (le_of_eq ?_) (Finset.single_le_sum (f := fun c ↦
            ‖(if o x' = true then (if g c x' = true then (if h c x' = true then y x' else 0)
              else 0) else 0)‖ ^ 2) (fun _ _ ↦ sq_nonneg _) (Finset.mem_univ c))
          simp [hox, hqx, hgc, hhc]
      · refine le_trans (le_of_eq ?_) (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)
        simp [hox, hqx]
    · refine le_trans (le_of_eq ?_) (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)
      simp [hox]
  -- Each cell piece is bounded by its weighted input.
  have hcellv : ∀ c, nsq (Π[o, true] *ᵥ (Π[g c, true] *ᵥ (Π[h c, true] *ᵥ y))) ≤
      a c ^ 2 * nsq (Π[h c, true] *ᵥ (Π[lam, true] *ᵥ (Π[q, false] *ᵥ v))) := fun c ↦ by
    rw [hpiece c]
    have hK : ∀ u, (Π[o, true] * Π[g c, true] * U * Π[g c, false] * Π[h c, true] *
        Π[lam, true]) *ᵥ u = (Π[o, true] * Π[g c, true] * U * Π[g c, false] * Π[h c, true] *
          Π[lam, true]) *ᵥ (Π[h c, true] *ᵥ (Π[lam, true] *ᵥ u)) := fun u ↦ by
      rw [mulVec_mulVec, mulVec_mulVec]
      congr 1
      ext x' x
      simp only [labelProjector, mul_diagonal]
      by_cases h1 : h c x = true <;> by_cases h2 : lam x = true <;> simp [h1, h2]
    rw [hK]
    refine (nsq_mulVec_le _ _).trans ?_
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hcell c) 2)
      (nsq_nonneg _)
  -- Sum over the cells.
  rw [hlhs]
  calc nsq (Π[o, true] *ᵥ (Π[q, true] *ᵥ y))
      ≤ ∑ c, nsq (Π[o, true] *ᵥ (Π[g c, true] *ᵥ (Π[h c, true] *ᵥ y))) := by
        simp only [nsq]
        rw [Finset.sum_comm]
        exact Finset.sum_le_sum fun x' _ ↦ hpt x'
    _ ≤ ∑ c, a c ^ 2 * nsq (Π[h c, true] *ᵥ (Π[lam, true] *ᵥ (Π[q, false] *ᵥ v))) :=
        Finset.sum_le_sum fun c _ ↦ hcellv c
    _ = ∑ x', (if lam x' = true then (if q x' = false then ‖v x'‖ ^ 2 else 0) else 0) *
          ∑ c, (if h c x' = true then a c ^ 2 else 0) := by
        simp only [nsq, labelProjector_mulVec, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun x' _ ↦ Finset.sum_congr rfl fun c _ ↦ ?_
        by_cases h1 : h c x' = true <;> by_cases h2 : lam x' = true <;>
          by_cases h3 : q x' = false <;> simp [h1, h2, h3, mul_comm]
    _ ≤ ∑ x', R * ‖v x'‖ ^ 2 := by
        refine Finset.sum_le_sum fun x' _ ↦ ?_
        split_ifs with h2 h3
        · rw [mul_comm]
          exact mul_le_mul_of_nonneg_right (hmult x' h2) (sq_nonneg _)
        · rw [zero_mul]
          exact mul_nonneg hR (sq_nonneg _)
        · rw [zero_mul]
          exact mul_nonneg hR (sq_nonneg _)
    _ = R * nsq v := by rw [nsq, Finset.mul_sum]

/-- The amplitude a cell event gains, bounded by its commutator. -/
theorem l2_opNorm_cell_enter_le (U : Matrix n n ℂ) (g h lam : n → Bool) :
    ‖Π[g, true] * U * Π[g, false] * Π[h, true] * Π[lam, true]‖ ≤
      ‖(Π[g, true] * U - U * Π[g, true]) * Π[h, true] * Π[lam, true]‖ := by
  have he : Π[g, true] * U * Π[g, false] * Π[h, true] * Π[lam, true] =
      Π[g, true] * ((Π[g, true] * U - U * Π[g, true]) * Π[h, true] * Π[lam, true]) *
        Π[g, false] := by
    ext x' x
    simp only [labelProjector, diagonal_mul, mul_diagonal, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.sub_apply]
    cases g x <;> cases g x' <;> simp
  rw [he]
  refine (l2_opNorm_mul _ _).trans ?_
  refine (mul_le_of_le_one_right (norm_nonneg _) (l2_opNorm_labelProjector_le_one _ _)).trans ?_
  refine (l2_opNorm_mul _ _).trans ?_
  exact mul_le_of_le_one_left (norm_nonneg _) (l2_opNorm_labelProjector_le_one _ _)

/-- The amplitude a cell event loses, bounded by its commutator, for `U` preserving `h`. -/
theorem l2_opNorm_cell_leave_le (U : Matrix n n ℂ) (g h lam : n → Bool)
    (hh : ∀ x x', U x' x ≠ 0 → h x' = h x) :
    ‖Π[lam, true] * Π[g, true] * Uᴴ * Π[g, false] * Π[h, true]‖ ≤
      ‖(Π[g, true] * U - U * Π[g, true]) * Π[h, true] * Π[lam, true]‖ := by
  rw [← l2_opNorm_conjTranspose]
  have he : (Π[lam, true] * Π[g, true] * Uᴴ * Π[g, false] * Π[h, true])ᴴ =
      -(Π[g, false] * ((Π[g, true] * U - U * Π[g, true]) * Π[h, true] * Π[lam, true]) *
        Π[g, true]) := by
    simp only [conjTranspose_mul, conjTranspose_labelProjector', conjTranspose_conjTranspose]
    ext x' x
    simp only [labelProjector, diagonal_mul, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.sub_apply, Matrix.neg_apply]
    by_cases hU : U x' x = 0
    · simp [hU]
    · rw [hh x x' hU]
      by_cases hgx : g x = true <;> by_cases hgx' : g x' = true <;> simp [hgx, hgx']
  rw [he, norm_neg]
  refine (l2_opNorm_mul _ _).trans ?_
  refine (mul_le_of_le_one_right (norm_nonneg _) (l2_opNorm_labelProjector_le_one _ _)).trans ?_
  refine (l2_opNorm_mul _ _).trans ?_
  exact mul_le_of_le_one_left (norm_nonneg _) (l2_opNorm_labelProjector_le_one _ _)

/-- The commutator splits into the amplitude entering and the amplitude leaving the event. -/
theorem l2_opNorm_commutator_le_of_enter_leave (U : Matrix n n ℂ) (q lam : n → Bool) {R : ℝ}
    (hR : 0 ≤ R) (hin : ‖Π[q, true] * U * Π[q, false] * Π[lam, true]‖ ≤ √R)
    (hout : ‖Π[lam, true] * Π[q, true] * Uᴴ * Π[q, false]‖ ≤ √R) :
    ‖(Π[q, true] * U - U * Π[q, true]) * Π[lam, true]‖ ≤ √R := by
  have hout' : ‖Π[q, false] * U * Π[q, true] * Π[lam, true]‖ ≤ √R := by
    rw [← l2_opNorm_conjTranspose]
    simpa only [conjTranspose_mul, conjTranspose_labelProjector', conjTranspose_conjTranspose,
      Matrix.mul_assoc] using hout
  refine l2_opNorm_le_of_nsq_le hR fun v ↦ ?_
  have hsplit : (Π[q, true] * U - U * Π[q, true]) * Π[lam, true] =
      Π[q, true] * U * Π[q, false] * Π[lam, true] -
        Π[q, false] * U * Π[q, true] * Π[lam, true] := by
    have h1 : (Π[q, false] : Matrix n n ℂ) = 1 - Π[q, true] := by
      rw [one_sub_labelProjector_bool]
      rfl
    rw [h1]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]
    abel
  rw [hsplit, sub_mulVec, nsq_sub_of_disjoint]
  · have e1 : (Π[q, true] * U * Π[q, false] * Π[lam, true]) *ᵥ v =
        (Π[q, true] * U * Π[q, false] * Π[lam, true]) *ᵥ (Π[q, false] *ᵥ v) := by
      rw [mulVec_mulVec]
      congr 1
      simp only [Matrix.mul_assoc, labelProjector_mul_mul_self]
    have e2 : (Π[q, false] * U * Π[q, true] * Π[lam, true]) *ᵥ v =
        (Π[q, false] * U * Π[q, true] * Π[lam, true]) *ᵥ (Π[q, true] *ᵥ v) := by
      rw [mulVec_mulVec]
      congr 1
      simp only [Matrix.mul_assoc, labelProjector_mul_mul_self]
    rw [e1, e2]
    have hs : 0 ≤ √R := Real.sqrt_nonneg R
    calc nsq ((Π[q, true] * U * Π[q, false] * Π[lam, true]) *ᵥ (Π[q, false] *ᵥ v)) +
          nsq ((Π[q, false] * U * Π[q, true] * Π[lam, true]) *ᵥ (Π[q, true] *ᵥ v))
        ≤ (√R) ^ 2 * nsq (Π[q, false] *ᵥ v) + (√R) ^ 2 * nsq (Π[q, true] *ᵥ v) := by
          refine add_le_add ?_ ?_
          · exact (nsq_mulVec_le _ _).trans (mul_le_mul_of_nonneg_right
              (pow_le_pow_left₀ (norm_nonneg _) hin 2) (nsq_nonneg _))
          · exact (nsq_mulVec_le _ _).trans (mul_le_mul_of_nonneg_right
              (pow_le_pow_left₀ (norm_nonneg _) hout' 2) (nsq_nonneg _))
      _ = R * nsq v := by
          rw [Real.sq_sqrt hR, ← mul_add, add_comm, nsq_labelProjector_add]
  · intro x'
    simp only [← mulVec_mulVec, labelProjector_mulVec]
    cases q x' <;> simp

/-- **The union bound over cells.** Let the event `q` be covered by the cell events `g c`
(`g c ≤ q`), each paired with a label `h c` preserved by `U`: every transition of `U` into or out
of the event has some cell `c` with `g c` and `h c` on its event side. If the commutator of `U`
with each cell event, restricted to `h c` and to inputs in `lam`, has norm at most `a c`, and
every basis state in `lam` meets the labels `h c` with `∑ (a c)² ≤ R`, then
`‖[Q, U] Λ‖ ≤ √R`. -/
theorem l2_opNorm_commutator_le_of_cover (U : Matrix n n ℂ) (q lam : n → Bool)
    (g h : ι → n → Bool) (a : ι → ℝ) {R : ℝ} (hR : 0 ≤ R)
    (hsub : ∀ c x, g c x = true → q x = true)
    (hh : ∀ c x x', U x' x ≠ 0 → h c x' = h c x)
    (hcover : ∀ x x', U x' x ≠ 0 → q x ≠ q x' →
      ∃ c, (g c x' = true ∧ h c x' = true ∧ q x' = true) ∨
        (g c x = true ∧ h c x = true ∧ q x = true))
    (hcell : ∀ c, ‖(Π[g c, true] * U - U * Π[g c, true]) * Π[h c, true] * Π[lam, true]‖ ≤ a c)
    (hmult : ∀ x, ∑ c, (if h c x = true then a c ^ 2 else 0) ≤ R) :
    ‖(Π[q, true] * U - U * Π[q, true]) * Π[lam, true]‖ ≤ √R := by
  refine l2_opNorm_commutator_le_of_enter_leave U q lam hR ?_ ?_
  · -- Entering.
    have h := l2_opNorm_enter_le (o := fun _ ↦ true) U q lam g h a hR hsub hh
      (fun x x' hU hq hq' _ ↦ by
        obtain ⟨c, hc⟩ := hcover x x' hU (by rw [hq, hq']; decide)
        rcases hc with ⟨h1, h2, -⟩ | ⟨-, -, h3⟩
        · exact ⟨c, h1, h2⟩
        · simp [hq] at h3)
      (fun c ↦ by
        rw [labelProjector_const_true, Matrix.one_mul]
        exact (l2_opNorm_cell_enter_le U (g c) (h c) lam).trans (hcell c)) fun x _ ↦ hmult x
    rwa [labelProjector_const_true, Matrix.one_mul] at h
  · -- Leaving: entering for `Uᴴ`.
    have h := l2_opNorm_enter_le (lam := fun _ ↦ true) Uᴴ lam q g h a hR hsub
      (fun c x x' hU ↦ (hh c x' x fun h0 ↦ hU (by simp [conjTranspose_apply, h0])).symm)
      (fun x x' hU hq hq' _ ↦ by
        have hU' : U x x' ≠ 0 := fun h0 ↦ hU (by simp [conjTranspose_apply, h0])
        obtain ⟨c, hc⟩ := hcover x' x hU' (by rw [hq, hq']; decide)
        rcases hc with ⟨-, -, h3⟩ | ⟨h1, h2, -⟩
        · simp [hq] at h3
        · exact ⟨c, h1, h2⟩)
      (fun c ↦ by
        rw [labelProjector_const_true, Matrix.mul_one]
        exact (l2_opNorm_cell_leave_le U (g c) (h c) lam (hh c)).trans (hcell c))
      (fun x _ ↦ hmult x)
    rwa [labelProjector_const_true, Matrix.mul_one] at h

end union

/-! ## Products of rounds -/

section prod

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The product of the calls of a round, slot `0` first. -/
def roundProd : {w : ℕ} → (Fin w → Matrix n n ℂ) → Matrix n n ℂ
  | 0, _ => 1
  | _ + 1, V => roundProd (fun i ↦ V i.succ) * V 0

theorem roundProd_zero (V : Fin 0 → Matrix n n ℂ) : roundProd V = 1 :=
  rfl

theorem roundProd_succ {w : ℕ} (V : Fin (w + 1) → Matrix n n ℂ) :
    roundProd V = roundProd (fun i ↦ V i.succ) * V 0 :=
  rfl

omit [Fintype n] in
/-- Matrices whose nonzero entries keep a label. -/
def Preserves {κ : Type*} (β : n → κ) (M : Matrix n n ℂ) : Prop :=
  ∀ x x', M x' x ≠ 0 → β x' = β x

omit [DecidableEq n] in
theorem Preserves.mul {κ : Type*} {β : n → κ} {M M' : Matrix n n ℂ} (h : Preserves β M)
    (h' : Preserves β M') : Preserves β (M * M') := fun x x' hx ↦ by
  rw [Matrix.mul_apply] at hx
  obtain ⟨y, -, hy⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx
  exact (h y x' (left_ne_zero_of_mul hy)).trans (h' x y (right_ne_zero_of_mul hy))

omit [Fintype n] in
theorem preserves_one {κ : Type*} (β : n → κ) : Preserves β (1 : Matrix n n ℂ) := fun x x' h ↦ by
  rw [Matrix.one_apply] at h
  split_ifs at h with hx
  · rw [hx]
  · exact absurd rfl h

omit [Fintype n] in
theorem preserves_basisMatrix {κ : Type*} (β : n → κ) (f : n → n) (hf : ∀ x, β (f x) = β x) :
    Preserves β (basisMatrix f) := fun x x' h ↦ by
  rw [basisMatrix_apply] at h
  split_ifs at h with hx
  · rw [hx, hf]
  · exact absurd rfl h

/-- A label preserved by every call is preserved by the round. -/
theorem Preserves.roundProd {κ : Type*} {β : n → κ} :
    ∀ {w : ℕ} {V : Fin w → Matrix n n ℂ}, (∀ i, Preserves β (V i)) → Preserves β (roundProd V)
  | 0, _, _ => preserves_one β
  | _ + 1, _, hV => (Preserves.roundProd fun i ↦ hV i.succ).mul (hV 0)

/-- A projector of a preserved label commutes. -/
theorem Preserves.labelProjector_mul_comm {β : n → Bool} {M : Matrix n n ℂ} (h : Preserves β M)
    (b : Bool) : labelProjector β b * M = M * labelProjector β b :=
  labelProjector_mul_comm_of_preserves M β b h

/-- Conjugating every call by an involution conjugates the round. -/
theorem roundProd_conj (C' : Matrix n n ℂ) (hC : C' * C' = 1) :
    ∀ {w : ℕ} (B : Fin w → Matrix n n ℂ),
      roundProd (fun i ↦ C' * B i * C') = C' * roundProd B * C'
  | 0, _ => by simp [roundProd_zero, hC]
  | _ + 1, B => by
      rw [roundProd_succ, roundProd_succ, roundProd_conj C' hC (fun i ↦ B i.succ)]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc C' C' (B 0 * C'), hC, Matrix.one_mul]

/-- A round of contractions is a contraction. -/
theorem l2_opNorm_roundProd_le_one :
    ∀ {w : ℕ} {V : Fin w → Matrix n n ℂ}, (∀ i, ‖V i‖ ≤ 1) → ‖roundProd V‖ ≤ 1
  | 0, _, _ => Matrix.l2_opNorm_one_le
  | _ + 1, _, hV => (l2_opNorm_mul _ _).trans ((mul_le_mul (l2_opNorm_roundProd_le_one
      fun i ↦ hV i.succ) (hV 0) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1))

end prod

/-! ## Calls on one slot of a round -/

section slot

variable {w : ℕ} {S N : Type} [Fintype S] [DecidableEq S] [Fintype N] [DecidableEq N]

/-- Splitting the round register into slot `j` with the runtime register, and the other slots. -/
def slotEquiv (j : Fin w) : (Fin w → S) × N ≃ (S × N) × ({i // i ≠ j} → S) where
  toFun x := ((x.1 j, x.2), fun i ↦ x.1 i)
  invFun y := (fun i ↦ if h : i = j then y.1.1 else y.2 ⟨i, h⟩, y.1.2)
  left_inv x := Prod.ext (funext fun i ↦ by
    by_cases h : i = j
    · subst h
      simp
    · simp [h]) rfl
  right_inv y := by
    obtain ⟨⟨s, d⟩, r⟩ := y
    refine Prod.ext (by simp) (funext fun i ↦ ?_)
    simp [i.2]

/-- An operator on slot `j` and the runtime register, the identity on the other slots. -/
noncomputable def slotLift (j : Fin w) (M : Matrix (S × N) (S × N) ℂ) :
    Matrix ((Fin w → S) × N) ((Fin w → S) × N) ℂ :=
  onFactor (slotEquiv j) M

omit [Fintype S] [Fintype N] [DecidableEq N] in
theorem slotLift_apply (j : Fin w) (M : Matrix (S × N) (S × N) ℂ) (x' x : (Fin w → S) × N) :
    slotLift j M x' x =
      if (fun i : {i // i ≠ j} ↦ x'.1 i) = (fun i : {i // i ≠ j} ↦ x.1 i) then
        M (x'.1 j, x'.2) (x.1 j, x.2)
        else 0 := by
  rw [slotLift, onFactor_apply]
  rfl

omit [DecidableEq N] in
theorem slotLift_mul (j : Fin w) (M M' : Matrix (S × N) (S × N) ℂ) :
    slotLift j (M * M') = slotLift j M * slotLift j M' :=
  onFactor_mul _ M M'

omit [Fintype S] [Fintype N] [DecidableEq N] in
theorem slotLift_sub (j : Fin w) (M M' : Matrix (S × N) (S × N) ℂ) :
    slotLift j (M - M') = slotLift j M - slotLift j M' := by
  ext x' x
  simp only [slotLift_apply, Matrix.sub_apply]
  split_ifs <;> simp

theorem l2_opNorm_slotLift_le (j : Fin w) (M : Matrix (S × N) (S × N) ℂ) :
    ‖slotLift j M‖ ≤ ‖M‖ := by
  rw [slotLift, onFactor, reindex_apply, Equiv.symm_symm, Matrix.l2_opNorm_submatrix_equiv]
  exact Matrix.l2_opNorm_kronecker_one_le M

omit [Fintype S] [Fintype N] [DecidableEq N] in
/-- An operator on the runtime register alone stays one. -/
theorem slotLift_one_kronecker (j : Fin w) (C : Matrix N N ℂ) :
    slotLift j ((1 : Matrix S S ℂ) ⊗ₖ C) = (1 : Matrix (Fin w → S) (Fin w → S) ℂ) ⊗ₖ C := by
  ext ⟨a', s'⟩ ⟨a, s⟩
  rw [slotLift_apply, kroneckerMap_apply, kroneckerMap_apply, Matrix.one_apply, Matrix.one_apply]
  by_cases ha : a' = a
  · subst ha
    simp
  · have hne : ¬((fun i : {i // i ≠ j} ↦ a' i) = (fun i : {i // i ≠ j} ↦ a i) ∧ a' j = a j) :=
      fun h ↦ ha (funext fun i ↦ by
        by_cases hi : i = j
        · subst hi
          exact h.2
        · exact congrFun h.1 (⟨i, hi⟩ : {i // i ≠ j}))
    simp only [ha, ↓reduceIte, zero_mul]
    split_ifs with h1 h2
    · exact absurd (And.intro h1 h2) hne
    · simp
    · rfl

omit [Fintype S] [Fintype N] in
/-- A label of the runtime register stays one. -/
theorem slotLift_labelProjector (j : Fin w) (β : N → Bool) (b : Bool) :
    slotLift j (labelProjector (fun p : S × N ↦ β p.2) b) =
      labelProjector (fun x : (Fin w → S) × N ↦ β x.2) b := by
  rw [← Sponge.one_kronecker_labelProjector, slotLift_one_kronecker,
    Sponge.one_kronecker_labelProjector]

end slot

/-! ## Two ring identities -/

section ring

variable {R : Type*} [Ring R]

/-- Conjugating a commutator by an invertible element commuting with the projectors. -/
theorem conj_commutator_eq {G U Sh Sh' P : R} (h1 : Sh' * Sh = 1) (hG : Sh' * G = G * Sh')
    (hP : P * Sh = Sh * P) :
    Sh' * ((G * (Sh * U * Sh') - Sh * U * Sh' * G) * P) * Sh = (G * U - U * G) * P := by
  rw [sub_mul, mul_sub, sub_mul, sub_mul]
  congr 1
  · rw [show Sh' * (G * (Sh * U * Sh') * P) * Sh = Sh' * G * Sh * U * Sh' * (P * Sh) by
      simp only [mul_assoc], hG, hP,
      show G * Sh' * Sh * U * Sh' * (Sh * P) = G * (Sh' * Sh) * U * (Sh' * Sh) * P by
        simp only [mul_assoc], h1, mul_one, mul_one]
  · rw [show Sh' * (Sh * U * Sh' * G * P) * Sh = Sh' * Sh * U * (Sh' * G) * (P * Sh) by
      simp only [mul_assoc], hG, hP,
      show Sh' * Sh * U * (G * Sh') * (Sh * P) = Sh' * Sh * U * G * (Sh' * Sh) * P by
        simp only [mul_assoc], h1, one_mul, mul_one]

/-- A commutator through an operator that agrees with `E V` on a projector. -/
theorem commutator_mul_eq_of_mul_eq {G U E V H L : R} (hU : U * H = E * V * H)
    (hGE : G * E = E * G) (hGH : H * G = G * H) (hHL : H * L = L * H) :
    (G * U - U * G) * (H * L) = E * ((G * V - V * G) * L) * H := by
  simp only [sub_mul, mul_sub]
  congr 1
  · rw [show G * U * (H * L) = G * (U * H) * L by simp only [mul_assoc], hU,
      show G * (E * V * H) * L = G * E * V * (H * L) by simp only [mul_assoc], hGE, hHL]
    simp only [mul_assoc]
  · rw [show U * G * (H * L) = U * (H * G) * L by rw [hGH]; simp only [mul_assoc],
      show U * (H * G) * L = U * H * G * L by simp only [mul_assoc], hU,
      show E * V * H * G * L = E * V * (H * G) * L by simp only [mul_assoc], hGH,
      show E * V * (G * H) * L = E * V * G * (H * L) by simp only [mul_assoc], hHL]
    simp only [mul_assoc]

end ring

/-! ## Rounds of one oracle port -/

section port

variable {w : ℕ} {A Y N : Type} [Fintype A] [DecidableEq A] [Fintype Y] [DecidableEq Y]
  [AddCommGroup Y] [Fintype N] [DecidableEq N]

/-- Adding the read values `rd s` at the queried cells into the slots selected by `P`. -/
def addSet (rd : N → A → Y) (P : Fin w → (Fin w → A × Y) → Bool)
    (x : (Fin w → A × Y) × N) : (Fin w → A × Y) × N :=
  (fun i ↦ if P i x.1 then ((x.1 i).1, (x.1 i).2 + rd x.2 (x.1 i).1) else x.1 i, x.2)

/-- A slot selection reading only the queried cells. -/
def CellsOnly (P : Fin w → (Fin w → A × Y) → Bool) : Prop :=
  ∀ i a a', (∀ j, (a j).1 = (a' j).1) → P i a = P i a'

/-- The queried cells of a basis state of the round register. -/
def cells (x : (Fin w → A × Y) × N) : Fin w → A :=
  fun i ↦ (x.1 i).1

omit [Fintype A] [DecidableEq A] [Fintype Y] [DecidableEq Y] [Fintype N] [DecidableEq N] in
theorem cells_addSet (rd : N → A → Y) (P : Fin w → (Fin w → A × Y) → Bool)
    (x : (Fin w → A × Y) × N) : cells (addSet rd P x) = cells x := by
  funext i
  simp only [cells, addSet]
  split_ifs <;> rfl

omit [Fintype A] [DecidableEq A] [Fintype Y] [DecidableEq Y] [Fintype N] [DecidableEq N] in
theorem addSet_comp (rd : N → A → Y) {P P' : Fin w → (Fin w → A × Y) → Bool}
    (hP : CellsOnly P) (hd : ∀ i a, P i a = true → P' i a = false) :
    addSet rd P ∘ addSet rd P' = addSet rd (fun i a ↦ P i a || P' i a) := by
  funext x
  refine Prod.ext (funext fun i ↦ ?_) rfl
  have hc : P i (addSet rd P' x).1 = P i x.1 :=
    hP i _ _ fun j ↦ congrFun (cells_addSet rd P' x) j
  change (if P i (addSet rd P' x).1 then _ else _) = _
  rw [hc]
  simp only [addSet]
  by_cases h1 : P i x.1 = true
  · have h2 := hd i x.1 h1
    simp [h1, h2]
  · by_cases h2 : P' i x.1 = true <;> simp [h1, h2]

omit [Fintype A] [DecidableEq A] [Fintype Y] [DecidableEq Y] [Fintype N] [DecidableEq N] in
theorem addSet_injective (rd : N → A → Y) {P : Fin w → (Fin w → A × Y) → Bool}
    (hP : CellsOnly P) : Function.Injective (addSet rd P) := by
  intro x x' h
  have h2 : x.2 = x'.2 := by
    have h' := congrArg Prod.snd h
    exact h'
  have hc : cells x = cells x' := by rw [← cells_addSet rd P x, h, cells_addSet]
  refine Prod.ext (funext fun i ↦ ?_) h2
  have hi := congrFun (congrArg Prod.fst h) i
  have hPi : P i x.1 = P i x'.1 := hP i _ _ fun j ↦ congrFun hc j
  have hci : (x.1 i).1 = (x'.1 i).1 := congrFun hc i
  simp only [addSet, hPi, h2] at hi
  split_ifs at hi
  · refine Prod.ext hci ?_
    have h' := congrArg Prod.snd hi
    simp only [hci] at h'
    exact add_right_cancel h'
  · exact hi

omit [Fintype A] [DecidableEq A] [Fintype Y] [DecidableEq Y] [AddCommGroup Y] [Fintype N]
  [DecidableEq N] in
theorem cellsOnly_const (b : Bool) : CellsOnly (fun _ _ ↦ b : Fin w → (Fin w → A × Y) → Bool) :=
  fun _ _ _ _ ↦ rfl

/-- The calls of a round on the slots `σ t`, as one basis map. -/
theorem roundProd_basisMatrix_addSet (rd : N → A → Y) (P : Fin w → (Fin w → A × Y) → Bool)
    (hP : CellsOnly P) : ∀ {k : ℕ} (σ : Fin k → Fin w), Function.Injective σ →
      roundProd (fun t ↦ basisMatrix (addSet rd (fun i a ↦ decide (i = σ t) && P i a))) =
        basisMatrix (addSet rd (fun i a ↦ decide (∃ t, σ t = i) && P i a))
  | 0, σ, _ => by
      rw [roundProd_zero]
      have h : addSet rd (fun i a ↦ decide (∃ t, σ t = i) && P i a) = id := by
        funext x
        refine Prod.ext (funext fun i ↦ ?_) rfl
        simp [addSet]
      rw [h, basisMatrix_id]
  | k + 1, σ, hσ => by
      rw [roundProd_succ, roundProd_basisMatrix_addSet rd P hP (fun t ↦ σ t.succ)
        (hσ.comp (Fin.succ_injective _)), ← basisMatrix_comp, addSet_comp rd
        (fun i a a' h ↦ by simp [hP i a a' h]) (fun i a h ↦ by
          simp only [Bool.and_eq_true, decide_eq_true_eq] at h
          obtain ⟨⟨t, ht⟩, -⟩ := h
          have hne : σ t.succ ≠ σ 0 := fun he ↦ Fin.succ_ne_zero t (hσ he)
          simp [← ht, hne])]
      congr 2
      funext i a
      by_cases h0 : i = σ 0
      · subst h0
        cases P (σ 0) a <;> simp
      · have h0' : σ 0 ≠ i := Ne.symm h0
        cases P i a <;> simp [Fin.exists_fin_succ, h0, h0']

/-- The oracle port: the table oracle of `rd` conjugated by `C` on the runtime register. -/
noncomputable def portMat (rd : N → A → Y) (C : Matrix N N ℂ) :
    Matrix ((A × Y) × N) ((A × Y) × N) ℂ :=
  ((1 : Matrix (A × Y) (A × Y) ℂ) ⊗ₖ C) * tableOracle rd * ((1 : Matrix (A × Y) (A × Y) ℂ) ⊗ₖ C)

/-- A basis map conjugated by `C` on the runtime register. -/
noncomputable def conjC (C : Matrix N N ℂ) (f : (Fin w → A × Y) × N → (Fin w → A × Y) × N) :
    Matrix ((Fin w → A × Y) × N) ((Fin w → A × Y) × N) ℂ :=
  ((1 : Matrix (Fin w → A × Y) (Fin w → A × Y) ℂ) ⊗ₖ C) * basisMatrix f *
    ((1 : Matrix (Fin w → A × Y) (Fin w → A × Y) ℂ) ⊗ₖ C)

omit [Fintype A] [Fintype Y] [Fintype N] in
theorem slotLift_tableOracle (rd : N → A → Y) (j : Fin w) :
    slotLift j (tableOracle rd) = basisMatrix (addSet rd (fun i _ ↦ decide (i = j))) := by
  rw [slotLift, tableOracle, onFactor_basisMatrix]
  congr 1
  funext x
  refine Prod.ext (funext fun i ↦ ?_) rfl
  by_cases hi : i = j
  · subst hi
    simp [slotEquiv, addSet, oracleEquiv_apply]
  · simp [slotEquiv, addSet, hi]

theorem slotLift_portMat (rd : N → A → Y) (C : Matrix N N ℂ) (j : Fin w) :
    slotLift j (portMat rd C) = conjC C (addSet rd (fun i _ ↦ decide (i = j))) := by
  rw [portMat, slotLift_mul, slotLift_mul, slotLift_one_kronecker, slotLift_tableOracle, conjC]

variable {C : Matrix N N ℂ}

omit [AddCommGroup Y] in
theorem one_kronecker_mul_self (hC : C * C = 1) :
    ((1 : Matrix (Fin w → A × Y) (Fin w → A × Y) ℂ) ⊗ₖ C) *
      ((1 : Matrix (Fin w → A × Y) (Fin w → A × Y) ℂ) ⊗ₖ C) = 1 := by
  rw [← mul_kronecker_mul, Matrix.one_mul, hC, one_kronecker_one]

omit [AddCommGroup Y] in
theorem conjC_comp (hC : C * C = 1) (f g : (Fin w → A × Y) × N → (Fin w → A × Y) × N) :
    conjC C (f ∘ g) = conjC C f * conjC C g := by
  rw [conjC, conjC, conjC, basisMatrix_comp]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc ((1 : Matrix (Fin w → A × Y) (Fin w → A × Y) ℂ) ⊗ₖ C)
    ((1 : Matrix (Fin w → A × Y) (Fin w → A × Y) ℂ) ⊗ₖ C), one_kronecker_mul_self hC,
    Matrix.one_mul]

omit [AddCommGroup Y] in
theorem conjC_id (hC : C * C = 1) : conjC C (id : (Fin w → A × Y) × N → _) = 1 := by
  rw [conjC, basisMatrix_id, Matrix.mul_one, one_kronecker_mul_self hC]

omit [Fintype A] [Fintype Y] [Fintype N] [DecidableEq N] [AddCommGroup Y] in
/-- An operator on the runtime register keeps the slots. -/
theorem preserves_one_kronecker {κ : Type*} (φ : (Fin w → A × Y) → κ) :
    Preserves (fun x : (Fin w → A × Y) × N ↦ φ x.1)
      ((1 : Matrix (Fin w → A × Y) (Fin w → A × Y) ℂ) ⊗ₖ C) := fun x x' h ↦ by
  obtain ⟨a, s⟩ := x
  obtain ⟨a', s'⟩ := x'
  rw [(Sponge.one_kronecker_ne_zero h).1]

omit [AddCommGroup Y] in
/-- A basis map agreeing with another on a label of the slots, conjugated. -/
theorem conjC_mul_labelProjector (f g : (Fin w → A × Y) × N → (Fin w → A × Y) × N)
    (β : (Fin w → A × Y) → Bool) (h : ∀ x, β x.1 = true → f x = g x) :
    conjC C f * labelProjector (fun x : (Fin w → A × Y) × N ↦ β x.1) true =
      conjC C g * labelProjector (fun x : (Fin w → A × Y) × N ↦ β x.1) true := by
  have hc := (preserves_one_kronecker (N := N) (C := C) β).labelProjector_mul_comm true
  have hb : basisMatrix f * labelProjector (fun x : (Fin w → A × Y) × N ↦ β x.1) true =
      basisMatrix g * labelProjector (fun x : (Fin w → A × Y) × N ↦ β x.1) true := by
    ext x' x
    simp only [labelProjector, mul_diagonal, basisMatrix_apply]
    by_cases hx : β x.1 = true
    · rw [h x hx]
    · simp [hx]
  rw [conjC, conjC, Matrix.mul_assoc _ _ (labelProjector _ true), ← hc, ← Matrix.mul_assoc,
    Matrix.mul_assoc _ (basisMatrix f), hb, ← Matrix.mul_assoc, Matrix.mul_assoc, hc,
    ← Matrix.mul_assoc]

omit [DecidableEq N] in
theorem entry_eq_of_mul_labelProjector_eq {n : Type*} [Fintype n] [DecidableEq n]
    {M M' : Matrix n n ℂ} {β : n → Bool}
    (h : M * labelProjector β true = M' * labelProjector β true)
    {x x' : n} (hx : β x = true) : M x' x = M' x' x := by
  have := congrFun (congrFun h x') x
  simpa [labelProjector, mul_diagonal, hx] using this

omit [AddCommGroup Y] in
theorem l2_opNorm_one_kronecker_le_one (hC : C * C = 1) (hCh : Cᴴ = C) :
    ‖(1 : Matrix (Fin w → A × Y) (Fin w → A × Y) ℂ) ⊗ₖ C‖ ≤ 1 :=
  Matrix.l2_opNorm_le_one_of_conjTranspose_mul_self (by
    rw [conjTranspose_kronecker, conjTranspose_one, hCh, one_kronecker_mul_self hC])

omit [DecidableEq N] in
theorem l2_opNorm_basisMatrix_le_one {n : Type*} [Fintype n] [DecidableEq n] {f : n → n}
    (hf : Function.Injective f) : ‖basisMatrix f‖ ≤ 1 :=
  Matrix.l2_opNorm_le_one_of_conjTranspose_mul_self (conjTranspose_basisMatrix_mul_self hf)

omit [AddCommGroup Y] in
theorem l2_opNorm_conjC_le_one (hC : C * C = 1) (hCh : Cᴴ = C)
    {f : (Fin w → A × Y) × N → (Fin w → A × Y) × N} (hf : Function.Injective f) :
    ‖conjC C f‖ ≤ 1 := by
  have h1 := l2_opNorm_one_kronecker_le_one (w := w) (A := A) (Y := Y) hC hCh
  refine (l2_opNorm_mul _ _).trans ?_
  refine (mul_le_mul ((l2_opNorm_mul _ _).trans ?_) h1 (norm_nonneg _) zero_le_one).trans_eq
    (one_mul 1)
  exact (mul_le_mul h1 (l2_opNorm_basisMatrix_le_one hf) (norm_nonneg _) zero_le_one).trans_eq
    (one_mul 1)

/-- The round of a port as one conjugated basis map. -/
theorem roundProd_portMat (rd : N → A → Y) (hC : C * C = 1) :
    roundProd (fun j : Fin w ↦ slotLift j (portMat rd C)) =
      conjC C (addSet rd (fun _ _ ↦ true)) := by
  simp only [slotLift_portMat, conjC]
  rw [roundProd_conj _ (one_kronecker_mul_self hC)]
  have h := roundProd_basisMatrix_addSet rd (fun _ _ ↦ true) (cellsOnly_const true)
    (id : Fin w → Fin w) Function.injective_id
  simp only [id, Bool.and_true] at h
  have he : (fun i a ↦ decide (∃ t, t = i)) =
      (fun _ _ ↦ true : Fin w → (Fin w → A × Y) → Bool) := by
    funext i a
    simp
  rw [h, he]

/-- A round, and its pieces, keep the queried cells. -/
theorem preserves_conjC_cells (rd : N → A → Y) (P : Fin w → (Fin w → A × Y) → Bool) :
    Preserves (cells (N := N)) (conjC C (addSet rd P)) :=
  ((preserves_one_kronecker (C := C) fun a i ↦ (a i).1).mul
    (preserves_basisMatrix _ _ (cells_addSet rd P))).mul
    (preserves_one_kronecker (C := C) fun a i ↦ (a i).1)

/-- The calls of a round on the slots of cells other than `c` keep every label `β` that the
port keeps on queries of other cells. -/
theorem preserves_conjC_addSet_ne (rd : N → A → Y) (hC : C * C = 1) (c : A) (β : N → Bool)
    (hpres : ∀ p p' : (A × Y) × N, portMat rd C p' p ≠ 0 → p.1.1 ≠ c → β p'.2 = β p.2) :
    Preserves (fun x : (Fin w → A × Y) × N ↦ β x.2)
      (conjC C (addSet rd (fun i a ↦ decide ((a i).1 ≠ c)))) := by
  have hP : CellsOnly (fun i a ↦ decide ((a i).1 ≠ c) : Fin w → (Fin w → A × Y) → Bool) :=
    fun i a a' h ↦ by simp [h i]
  have h := roundProd_basisMatrix_addSet rd _ hP (id : Fin w → Fin w) Function.injective_id
  have he : addSet rd (fun i a ↦ decide (∃ t, id t = i) && decide ((a i).1 ≠ c)) =
      addSet rd (fun i a ↦ decide ((a i).1 ≠ c) : Fin w → (Fin w → A × Y) → Bool) := by
    congr 1
    funext i a
    simp
  rw [he] at h
  rw [conjC, ← h, ← roundProd_conj _ (one_kronecker_mul_self hC)]
  refine Preserves.roundProd fun j x x' hx ↦ ?_
  change conjC C (addSet rd (fun i a ↦ decide (i = id j) && decide ((a i).1 ≠ c))) x' x ≠ 0 at hx
  by_cases hj : (x.1 j).1 ≠ c
  · have hag := conjC_mul_labelProjector (C := C)
      (addSet rd (fun i a ↦ decide (i = id j) && decide ((a i).1 ≠ c)))
      (addSet rd (fun i _ ↦ decide (i = j))) (fun a ↦ decide ((a j).1 ≠ c)) fun y hy ↦ by
        refine Prod.ext (funext fun i ↦ ?_) rfl
        by_cases hi : i = j
        · subst hi
          simp only [decide_eq_true_eq] at hy
          simp [addSet, hy]
        · simp [addSet, hi]
    rw [entry_eq_of_mul_labelProjector_eq hag (by simpa using hj), ← slotLift_portMat,
      slotLift_apply] at hx
    split_ifs at hx
    · exact hpres (x.1 j, x.2) (x'.1 j, x'.2) hx hj
    · exact absurd rfl hx
  · have hag := conjC_mul_labelProjector (C := C)
      (addSet rd (fun i a ↦ decide (i = id j) && decide ((a i).1 ≠ c))) id
      (fun a ↦ decide ((a j).1 = c)) fun y hy ↦ by
        refine Prod.ext (funext fun i ↦ ?_) rfl
        by_cases hi : i = j
        · subst hi
          simp only [decide_eq_true_eq] at hy
          simp [addSet, hy]
        · simp [addSet, hi]
    rw [entry_eq_of_mul_labelProjector_eq hag (by simpa using hj), conjC_id hC,
      Matrix.one_apply] at hx
    split_ifs at hx with hxx
    · rw [hxx]
    · exact absurd rfl hx

/-! ### The shear -/

/-- Subtract the response of slot `k` from the other slots querying `c`. -/
def shearSub (k : Fin w) (c : A) (a : Fin w → A × Y) : Fin w → A × Y :=
  fun i ↦ if i ≠ k ∧ (a i).1 = c then ((a i).1, (a i).2 - (a k).2) else a i

/-- Add the response of slot `k` to the other slots querying `c`. -/
def shearAdd (k : Fin w) (c : A) (a : Fin w → A × Y) : Fin w → A × Y :=
  fun i ↦ if i ≠ k ∧ (a i).1 = c then ((a i).1, (a i).2 + (a k).2) else a i

omit [Fintype A] [Fintype Y] [DecidableEq Y] in
theorem shearSub_fst (k : Fin w) (c : A) (a : Fin w → A × Y) (i : Fin w) :
    (shearSub k c a i).1 = (a i).1 := by
  unfold shearSub
  split_ifs <;> rfl

omit [Fintype A] [Fintype Y] [DecidableEq Y] in
theorem shearAdd_fst (k : Fin w) (c : A) (a : Fin w → A × Y) (i : Fin w) :
    (shearAdd k c a i).1 = (a i).1 := by
  unfold shearAdd
  split_ifs <;> rfl

omit [Fintype A] [Fintype Y] [DecidableEq Y] in
theorem shearSub_self (k : Fin w) (c : A) (a : Fin w → A × Y) : shearSub k c a k = a k := by
  simp [shearSub]

omit [Fintype A] [Fintype Y] [DecidableEq Y] in
theorem shearAdd_self (k : Fin w) (c : A) (a : Fin w → A × Y) : shearAdd k c a k = a k := by
  simp [shearAdd]

omit [Fintype A] [Fintype Y] [DecidableEq Y] in
theorem shearSub_shearAdd (k : Fin w) (c : A) (a : Fin w → A × Y) :
    shearSub k c (shearAdd k c a) = a := by
  funext i
  unfold shearSub
  rw [shearAdd_self, shearAdd_fst]
  unfold shearAdd
  split_ifs <;> simp

omit [Fintype A] [Fintype Y] [DecidableEq Y] in
theorem shearAdd_shearSub (k : Fin w) (c : A) (a : Fin w → A × Y) :
    shearAdd k c (shearSub k c a) = a := by
  funext i
  unfold shearAdd
  rw [shearSub_self, shearSub_fst]
  unfold shearSub
  split_ifs <;> simp

omit [Fintype A] [Fintype Y] [DecidableEq Y] [Fintype N] [DecidableEq N] in
/-- **The shear merges the slots of one cell.** Conjugated by the shear of slot `k` querying `c`,
the round adds into slot `k` and into the slots of the other cells only. -/
theorem shear_addSet_eq (rd : N → A → Y) (k : Fin w) (c : A) (x : (Fin w → A × Y) × N)
    (hx : (x.1 k).1 = c) :
    Prod.map (shearSub k c) id (addSet rd (fun _ _ ↦ true) (Prod.map (shearAdd k c) id x)) =
      (addSet rd (fun i a ↦ decide ((a i).1 ≠ c)) ∘ addSet rd (fun i _ ↦ decide (i = k))) x := by
  obtain ⟨a, s⟩ := x
  simp only at hx
  refine Prod.ext (funext fun i ↦ ?_) rfl
  by_cases hik : i = k
  · subst hik
    simp [shearSub, shearAdd, addSet, hx]
  · by_cases hc : (a i).1 = c
    · simp [shearSub, shearAdd, addSet, hik, hc, hx]
      exact Prod.ext hc.symm rfl
    · simp [shearSub, shearAdd, addSet, hik, hc]

/-- The shear as a basis map of the round register. -/
noncomputable def shearMat (k : Fin w) (c : A) (add : Bool) :
    Matrix ((Fin w → A × Y) × N) ((Fin w → A × Y) × N) ℂ :=
  basisMatrix (Prod.map (if add then shearAdd k c else shearSub k c) id)

omit [AddCommGroup Y] in
theorem conjC_prodMap (hC : C * C = 1) (f : (Fin w → A × Y) → (Fin w → A × Y)) :
    conjC C (Prod.map f id : (Fin w → A × Y) × N → _) = basisMatrix (Prod.map f id) := by
  rw [conjC, ← basisMatrix_kronecker_one, ← mul_kronecker_mul, ← mul_kronecker_mul]
  simp only [Matrix.one_mul, Matrix.mul_one, hC]

omit [Fintype A] [Fintype Y] [Fintype N] [AddCommGroup Y] in
theorem preserves_basisMatrix_prodMap {κ : Type*} (β : N → κ)
    (f : (Fin w → A × Y) → (Fin w → A × Y)) :
    Preserves (fun x : (Fin w → A × Y) × N ↦ β x.2) (basisMatrix (Prod.map f id)) :=
  preserves_basisMatrix _ _ fun _ ↦ rfl

omit [Fintype A] [Fintype Y] [Fintype N] in
theorem preserves_shearMat_cells (k : Fin w) (c : A) (add : Bool) :
    Preserves (cells (N := N)) (shearMat (N := N) (Y := Y) k c add) := by
  refine preserves_basisMatrix _ _ fun x ↦ funext fun i ↦ ?_
  cases add
  · exact shearSub_fst k c x.1 i
  · exact shearAdd_fst k c x.1 i

theorem shearMat_mul_shearMat (k : Fin w) (c : A) (add : Bool) :
    shearMat (N := N) (Y := Y) k c add * shearMat k c (!add) = 1 := by
  rw [shearMat, shearMat, ← basisMatrix_comp, Prod.map_comp_map]
  have h : (if add then shearAdd k c else shearSub k c) ∘
      (if (!add) then shearAdd k c else shearSub k c) = (id : (Fin w → A × Y) → _) := by
    funext a
    cases add
    · exact shearSub_shearAdd k c a
    · exact shearAdd_shearSub k c a
  rw [h, Function.id_comp, Prod.map_id, basisMatrix_id]

theorem l2_opNorm_shearMat_le_one (k : Fin w) (c : A) (add : Bool) :
    ‖shearMat (N := N) (Y := Y) k c add‖ ≤ 1 := by
  refine l2_opNorm_basisMatrix_le_one (Function.LeftInverse.injective
    (g := Prod.map (if (!add) then shearAdd k c else shearSub k c) id) fun x ↦ ?_)
  obtain ⟨a, s⟩ := x
  cases add
  · exact Prod.ext (shearAdd_shearSub k c a) rfl
  · exact Prod.ext (shearSub_shearAdd k c a) rfl

/-! ### One cell of the union -/

/-- **The commutator of a round with one cell event, on the states querying the cell at slot
`k`**, is at most that of a single call: by the shear, the slots of the cell act as slot `k`
alone, and the other slots keep the cell event. -/
theorem l2_opNorm_commutator_cell_le (rd : N → A → Y) (hC : C * C = 1) (hCh : Cᴴ = C)
    (g lam : N → Bool) (k : Fin w) (c : A)
    (hE : Preserves (fun x : (Fin w → A × Y) × N ↦ g x.2)
      (conjC C (addSet rd (fun i a ↦ decide ((a i).1 ≠ c)))))
    {a0 : ℝ} (hcell : ‖(labelProjector (fun p : (A × Y) × N ↦ g p.2) true * portMat rd C -
      portMat rd C * labelProjector (fun p : (A × Y) × N ↦ g p.2) true) *
        labelProjector (fun p : (A × Y) × N ↦ lam p.2) true‖ ≤ a0) :
    ‖(labelProjector (fun x : (Fin w → A × Y) × N ↦ g x.2) true *
          roundProd (fun j : Fin w ↦ slotLift j (portMat rd C)) -
        roundProd (fun j : Fin w ↦ slotLift j (portMat rd C)) *
          labelProjector (fun x : (Fin w → A × Y) × N ↦ g x.2) true) *
      labelProjector (fun x : (Fin w → A × Y) × N ↦ decide ((x.1 k).1 = c)) true *
        labelProjector (fun x : (Fin w → A × Y) × N ↦ lam x.2) true‖ ≤
        a0 := by
  set U := roundProd (fun j : Fin w ↦ slotLift j (portMat rd C))
  set Sh := shearMat (N := N) (Y := Y) k c false
  set Sh' := shearMat (N := N) (Y := Y) k c true
  set H : Matrix ((Fin w → A × Y) × N) ((Fin w → A × Y) × N) ℂ :=
    labelProjector (fun x : (Fin w → A × Y) × N ↦ decide ((x.1 k).1 = c)) true
  set E := conjC C (addSet rd (fun i a ↦ decide ((a i).1 ≠ c)))
  set V := slotLift k (portMat rd C)
  set G : Matrix ((Fin w → A × Y) × N) ((Fin w → A × Y) × N) ℂ :=
    labelProjector (fun x : (Fin w → A × Y) × N ↦ g x.2) true
  set L : Matrix ((Fin w → A × Y) × N) ((Fin w → A × Y) × N) ℂ :=
    labelProjector (fun x : (Fin w → A × Y) × N ↦ lam x.2) true
  have hU : U = conjC C (addSet rd (fun _ _ ↦ true)) := roundProd_portMat rd hC
  have hSh : Sh = conjC C (Prod.map (shearSub k c) id) := (conjC_prodMap hC _).symm
  have hSh' : Sh' = conjC C (Prod.map (shearAdd k c) id) := (conjC_prodMap hC _).symm
  have hU' : Sh * U * Sh' * H = E * V * H := by
    have hag : conjC C ((Prod.map (shearSub k c) id ∘ addSet rd (fun _ _ ↦ true)) ∘
        Prod.map (shearAdd k c) id) * H =
        conjC C (addSet rd (fun i a ↦ decide ((a i).1 ≠ c)) ∘
          addSet rd (fun i _ ↦ decide (i = k))) * H :=
      conjC_mul_labelProjector _ _ (fun a ↦ decide ((a k).1 = c)) fun x hx ↦
        shear_addSet_eq rd k c x (by simpa using hx)
    rw [hU, hSh, hSh', ← conjC_comp hC, ← conjC_comp hC, hag, conjC_comp hC,
      ← slotLift_portMat]
  have h1 : Sh' * Sh = 1 := shearMat_mul_shearMat k c true
  have hG : Sh' * G = G * Sh' :=
    ((preserves_basisMatrix_prodMap g _).labelProjector_mul_comm true).symm
  have hHL : H * L = L * H := Sponge.labelProjector_mul_comm _ _ _ _
  have hH : H * Sh = Sh * H :=
    labelProjector_mul_comm_of_preserves Sh _ true fun x x' h ↦ by
      have := preserves_shearMat_cells (N := N) k c false x x' h
      rw [show (x'.1 k).1 = (x.1 k).1 from congrFun this k]
  have hLSh : L * Sh = Sh * L :=
    (preserves_basisMatrix_prodMap lam _).labelProjector_mul_comm true
  have hP : H * L * Sh = Sh * (H * L) := by
    rw [Matrix.mul_assoc, hLSh, ← Matrix.mul_assoc, hH, Matrix.mul_assoc]
  have hGE : G * E = E * G := hE.labelProjector_mul_comm true
  have hGH : H * G = G * H := Sponge.labelProjector_mul_comm _ _ _ _
  have key := conj_commutator_eq (G := G) (U := U) h1 hG hP
  have key2 := commutator_mul_eq_of_mul_eq (G := G) (L := L) hU' hGE hGH hHL
  have hX : (G * V - V * G) * L =
      slotLift k ((labelProjector (fun p : (A × Y) × N ↦ g p.2) true * portMat rd C -
        portMat rd C * labelProjector (fun p : (A × Y) × N ↦ g p.2) true) *
          labelProjector (fun p : (A × Y) × N ↦ lam p.2) true) := by
    rw [slotLift_mul, slotLift_sub, slotLift_mul, slotLift_mul, slotLift_labelProjector,
      slotLift_labelProjector]
  rw [Matrix.mul_assoc _ H, ← key, key2, hX]
  have hE1 : ‖E‖ ≤ 1 := l2_opNorm_conjC_le_one hC hCh (addSet_injective rd fun i a a' h ↦ by
    simp [h i])
  calc _ ≤ ‖E * slotLift k _ * H‖ := l2_opNorm_sandwich_le (l2_opNorm_shearMat_le_one k c true)
          (l2_opNorm_shearMat_le_one k c false)
    _ ≤ ‖slotLift k _‖ := l2_opNorm_sandwich_le hE1 (l2_opNorm_labelProjector_le_one _ _)
    _ ≤ _ := l2_opNorm_slotLift_le _ _
    _ ≤ a0 := hcell

/-- **The parallel transition lemma.** Let the event `q` of the runtime register be the union of
the cell events `g c` (`g c ≤ q`), each kept by the port on queries of other cells, and let a
single call satisfy `‖[G c, O] Λ‖ ≤ √r` for every cell. Then a round of `w` calls satisfies
`‖[Q, U] Λ‖ ≤ √(w r)`. -/
theorem l2_opNorm_commutator_roundProd_portMat_le (rd : N → A → Y) (hC : C * C = 1)
    (hCh : Cᴴ = C) (q lam : N → Bool) (g : A → N → Bool) {r : ℝ} (hr : 0 ≤ r)
    (hsub : ∀ c s, g c s = true → q s = true) (hunion : ∀ s, q s = true → ∃ c, g c s = true)
    (hpres : ∀ c (p p' : (A × Y) × N), portMat rd C p' p ≠ 0 → p.1.1 ≠ c → g c p'.2 = g c p.2)
    (hcell : ∀ c, ‖(labelProjector (fun p : (A × Y) × N ↦ g c p.2) true * portMat rd C -
      portMat rd C * labelProjector (fun p : (A × Y) × N ↦ g c p.2) true) *
        labelProjector (fun p : (A × Y) × N ↦ lam p.2) true‖ ≤ √r) :
    ‖(labelProjector (fun x : (Fin w → A × Y) × N ↦ q x.2) true *
          roundProd (fun j : Fin w ↦ slotLift j (portMat rd C)) -
        roundProd (fun j : Fin w ↦ slotLift j (portMat rd C)) *
          labelProjector (fun x : (Fin w → A × Y) × N ↦ q x.2) true) *
      labelProjector (fun x : (Fin w → A × Y) × N ↦ lam x.2) true‖ ≤ √(w * r) := by
  set U := roundProd (fun j : Fin w ↦ slotLift j (portMat rd C))
  have hU : U = conjC C (addSet rd (fun _ _ ↦ true)) := roundProd_portMat rd hC
  have hcells : Preserves (cells (N := N)) U := by
    rw [hU]
    exact preserves_conjC_cells rd _
  have hE : ∀ c, Preserves (fun x : (Fin w → A × Y) × N ↦ g c x.2)
      (conjC C (addSet rd (fun i a ↦ decide ((a i).1 ≠ c)))) := fun c ↦
    preserves_conjC_addSet_ne rd hC c (g c) (hpres c)
  have hUE : ∀ c (x x' : (Fin w → A × Y) × N), (∀ k, (x.1 k).1 ≠ c) →
      U x' x = conjC C (addSet rd (fun i a ↦ decide ((a i).1 ≠ c))) x' x := fun c x x' hx ↦ by
    rw [hU]
    refine entry_eq_of_mul_labelProjector_eq (conjC_mul_labelProjector _ _
      (fun a ↦ decide (∀ k, (a k).1 ≠ c)) fun y hy ↦ ?_) (by simpa using hx)
    simp only [decide_eq_true_eq] at hy
    refine Prod.ext (funext fun i ↦ ?_) rfl
    simp [addSet, hy i]
  refine l2_opNorm_commutator_le_of_cover (ι := Fin w × A) U (fun x ↦ q x.2) (fun x ↦ lam x.2)
    (fun p x ↦ g p.2 x.2) (fun p x ↦ decide ((x.1 p.1).1 = p.2)) (fun _ ↦ √r)
    (mul_nonneg (Nat.cast_nonneg w) hr) (fun p x h ↦ hsub p.2 x.2 h) ?_ ?_ ?_ ?_
  · intro p x x' h
    rw [show (x'.1 p.1).1 = (x.1 p.1).1 from congrFun (hcells x x' h) p.1]
  · intro x x' h hq
    have hcx : ∀ k, (x'.1 k).1 = (x.1 k).1 := fun k ↦ congrFun (hcells x x' h) k
    by_cases hq' : q x'.2 = true
    · obtain ⟨c, hc⟩ := hunion _ hq'
      by_cases hk : ∃ k, (x.1 k).1 = c
      · obtain ⟨k, hk⟩ := hk
        exact ⟨(k, c), Or.inl ⟨hc, by simp [hcx k, hk], hq'⟩⟩
      · have hk' : ∀ k, (x.1 k).1 ≠ c := fun k hk' ↦ hk ⟨k, hk'⟩
        have hE' : conjC C (addSet rd (fun i a ↦ decide ((a i).1 ≠ c))) x' x ≠ 0 := by
          rwa [hUE c x x' hk'] at h
        have hqx : q x.2 = true := hsub c x.2 ((hE c x x' hE').symm.trans hc)
        exact absurd (hqx.trans hq'.symm) hq
    · have hq'' : q x'.2 = false := by simpa using hq'
      have hqx : q x.2 = true := by
        by_contra h0
        exact hq ((Bool.eq_false_iff.mpr h0).trans hq''.symm)
      obtain ⟨c, hc⟩ := hunion _ hqx
      by_cases hk : ∃ k, (x.1 k).1 = c
      · obtain ⟨k, hk⟩ := hk
        exact ⟨(k, c), Or.inr ⟨hc, by simp [hk], hqx⟩⟩
      · have hk' : ∀ k, (x.1 k).1 ≠ c := fun k hk' ↦ hk ⟨k, hk'⟩
        have hE' : conjC C (addSet rd (fun i a ↦ decide ((a i).1 ≠ c))) x' x ≠ 0 := by
          rwa [hUE c x x' hk'] at h
        exact absurd (hsub c x'.2 ((hE c x x' hE').trans hc)) hq'
  · intro p
    exact l2_opNorm_commutator_cell_le rd hC hCh (g p.2) lam p.1 p.2 (hE p.2) (hcell p.2)
  · intro x
    refine le_of_eq ?_
    rw [Fintype.sum_prod_type]
    simp [Real.sq_sqrt hr]

end port

/-! ## Rounds of the hardwired port `h` -/

section hardwired

open Sponge

variable {X Z : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
  {M : Type} [Fintype M] [DecidableEq M] [AddCommGroup X] [AddCommGroup Z]

variable (X Z M) in
/-- The value the hardwired port `h` adds for the cell `z`: the hardwired value, else the
database content. -/
def hwReadH (s : HwReg X Z M) (z : Z) : X :=
  (s.2.1.1 z).getD (s.1.1.lookup z)

theorem spongeHardwired_U_h_eq (W₀ : Hw X Z) (m₀ : M) :
    (spongeHardwired X Z W₀ m₀).U .h = portMat (hwReadH X Z M) (compressReg X Z M) :=
  rfl

omit [Fintype M] [AddCommGroup X] [AddCommGroup Z] in
theorem one_kronecker_hwProjector (T : Set (HwReg X Z M)) [DecidablePred (· ∈ T)] :
    (1 : Matrix (Z × X) (Z × X) ℂ) ⊗ₖ hwProjector T =
      labelProjector (fun p : (Z × X) × HwReg X Z M ↦ decide (p.2 ∈ T)) true := by
  rw [hwProjector, one_kronecker_labelProjector]

omit [Fintype M] [AddCommGroup X] [AddCommGroup Z] in
theorem diagonal_dbGrade_eq (n : ℕ) :
    (diagonal fun q : (Z × X) × HwReg X Z M ↦ if dbGrade q.2.1 ≤ n then (1 : ℂ) else 0) =
      labelProjector (fun q : (Z × X) × HwReg X Z M ↦ decide (dbGrade q.2.1 ≤ n)) true := by
  simp [labelProjector]

/-- **The parallel transition lemma for the hardwired port `h`** (Corollary C). Let the event `S`
of the hardwired register be the union of cell events `Sc c`, each depending only on the cell `c`
of `D.h`, on `D.k`, `D.k'` and on the classical data, upward closed with fresh bound `ε` below
`n + 1` entries. Then a round of `w` calls of port `h`, on grades at most `n`, has
`‖[Q, U] P‖ ≤ √(6 w ε)`. -/
theorem l2_opNorm_commutator_hRound_le (S : Set (HwReg X Z M)) [DecidablePred (· ∈ S)]
    (Sc : Z → Set (HwReg X Z M)) [∀ c, DecidablePred (· ∈ Sc c)] (hsub : ∀ c, Sc c ⊆ S)
    (hunion : ∀ s ∈ S, ∃ c, s ∈ Sc c)
    (hloc : ∀ c (s s' : HwReg X Z M), s'.1.1 c = s.1.1 c → s'.1.2 = s.1.2 → s'.2 = s.2 →
      (s' ∈ Sc c ↔ s ∈ Sc c))
    (hup : ∀ c W m, UpClosed (slice (Sc c) W m)) {n : ℕ} {ε : ℝ≥0∞} (hεtop : ε ≠ ⊤)
    (hε : ∀ c W m, FreshBound (slice (Sc c) W m) (n + 1) ε) (W₀ : Hw X Z) (m₀ : M) (w : ℕ) :
    ‖(labelProjector (fun x : (Fin w → Z × X) × HwReg X Z M ↦ decide (x.2 ∈ S)) true *
          roundProd (fun j : Fin w ↦ slotLift j (portMat (hwReadH X Z M) (compressReg X Z M))) -
        roundProd (fun j : Fin w ↦ slotLift j (portMat (hwReadH X Z M) (compressReg X Z M))) *
          labelProjector (fun x : (Fin w → Z × X) × HwReg X Z M ↦ decide (x.2 ∈ S)) true) *
      labelProjector (fun x : (Fin w → Z × X) × HwReg X Z M ↦ decide (dbGrade x.2.1 ≤ n))
        true‖ ≤ √(w * (6 * ε.toReal)) := by
  refine l2_opNorm_commutator_roundProd_portMat_le (hwReadH X Z M)
    (compressReg_mul_self (X := X) (Z := Z) (M := M))
    conjTranspose_compressReg (fun s ↦ decide (s ∈ S)) (fun s ↦ decide (dbGrade s.1 ≤ n))
    (fun c s ↦ decide (s ∈ Sc c)) (by positivity) (fun c s h ↦ ?_) (fun s h ↦ ?_)
    (fun c p p' h hc ↦ ?_) (fun c ↦ ?_)
  · simp only [decide_eq_true_eq] at h ⊢
    exact hsub c h
  · simp only [decide_eq_true_eq] at h ⊢
    exact hunion s h
  · obtain ⟨h2, -, h3⟩ := eraseCell_of_spongeHardwired_U_ne_zero W₀ m₀ .h p.1 p'.1 p.2 p'.2 h
    simp only [eraseCell, Prod.mk.injEq] at h3
    have h1 : p'.2.1.1 c = p.2.1.1 c := by
      have := congrFun h3.1 c
      rwa [Function.update_of_ne (Ne.symm hc), Function.update_of_ne (Ne.symm hc)] at this
    exact decide_eq_decide.mpr (hloc c p.2 p'.2 h1 (Prod.ext h3.2.1 h3.2.2) h2)
  · have cert : ((6 * ε.toReal) • (1 : Matrix ((Z × X) × HwReg X Z M) ((Z × X) × HwReg X Z M) ℂ) -
        ((((1 : Matrix (Z × X) (Z × X) ℂ) ⊗ₖ hwProjector (Sc c)) *
            portMat (hwReadH X Z M) (compressReg X Z M) -
          portMat (hwReadH X Z M) (compressReg X Z M) *
            ((1 : Matrix (Z × X) (Z × X) ℂ) ⊗ₖ hwProjector (Sc c))) *
          diagonal fun q : (Z × X) × HwReg X Z M ↦ if dbGrade q.2.1 ≤ n then (1 : ℂ) else 0)ᴴ *
        ((((1 : Matrix (Z × X) (Z × X) ℂ) ⊗ₖ hwProjector (Sc c)) *
            portMat (hwReadH X Z M) (compressReg X Z M) -
          portMat (hwReadH X Z M) (compressReg X Z M) *
            ((1 : Matrix (Z × X) (Z × X) ℂ) ⊗ₖ hwProjector (Sc c))) *
          diagonal fun q : (Z × X) × HwReg X Z M ↦
            if dbGrade q.2.1 ≤ n then (1 : ℂ) else 0)).PosSemidef :=
      posSemidef_spongeHardwired_certificate (Sc c) (hup c) hεtop (hε c) W₀ m₀ .h
    rw [one_kronecker_hwProjector, diagonal_dbGrade_eq] at cert
    exact (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr
      (l2_opNorm_sq_le_of_posSemidef (by positivity) cert)

end hardwired

end Quantum.Par

end
