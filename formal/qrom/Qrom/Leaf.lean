module

public import Qrom.Search

@[expose] public section

/-!
# The check of one leaf against the compressed database

For one leaf, with joint post-state `J` on `B × Database X Y` and output set `Z`, the check
`∃ z ∈ Z, good z (H z)` read on the compressed database is the operator `F diag(d) F`
(`Qrom.tabCompress_mul_diagonal_mul`), where `d` is the indicator of the total tables passing the
check. Since `d ≤ orFn Z`, its weight is at most that of `F E F` with `E = orProj Z`, and
`√(weight of F E F) ≤ √(weight of Bad) + ‖F E F - E‖ √(tr J)` (`Qrom.sqrt_check_le`).
-/

open Matrix OracleSpec
open scoped Kronecker ENNReal ComplexOrder Matrix.Norms.L2Operator

set_option linter.unusedSectionVars false

namespace Qrom

open Quantum Quantum.MatrixMap

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

/-! ## Tabulating a weight on functions -/

/-- The weight `c` on functions, carried to the total tables. -/
noncomputable def tabWeight (c : (X → Y) → ℂ) (D : Database X Y) : ℂ :=
  ∑ H : X → Y, if D = Database.ofFun H then c H else 0

theorem basisMatrix_mul_diagonal_mul (c : (X → Y) → ℂ) :
    basisMatrix (Database.ofFun : (X → Y) → Database X Y) * diagonal c *
        (basisMatrix (Database.ofFun : (X → Y) → Database X Y))ᴴ =
      diagonal (tabWeight c) := by
  ext D D'
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, conjTranspose_apply, basisMatrix_apply]
  by_cases h : D = D'
  · subst h
    rw [diagonal_apply_eq, tabWeight]
    refine Finset.sum_congr rfl fun H _ ↦ ?_
    split_ifs <;> simp
  · rw [diagonal_apply_ne _ h]
    refine Finset.sum_eq_zero fun H _ ↦ ?_
    by_cases h1 : D = Database.ofFun H
    · have h2 : D' ≠ Database.ofFun H := fun h2 ↦ h (h1.trans h2.symm)
      simp [h2]
    · simp [h1]

variable [Nonempty Y]

theorem tabCompress_mul_diagonal_mul (c : (X → Y) → ℂ) :
    tabCompress X Y * diagonal c * (tabCompress X Y)ᴴ =
      compressAll X Y * diagonal (tabWeight c) * compressAll X Y := by
  rw [tabCompress, conjTranspose_mul, conjTranspose_compressAll, ← basisMatrix_mul_diagonal_mul]
  simp only [Matrix.mul_assoc]

/-! ## Traces against projectors -/

variable {B : Type*} [Fintype B] [DecidableEq B]

/-- Against a Hermitian idempotent, the trace of `P J` is the weight of the Kraus map of `P`. -/
theorem trace_one_kronecker_mul_eq_conj {S : Type*} [Fintype S] [DecidableEq S]
    {P : Matrix S S ℂ} (hP : Pᴴ = P) (hPP : P * P = P) (J : Matrix (B × S) (B × S) ℂ) :
    (((1 : Matrix B B ℂ) ⊗ₖ P) * J).trace = (conj ((1 : Matrix B B ℂ) ⊗ₖ P) J).trace := by
  rw [conj_apply, conjTranspose_kronecker, conjTranspose_one, hP, Matrix.trace_mul_cycle,
    ← mul_kronecker_mul, Matrix.one_mul, hPP]

/-- The weight of a Kraus map is nonnegative on a positive semidefinite operator. -/
theorem trace_conj_re_nonneg {S T : Type*} [Fintype S] [Fintype T] (R : Matrix T S ℂ)
    {J : Matrix S S ℂ} (hJ : J.PosSemidef) : 0 ≤ (conj R J).trace.re :=
  (hJ.mul_mul_conjTranspose_same R).trace_nonneg |> fun h ↦ by
    rw [conj_apply]
    exact (RCLike.nonneg_iff.mp h).1

/-- A diagonal `0`/`1` matrix is a Hermitian idempotent. -/
theorem diagonal_zero_one {S : Type*} [Fintype S] [DecidableEq S] {e : S → ℂ}
    (he : ∀ a, e a = 0 ∨ e a = 1) :
    (diagonal e)ᴴ = diagonal e ∧ diagonal e * diagonal e = diagonal e := by
  refine ⟨?_, ?_⟩
  · rw [diagonal_conjTranspose]
    congr 1
    funext a
    rcases he a with h | h <;> simp [h]
  · rw [diagonal_mul_diagonal]
    congr 1
    funext a
    rcases he a with h | h <;> simp [h]

/-- The norm of a diagonal `0`/`1` matrix is at most one. -/
theorem norm_diagonal_zero_one_le {S : Type*} [Fintype S] [DecidableEq S] {e : S → ℂ}
    (he : ∀ a, e a = 0 ∨ e a = 1) : ‖(diagonal e : Matrix S S ℂ)‖ ≤ 1 := by
  rw [l2_opNorm_diagonal]
  refine pi_norm_le_iff_of_nonneg zero_le_one |>.mpr fun a ↦ ?_
  rcases he a with h | h <;> simp [h]

theorem norm_one_kronecker_le {S : Type*} [Fintype S] [DecidableEq S] (M : Matrix S S ℂ) :
    ‖(1 : Matrix B B ℂ) ⊗ₖ M‖ ≤ ‖M‖ := by
  refine (norm_kronecker_le _ _).trans ?_
  exact mul_le_of_le_one_left (norm_nonneg _) l2_opNorm_one_le

theorem one_kronecker_sub {S : Type*} (M N : Matrix S S ℂ) :
    (1 : Matrix B B ℂ) ⊗ₖ (M - N) = (1 : Matrix B B ℂ) ⊗ₖ M - (1 : Matrix B B ℂ) ⊗ₖ N := by
  ext ⟨a, c⟩ ⟨b, d⟩
  simp [kroneckerMap_apply, mul_sub]

theorem one_kronecker_add {S : Type*} (M N : Matrix S S ℂ) :
    (1 : Matrix B B ℂ) ⊗ₖ (M + N) = (1 : Matrix B B ℂ) ⊗ₖ M + (1 : Matrix B B ℂ) ⊗ₖ N := by
  ext ⟨a, c⟩ ⟨b, d⟩
  simp [kroneckerMap_apply, mul_add]

/-! ## The check of one leaf -/

variable (good : X → Y → Prop) [∀ z, DecidablePred (good z)] (Z : Finset X)

/-- The check on a function: some output cell holds a good value. -/
noncomputable def checkFn (H : X → Y) : ℂ :=
  if ∃ z ∈ Z, good z (H z) then 1 else 0

/-- The tabulated check is at most the indicator of `orProj`, and the gap is `0` or `1`. -/
theorem orFn_sub_tabWeight_mem (D : Database X Y) :
    orFn good Z D - tabWeight (checkFn good Z) D = 0 ∨
      orFn good Z D - tabWeight (checkFn good Z) D = 1 := by
  by_cases hD : ∃ H, D = Database.ofFun H
  · obtain ⟨H, rfl⟩ := hD
    have htab : tabWeight (checkFn good Z) (Database.ofFun H) = checkFn good Z H := by
      rw [tabWeight, Finset.sum_eq_single H]
      · simp
      · intro H' _ hH'
        have : Database.ofFun H ≠ Database.ofFun H' := fun h ↦ hH' (Database.ofFun_injective h).symm
        simp [this]
      · simp
    have hor : orFn good Z (Database.ofFun H) = checkFn good Z H := by
      unfold orFn checkFn Database.ofFun
      congr 1
      exact propext ⟨fun ⟨z, hz, y, hy, hg⟩ ↦ ⟨z, hz, Option.some_injective _ hy ▸ hg⟩,
        fun ⟨z, hz, hg⟩ ↦ ⟨z, hz, H z, rfl, hg⟩⟩
    left
    rw [htab, hor, sub_self]
  · have htab : tabWeight (checkFn good Z) D = 0 :=
      Finset.sum_eq_zero fun H _ ↦ by
        rw [ite_eq_right_iff]
        exact fun h ↦ absurd ⟨H, h⟩ hD
    rw [htab, sub_zero]
    exact orFn_mem good Z D

/-- `orProj Z` lies below the search event. -/
theorem orProj_mul_eventProj : orProj good Z * eventProj (searchEvent good) = orProj good Z := by
  rw [orProj_eq_diagonal, eventProj, labelProjector, diagonal_mul_diagonal]
  congr 1
  funext D
  by_cases h : ∃ z ∈ Z, ∃ y, D z = some y ∧ good z y
  · obtain ⟨z, _, y, hy, hg⟩ := h
    have : searchEvent good D = true := by
      simp only [searchEvent, decide_eq_true_eq]
      exact ⟨z, y, hy, hg⟩
    simp [this]
  · have : orFn good Z D = 0 := by simp only [orFn, h, ↓reduceIte]
    rw [this, zero_mul]

/-- **The check of one leaf.** For a positive semidefinite `J`,
`√(re tr ((1 ⊗ F diag(d) F) J)) ≤ √(re tr (conj (1 ⊗ Bad) J)) + ‖F E F - E‖ √(re tr J)`. -/
theorem sqrt_check_le {J : Matrix (B × Database X Y) (B × Database X Y) ℂ} (hJ : J.PosSemidef) :
    √((((1 : Matrix B B ℂ) ⊗ₖ (compressAll X Y * diagonal (tabWeight (checkFn good Z)) *
        compressAll X Y)) * J).trace.re) ≤
      √(conj ((1 : Matrix B B ℂ) ⊗ₖ eventProj (searchEvent good)) J).trace.re +
        ‖compressAll X Y * orProj good Z * compressAll X Y - orProj good Z‖ *
          √J.trace.re := by
  set F := compressAll X Y with hFdef
  set E := orProj good Z with hEdef
  set q : Database X Y → ℂ := fun D ↦ orFn good Z D - tabWeight (checkFn good Z) D with hqdef
  have hFF : F * F = 1 := compressAll_mul_self X Y
  have hFh : Fᴴ = F := conjTranspose_compressAll X Y
  have hEd : E = diagonal (orFn good Z) := orProj_eq_diagonal good Z
  have hE := diagonal_zero_one (orFn_mem good Z)
  rw [← hEd] at hE
  have hq := diagonal_zero_one (orFn_sub_tabWeight_mem good Z)
  -- the projector `F E F`
  have hÊh : (F * E * F)ᴴ = F * E * F := by
    rw [conjTranspose_mul, conjTranspose_mul, hFh, hE.1, Matrix.mul_assoc]
  have hÊÊ : F * E * F * (F * E * F) = F * E * F := by
    rw [show F * E * F * (F * E * F) = F * E * (F * F) * E * F by simp only [Matrix.mul_assoc],
      hFF, Matrix.mul_one, Matrix.mul_assoc F E E, hE.2]
  -- step 1: the check is at most the weight of `F E F`
  have hq2 : (diagonal q * F)ᴴ * (diagonal q * F) = F * diagonal q * F := by
    rw [conjTranspose_mul, hFh, hq.1]
    calc F * diagonal q * (diagonal q * F) = F * (diagonal q * diagonal q) * F := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hq.2]
  have hsplit : F * diagonal (tabWeight (checkFn good Z)) * F =
      F * E * F - (diagonal q * F)ᴴ * (diagonal q * F) := by
    rw [hq2, hEd, ← Matrix.sub_mul, ← Matrix.mul_sub, diagonal_sub]
    congr 2
    funext D
    simp [q]
  have h1 : ((((1 : Matrix B B ℂ) ⊗ₖ (F * diagonal (tabWeight (checkFn good Z)) * F)) *
      J).trace.re) ≤ (conj ((1 : Matrix B B ℂ) ⊗ₖ (F * E * F)) J).trace.re := by
    rw [hsplit, one_kronecker_sub, Matrix.sub_mul, trace_sub, Complex.sub_re,
      trace_one_kronecker_mul_eq_conj hÊh hÊÊ]
    have : 0 ≤ ((((1 : Matrix B B ℂ) ⊗ₖ ((diagonal q * F)ᴴ * (diagonal q * F))) * J).trace.re) := by
      have heq : (1 : Matrix B B ℂ) ⊗ₖ ((diagonal q * F)ᴴ * (diagonal q * F)) =
          ((1 : Matrix B B ℂ) ⊗ₖ (diagonal q * F))ᴴ * ((1 : Matrix B B ℂ) ⊗ₖ (diagonal q * F)) := by
        rw [conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul, Matrix.one_mul]
      have key : ((((1 : Matrix B B ℂ) ⊗ₖ (diagonal q * F))ᴴ *
          ((1 : Matrix B B ℂ) ⊗ₖ (diagonal q * F))) * J).trace =
          (conj ((1 : Matrix B B ℂ) ⊗ₖ (diagonal q * F)) J).trace := by
        rw [conj_apply, Matrix.trace_mul_comm (_ * J), ← Matrix.mul_assoc]
      rw [heq, key]
      exact trace_conj_re_nonneg _ hJ
    linarith
  -- step 2: the triangle inequality around `E`
  have h2 : √(conj ((1 : Matrix B B ℂ) ⊗ₖ (F * E * F)) J).trace.re ≤
      √(conj ((1 : Matrix B B ℂ) ⊗ₖ E) J).trace.re +
        √(conj ((1 : Matrix B B ℂ) ⊗ₖ (F * E * F - E)) J).trace.re := by
    have := sqrt_re_trace_conj_add_le hJ ((1 : Matrix B B ℂ) ⊗ₖ E)
      ((1 : Matrix B B ℂ) ⊗ₖ (F * E * F - E))
    rwa [← one_kronecker_add, add_sub_cancel] at this
  -- step 3: the remainder is at most `‖F E F - E‖ √(tr J)`
  have h3 : √(conj ((1 : Matrix B B ℂ) ⊗ₖ (F * E * F - E)) J).trace.re ≤
      ‖F * E * F - E‖ * √J.trace.re := by
    have hle := re_trace_conj_le ((1 : Matrix B B ℂ) ⊗ₖ (F * E * F - E)) hJ
    have hn := norm_one_kronecker_le (B := B) (F * E * F - E)
    calc _ ≤ √(‖(1 : Matrix B B ℂ) ⊗ₖ (F * E * F - E)‖ ^ 2 * J.trace.re) := Real.sqrt_le_sqrt hle
      _ = ‖(1 : Matrix B B ℂ) ⊗ₖ (F * E * F - E)‖ * √J.trace.re := by
          rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]
      _ ≤ _ := mul_le_mul_of_nonneg_right hn (Real.sqrt_nonneg _)
  -- step 4: `E` lies below the event
  have h4 : (conj ((1 : Matrix B B ℂ) ⊗ₖ E) J).trace.re ≤
      (conj ((1 : Matrix B B ℂ) ⊗ₖ eventProj (searchEvent good)) J).trace.re := by
    have hEB : (1 : Matrix B B ℂ) ⊗ₖ E =
        ((1 : Matrix B B ℂ) ⊗ₖ E) * ((1 : Matrix B B ℂ) ⊗ₖ eventProj (searchEvent good)) := by
      rw [← mul_kronecker_mul, Matrix.one_mul, orProj_mul_eventProj]
    rw [hEB, MatrixMap.conj_mul, LinearMap.comp_apply]
    have hσ : (conj ((1 : Matrix B B ℂ) ⊗ₖ eventProj (searchEvent good)) J).PosSemidef := by
      rw [conj_apply]
      exact hJ.mul_mul_conjTranspose_same _
    refine (re_trace_conj_le _ hσ).trans ?_
    have hn : ‖(1 : Matrix B B ℂ) ⊗ₖ E‖ ≤ 1 :=
      (norm_one_kronecker_le E).trans (by
        rw [hEd]
        exact norm_diagonal_zero_one_le (orFn_mem good Z))
    have h0 := trace_conj_re_nonneg ((1 : Matrix B B ℂ) ⊗ₖ eventProj (searchEvent good)) hJ
    calc _ ≤ 1 ^ 2 * (conj ((1 : Matrix B B ℂ) ⊗ₖ eventProj (searchEvent good)) J).trace.re :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hn 2) h0
      _ = _ := by rw [one_pow, one_mul]
  calc _ ≤ √(conj ((1 : Matrix B B ℂ) ⊗ₖ (F * E * F)) J).trace.re := Real.sqrt_le_sqrt h1
    _ ≤ _ := h2
    _ ≤ _ := add_le_add (Real.sqrt_le_sqrt h4) h3

end Qrom
