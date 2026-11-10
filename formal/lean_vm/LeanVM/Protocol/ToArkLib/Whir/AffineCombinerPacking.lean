/-
  LeanVM.Protocol.ToArkLib.Whir.AffineCombinerPacking

  Packing the lanes of an interleaved word into one word over an extension field: an exceptional
  pair of the lanes is an exceptional pair of the packed word. Candidate for ArkLib.
-/

module

public import LeanVM.Protocol.ToArkLib.Whir.AffineCombinerCore
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.LinearAlgebra.Dimension.Free

/-!
# Packing lanes

[CYWZ26, preprint], Section 5.1, "Interleaving and shared agreement": fix an extension `L` of `F`
and `F`-linearly independent `b : ρ → L`. A tuple of lanes `w : ρ → ι → F` packs into the word
`Σ_r w r · b r` over `L`, a tuple of polynomials `P : ρ → F[X]` into `Σ_r P r · b r ∈ L[X]`, and
agreement of the packed objects at a domain point is agreement of every lane. The challenges stay
in `F`.

`excSet_subset_excSetL`: an exceptional pair of the lanes is an exceptional pair of the packed
word. A witness `Ũ`, `Ṽ` over `L` for the packed tuple would project, coefficient by coefficient,
along an `F`-linear left inverse `π` of `c ↦ Σ_r c_r b_r`, to witnesses of the lanes
(`proj`, which commutes with evaluation at points of `F` and with multiplication by `α + β X`).

`exists_packing`: such `b` and `π` exist in `AlgebraicClosure F` for a finite field `F` (an
algebraically closed field is infinite, so infinite-dimensional over a finite `F`).
-/

namespace LeanVM.Protocol.Whir.AffineCombiner

open Finset Polynomial

@[expose] public section

variable {F L : Type*} [Field F] [Field L] [Algebra F L]

/-! ## Projecting coefficients -/

section Proj

/-- Apply an `F`-linear map `φ : L → F` to every coefficient. -/
noncomputable def proj (φ : L →ₗ[F] F) (Q : L[X]) : F[X] :=
  ∑ k ∈ range (Q.natDegree + 1), C (φ (Q.coeff k)) * X ^ k

@[simp] theorem coeff_proj (φ : L →ₗ[F] F) (Q : L[X]) (k : ℕ) :
    (proj φ Q).coeff k = φ (Q.coeff k) := by
  simp only [proj, finsetSum_coeff, coeff_C_mul_X_pow, sum_ite_eq, mem_range]
  split
  · rfl
  · rw [coeff_eq_zero_of_natDegree_lt (by omega), map_zero]

theorem natDegree_proj_le (φ : L →ₗ[F] F) (Q : L[X]) : (proj φ Q).natDegree ≤ Q.natDegree :=
  natDegree_le_iff_coeff_eq_zero.mpr fun k hk ↦ by
    rw [coeff_proj, coeff_eq_zero_of_natDegree_lt (by exact_mod_cast hk), map_zero]

theorem proj_add (φ : L →ₗ[F] F) (Q Q' : L[X]) : proj φ (Q + Q') = proj φ Q + proj φ Q' := by
  ext k; simp

theorem proj_linL_mul (φ : L →ₗ[F] F) (α β : F) (Q : L[X]) :
    proj φ (linL α β * Q) = lin α β * proj φ Q := by
  ext k
  simp only [coeff_proj, linL, lin, add_mul, coeff_add, coeff_C_mul, mul_assoc]
  rcases k with _ | k
  · simp [← Algebra.smul_def]
  · simp only [coeff_X_mul, ← Algebra.smul_def, map_add, map_smul, smul_eq_mul, coeff_proj]

theorem eval_proj (φ : L →ₗ[F] F) (Q : L[X]) (a : F) :
    (proj φ Q).eval a = φ (Q.eval (algebraMap F L a)) := by
  rw [eval_eq_sum_range' (n := Q.natDegree + 1) (Nat.lt_succ_of_le (natDegree_proj_le φ Q)),
    eval_eq_sum_range, map_sum]
  refine sum_congr rfl fun k _ ↦ ?_
  rw [coeff_proj, ← map_pow, mul_comm (Q.coeff k), ← Algebra.smul_def, map_smul, smul_eq_mul,
    mul_comm]

end Proj

/-! ## Packing -/

section Packing

variable {ι ρ : Type*} [Fintype ι] [DecidableEq ι] [Fintype ρ]

/-- The packed word `Σ_r w r · b r`. -/
def packW (b : ρ → L) (w : ρ → ι → F) : ι → L := fun x ↦ ∑ r, algebraMap F L (w r x) * b r

/-- The packed polynomial `Σ_r P r · b r`. -/
noncomputable def packP (b : ρ → L) (P : ρ → F[X]) : L[X] :=
  ∑ r, (P r).map (algebraMap F L) * C (b r)

theorem natDegree_packP_le (b : ρ → L) {d : ℕ} {P : ρ → F[X]} (hP : DegLE d P) :
    (packP b P).natDegree ≤ d := by
  refine natDegree_sum_le_of_forall_le _ _ fun r _ ↦ ?_
  exact (natDegree_mul_le).trans (by simpa using hP r)

theorem eval_packP (b : ρ → L) (P : ρ → F[X]) (a : F) :
    (packP b P).eval (algebraMap F L a) = ∑ r, algebraMap F L ((P r).eval a) * b r := by
  simp [packP, eval_finsetSum, eval_map, eval₂_at_apply]

theorem coeff_packP (b : ρ → L) (P : ρ → F[X]) (k : ℕ) :
    (packP b P).coeff k = ∑ r, algebraMap F L ((P r).coeff k) * b r := by
  simp [packP, finsetSum_coeff, coeff_mul_C]

variable (dom : ι ↪ F) (b : ρ → L) (π : L →ₗ[F] (ρ → F))
  (hπ : ∀ c : ρ → F, π (∑ r, algebraMap F L (c r) * b r) = c)

include hπ in
theorem proj_packP (P : ρ → F[X]) (r : ρ) :
    proj ((LinearMap.proj r).comp π) (packP b P) = P r := by
  ext k
  rw [coeff_proj, coeff_packP]
  exact congrFun (hπ fun s ↦ (P s).coeff k) r

omit [DecidableEq ι] in
include hπ in
/-- **Packing** ([CYWZ26, Section 5.1]): every exceptional pair of the lanes `(f, g)` is an
exceptional pair of the packed word. -/
theorem excSet_subset_excSetL [Fintype F] (f g : ρ → ι → F) (d A : ℕ) :
    excSet dom f g d A ⊆ excSetL dom (packW b f) (packW b g) d A := by
  classical
  intro p hp
  obtain ⟨P, hP, hA, hno⟩ := (mem_excSet _ _ _ _ _ _).mp hp
  -- Lane agreement implies packed agreement.
  have hsub : agree dom P (comb dom f g p.1 p.2) ⊆
      agreeL dom (packW b f) (packW b g) (packP b P) p.1 p.2 := by
    intro x hx
    rw [mem_agree] at hx
    rw [mem_agreeL, pt, eval_packP, eval_linL, packW, packW, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun r _ ↦ ?_
    rw [hx r, comb]
    simp only [map_add, map_mul]
    ring
  refine mem_filter.mpr ⟨mem_univ _, packP b P, natDegree_packP_le b hP,
    hA.trans (card_le_card hsub), ?_⟩
  rintro ⟨U, V, hU, hV, hPUV, hloss⟩
  apply hno
  let πr : ρ → L →ₗ[F] F := fun r ↦ (LinearMap.proj r).comp π
  refine ⟨fun r ↦ proj (πr r) U, fun r ↦ proj (πr r) V, fun r ↦ (natDegree_proj_le _ _).trans hU,
    fun r ↦ (natDegree_proj_le _ _).trans hV, fun r ↦ ?_, ?_⟩
  · rw [← proj_packP b π hπ P r, hPUV, proj_add, proj_linL_mul]
  · refine le_trans (card_le_card fun x hx ↦ ?_) hloss
    obtain ⟨hx, hbad⟩ := mem_filter.mp hx
    refine mem_filter.mpr ⟨hsub hx, ?_⟩
    by_contra hgood
    push Not at hgood
    obtain ⟨r, hr⟩ := hbad
    have hf : π (packW b f x) = fun s ↦ f s x := hπ fun s ↦ f s x
    have hg : π (packW b g x) = fun s ↦ g s x := hπ fun s ↦ g s x
    rcases hr with hr | hr
    · apply hr
      rw [eval_proj, ← pt, hgood.1]
      exact congrFun hf r
    · apply hr
      rw [eval_proj, ← pt, hgood.2]
      exact congrFun hg r

end Packing

/-! ## Existence of a packing -/

/-- **A packing exists**: over a finite field `F`, the algebraic closure contains `|ρ|`
`F`-independent elements `b`, with an `F`-linear left inverse `π` of `c ↦ Σ_r c_r b_r`. -/
theorem exists_packing {ρ : Type*} [Fintype ρ] [Finite F] :
    ∃ (b : ρ → AlgebraicClosure F) (π : AlgebraicClosure F →ₗ[F] (ρ → F)),
      ∀ c : ρ → F, π (∑ r, algebraMap F (AlgebraicClosure F) (c r) * b r) = c := by
  classical
  set K := AlgebraicClosure F
  -- `K` is infinite, hence not finite-dimensional over the finite field `F`.
  have hinf : ¬ Module.Finite F K := fun h ↦ by
    have := h
    have : Finite K := Module.finite_of_finite F
    exact not_finite K
  -- An injective linear map from `ρ → F`.
  obtain ⟨b, hb⟩ : ∃ b : ρ → K, LinearIndependent F b := by
    have hrank : (Fintype.card ρ : Cardinal) ≤ Module.rank F K := by
      by_contra h
      exact hinf (Module.rank_lt_aleph0_iff.mp ((not_le.mp h).trans Cardinal.natCast_lt_aleph0))
    obtain ⟨v, hv⟩ := exists_linearIndependent_of_le_rank hrank
    exact ⟨v ∘ Fintype.equivFin ρ, hv.comp _ (Fintype.equivFin ρ).injective⟩
  let φ : (ρ → F) →ₗ[F] K := Fintype.linearCombination F b
  have hφ : LinearMap.ker φ = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    exact linearIndependent_iff_injective_fintypeLinearCombination.mp hb
  obtain ⟨π, hπ⟩ := LinearMap.exists_leftInverse_of_injective φ hφ
  refine ⟨b, π, fun c ↦ ?_⟩
  have := LinearMap.congr_fun hπ c
  simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
  have e : φ c = ∑ r, algebraMap F K (c r) * b r := by
    simp [φ, Fintype.linearCombination_apply, Algebra.smul_def]
  rw [← e]
  exact this

end
end LeanVM.Protocol.Whir.AffineCombiner
