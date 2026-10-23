import LeanDa.ReedSolomon
import Mathlib.Algebra.MvPolynomial.SchwartzZippel

/-!
# The membership test

Proposition prop:rs-membership of `doc/leanvm/body/d-novel-basis.tex` for the crate's code. The
dual codeword is the encoding of the tensor `⊗_j (1, z_j)` (`dual_eq_sum`), so its inner product
with a row `w` is the multilinear polynomial `Σ_u ⟨Xᵤ, w⟩ z^u` in the challenges
(`eval_membershipPoly`). A codeword is orthogonal to every `Xᵤ` (`rsCode_le_orthogonal`), so it
passes for every `z` (`dot_dual_eq_zero`). A row that is not a codeword is not orthogonal to some
`Xᵤ` (`mem_rsCode_of_orthogonal`), so the polynomial is nonzero, of total degree at most `14`,
and Schwartz-Zippel bounds its zeros (`card_acceptSet_le`): at most `14 |E|^13` of the
`|E|^14` challenges accept it.
-/

open Polynomial Module

namespace LeanDa

/-! ## Bits of a coefficient index -/

/-- The bits of `u`. -/
def bitsOf (u : Fin (2 ^ 14)) : Finset (Fin 14) := Finset.univ.filter fun j ↦ (u : ℕ).testBit j

theorem eq_of_testBit_eq {u v : Fin (2 ^ 14)} (h : ∀ j : Fin 14, (u : ℕ).testBit j = (v : ℕ).testBit j) :
    u = v := by
  refine Fin.ext (Nat.eq_of_testBit_eq fun i ↦ ?_)
  by_cases hi : i < 14
  · exact h ⟨i, hi⟩
  · have hle : 2 ^ 14 ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_eq_false_of_lt (by omega), Nat.testBit_eq_false_of_lt (by omega)]

theorem bitsOf_injective : Function.Injective bitsOf := by
  intro u v h
  refine eq_of_testBit_eq fun j ↦ ?_
  have := congrArg (fun t ↦ j ∈ t) h
  simp only [bitsOf, Finset.mem_filter, Finset.mem_univ, true_and, eq_iff_iff] at this
  exact Bool.eq_iff_iff.mpr this

theorem bitsOf_bijective : Function.Bijective bitsOf :=
  (Fintype.bijective_iff_injective_and_card bitsOf).mpr
    ⟨bitsOf_injective, by simp [Fintype.card_finset]⟩

theorem tensor_eq (z : Fin 14 → E) (u : Fin (2 ^ 14)) : tensor z u = ∏ j ∈ bitsOf u, z j := by
  rw [tensor, bitsOf, Finset.prod_filter]

theorem novelX_eval (u : Fin (2 ^ 14)) (x : K) :
    (novelX u).eval x = ∏ j ∈ bitsOf u, (normW j).eval x := by
  unfold novelX AdditiveNTT.Xⱼ normW
  rw [eval_prod, bitsOf, Finset.prod_filter]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [eval_pow, Nat.getBit_eq_testBit]
  split_ifs <;> simp

/-- **The dual codeword is the encoding of the tensor**: `L(x) = Σ_u (⊗_j (1, z_j))_u Xᵤ(x)`. -/
theorem dual_eq_sum (z : Fin 14 → E) (b : Fin (2 ^ 15)) :
    dual z b = ∑ u, tensor z u * ι ((novelX u).eval (point b)) := by
  rw [dual, Finset.prod_one_add, Finset.powerset_univ,
    ← bitsOf_bijective.sum_comp fun t ↦ ∏ j ∈ t, z j * ι ((normW j).eval (point b))]
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  rw [tensor_eq, novelX_eval, map_prod, ← Finset.prod_mul_distrib]

/-! ## The membership polynomial -/

/-- The coefficients `⟨Xᵤ, w⟩` of a row on the domain. -/
noncomputable def novelCoeff (w : Row) (u : Fin (2 ^ 14)) : K :=
  ∑ b : Fin (2 ^ 15), (novelX u).eval (point b) * w b

/-- The exponent of the monomial `∏_(j ∈ bits u) z_j`. -/
noncomputable def monoExp (u : Fin (2 ^ 14)) : Fin 14 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun j ↦ if (u : ℕ).testBit j then 1 else 0

theorem monoExp_injective : Function.Injective monoExp := by
  intro u v h
  refine eq_of_testBit_eq fun j ↦ ?_
  have := congrArg (fun s ↦ s j) h
  simp only [monoExp, Finsupp.coe_equivFunOnFinite_symm] at this
  cases hu : (u : ℕ).testBit j <;> cases hv : (v : ℕ).testBit j <;> simp_all

/-- A sum of monomials, one per index. Kept generic in `N`: at `N = 2^14` the kernel would
unfold `Finset.univ` to compare instances. -/
noncomputable def sumMonomials {N : ℕ} (f : Fin N → Fin 14 →₀ ℕ) (c : Fin N → E) :
    MvPolynomial (Fin 14) E :=
  ∑ v, MvPolynomial.monomial (f v) (c v)

theorem coeff_sumMonomials {N : ℕ} (f : Fin N → Fin 14 →₀ ℕ) (hf : Function.Injective f)
    (c : Fin N → E) (u : Fin N) : (sumMonomials f c).coeff (f u) = c u := by
  rw [sumMonomials, MvPolynomial.coeff_sum, Finset.sum_eq_single u]
  · simp
  · intro v _ hv
    simp [MvPolynomial.coeff_monomial, hf.ne hv]
  · intro hu
    exact absurd (Finset.mem_univ u) hu

/-- `⟨L, w⟩` as a polynomial in the challenges: `Σ_u ⟨Xᵤ, w⟩ z^u`. -/
noncomputable def membershipPoly (w : Row) : MvPolynomial (Fin 14) E :=
  sumMonomials monoExp fun u ↦ ι (novelCoeff w u)

theorem dot_dual_eq_sum (w : Row) (z : Fin 14 → E) :
    dot (dual z) w = ∑ u, ι (novelCoeff w u) * tensor z u := by
  simp only [dot, dual_eq_sum, Finset.sum_mul, novelCoeff, map_sum, map_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ ↦ Finset.sum_congr rfl fun b _ ↦ ?_
  ring

theorem eval_membershipPoly (w : Row) (z : Fin 14 → E) :
    MvPolynomial.eval z (membershipPoly w) = dot (dual z) w := by
  have hmono : ∀ u, MvPolynomial.eval z (MvPolynomial.monomial (monoExp u) (ι (novelCoeff w u))) =
      ι (novelCoeff w u) * tensor z u := by
    intro u
    rw [MvPolynomial.eval_monomial, Finsupp.prod_fintype _ _ fun _ ↦ pow_zero _, tensor]
    refine congrArg (ι (novelCoeff w u) * ·) (Finset.prod_congr rfl fun j _ ↦ ?_)
    simp only [monoExp, Finsupp.coe_equivFunOnFinite_symm]
    split_ifs <;> simp
  rw [membershipPoly, sumMonomials, map_sum, dot_dual_eq_sum]
  exact Finset.sum_congr rfl fun u _ ↦ hmono u

theorem coeff_membershipPoly (w : Row) (u : Fin (2 ^ 14)) :
    (membershipPoly w).coeff (monoExp u) = ι (novelCoeff w u) := by
  rw [membershipPoly]
  exact coeff_sumMonomials monoExp monoExp_injective (fun u ↦ ι (novelCoeff w u)) u

theorem membershipPoly_ne_zero {w : Row} {u₀ : Fin (2 ^ 14)} (h : novelCoeff w u₀ ≠ 0) :
    membershipPoly w ≠ 0 := by
  rw [MvPolynomial.ne_zero_iff]
  refine ⟨monoExp u₀, ?_⟩
  rw [coeff_membershipPoly]
  exact (map_ne_zero_iff ι ι.injective).mpr h

theorem totalDegree_membershipPoly_le (w : Row) : (membershipPoly w).totalDegree ≤ 14 := by
  rw [membershipPoly, sumMonomials]
  refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun u _ ↦ ?_)
  refine (MvPolynomial.totalDegree_monomial_le _ _).trans ?_
  rw [Finsupp.sum_fintype _ _ fun _ ↦ rfl]
  calc ∑ j : Fin 14, monoExp u j ≤ ∑ _j : Fin 14, 1 := by
        refine Finset.sum_le_sum fun j _ ↦ ?_
        simp only [monoExp, Finsupp.coe_equivFunOnFinite_symm]
        split_ifs <;> simp
    _ = 14 := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]

/-! ## Completeness and soundness -/

/-- **A codeword passes for every challenge.** -/
theorem dot_dual_eq_zero {w : Row} (hw : w ∈ rsCode) (z : Fin 14 → E) : dot (dual z) w = 0 := by
  rw [dot_dual_eq_sum]
  refine Finset.sum_eq_zero fun u _ ↦ ?_
  have horth := rsCode_le_orthogonal hw
  rw [LinearMap.BilinForm.mem_orthogonal_iff] at horth
  have hX : evalDomain (novelX u) ∈ rsCode :=
    mem_rsCode.mpr ⟨novelX u, (AdditiveNTT.basisVectors (ZMod 2) basis 14 (by norm_num) u).2, rfl⟩
  have h0 : novelCoeff w u = 0 := by
    have := horth _ hX
    change dotForm (evalDomain (novelX u)) w = 0 at this
    rwa [dotForm_apply] at this
  simp [h0]

/-- The challenges for which a row is orthogonal to the dual codeword. -/
noncomputable def acceptSet (w : Row) : Finset (Fin 14 → E) :=
  Finset.univ.filter fun z ↦ dot (dual z) w = 0

theorem mem_acceptSet {w : Row} {z : Fin 14 → E} : z ∈ acceptSet w ↔ dot (dual z) w = 0 := by
  simp [acceptSet]

/-- **Schwartz-Zippel**: a row that is not a codeword is orthogonal to the dual codeword for at
most `14 |E|^13` of the `|E|^14` challenges. -/
theorem card_acceptSet_le {w : Row} (hw : w ∉ rsCode) :
    (acceptSet w).card ≤ 14 * Fintype.card E ^ 13 := by
  unfold acceptSet
  obtain ⟨u₀, hu₀⟩ : ∃ u, novelCoeff w u ≠ 0 := by
    by_contra h
    push Not at h
    exact hw (mem_rsCode_of_orthogonal h)
  have hp := membershipPoly_ne_zero hu₀
  have hsz := MvPolynomial.schwartz_zippel_totalDegree hp (Finset.univ : Finset E)
  simp only [Fintype.piFinset_univ, Finset.card_univ, eval_membershipPoly] at hsz
  have hE : (0 : ℚ≥0) < Fintype.card E := by exact_mod_cast Fintype.card_pos
  have hdeg : ((membershipPoly w).totalDegree : ℚ≥0) ≤ 14 := by
    exact_mod_cast totalDegree_membershipPoly_le w
  have h1 : ((Finset.univ.filter fun z : Fin 14 → E ↦ dot (dual z) w = 0).card : ℚ≥0) ≤
      14 * (Fintype.card E : ℚ≥0) ^ 13 := by
    have h2 := hsz.trans (div_le_div_of_nonneg_right hdeg hE.le)
    rw [div_le_div_iff₀ (pow_pos hE 14) hE] at h2
    have h3 : ((Finset.univ.filter fun z : Fin 14 → E ↦ dot (dual z) w = 0).card : ℚ≥0) *
        Fintype.card E ≤ 14 * (Fintype.card E : ℚ≥0) ^ 13 * Fintype.card E := by
      calc _ ≤ 14 * (Fintype.card E : ℚ≥0) ^ 14 := h2
        _ = _ := by ring
    exact le_of_mul_le_mul_right h3 hE
  exact_mod_cast h1

end LeanDa
