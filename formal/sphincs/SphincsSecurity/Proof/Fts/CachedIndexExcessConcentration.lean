import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.CachedIndexHashMoments
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal

noncomputable def cachedIndexExcessMoment (parameter : PublicParameter) (cache : QueryCache HashSpec) : ENNReal :=
  ∑ index : Index, positiveScoreMoment (cachedIndexExcessScore parameter cache index) 2

theorem cachedIndexExcessExceptional_moment_ge (parameter : PublicParameter) (cache : QueryCache HashSpec)
    (hbad : CachedIndexExcessExceptional parameter cache) :
    (2 ^ 160 : ENNReal) ≤ cachedIndexExcessMoment parameter cache := by
  obtain ⟨index, hindex⟩ := hbad
  have hpower : (2 ^ 160 : ℝ) ≤ max (cachedIndexExcessScore parameter cache index) 0 ^ 2 := by
    calc
      _ = (2 ^ 80 : ℝ) ^ 2 := by rw [← pow_mul]
      _ ≤ _ := pow_le_pow_left₀ (by positivity) (hindex.le.trans (le_max_left _ _)) 2
  have hreal := ENNReal.ofReal_le_ofReal hpower
  rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_ofNat] at hreal
  exact hreal.trans (Finset.single_le_sum (s := Finset.univ)
    (f := fun index => positiveScoreMoment (cachedIndexExcessScore parameter cache index) 2)
    (fun _ _ => zero_le) (Finset.mem_univ index))

theorem cachedIndexExcessMoment_zero_of_no_message (parameter : PublicParameter)
    (cache : QueryCache HashSpec)
    (hnone : ∀ input, FtsProbeSimulation.MessageHashInput parameter input → cache input = none) :
    cachedIndexExcessMoment parameter cache = 0 := by
  apply Finset.sum_eq_zero
  intro index _
  exact positiveScoreMoment_zero_of_nonpos _
    (cachedIndexExcessScore_nonpos_of_no_message parameter cache hnone index) 2 (by decide)

theorem expected_cachedIndexExcessMoment_le (parameter : PublicParameter)
    (cache : QueryCache HashSpec) (hfinite : Finite cache) (input : HashInput) (hfresh : cache input = none) :
    (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
      cachedIndexExcessMoment parameter (cache.cacheQuery input output)) ≤
        cachedIndexExcessMoment parameter cache + (2 ^ 10 : ENNReal)⁻¹ := by
  calc
    _ = ∑ index : Index, ∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
        positiveScoreMoment (cachedIndexExcessScore parameter (cache.cacheQuery input output) index) 2 := by
      simp only [cachedIndexExcessMoment, Finset.mul_sum]
      exact Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)
    _ ≤ ∑ index : Index, (positiveScoreMoment (cachedIndexExcessScore parameter cache index) 2 +
        ((2 ^ 36 : Nat) : ENNReal)⁻¹) :=
      Finset.sum_le_sum (fun index _ => expected_cachedIndexScore_second_le parameter cache hfinite input hfresh index)
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      congr 1
      have hcard : Fintype.card Index = 2 ^ 26 := Fintype.card_fin _
      rw [hcard]
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      norm_num [ENNReal.toReal_mul, ENNReal.toReal_inv]

end SphincsSecurity.Concrete
