import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.CacheIndexMultiplicity

/-! ## CacheGrowthCharge -/

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem enncard_cacheQuery_of_fresh (cache : QueryCache HashSpec) (input : HashInput)
    (output : HashOutput) (hfresh : cache input = none) :
    QueryCache.enncard (cache.cacheQuery input output) = QueryCache.enncard cache + 1 := by
  have hset : (cache.cacheQuery input output).toSet = insert ⟨input, output⟩ cache.toSet := by
    apply Set.Subset.antisymm (QueryCache.toSet_cacheQuery_subset_insert cache input output)
    rintro pair (heq | hold)
    · subst pair
      exact QueryCache.cacheQuery_self _ _ _
    · exact QueryCache.toSet_mono (QueryCache.le_cacheQuery cache hfresh) hold
  have hnot : (⟨input, output⟩ : Sigma HashSpec.Range) ∉ cache.toSet := by
    simp only [QueryCache.mem_toSet, hfresh, reduceCtorEq, not_false_eq_true]
  unfold QueryCache.enncard
  rw [hset, Set.encard_insert_of_notMem hnot]
  simp

end SphincsSecurity.Concrete

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (MessageHashInput)
attribute [local instance] Classical.propDecidable

theorem cachedIndexMultiplicity_le_enncard (parameter : PublicParameter) (cache : QueryCache HashSpec)
    (hfinite : Finite cache) (index : Index) :
    cachedIndexMultiplicity parameter cache index ≤ QueryCache.enncard cache := by
  unfold cachedIndexMultiplicity cacheMessageWeight
  rw [tsum_eq_sum (s := hfinite.toFinset) (fun input hnot => by
    have hnone : cache input = none := by
      by_contra h
      exact hnot (hfinite.mem_toFinset.mpr h)
    simp only [cacheMessageEntryWeight, hnone])]
  calc
    _ ≤ ∑ _input ∈ hfinite.toFinset, (1 : ENNReal) := by
      apply Finset.sum_le_sum
      intro input _
      unfold cacheMessageEntryWeight
      cases cache input <;> simp only
      · exact zero_le
      · split_ifs <;> norm_num
    _ = _ := by
      rw [Finset.sum_const, nsmul_eq_mul, mul_one,
        ← Set.ncard_eq_toFinset_card {input | cache input ≠ none} hfinite]
      exact hfinite.cachedInputs_ncard_toENNReal_eq_enncard

theorem cachedIndexMultiplicity_ne_top (parameter : PublicParameter) (cache : QueryCache HashSpec)
    (hfinite : Finite cache) (index : Index) : cachedIndexMultiplicity parameter cache index ≠ ⊤ := by
  apply ne_top_of_le_ne_top _ (cachedIndexMultiplicity_le_enncard parameter cache hfinite index)
  rw [← hfinite.cachedInputs_ncard_toENNReal_eq_enncard]
  finiteness

noncomputable def cachedIndexExcessScore (parameter : PublicParameter) (cache : QueryCache HashSpec)
    (index : Index) : ℝ :=
  (cachedIndexMultiplicity parameter cache index).toReal - (QueryCache.enncard cache).toReal / 2 ^ 36

theorem cachedIndexExcessScore_cacheQuery (parameter : PublicParameter) (cache : QueryCache HashSpec)
    (hfinite : Finite cache) (input : HashInput) (output : HashOutput)
    (hfresh : cache input = none) (index : Index) :
    cachedIndexExcessScore parameter (cache.cacheQuery input output) index =
      cachedIndexExcessScore parameter cache index +
        (if MessageHashInput parameter input ∧ Admissible (truncateMessageDigest output) ∧
          (hashOutputFewTimeView output).1 = index then 1 else 0) - (2 ^ 36 : ℝ)⁻¹ := by
  have hcount := cachedIndexMultiplicity_ne_top parameter cache hfinite index
  have hcard : QueryCache.enncard cache ≠ ⊤ := by
    rw [← hfinite.cachedInputs_ncard_toENNReal_eq_enncard]
    finiteness
  unfold cachedIndexExcessScore
  rw [cachedIndexMultiplicity_cacheQuery parameter cache input output hfresh,
    enncard_cacheQuery_of_fresh cache input output hfresh,
    ENNReal.toReal_add hcard (by finiteness), ENNReal.toReal_one]
  split_ifs <;> simp only [add_zero, ENNReal.toReal_add hcount (by finiteness), ENNReal.toReal_one] <;> ring

theorem cachedIndexExcessScore_nonpos_of_no_message (parameter : PublicParameter)
    (cache : QueryCache HashSpec) (hnone : ∀ input, MessageHashInput parameter input → cache input = none)
    (index : Index) : cachedIndexExcessScore parameter cache index ≤ 0 := by
  rw [cachedIndexExcessScore, cachedIndexMultiplicity, cacheMessageWeight_of_no_message parameter _ cache hnone,
    ENNReal.toReal_zero, zero_sub]
  exact neg_nonpos.mpr (div_nonneg ENNReal.toReal_nonneg (by positivity))

def CachedIndexExcessExceptional (parameter : PublicParameter) (cache : QueryCache HashSpec) : Prop :=
  ∃ index, (2 ^ 80 : ℝ) < cachedIndexExcessScore parameter cache index

theorem cachedIndexExcessExceptional_of_bound_failure (parameter : PublicParameter)
    (cache : QueryCache HashSpec) (hfinite : Finite cache) (spent : Nat)
    (hcache : QueryCache.enncard cache ≤ spent) (index : Index)
    (hbad : (spent : ENNReal) * ((2 ^ 36 : Nat) : ENNReal)⁻¹ + ((2 ^ 80 : Nat) : ENNReal) <
      cachedIndexMultiplicity parameter cache index) : CachedIndexExcessExceptional parameter cache := by
  have hcard : QueryCache.enncard cache ≠ ⊤ := by
    rw [← hfinite.cachedInputs_ncard_toENNReal_eq_enncard]
    finiteness
  have hreal := (ENNReal.toReal_lt_toReal (by finiteness)
    (cachedIndexMultiplicity_ne_top parameter cache hfinite index)).mpr hbad
  have hcacheReal := (ENNReal.toReal_le_toReal hcard (by finiteness)).mpr hcache
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)] at hreal
  norm_num [ENNReal.toReal_mul, ENNReal.toReal_inv] at hreal hcacheReal
  refine ⟨index, ?_⟩
  unfold cachedIndexExcessScore
  have hscaled := div_le_div_of_nonneg_right hcacheReal (by positivity : (0 : ℝ) ≤ 2 ^ 36)
  norm_num at hscaled ⊢
  linarith

theorem cachedIndex_bound_of_no_excess (parameter : PublicParameter) (cache : QueryCache HashSpec)
    (hfinite : Finite cache) (spent : Nat) (hcache : QueryCache.enncard cache ≤ spent)
    (hclean : ¬ CachedIndexExcessExceptional parameter cache) (index : Index) :
    cachedIndexMultiplicity parameter cache index ≤
      (spent : ENNReal) * ((2 ^ 36 : Nat) : ENNReal)⁻¹ + ((2 ^ 80 : Nat) : ENNReal) := by
  by_contra hbad
  exact hclean (cachedIndexExcessExceptional_of_bound_failure parameter cache hfinite spent hcache index
    (lt_of_not_ge hbad))

end SphincsSecurity.Concrete
