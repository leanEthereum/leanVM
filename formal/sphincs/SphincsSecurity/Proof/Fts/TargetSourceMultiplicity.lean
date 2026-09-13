import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.FewTimeConditionalCoverage
import SphincsSecurity.Proof.Fts.NormalizedTargetCacheQuery
import SphincsSecurity.Proof.Fts.TargetSigningMatchFactors
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def excludedCacheSourceCount (parameter : PublicParameter) (cache : QueryCache HashSpec)
    (targetInput : HashInput) (source : FewTimeView) : ENNReal :=
  cacheMessageWeight parameter (fun input view => if input = targetInput then 0 else if view = source then 1 else 0) cache

theorem excludedCacheSourceCount_weight (parameter : PublicParameter) (cache : QueryCache HashSpec)
    (targetInput : HashInput) (weight : FewTimeView → ENNReal) :
    (∑ source : FewTimeView, excludedCacheSourceCount parameter cache targetInput source * weight source) =
      cacheMessageWeight parameter (fun input view => if input = targetInput then 0 else weight view) cache := by
  simp only [excludedCacheSourceCount, ← cacheMessageWeight_mul_right]
  rw [← cacheMessageWeight_sum]
  apply congrArg (fun f : HashInput → FewTimeView → ENNReal => cacheMessageWeight parameter f cache)
  funext input view
  by_cases heq : input = targetInput
  · simp only [heq, if_true, zero_mul, Finset.sum_const_zero]
  · simp only [heq, if_false, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem normalizedCachedTargetSubsetMatch_eq_sourceCount (parameter : PublicParameter) (cache : QueryCache HashSpec)
    (targetInput : HashInput) (target : FewTimeView) (required : Finset FtsTree) :
    normalizedCachedTargetSubsetMatch parameter cache targetInput target required =
      ∑ source : FewTimeView, excludedCacheSourceCount parameter cache targetInput source * normalizedSourceSubsetMatch target source required := by
  rw [excludedCacheSourceCount_weight, normalizedCachedTargetSubsetMatch_eq_weight]

noncomputable def optionalSourceCount (views : Fin n → Option FewTimeView) (source : FewTimeView) : ENNReal :=
  ∑ slot : Fin n, if views slot = some source then 1 else 0

theorem optionalSourceCount_weight (views : Fin n → Option FewTimeView) (weight : FewTimeView → ENNReal) :
    (∑ source : FewTimeView, optionalSourceCount views source * weight source) =
      ∑ slot : Fin n, match views slot with | none => 0 | some source => weight source := by
  simp only [optionalSourceCount, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro slot _
  cases hview : views slot with
  | none => simp only [reduceCtorEq, if_false, zero_mul, Finset.sum_const_zero]
  | some source => simp only [Option.some.injEq, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem normalizedTargetTreeMatchCount_eq_sourceCount (views : Fin n → Option FewTimeView) (target : FewTimeView) (tree : FtsTree) :
    (Fintype.card FtsLeaf : ENNReal) * (targetTreeMatchCount views target tree : ENNReal) =
      ∑ source : FewTimeView, optionalSourceCount views source * normalizedSourceSubsetMatch target source {tree} := by
  rw [optionalSourceCount_weight]
  simp only [targetTreeMatchCount, Nat.cast_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro slot _
  cases hview : views slot with
  | none => simp only [reduceCtorEq, false_and, exists_false, if_false, Nat.cast_zero, mul_zero]
  | some source => simp only [Option.some.injEq, exists_eq_left', normalizedSourceSubsetMatch_singleton, sourceTreeMatch]

theorem optionalSourceCount_index (views : Fin n → Option FewTimeView) (index : Index) :
    (∑ source : FewTimeView, if source.1 = index then optionalSourceCount views source else 0) =
      ((signingSlotsAtIndex views index).card : ENNReal) := by
  have heq (source : FewTimeView) : (if source.1 = index then optionalSourceCount views source else 0) =
      optionalSourceCount views source * (if source.1 = index then 1 else 0) := by
    split_ifs <;> simp only [mul_one, mul_zero]
  simp only [heq]
  rw [optionalSourceCount_weight]
  simp only [signingSlotsAtIndex, Finset.card_eq_sum_ones, Finset.sum_filter, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro slot _
  cases hview : views slot with
  | none => simp only [reduceCtorEq, false_and, exists_false, if_false, Nat.cast_zero]
  | some source => simp only [Option.some.injEq, exists_eq_left', Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

end SphincsSecurity.Concrete
