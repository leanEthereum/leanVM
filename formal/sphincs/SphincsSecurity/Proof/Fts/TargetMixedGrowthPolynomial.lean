import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.NormalizedTargetMatches
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem normalizedSourceSubsetMatch_mul (target source : FewTimeView) (left right : Finset FtsTree)
    (hdisjoint : Disjoint left right) :
    normalizedSourceSubsetMatch target source left * normalizedSourceSubsetMatch target source right =
      normalizedSourceSubsetMatch target source (left ∪ right) := by
  unfold normalizedSourceSubsetMatch
  rw [Finset.card_union_of_disjoint hdisjoint, pow_add, Nat.cast_mul, ← sourceSubsetMatch_mul, Nat.cast_mul]
  ring

theorem normalizedSourceSubsetMatch_singletons (target source : FewTimeView) (required : Finset FtsTree) :
    (∏ tree ∈ required, normalizedSourceSubsetMatch target source {tree}) = normalizedSourceSubsetMatch target source required := by
  simp only [normalizedSourceSubsetMatch, sourceSubsetMatch, Finset.card_singleton, pow_one,
    Finset.prod_singleton, Finset.prod_mul_distrib, Finset.prod_const, Nat.cast_pow, Nat.cast_prod]

noncomputable def targetCacheArrivalPolynomial (cached : Fin m → ENNReal) (groups : Fin m → Finset FtsTree)
    (target source : FewTimeView) : ENNReal :=
  ∑ selected ∈ (Finset.univ : Finset (Fin m)).powerset.erase ∅,
    (∏ slot ∈ selected, normalizedSourceSubsetMatch target source (groups slot)) *
      ∏ slot ∈ (Finset.univ : Finset (Fin m)) \ selected, cached slot

theorem targetCacheProduct_add_arrival (cached : Fin m → ENNReal) (groups : Fin m → Finset FtsTree)
    (target source : FewTimeView) :
    (∏ slot : Fin m, cached slot) + targetCacheArrivalPolynomial cached groups target source =
      ∏ slot : Fin m, (cached slot + normalizedSourceSubsetMatch target source (groups slot)) := by
  rw [show (∏ slot : Fin m, (cached slot + normalizedSourceSubsetMatch target source (groups slot))) =
    ∏ slot : Fin m, (normalizedSourceSubsetMatch target source (groups slot) + cached slot) by simp only [add_comm]]
  rw [Finset.prod_add, ← Finset.add_sum_erase _ _ (Finset.empty_mem_powerset _)]
  simp only [Finset.prod_empty, Finset.sdiff_empty, one_mul, targetCacheArrivalPolynomial]

theorem targetLogProduct_insert_expansion (logged : FtsTree → ENNReal) (required : Finset FtsTree) (target source : FewTimeView) :
    (∏ tree ∈ required, (logged tree + normalizedSourceSubsetMatch target source {tree})) =
      ∑ selected ∈ required.powerset, normalizedSourceSubsetMatch target source selected *
        ∏ tree ∈ required \ selected, logged tree := by
  rw [show (∏ tree ∈ required, (logged tree + normalizedSourceSubsetMatch target source {tree})) =
    ∏ tree ∈ required, (normalizedSourceSubsetMatch target source {tree} + logged tree) by simp only [add_comm]]
  rw [Finset.prod_add]
  simp only [normalizedSourceSubsetMatch_singletons]

noncomputable def targetMixedGrowthPolynomial (cached : Fin m → ENNReal) (logged : FtsTree → ENNReal)
    (groups : Fin m → Finset FtsTree) (required : Finset FtsTree) (target source : FewTimeView) : ENNReal :=
  targetCacheArrivalPolynomial cached groups target source *
    ∏ tree ∈ required, (logged tree + normalizedSourceSubsetMatch target source {tree})

theorem expected_targetMixedGrowthPolynomial (cached : Fin m → ENNReal) (logged : FtsTree → ENNReal)
    (groups : Fin m → Finset FtsTree) (required : Finset FtsTree) (target : FewTimeView)
    (hgroups : ∀ slot, (groups slot).Nonempty) (hdisjoint : Pairwise (fun i j => Disjoint (groups i) (groups j)))
    (hremaining : ∀ slot, Disjoint (groups slot) required) :
    (∑' source, Pr[= source | ($ᵗ FewTimeView : ProbComp FewTimeView)] *
      targetMixedGrowthPolynomial cached logged groups required target source) =
      (Fintype.card Index : ENNReal)⁻¹ *
        ∑ selected ∈ (Finset.univ : Finset (Fin m)).powerset.erase ∅,
          ∑ trees ∈ required.powerset,
            (∏ slot ∈ (Finset.univ : Finset (Fin m)) \ selected, cached slot) *
              ∏ tree ∈ required \ trees, logged tree := by
  simp only [targetMixedGrowthPolynomial, targetCacheArrivalPolynomial, targetLogProduct_insert_expansion]
  simp only [Finset.sum_mul]
  simp only [Finset.mul_sum]
  rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  apply Finset.sum_congr rfl
  intro selected hselected
  rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  apply Finset.sum_congr rfl
  intro trees htrees
  have hselectedNonempty := Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp hselected).1
  have hpair : (selected : Set (Fin m)).PairwiseDisjoint groups := fun i _ j _ hij => hdisjoint hij
  have hsep : Disjoint (selected.biUnion groups) trees := by
    rw [Finset.disjoint_biUnion_left]
    intro slot _
    exact (hremaining slot).mono_right (Finset.mem_powerset.mp htrees)
  have hpoint (source : FewTimeView) :
      (∏ slot ∈ selected, normalizedSourceSubsetMatch target source (groups slot)) *
        (∏ slot ∈ (Finset.univ : Finset (Fin m)) \ selected, cached slot) *
          (normalizedSourceSubsetMatch target source trees * ∏ tree ∈ required \ trees, logged tree) =
      normalizedSourceSubsetMatch target source (selected.biUnion groups ∪ trees) *
        ((∏ slot ∈ (Finset.univ : Finset (Fin m)) \ selected, cached slot) * ∏ tree ∈ required \ trees, logged tree) := by
    rw [normalizedSourceSubsetMatch_prod target source groups selected hpair, ← normalizedSourceSubsetMatch_mul target source _ _ hsep]
    ring
  simp only [hpoint, ← mul_assoc, ENNReal.tsum_mul_right]
  obtain ⟨slot, hslot⟩ := hselectedNonempty
  obtain ⟨tree, htree⟩ := hgroups slot
  rw [expected_normalizedSourceSubsetMatch target (selected.biUnion groups ∪ trees)
    ⟨tree, Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨slot, hslot, htree⟩)⟩]

end SphincsSecurity.Concrete
