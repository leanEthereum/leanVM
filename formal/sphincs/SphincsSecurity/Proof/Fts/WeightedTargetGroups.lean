import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.SourceGroupExpectation
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem expected_weighted_targetGroups {α : Type} [Fintype α] [DecidableEq α] (groups : α → Finset FtsTree)
    (hne : ∀ slot, (groups slot).Nonempty) (hdisjoint : Pairwise (fun i j => Disjoint (groups i) (groups j)))
    (weight : α → FewTimeView → ENNReal) :
    (∑' target, Pr[= target | ($ᵗ FewTimeView : ProbComp FewTimeView)] *
      ∏ slot : α, ∑ source : FewTimeView, weight slot source * normalizedSourceSubsetMatch target source (groups slot)) =
        (Fintype.card Index : ENNReal)⁻¹ *
          ∑ index : Index, ∏ slot : α, ∑ source : FewTimeView, if source.1 = index then weight slot source else 0 := by
  classical
  have hproduct (target : FewTimeView) :
      (∏ slot : α, ∑ source : FewTimeView, weight slot source * normalizedSourceSubsetMatch target source (groups slot)) =
        ∑ sources : α → FewTimeView, (∏ slot : α, weight slot (sources slot)) *
          ∏ slot : α, normalizedSourceSubsetMatch target (sources slot) (groups slot) := by
    rw [Fintype.prod_sum]
    simp only [Finset.prod_mul_distrib]
  have hindex (index : Index) :
      (∏ slot : α, ∑ source : FewTimeView, if source.1 = index then weight slot source else 0) =
        ∑ sources : α → FewTimeView, ∏ slot : α, if (sources slot).1 = index then weight slot (sources slot) else 0 :=
    Fintype.prod_sum _
  have hexpect (sources : α → FewTimeView) :
      (∑ target : FewTimeView, Pr[= target | ($ᵗ FewTimeView : ProbComp FewTimeView)] *
        ((∏ slot : α, weight slot (sources slot)) * ∏ slot : α, normalizedSourceSubsetMatch target (sources slot) (groups slot))) =
        (∏ slot : α, weight slot (sources slot)) * ((Fintype.card Index : ENNReal)⁻¹ *
          ∑ index : Index, ∏ slot : α, if (sources slot).1 = index then (1 : ENNReal) else 0) := by
    simp only [mul_left_comm (Pr[= _ | ($ᵗ FewTimeView : ProbComp FewTimeView)]), ← Finset.mul_sum]
    apply congrArg (fun value : ENNReal => (∏ slot : α, weight slot (sources slot)) * value)
    simpa only [tsum_fintype] using expected_normalized_sourceGroupMatches groups hne hdisjoint sources
  simp only [tsum_fintype, hproduct, hindex, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [hexpect, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro index _
  apply Finset.sum_congr rfl
  intro sources _
  rw [show (∏ slot : α, if (sources slot).1 = index then weight slot (sources slot) else 0) =
      (∏ slot : α, weight slot (sources slot)) * ∏ slot : α, if (sources slot).1 = index then (1 : ENNReal) else 0 by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro slot _
    split_ifs <;> simp only [mul_one, mul_zero]]
  ring

end SphincsSecurity.Concrete
