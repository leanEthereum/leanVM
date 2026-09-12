import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.ProposalWordDistribution
import SphincsSecurity.Proof.Fts.UniformProposalMoments
namespace SphincsSecurity.Concrete

open _root_.OracleComp ENNReal

theorem evalDist_sampleUniformProposalWord {α : Type} [SampleableType α] [Fintype α] [Nonempty α] (steps : Nat) :
    𝒟[sampleUniformProposalWord α steps] =
      (liftM (independentProposalWord (PMF.uniformOfFintype α) steps) : SPMF (List α)) := by
  induction steps with
  | zero => simp only [sampleUniformProposalWord, independentProposalWord, evalDist_pure]
  | succ steps ih =>
      simp only [sampleUniformProposalWord, evalDist_bind, evalDist_pure, evalDist_uniformSample, ih,
        independentProposalWord, PMF.map, Function.comp_def, ← PMF.monad_bind_eq_bind, PMF.evalDist_eq]
      simp only [← PMF.monad_pure_eq_pure, liftM_pure]

noncomputable def targetProposalAcceptance : ENNReal := targetProposalOverhead⁻¹

theorem targetProposalAcceptance_ne_zero : targetProposalAcceptance ≠ 0 := by
  rw [targetProposalAcceptance, ENNReal.inv_ne_zero]
  unfold targetProposalOverhead
  finiteness

theorem targetProposalAcceptance_lt_one : targetProposalAcceptance < 1 := by
  rw [targetProposalAcceptance, ENNReal.inv_lt_one]
  unfold targetProposalOverhead
  apply (ENNReal.toReal_lt_toReal (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_div]

theorem targetProposalAcceptance_cap {Ω : Type*} (record : PMF Ω) (label : Ω → Index)
    (hbound : ∀ index, (record.map label) index ≤ targetProposalIndexRate) (index : Index) :
    targetProposalAcceptance * (record.map label) index ≤ PMF.uniformOfFintype Index index := by
  rw [PMF.uniformOfFintype_apply, targetProposalAcceptance]
  calc
    _ ≤ targetProposalOverhead⁻¹ * targetProposalIndexRate := mul_le_mul' le_rfl (hbound index)
    _ = _ := by
      have hpositive : 0 < targetProposalOverhead :=
        zero_lt_one.trans (ENNReal.inv_lt_one.mp targetProposalAcceptance_lt_one)
      rw [targetProposalIndexRate, ← mul_assoc,
        ENNReal.inv_mul_cancel hpositive.ne'
          (by unfold targetProposalOverhead; finiteness), one_mul]

end SphincsSecurity.Concrete
