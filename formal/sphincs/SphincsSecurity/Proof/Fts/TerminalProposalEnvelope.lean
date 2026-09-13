import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.CertificateMonitor
import SphincsSecurity.Proof.Fts.OriginalTerminalProposal
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal

noncomputable def terminalCertificatePrice (required : Finset FtsTree) (word : List Index) : ENNReal :=
  (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹) *
    (∑ index : Index, (word.count index : ENNReal) ^ required.card) * targetCertificateScale required

theorem terminalProposalPotential_eq_uniform_suffix (total : Nat) (consumed : List Index)
    (hused : consumed.length ≤ total) (payoff : List Index → ENNReal) :
    terminalProposalPotential (PMF.uniformOfFintype Index) total payoff consumed =
      ∑' suffix, Pr[= suffix | sampleUniformProposalWord Index (total - consumed.length)] *
        payoff (consumed ++ suffix) := by
  rw [terminalProposalPotential, completeProposalWord_eq_padding, ← PMF.monad_map_eq_map,
    tsum_probOutput_map_mul, List.take_of_length_le hused]
  apply tsum_congr
  intro suffix
  simp only [probOutput_def, evalDist_sampleUniformProposalWord, PMF.evalDist_eq]

theorem terminalProposalPotential_scale {α : Type} (base : PMF α) (total : Nat)
    (payoff : List α → ENNReal) (consumed : List α) (left right : ENNReal) :
    terminalProposalPotential base total (fun word => left * payoff word * right) consumed =
      left * terminalProposalPotential base total payoff consumed * right := by
  unfold terminalProposalPotential
  calc
    _ = ∑' word, (left * (Pr[= word | completeProposalWord base total consumed] * payoff word)) * right := by
      apply tsum_congr
      intro word
      ring
    _ = _ := by rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_left]

theorem targetProposalPrefix_length_le (completed total : Nat) (consumed : List Index)
    (hcompleted : completed ≤ signatureLimit) (htotal : 25313293 ≤ total)
    (hprefix : (consumed.length : ENNReal) ≤ targetProposalOverhead * completed + 131072) :
    consumed.length ≤ total := by
  apply (Nat.cast_le (α := ENNReal)).mp
  calc
    _ ≤ targetProposalOverhead * completed + 131072 := hprefix
    _ ≤ targetProposalOverhead * signatureLimit + 131072 :=
      add_le_add (mul_le_mul' le_rfl (Nat.cast_le.mpr hcompleted)) le_rfl
    _ ≤ targetProposalOverhead * signatureLimit + 131072 + 13 := le_self_add
    _ = (25313293 : ENNReal) := targetProposalPoolMinimum_eq
    _ ≤ (total : ENNReal) := by exact_mod_cast htotal

theorem reuseRawEnvelope_le_terminalProposalPotential (key : SecretKey)
    (spent queries completed total : Nat) (state : CoverLogState) (required : Finset FtsTree)
    (consumed : List Index) (hqueries : spent + queries ≤ 2 ^ 127)
    (hcompleted : completed ≤ signatureLimit)
    (hcache : ∀ index : Index, cachedIndexMultiplicity key.parameter state.1 index ≤
      (spent : ENNReal) * ((2 ^ 36 : Nat) : ENNReal)⁻¹ + ((2 ^ 80 : Nat) : ENNReal))
    (hcounts : ∀ index : Index,
      (signingSlotsAtIndex (observedOptionalSigningViews
        (FtsProbeSimulation.messageAnswers key.parameter state.1) key.root state.2) index).card ≤ consumed.count index)
    (htotal : 25313293 ≤ total)
    (hprefix : (consumed.length : ENNReal) ≤ targetProposalOverhead * completed + 131072) :
    reuseRawEnvelope key nearUniformDigestReuseWeight queries (signatureLimit - completed) state ∅ required ≤
      terminalProposalPotential (PMF.uniformOfFintype Index) total
        (fun word => ∑ index : Index, (word.count index : ENNReal) ^ required.card) consumed := by
  rw [terminalProposalPotential_eq_uniform_suffix total consumed
    (targetProposalPrefix_length_le completed total consumed hcompleted htotal hprefix)]
  exact reuseRawEnvelope_le_expected_terminalProposalWord key spent queries completed total state required consumed
    hqueries hcompleted hcache hcounts htotal hprefix

theorem targetCreationPrice_le_terminalProposalPotential (key : SecretKey)
    (spent queries completed total : Nat) (state : CoverLogState) (required : Finset FtsTree)
    (consumed : List Index) (hqueries : spent + queries ≤ 2 ^ 127)
    (hcompleted : completed ≤ signatureLimit)
    (hcache : ∀ index : Index, cachedIndexMultiplicity key.parameter state.1 index ≤
      (spent : ENNReal) * ((2 ^ 36 : Nat) : ENNReal)⁻¹ + ((2 ^ 80 : Nat) : ENNReal))
    (hcounts : ∀ index : Index,
      (signingSlotsAtIndex (observedOptionalSigningViews
        (FtsProbeSimulation.messageAnswers key.parameter state.1) key.root state.2) index).card ≤ consumed.count index)
    (htotal : 25313293 ≤ total)
    (hprefix : (consumed.length : ENNReal) ≤ targetProposalOverhead * completed + 131072) :
    targetCreationPrice key nearUniformDigestReuseWeight queries (signatureLimit - completed) required state ≤
      terminalProposalPotential (PMF.uniformOfFintype Index) total (terminalCertificatePrice required) consumed := by
  unfold terminalCertificatePrice
  rw [targetCreationPrice, terminalProposalPotential_scale]
  exact mul_le_mul' (mul_le_mul' le_rfl
    (reuseRawEnvelope_le_terminalProposalPotential key spent queries completed total state required consumed
      hqueries hcompleted hcache hcounts htotal hprefix)) le_rfl

theorem certificateMonitorCharge_le_terminalPrice (key : SecretKey) (budget total : Nat)
    (required : Finset FtsTree) (input : (OracleWorld + SigningSpec).Domain)
    (state : CertificateMonitorState) (consumed : List Index) (hbudget : budget ≤ 2 ^ 127)
    (hcompleted : state.2.log.length ≤ signatureLimit)
    (hcounts : ∀ index : Index,
      (signingSlotsAtIndex (observedOptionalSigningViews
        (FtsProbeSimulation.messageAnswers key.parameter state.1) key.root state.2.log) index).card ≤ consumed.count index)
    (htotal : 25313293 ≤ total)
    (hprefix : (consumed.length : ENNReal) ≤ targetProposalOverhead * state.2.log.length + 131072) :
    certificateMonitorCharge key budget required input state ≤
      certificateMonitorMass key budget input state *
        terminalProposalPotential (PMF.uniformOfFintype Index) total (terminalCertificatePrice required) consumed := by
  classical
  by_cases hactive : CertificateMonitorActive key budget input state
  · rw [certificateMonitorCharge, certificateMonitorMass, if_pos hactive, if_pos hactive]
    apply mul_le_mul' le_rfl
    have hspent : state.2.spent ≤ budget := hactive.2.1.2.2
    exact targetCreationPrice_le_terminalProposalPotential key state.2.spent (budget - state.2.spent)
      state.2.log.length total (certificateMonitorCoverState state) required consumed (by omega)
      hcompleted hactive.2.1.2.1.index_le hcounts htotal hprefix
  · simp only [certificateMonitorCharge, certificateMonitorMass, if_neg hactive, zero_mul, le_refl]

end SphincsSecurity.Concrete
