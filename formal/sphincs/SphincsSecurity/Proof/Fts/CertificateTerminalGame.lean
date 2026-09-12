import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.CertificateGame
import SphincsSecurity.Proof.Fts.OriginalTerminalProposal
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem simulateQ_certificateProposalImpl_complete {α : Type} (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule) (total : Nat)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : List Index × CertificateMonitorState) :
    ((simulateQ (certificateProposalImpl key budget required stopAfter) computation).run state).bind
        (fun result => completeProposalWord (PMF.uniformOfFintype Index) total result.2.1) =
      completeProposalWord (PMF.uniformOfFintype Index) total state.1 :=
  simulateQ_originalProposalImpl_complete key (fun current : CertificateMonitorState => current.2.spent) (certificateMonitorEnabled key budget)
    (certificateMonitorUpdate key budget required stopAfter) total computation state

theorem expected_certificateProposalImpl_terminalPotential (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule) (total : Nat) (payoff : List Index → ENNReal)
    (input : (OracleWorld + SigningSpec).Domain) (state : List Index × CertificateMonitorState) :
    (∑' result, Pr[= result | (certificateProposalImpl key budget required stopAfter input).run state] *
        terminalProposalPotential (PMF.uniformOfFintype Index) total payoff result.2.1) =
      terminalProposalPotential (PMF.uniformOfFintype Index) total payoff state.1 :=
  expected_originalProposalImpl_terminalPotential key (fun current : CertificateMonitorState => current.2.spent) (certificateMonitorEnabled key budget)
    (certificateMonitorUpdate key budget required stopAfter) total payoff input state

theorem certificateGame_complete (adversary : Adversary) (budget : Nat) (required : Finset FtsTree)
    (stopAfter : SecretKey → CertificateStopRule) (stopped : Bool) (total : Nat) :
    (certificateGame adversary budget required stopAfter stopped).bind
        (fun result => completeProposalWord (PMF.uniformOfFintype Index) total result.2.1) =
      independentProposalWord (PMF.uniformOfFintype Index) total := by
  rw [certificateGame, PMF.monad_bind_eq_bind, PMF.bind_bind]
  simp_rw [simulateQ_certificateProposalImpl_complete, completeProposalWord_nil]
  exact PMF.bind_const _ _

noncomputable def certificateTerminalGame (adversary : Adversary) (budget : Nat) (required : Finset FtsTree)
    (stopAfter : SecretKey → CertificateStopRule) (stopped : Bool) (total : Nat) :
    PMF (CertificateGameResult × List Index) :=
  (certificateGame adversary budget required stopAfter stopped).bind fun result =>
    (completeProposalWord (PMF.uniformOfFintype Index) total result.2.1).map (fun word => (result, word))

theorem certificateTerminalGame_game (adversary : Adversary) (budget : Nat) (required : Finset FtsTree)
    (stopAfter : SecretKey → CertificateStopRule) (stopped : Bool) (total : Nat) :
    (certificateTerminalGame adversary budget required stopAfter stopped total).map Prod.fst =
      certificateGame adversary budget required stopAfter stopped := by
  rw [certificateTerminalGame, PMF.map_bind]
  simp only [PMF.map_comp, Function.comp_def]
  change (certificateGame adversary budget required stopAfter stopped).bind (fun result =>
    (completeProposalWord (PMF.uniformOfFintype Index) total result.2.1).map (Function.const _ result)) = _
  simp only [PMF.map_const, PMF.bind_pure]

theorem certificateTerminalGame_word (adversary : Adversary) (budget : Nat) (required : Finset FtsTree)
    (stopAfter : SecretKey → CertificateStopRule) (stopped : Bool) (total : Nat) :
    (certificateTerminalGame adversary budget required stopAfter stopped total).map Prod.snd =
      independentProposalWord (PMF.uniformOfFintype Index) total := by
  rw [certificateTerminalGame, PMF.map_bind]
  simp only [PMF.map_comp, Function.comp_def]
  change (certificateGame adversary budget required stopAfter stopped).bind (fun result =>
    (completeProposalWord (PMF.uniformOfFintype Index) total result.2.1).map id) = _
  simp only [PMF.map_id]
  exact certificateGame_complete adversary budget required stopAfter stopped total

theorem certificateTerminalGame_cost_le (adversary : Adversary) (q : Nat) (required : Finset FtsTree)
    (stopAfter : SecretKey → CertificateStopRule) (stopped : Bool) (total : Nat)
    (hbound : HasHashQueryBound scheme adversary q) (result : CertificateGameResult × List Index)
    (hr : result ∈ (certificateTerminalGame adversary q required stopAfter stopped total).support) :
    result.1.2.2.2.spent ≤ q ∧ result.1.2.2.2.creationMass ≤ q := by
  have hm := (PMF.mem_support_map_iff Prod.fst _ _).mpr ⟨result, hr, rfl⟩
  rw [certificateTerminalGame_game] at hm
  exact certificateGame_cost_le adversary q required stopAfter stopped hbound result.1 hm

theorem expected_certificateTerminalGame_mass_payoff_le (adversary : Adversary) (q : Nat)
    (required : Finset FtsTree) (stopAfter : SecretKey → CertificateStopRule) (stopped : Bool) (total : Nat)
    (hbound : HasHashQueryBound scheme adversary q) (payoff : List Index → ENNReal) :
    (∑' result, Pr[= result | certificateTerminalGame adversary q required stopAfter stopped total] *
        (result.1.2.2.2.creationMass * payoff result.2)) ≤
      (q : ENNReal) * ∑' word, Pr[= word | independentProposalWord (PMF.uniformOfFintype Index) total] * payoff word := by
  have hword := congrArg (fun law : PMF (List Index) => ∑' word, Pr[= word | law] * payoff word)
    (certificateTerminalGame_word adversary q required stopAfter stopped total)
  rw [← PMF.monad_map_eq_map, tsum_probOutput_map_mul] at hword
  calc
    _ ≤ ∑' result, (q : ENNReal) *
        (Pr[= result | certificateTerminalGame adversary q required stopAfter stopped total] * payoff result.2) := by
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hzero : Pr[= result | certificateTerminalGame adversary q required stopAfter stopped total] = 0
      · rw [hzero, zero_mul, zero_mul, mul_zero]
      · have hr : result ∈ (certificateTerminalGame adversary q required stopAfter stopped total).support := by
          simpa only [PMF.mem_support_iff, PMF.probOutput_eq_apply] using hzero
        have hmass := (certificateTerminalGame_cost_le adversary q required stopAfter stopped total hbound result hr).2
        calc
          _ ≤ Pr[= result | certificateTerminalGame adversary q required stopAfter stopped total] *
              ((q : ENNReal) * payoff result.2) := mul_le_mul' le_rfl (mul_le_mul' hmass le_rfl)
          _ = _ := by ring
    _ = _ := by rw [ENNReal.tsum_mul_left, hword]

end SphincsSecurity.Concrete
