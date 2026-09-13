import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.BankedProposalStep
import SphincsSecurity.Proof.Fts.ValidInterleavedCover

/-! ## SigningMacroBudget -/

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec

def signingMacroHashCost : (OracleWorld + SigningSpec).Domain → Nat
  | .inl (.inl _) => 0
  | .inl (.inr _) => 1
  | .inr _ => 1024

end SphincsSecurity.Concrete

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable

structure CertificateMonitor where
  log : QueryLog SigningSpec
  spent : Nat
  messageCalls : Nat
  proposals : Nat
  creationMass : ENNReal
  creationCost : ENNReal
  bank : HashInput → Bool
  stopped : Bool

abbrev CertificateMonitorState := QueryCache HashSpec × CertificateMonitor

def certificateMonitorCoverState (state : CertificateMonitorState) : CoverLogState :=
  (state.1, state.2.log)

def CertificateMonitorReady (key : SecretKey) (budget : Nat) (state : CertificateMonitorState) : Prop :=
  SigningDigestsCached key.parameter state.1 key.root state.2.log ∧
    ProposalCacheBound key state.1 state.2.spent ∧ state.2.spent ≤ budget

def CertificateMonitorActive (key : SecretKey) (budget : Nat)
    (input : (OracleWorld + SigningSpec).Domain) (state : CertificateMonitorState) : Prop :=
  state.2.stopped = false ∧ CertificateMonitorReady key budget state ∧
    ValidSigningStep state.2.log input ∧ signingMacroHashCost input ≤ budget - state.2.spent

abbrev CertificateStopRule := (input : (OracleWorld + SigningSpec).Domain) →
  CertificateMonitorState → Nat → ProposalExecutionRecord input → Bool

noncomputable def certificateMonitorEnabled (key : SecretKey) (budget : Nat)
    (message : Message) (state : CertificateMonitorState) : Bool :=
  decide (CertificateMonitorActive key budget (.inr message) state)

noncomputable def certificateMonitorUpdate (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain) (state : CertificateMonitorState)
    (length : Nat) (record : ProposalExecutionRecord input) : CertificateMonitor :=
  if CertificateMonitorActive key budget input state then
    let after := proposalRecordLogState input state.2.log record
    let next : CertificateMonitor :=
      { log := after.2
        spent := state.2.spent + record.trace.hashCalls
        messageCalls := state.2.messageCalls + record.trace.messageCalls.length
        proposals := state.2.proposals + length
        creationMass := state.2.creationMass + targetCreationMultiplier key state.1 input
        creationCost := state.2.creationCost + targetCreationMultiplier key state.1 input *
          targetCreationPrice key nearUniformDigestReuseWeight (budget - state.2.spent)
            (signatureLimit - state.2.log.length) required (certificateMonitorCoverState state)
        bank := completedTargetBank key required after state.2.bank
        stopped := false }
    { next with stopped := (stopAfter input state length record || decide (¬ CertificateMonitorReady key budget (record.cache, next))) }
  else { state.2 with stopped := true }

noncomputable def certificateLengthImpl (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule) :
    QueryImpl (OracleWorld + SigningSpec) (StateT CertificateMonitorState PMF) :=
  originalLengthImpl key (fun state => state.2.spent) (certificateMonitorEnabled key budget)
    (certificateMonitorUpdate key budget required stopAfter)

noncomputable def certificateProposalImpl (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule) :
    QueryImpl (OracleWorld + SigningSpec) (StateT (List Index × CertificateMonitorState) PMF) :=
  originalProposalImpl key (fun state => state.2.spent) (certificateMonitorEnabled key budget)
    (certificateMonitorUpdate key budget required stopAfter)

noncomputable def certificateMonitorPotential (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (state : CertificateMonitorState) : ENNReal :=
  bankedTargetEnvelope key nearUniformDigestReuseWeight (budget - state.2.spent)
    (signatureLimit - state.2.log.length) required (certificateMonitorCoverState state) state.2.bank state.2.stopped

noncomputable def certificateMonitorCharge (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (input : (OracleWorld + SigningSpec).Domain)
    (state : CertificateMonitorState) : ENNReal :=
  if CertificateMonitorActive key budget input state then
    targetCreationMultiplier key state.1 input * targetCreationPrice key nearUniformDigestReuseWeight
      (budget - state.2.spent) (signatureLimit - state.2.log.length) required (certificateMonitorCoverState state)
  else 0

noncomputable def certificateMonitorMass (key : SecretKey) (budget : Nat)
    (input : (OracleWorld + SigningSpec).Domain) (state : CertificateMonitorState) : ENNReal :=
  if CertificateMonitorActive key budget input state then targetCreationMultiplier key state.1 input else 0

def initialCertificateMonitor (spent : Nat) (stopped : Bool := false) : CertificateMonitor :=
  { log := []
    spent := spent
    messageCalls := 0
    proposals := 0
    creationMass := 0
    creationCost := 0
    bank := fun _ => false
    stopped := stopped }

theorem certificateMonitorUpdate_creationCost (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain) (state : CertificateMonitorState)
    (length : Nat) (record : ProposalExecutionRecord input) :
    (certificateMonitorUpdate key budget required stopAfter input state length record).creationCost =
      state.2.creationCost + certificateMonitorCharge key budget required input state := by
  by_cases hactive : CertificateMonitorActive key budget input state <;>
    simp only [certificateMonitorUpdate, certificateMonitorCharge, hactive, if_true, if_false, add_zero]

theorem certificateMonitorUpdate_creationMass (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain) (state : CertificateMonitorState)
    (length : Nat) (record : ProposalExecutionRecord input) :
    (certificateMonitorUpdate key budget required stopAfter input state length record).creationMass =
      state.2.creationMass + certificateMonitorMass key budget input state := by
  by_cases hactive : CertificateMonitorActive key budget input state <;>
    simp only [certificateMonitorUpdate, certificateMonitorMass, hactive, if_true, if_false, add_zero]

theorem certificateMonitorPotential_initial (key : SecretKey) (budget spent : Nat)
    (required : Finset FtsTree) (cache : QueryCache HashSpec) (stopped : Bool)
    (hnone : ∀ input, FtsProbeSimulation.MessageHashInput key.parameter input → cache input = none) :
    certificateMonitorPotential key budget required (cache, initialCertificateMonitor spent stopped) = 0 := by
  cases stopped with
  | false => exact bankedTargetEnvelope_initial key _ _ _ required _ hnone
  | true => simp only [certificateMonitorPotential, initialCertificateMonitor, bankedTargetEnvelope_stopped, certificateBankCount_empty]

theorem certificateMonitorUpdate_inactive (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain) (state : CertificateMonitorState)
    (length : Nat) (record : ProposalExecutionRecord input)
    (hactive : ¬ CertificateMonitorActive key budget input state) :
    certificateMonitorUpdate key budget required stopAfter input state length record = { state.2 with stopped := true } := by
  rw [certificateMonitorUpdate, if_neg hactive]

theorem certificateMonitorUpdate_spent (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain) (state : CertificateMonitorState)
    (length : Nat) (record : ProposalExecutionRecord input)
    (hactive : CertificateMonitorActive key budget input state) :
    (certificateMonitorUpdate key budget required stopAfter input state length record).spent =
      state.2.spent + record.trace.hashCalls := by
  simp only [certificateMonitorUpdate, if_pos hactive]

theorem certificateMonitorUpdate_messageCalls (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain) (state : CertificateMonitorState)
    (length : Nat) (record : ProposalExecutionRecord input)
    (hactive : CertificateMonitorActive key budget input state) :
    (certificateMonitorUpdate key budget required stopAfter input state length record).messageCalls =
      state.2.messageCalls + record.trace.messageCalls.length := by
  simp only [certificateMonitorUpdate, if_pos hactive]

theorem certificateMonitorPotential_advance_active (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain) (state : CertificateMonitorState)
    (length : Nat) (record : ProposalExecutionRecord input)
    (hactive : CertificateMonitorActive key budget input state) :
    certificateMonitorPotential key budget required
      (originalProposalAdvance (certificateMonitorUpdate key budget required stopAfter) input state length record) =
      bankedProposalRecordValue key nearUniformDigestReuseWeight (budget - state.2.spent)
        (signatureLimit - (state.2.log ++ signingLogFragment input record.output).length)
        required (certificateMonitorCoverState state) state.2.bank input record
        (certificateMonitorUpdate key budget required stopAfter input state length record).stopped := by
  simp only [certificateMonitorPotential, originalProposalAdvance, certificateMonitorUpdate, if_pos hactive,
    bankedProposalRecordValue, proposalRecordLogState, certificateMonitorCoverState, Nat.sub_sub]

theorem certificateMonitorPotential_advance_inactive (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain) (state : CertificateMonitorState)
    (length : Nat) (record : ProposalExecutionRecord input)
    (hactive : ¬ CertificateMonitorActive key budget input state) :
    certificateMonitorPotential key budget required
      (originalProposalAdvance (certificateMonitorUpdate key budget required stopAfter) input state length record) =
      certificateBankCount state.2.bank := by
  simp only [certificateMonitorPotential, originalProposalAdvance, certificateMonitorUpdate_inactive key budget
    required stopAfter input state length record hactive, bankedTargetEnvelope_stopped]

theorem certificateMonitor_sign_proposals_active (key : SecretKey) (budget : Nat)
    (message : Message) (state : CertificateMonitorState) :
    originalProposalActive key (fun state : CertificateMonitorState => state.2.spent)
      (certificateMonitorEnabled key budget) (.inr message) state =
        decide (CertificateMonitorActive key budget (.inr message) state) := by
  by_cases hactive : CertificateMonitorActive key budget (.inr message) state
  · simp only [originalProposalActive, certificateMonitorEnabled, hactive, decide_true,
      hactive.2.1.2.1, Bool.true_and]
  · simp only [originalProposalActive, certificateMonitorEnabled, hactive, decide_false, Bool.false_and]

theorem certificateLengthImpl_world_run (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule) (input : OracleWorld.Domain)
    (state : CertificateMonitorState) :
    (certificateLengthImpl key budget required stopAfter (.inl input)).run state =
      (originalProposalRecord key (.inl input) state.1).map (fun record =>
        (record.output, originalProposalAdvance (certificateMonitorUpdate key budget required stopAfter)
          (.inl input) state 0 record)) := by
  simp only [certificateLengthImpl, originalLengthImpl, lengthRecordImpl, originalProposalActive,
    StateT.run_mk, Bool.false_eq_true, if_false]

theorem certificateLengthImpl_sign_run (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule) (message : Message)
    (state : CertificateMonitorState) :
    (certificateLengthImpl key budget required stopAfter (.inr message)).run state =
      if CertificateMonitorActive key budget (.inr message) state then
        (recordLengthBridge (originalProposalRecord key (.inr message) state.1)
          targetProposalAcceptance targetProposalAcceptance_ne_zero targetProposalAcceptance_lt_one.le).map
            (fun result => (result.2.output, originalProposalAdvance (certificateMonitorUpdate key budget required stopAfter)
              (.inr message) state result.1 result.2))
      else (originalProposalRecord key (.inr message) state.1).map (fun record =>
        (record.output, originalProposalAdvance (certificateMonitorUpdate key budget required stopAfter)
          (.inr message) state 0 record)) := by
  simp only [certificateLengthImpl, originalLengthImpl, lengthRecordImpl, StateT.run_mk,
    certificateMonitor_sign_proposals_active, decide_eq_true_eq]

theorem certificateLengthImpl_inactive_run (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain) (state : CertificateMonitorState)
    (hactive : ¬ CertificateMonitorActive key budget input state) :
    (certificateLengthImpl key budget required stopAfter input).run state =
      (originalProposalRecord key input state.1).map (fun record =>
        (record.output, (record.cache, { state.2 with stopped := true }))) := by
  cases input with
  | inl world =>
      simp only [certificateLengthImpl_world_run, originalProposalAdvance,
        certificateMonitorUpdate_inactive key budget required stopAfter (.inl world) state 0 _ hactive]
  | inr message =>
      simp only [certificateLengthImpl_sign_run, if_neg hactive, originalProposalAdvance,
        certificateMonitorUpdate_inactive key budget required stopAfter (.inr message) state 0 _ hactive]

theorem simulateQ_certificateProposalImpl_length {α : Type} (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : List Index × CertificateMonitorState) :
    Prod.map id Prod.snd <$> (simulateQ (certificateProposalImpl key budget required stopAfter) computation).run state =
      (simulateQ (certificateLengthImpl key budget required stopAfter) computation).run state.2 :=
  simulateQ_originalProposalImpl_length _ _ _ _ _ _

end SphincsSecurity.Concrete
