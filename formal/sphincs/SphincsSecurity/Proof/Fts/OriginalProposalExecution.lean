import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.ProposalQueryProjection
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable

private theorem probCompLift_map {α β : Type} (comp : ProbComp α) (f : α → β) :
    (liftM comp : PMF α).map f = (liftM (f <$> comp) : PMF β) :=
  (liftM_map (m := ProbComp) (n := PMF) _ _).symm

private theorem tracedSigningRun_output {ω : Type} [Monoid ω]
    (trace : (input : OracleWorld.Domain) → OracleWorld.Range input → ω)
    (key : SecretKey) (message : Message) (cache : QueryCache HashSpec) :
    (fun result : TracedSigningRecord ω => (result.1.1.1, result.2)) <$>
      tracedSigningRun trace key message cache = (simulateQ romImpl (sign key message)).run cache := by
  calc
    _ = (fun result => (result.1.1, result.2)) <$>
        ((fun result : TracedSigningRecord ω => (result.1.1, result.2)) <$>
          tracedSigningRun trace key message cache) := by simp only [Functor.map_map]
    _ = _ := by rw [tracedSigningRun_forget, simulateQ_signWithView_fst_run]

private theorem completedSigningRecord_output {ω : Type} [Monoid ω]
    (trace : (input : OracleWorld.Domain) → OracleWorld.Range input → ω)
    (key : SecretKey) (message : Message) (cache : QueryCache HashSpec) :
    (completedSigningRecord trace key message cache).map (fun result => (result.1.1.1.1, result.1.2)) =
      (liftM ((simulateQ romImpl (sign key message)).run cache) : PMF _) := by
  calc
    _ = ((completedSigningRecord trace key message cache).map Prod.fst).map
        (fun result : TracedSigningRecord ω => (result.1.1.1, result.2)) := (PMF.map_comp _ _ _).symm
    _ = _ := by rw [completedSigningRecord_forget, probCompLift_map, tracedSigningRun_output]

structure ProposalExecutionRecord (input : (OracleWorld + SigningSpec).Domain) where
  output : (OracleWorld + SigningSpec).Range input
  cache : QueryCache HashSpec
  trace : SigningBoundaryTrace
  selectedView : Option FewTimeView
  index : Index

noncomputable def originalProposalRecord (key : SecretKey) :
    (input : (OracleWorld + SigningSpec).Domain) → QueryCache HashSpec → PMF (ProposalExecutionRecord input)
  | .inl world, cache =>
      (liftM ((romImpl world).run cache) : PMF _).map fun result =>
        ⟨result.1, result.2, signingBoundaryTrace key.parameter world result.1, none, 0⟩
  | .inr message, cache =>
      (completedSigningRecord (signingBoundaryTrace key.parameter) key message cache).map fun result =>
        ⟨result.1.1.1.1, result.1.2, result.1.1.2, result.1.1.1.2, result.2⟩

noncomputable def originalAdversaryPMFImpl (key : SecretKey) :
    QueryImpl (OracleWorld + SigningSpec) (StateT (QueryCache HashSpec) PMF) :=
  pmfSumImpl romImpl (fun message => simulateQ romImpl (sign key message))

theorem originalAdversaryImpl_split (key : SecretKey) :
    (romImpl + (fun message => simulateQ romImpl (sign key message))) = unloggedMappedAdversaryImpl key := by
  funext input
  cases input with
  | inl world => rfl
  | inr message =>
      change simulateQ romImpl (sign key message) = simulateQ romImpl (scheme.sign key message)
      have hsign : scheme.sign = sign := rfl
      rw [hsign]

theorem simulateQ_originalAdversaryPMFImpl {α : Type} (key : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (cache : QueryCache HashSpec) :
    (simulateQ (originalAdversaryPMFImpl key) computation).run cache =
      (liftM ((simulateQ (unloggedMappedAdversaryImpl key) computation).run cache) : PMF _) := by
  rw [originalAdversaryPMFImpl, pmfSumImpl_eq_lift_add, simulateQ_liftProbCompImpl_run,
    originalAdversaryImpl_split]

theorem originalProposalRecord_project (key : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain) (cache : QueryCache HashSpec) :
    (originalProposalRecord key input cache).map (fun result => (result.output, result.cache)) =
      (originalAdversaryPMFImpl key input).run cache := by
  cases input with
  | inl world =>
      rw [originalAdversaryPMFImpl, pmfSumImpl_inl, originalProposalRecord, PMF.map_comp]
      exact PMF.map_id _
  | inr message =>
      rw [originalAdversaryPMFImpl, pmfSumImpl_inr, originalProposalRecord, PMF.map_comp]
      exact completedSigningRecord_output (signingBoundaryTrace key.parameter) key message cache

theorem originalProposalRecord_index (key : SecretKey) (message : Message) (cache : QueryCache HashSpec) :
    (originalProposalRecord key (.inr message) cache).map (fun result => result.index) =
      (completedSigningRecord (signingBoundaryTrace key.parameter) key message cache).map Prod.snd := by
  rw [originalProposalRecord, PMF.map_comp]
  rfl

theorem originalProposalRecord_cap (key : SecretKey) (message : Message) (cache : QueryCache HashSpec)
    (spent : Nat) (hbound : ProposalCacheBound key cache spent) (index : Index) :
    targetProposalAcceptance *
      ((originalProposalRecord key (.inr message) cache).map (fun result => result.index)) index ≤
      PMF.uniformOfFintype Index index := by
  rw [originalProposalRecord_index]
  exact completedSigningRecord_acceptance_cap (signingBoundaryTrace key.parameter) key message cache spent hbound index

noncomputable def originalProposalActive {μ : Type} (key : SecretKey)
    (spent : QueryCache HashSpec × μ → Nat) (enabled : Message → QueryCache HashSpec × μ → Bool) :
    (OracleWorld + SigningSpec).Domain → QueryCache HashSpec × μ → Bool
  | .inl _, _ => false
  | .inr message, state => enabled message state && decide (ProposalCacheBound key state.1 (spent state))

noncomputable def originalRejectedProposal {μ : Type} (key : SecretKey)
    (spent : QueryCache HashSpec × μ → Nat) :
    (OracleWorld + SigningSpec).Domain → QueryCache HashSpec × μ → PMF Index
  | .inl _, _ => PMF.uniformOfFintype Index
  | .inr message, state =>
      if hbound : ProposalCacheBound key state.1 (spent state) then
        proposalResidualLaw (PMF.uniformOfFintype Index)
          ((originalProposalRecord key (.inr message) state.1).map (fun result => result.index))
          targetProposalAcceptance targetProposalAcceptance_lt_one
          (originalProposalRecord_cap key message state.1 (spent state) hbound)
      else PMF.uniformOfFintype Index

def originalProposalAdvance {μ : Type}
    (update : (input : (OracleWorld + SigningSpec).Domain) → QueryCache HashSpec × μ →
      Nat → ProposalExecutionRecord input → μ)
    (input : (OracleWorld + SigningSpec).Domain) (state : QueryCache HashSpec × μ)
    (length : Nat) (record : ProposalExecutionRecord input) : QueryCache HashSpec × μ :=
  (record.cache, update input state length record)

noncomputable def originalProposalImpl {μ : Type} (key : SecretKey)
    (spent : QueryCache HashSpec × μ → Nat) (enabled : Message → QueryCache HashSpec × μ → Bool)
    (update : (input : (OracleWorld + SigningSpec).Domain) → QueryCache HashSpec × μ →
      Nat → ProposalExecutionRecord input → μ) :
    QueryImpl (OracleWorld + SigningSpec) (StateT (List Index × (QueryCache HashSpec × μ)) PMF) :=
  proposalRecordImpl (fun input state => originalProposalRecord key input state.1)
    (fun _ record => record.output) (originalProposalAdvance update) (fun _ record => record.index)
    (originalRejectedProposal key spent) (originalProposalActive key spent enabled)
    targetProposalAcceptance targetProposalAcceptance_ne_zero targetProposalAcceptance_lt_one.le

noncomputable def originalLengthImpl {μ : Type} (key : SecretKey)
    (spent : QueryCache HashSpec × μ → Nat) (enabled : Message → QueryCache HashSpec × μ → Bool)
    (update : (input : (OracleWorld + SigningSpec).Domain) → QueryCache HashSpec × μ →
      Nat → ProposalExecutionRecord input → μ) :
    QueryImpl (OracleWorld + SigningSpec) (StateT (QueryCache HashSpec × μ) PMF) :=
  lengthRecordImpl (fun input state => originalProposalRecord key input state.1)
    (fun _ record => record.output) (originalProposalAdvance update) (originalProposalActive key spent enabled)
    targetProposalAcceptance targetProposalAcceptance_ne_zero targetProposalAcceptance_lt_one.le

theorem simulateQ_originalProposalImpl_length {μ α : Type} (key : SecretKey)
    (spent : QueryCache HashSpec × μ → Nat) (enabled : Message → QueryCache HashSpec × μ → Bool)
    (update : (input : (OracleWorld + SigningSpec).Domain) → QueryCache HashSpec × μ →
      Nat → ProposalExecutionRecord input → μ)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : List Index × (QueryCache HashSpec × μ)) :
    Prod.map id Prod.snd <$> (simulateQ (originalProposalImpl key spent enabled update) computation).run state =
      (simulateQ (originalLengthImpl key spent enabled update) computation).run state.2 :=
  simulateQ_proposalRecordImpl_project _ _ _ _ _ _ _ _ _ computation state

theorem simulateQ_originalLengthImpl_forget {μ α : Type} (key : SecretKey)
    (spent : QueryCache HashSpec × μ → Nat) (enabled : Message → QueryCache HashSpec × μ → Bool)
    (update : (input : (OracleWorld + SigningSpec).Domain) → QueryCache HashSpec × μ →
      Nat → ProposalExecutionRecord input → μ)
    (computation : OracleComp (OracleWorld + SigningSpec) α) (state : QueryCache HashSpec × μ) :
    Prod.map id Prod.fst <$> (simulateQ (originalLengthImpl key spent enabled update) computation).run state =
      (simulateQ (originalAdversaryPMFImpl key) computation).run state.1 := by
  apply simulateQ_lengthRecordImpl_project
    (fun input state => originalProposalRecord key input state.1)
    (fun _ record => record.output) (originalProposalAdvance update) (originalProposalActive key spent enabled)
    targetProposalAcceptance targetProposalAcceptance_ne_zero targetProposalAcceptance_lt_one.le
    (originalAdversaryPMFImpl key) Prod.fst (fun _ _ record => record.cache)
  · intros
    rfl
  · intro input state
    exact originalProposalRecord_project key input state.1

theorem simulateQ_originalProposalImpl_forget {μ α : Type} (key : SecretKey)
    (spent : QueryCache HashSpec × μ → Nat) (enabled : Message → QueryCache HashSpec × μ → Bool)
    (update : (input : (OracleWorld + SigningSpec).Domain) → QueryCache HashSpec × μ →
      Nat → ProposalExecutionRecord input → μ)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : List Index × (QueryCache HashSpec × μ)) :
    (fun result => (result.1, result.2.2.1)) <$>
      (simulateQ (originalProposalImpl key spent enabled update) computation).run state =
      (simulateQ (originalAdversaryPMFImpl key) computation).run state.2.1 := by
  calc
    _ = Prod.map id Prod.fst <$>
        (Prod.map id Prod.snd <$>
          (simulateQ (originalProposalImpl key spent enabled update) computation).run state) := by
      simp only [Functor.map_map]
      rfl
    _ = _ := by rw [simulateQ_originalProposalImpl_length, simulateQ_originalLengthImpl_forget]

theorem simulateQ_originalProposalImpl_original {μ α : Type} (key : SecretKey)
    (spent : QueryCache HashSpec × μ → Nat) (enabled : Message → QueryCache HashSpec × μ → Bool)
    (update : (input : (OracleWorld + SigningSpec).Domain) → QueryCache HashSpec × μ →
      Nat → ProposalExecutionRecord input → μ)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (state : List Index × (QueryCache HashSpec × μ)) :
    (fun result => (result.1, result.2.2.1)) <$>
      (simulateQ (originalProposalImpl key spent enabled update) computation).run state =
      (liftM ((simulateQ (unloggedMappedAdversaryImpl key) computation).run state.2.1) : PMF _) := by
  rw [simulateQ_originalProposalImpl_forget, simulateQ_originalAdversaryPMFImpl]

end SphincsSecurity.Concrete
