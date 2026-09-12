import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.BankedProposalStep
import SphincsSecurity.Proof.Reference.DirectQueryBudget
import SphincsSecurity.Proof.Reference.SigningBoundaryHashCost
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem probCompLift_support {α : Type} (computation : ProbComp α) :
    (liftM computation : PMF α).support = support computation := by
  ext value
  rw [PMF.mem_support_iff, ← PMF.probOutput_eq_apply, mem_support_iff]
  rfl

theorem originalProposalRecord_boundary (key : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain) (cache : QueryCache HashSpec) :
    (originalProposalRecord key input cache).map (fun record => ((record.output, record.trace), record.cache)) =
      (liftM (boundaryRun key.parameter (expandedAdversaryImpl key input) cache) : PMF _) := by
  cases input with
  | inl world =>
      simp only [originalProposalRecord, PMF.map_comp, expandedAdversaryImpl]
      rw [boundaryRun_query]
      exact (liftM_map (m := ProbComp) (n := PMF) _ _).symm
  | inr message =>
      rw [originalProposalRecord, PMF.map_comp]
      calc
        _ = ((completedSigningRecord (signingBoundaryTrace key.parameter) key message cache).map Prod.fst).map
            signingRecordResponse := (PMF.map_comp _ _ _).symm
        _ = _ := by
          rw [completedSigningRecord_forget, ← PMF.monad_map_eq_map,
            ← liftM_map (m := ProbComp) (n := PMF), tracedSigningRun_signature]
          rfl

theorem originalProposalRecord_boundary_support (key : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain) (cache : QueryCache HashSpec)
    (record : ProposalExecutionRecord input) (hr : record ∈ (originalProposalRecord key input cache).support) :
    ((record.output, record.trace), record.cache) ∈
      support (boundaryRun key.parameter (expandedAdversaryImpl key input) cache) := by
  have hm := (PMF.mem_support_map_iff
    (fun record : ProposalExecutionRecord input => ((record.output, record.trace), record.cache))
    (originalProposalRecord key input cache) _).mpr ⟨record, hr, rfl⟩
  rwa [originalProposalRecord_boundary, probCompLift_support] at hm

theorem originalProposalRecord_query_bound {α : Type} (key : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) α)
    (q : Nat)
    (hbound : (simulateQ (expandedAdversaryImpl key) (OracleSpec.query input >>= next)).IsQueryBoundP (· matches .inr _) q)
    (cache : QueryCache HashSpec) (record : ProposalExecutionRecord input)
    (hr : record ∈ (originalProposalRecord key input cache).support) :
    record.trace.hashCalls ≤ q ∧
      (simulateQ (expandedAdversaryImpl key) (next record.output)).IsQueryBoundP (· matches .inr _)
        (q - record.trace.hashCalls) := by
  rw [simulateQ_bind, simulateQ_spec_query] at hbound
  exact boundaryRun_bind_query_bound key.parameter (expandedAdversaryImpl key input)
    (fun output => simulateQ (expandedAdversaryImpl key) (next output)) q hbound cache _
    (originalProposalRecord_boundary_support key input cache record hr)

theorem originalProposalRecord_sign_hashCalls (key : SecretKey) (message : Message)
    (cache : QueryCache HashSpec) (record : ProposalExecutionRecord (.inr message))
    (hr : record ∈ (originalProposalRecord key (.inr message) cache).support) :
    28504 ≤ record.trace.hashCalls :=
  boundaryHashAtLeast_sign key.parameter key message cache _
    (originalProposalRecord_boundary_support key (.inr message) cache record hr)

theorem targetCreationMultiplier_le_record_hashCalls (key : SecretKey)
    (input : (OracleWorld + SigningSpec).Domain) (cache : QueryCache HashSpec)
    (record : ProposalExecutionRecord input) (hr : record ∈ (originalProposalRecord key input cache).support) :
    targetCreationMultiplier key cache input ≤ record.trace.hashCalls := by
  cases input with
  | inl world =>
      rw [originalProposalRecord_world_hashCalls key world cache record hr, targetCreationMultiplier]
      cases world with
      | inl sample => exact le_refl _
      | inr input =>
          simp only [freshWorldTargetHashCost, signingExecutionHashCost]
          split_ifs <;> norm_num
  | inr message =>
      have hmass := mul_le_mul' (le_refl (((2 ^ ftsTreeHeight : Nat) : ENNReal)))
        (freshDigestSelectionProbability_le_one key message cache)
      calc
        _ ≤ ((2 ^ ftsTreeHeight : Nat) : ENNReal) := by simpa only [targetCreationMultiplier, mul_one] using hmass
        _ ≤ (28504 : Nat) := by norm_num [ftsTreeHeight]
        _ ≤ record.trace.hashCalls := Nat.cast_le.mpr (originalProposalRecord_sign_hashCalls key message cache record hr)

end SphincsSecurity.Concrete
