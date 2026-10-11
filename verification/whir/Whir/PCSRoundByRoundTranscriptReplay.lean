import Whir.PCSRoundByRoundEnvelope
import Whir.CausalStrategy
import Whir.InitialKnowledgeSchedule

/-! Public replies reproduce a causal execution without retaining the prover
strategy. Full-proof extensionality below is only a bridge to truncation; the
public state uses strictly prior reply slots and observed challenge coordinates. -/
namespace Whir.PCSRoundByRoundTranscriptState
open Concrete Protocol CausalGame CausalProbability CausalExecution CausalRefinement
open CausalStrategy CausalPositions

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option autoImplicit false

def replies (input : Public) (strategy : Strategy) (t : Tape input.config) : Array Reply :=
  (run strategy input [] (visibleBatches input.config t.1 (challenges input.config t))).toArray

theorem replay_run (input : Public) (strategy : Strategy) (batches : List Batch) :
    run (indexedStrategy (run strategy input [] batches).toArray) input [] batches =
      run strategy input [] batches := by
  apply List.ext_getElem! (by simp only [run_length])
  intro i
  by_cases bound : i < batches.length
  · rw [indexed_response _ input [] batches i bound]
    simp only [List.length_nil, Nat.zero_add, List.getElem!_toArray]
  · simp [getElem!_neg, run_length, bound]

theorem proof_replay (input : Public) (strategy : Strategy) (t : Tape input.config) :
    proof input (indexedStrategy (replies input strategy t)) t = proof input strategy t := by
  unfold proof CausalTerminal.proof replies
  rw [replay_run]

theorem initial_proof_congr (input : Public) (left right : Strategy) (t : Tape input.config)
    (same : proof input left t = proof input right t) : initial input left t = initial input right t := by
  unfold initial
  rw [same]

theorem level_proof_congr (input : Public) (left right : Strategy) (t : Tape input.config)
    (same : proof input left t = proof input right t) (i : Nat) :
    levelAt input left t i = levelAt input right t i := by
  unfold levelAt
  rw [same, initial_proof_congr input left right t same]

theorem fold_proof_congr (input : Public) (left right : Strategy) (t : Tape input.config)
    (same : proof input left t = proof input right t) (i j : Nat) :
    foldAt input left t i j = foldAt input right t i j := by
  unfold foldAt
  rw [same, level_proof_congr input left right t same]

theorem candidates_proof_congr (input : Public) (left right : Strategy) (t : Tape input.config)
    (same : proof input left t = proof input right t) (i j : Nat) :
    foldCandidates input left t i j = foldCandidates input right t i j := by
  unfold foldCandidates
  rw [level_proof_congr input left right t same]

theorem following_proof_congr (input : Public) (left right : Strategy) (t : Tape input.config)
    (same : proof input left t = proof input right t) (i : Nat) :
    followingCandidates input left t i = followingCandidates input right t i := by
  unfold followingCandidates
  rw [same]

theorem boundary_proof_congr (input : Public) (left right : Strategy) (t : Tape input.config)
    (same : proof input left t = proof input right t) (i : Nat) :
    CausalBoundary.boundary input left t i = CausalBoundary.boundary input right t i := by
  exact fold_proof_congr input left right t same i _

theorem terminal_before_proof_congr (input : Public) (left right : Strategy) (t : Tape input.config)
    (same : proof input left t = proof input right t) :
    CausalTerminal.before input left t = CausalTerminal.before input right t := by
  unfold CausalTerminal.before CausalTerminal.beforeChecked
  have terminalSame : CausalTerminal.proof input left t = CausalTerminal.proof input right t := same
  rw [terminalSame]

theorem core_proof_congr (input : Public) (left right : Strategy) (t : Tape input.config)
    (same : proof input left t = proof input right t) (q : Coordinate input.config) :
    PCSRoundByRoundEnvelope.core input left q t ↔ PCSRoundByRoundEnvelope.core input right q t := by
  unfold PCSRoundByRoundEnvelope.core WHIRFiatShamir.Envelope
  cases q with
  | initial => simp only [CausalBadEvents.Bad, set_get]
  | fold i j =>
    simp only [CausalBadEvents.Bad, set_get]
    unfold CausalFolds.Event
    rw [candidates_proof_congr input left right t same,
      candidates_proof_congr input left right t same,
      fold_proof_congr input left right t same,
      fold_proof_congr input left right t same]
  | ood i j =>
    simp only [CausalBadEvents.Bad, set_get]
    unfold CausalBoundary.OodEvent
    rw [following_proof_congr input left right t same]
  | query i =>
    dsimp only
    unfold WHIRFiatShamir.QueryEnvelope CausalBoundary.QueryPrior
    dsimp only
    simp only [same, level_proof_congr input left right t same,
      boundary_proof_congr input left right t same,
      following_proof_congr input left right t same]
  | tail j =>
    simp only [CausalBadEvents.Bad, set_get]
    unfold CausalTerminal.candidate CausalTerminal.pending
    have terminalSame : CausalTerminal.proof input left t = CausalTerminal.proof input right t := same
    rw [terminalSame, terminal_before_proof_congr input left right t same]

theorem core_indexed_congr (input : Public) (left right : Array Reply)
    (q : Coordinate input.config) (t : Tape input.config)
    (same : ∀ n, n < position q → left[n]! = right[n]!) :
    PCSRoundByRoundEnvelope.core input (indexedStrategy left) q t ↔
      PCSRoundByRoundEnvelope.core input (indexedStrategy right) q t :=
  Iff.of_eq (congrFun (envelope_indexed_eq input left right q t same) (get q t))

theorem rawMCA_proof_congr (input : Public) (left right : Strategy) (t : Tape input.config)
    (same : proof input left t = proof input right t) (i : Fin input.config.folds.size)
    (j : Fin input.config.folds[i.val]!) :
    InitialKnowledgeSchedule.RawMCA input left i j t ↔
      InitialKnowledgeSchedule.RawMCA input right i j t := by
  unfold InitialKnowledgeSchedule.RawMCA InitialKnowledgeSchedule.paired
  rw [level_proof_congr input left right t same]

theorem claimEscape_proof_congr (input : Public) (left right : Strategy) (t : Tape input.config)
    (same : proof input left t = proof input right t) (i : Fin input.config.folds.size)
    (j : Fin input.config.folds[i.val]!) :
    InitialKnowledgeSchedule.ClaimEscape input left i j t ↔
      InitialKnowledgeSchedule.ClaimEscape input right i j t := by
  unfold InitialKnowledgeSchedule.ClaimEscape
  rw [candidates_proof_congr input left right t same,
    fold_proof_congr input left right t same]

theorem queryPolynomial_oods_congr (n rate count i : Nat) (root : Oracle)
    (cs : LevelChallenges) (left right : LevelProof) (s : VerifierState E)
    (tape : LevelBoundary.QueryTape (n + rate) count) (f : Array E)
    (same : left.oods = right.oods) :
    QueryBatchSoundness.polynomial n rate count i root cs left s tape f =
      QueryBatchSoundness.polynomial n rate count i root cs right s tape f := by
  let qs := QueryBatchSoundness.queries (n + rate) count tape
  let l : LevelProof := {left with rows := qs.map (fun q => root[q]!)}
  let r : LevelProof := {right with rows := qs.map (fun q => root[q]!)}
  have oods : BatchingRefinement.oodError f cs l = BatchingRefinement.oodError f cs r := by
    funext j
    simp only [BatchingRefinement.oodError, l, r, same]
  have queries : BatchingRefinement.queryError f n cs l qs (i == 0) =
      BatchingRefinement.queryError f n cs r qs (i == 0) := by
    funext j
    rfl
  unfold QueryBatchSoundness.polynomial BatchingRefinement.errorPolynomial
  dsimp only
  rw [congrArg Array.size same]
  exact congrArg₂ (fun ood query => BatchingRefinement.batchPolynomial right.oods.size qs.size
    (BatchingRefinement.discrepancy f s) ood query) oods queries

theorem rawMCA_indexed_congr (input : Public) (left right : Array Reply) (t : Tape input.config)
    (i : Fin input.config.folds.size) (j : Fin input.config.folds[i.val]!)
    (same : ∀ n, n < position (.fold i j) → left[n]! = right[n]!) :
    InitialKnowledgeSchedule.RawMCA input (indexedStrategy left) i j t ↔
      InitialKnowledgeSchedule.RawMCA input (indexedStrategy right) i j t := by
  have prior : ∀ n, n < levelStart (challenges input.config t) i.val → left[n]! = right[n]! := by
    intro n bound
    apply same n
    rw [position_fold i j t]
    omega
  unfold InitialKnowledgeSchedule.RawMCA InitialKnowledgeSchedule.paired
  rw [CausalStrategy.levelAt_eq input left right t i.val (Nat.le_of_lt i.isLt) prior]

theorem claimEscape_indexed_congr (input : Public) (left right : Array Reply) (t : Tape input.config)
    (i : Fin input.config.folds.size) (j : Fin input.config.folds[i.val]!)
    (same : ∀ n, n < position (.fold i j) → left[n]! = right[n]!) :
    InitialKnowledgeSchedule.ClaimEscape input (indexedStrategy left) i j t ↔
      InitialKnowledgeSchedule.ClaimEscape input (indexedStrategy right) i j t := by
  have prior : ∀ n, n < levelStart (challenges input.config t) i.val → left[n]! = right[n]! := by
    intro n bound
    apply same n
    rw [position_fold i j t]
    omega
  have foldPrior : ∀ n, n < levelStart (challenges input.config t) i.val + j.val →
      left[n]! = right[n]! := by
    intro n bound
    apply same n
    simpa only [position_fold i j t] using bound
  unfold InitialKnowledgeSchedule.ClaimEscape
  rw [CausalStrategy.foldCandidates_eq input left right t i j.val prior,
    CausalStrategy.foldAt_eq input left right t i j.val (Nat.le_of_lt j.isLt) foldPrior]

#print axioms replay_run
#print axioms proof_replay
#print axioms core_proof_congr
#print axioms core_indexed_congr
#print axioms rawMCA_proof_congr
#print axioms claimEscape_proof_congr
#print axioms queryPolynomial_oods_congr
#print axioms rawMCA_indexed_congr
#print axioms claimEscape_indexed_congr
end Whir.PCSRoundByRoundTranscriptState
