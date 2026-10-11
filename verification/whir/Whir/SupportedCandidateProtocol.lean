import Whir.InitialKnowledgeSchedule
import Whir.AcceptedShapes
import Whir.SupportedCandidateCancellation

/-! Initial Root0 production knowledge certificate, with actual causal fold
exclusions instead of an abstract safe-schedule hypothesis. -/
namespace Whir.SupportedCandidateProtocol
open Concrete Protocol CausalGame CausalExecution CausalProbability ExecutionShapes
open CandidateFolding SupportedCandidateExtraction ParameterBounds InitialKnowledgeSchedule

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
attribute [local irreducible] ParameterBounds.config

abbrev initialLevel (p : Profile) : Fin (config p).folds.size :=
  ⟨0, (production_config_valid p).2.1⟩

/-- A large folded agreement set places the GIVEN whole Root1 coefficient
target in the Root0 postfold list. The Root1 target is not a compact message. -/
theorem target_member_of_agreement (p : Profile) (lanes : Nat) (root : BaseOracle)
    (claims : Array Claim) (strategy : Strategy) (t : Tape (config p))
    (valid : oracleValid (liftRoot root) (length (config p) 0) lanes = true)
    (laneBound : lanes ≤ 2 ^ (config p).folds[0]!)
    (target : Array E) (size : target.size = 2 ^ remaining (config p) 0)
    (H : Finset (Fin (length (config p) 0))) (enough : threshold (config p) 0 ≤ H.card)
    (agree : ∀ q ∈ H,
      (encode (remaining (config p) 0) (config p).rates[0]! target)[q.val]! =
      QueryBatchSoundness.oldWord (remaining (config p) 0) (config p).rates[0]!
        (liftRoot root) true (challenges (config p) t).levels[0]!.folds q) :
    target ∈ foldCandidates (Input p lanes root claims) strategy t 0 (config p).folds[0]! := by
  unfold foldCandidates
  change target ∈ arrayCandidates true (concreteEncoder (remaining (config p) 0) (config p).rates[0]!)
    (OracleReplay.oracleAt true (config p).folds[0]! (liftRoot root)
      (challenges (config p) t).levels[0]!.folds (config p).folds[0]!) (threshold (config p) 0)
  rw [AcceptedShapes.terminal_candidates true (config p).folds[0]! (remaining (config p) 0)
    (config p).rates[0]! (threshold (config p) 0) (liftRoot root) (challenges (config p) t).levels[0]!.folds
    (CausalStateCausality.challenge_folds_size (config p) t (initialLevel p))
    (by intro q; exact (OracleReplay.oracleValid_row _ _ _ valid q.val q.isLt).le.trans laneBound)]
  apply (arrayCandidates_mem_iff _ _ _ _ _).mpr
  refine ⟨by simpa using size, H, enough, ?_⟩
  intro lane q hq
  have zero : lane = 0 := Subsingleton.elim _ _
  subst lane
  have unpacked : Array.ofFn (unpack true 1 (2 ^ remaining (config p) 0) target 0) = target := by
    apply Array.ext
    · simpa using size.symm
    · intro j hj hj'
      simp [unpack, topIndex, getElem!_pos, hj']
  rw [ConcreteCandidates.concreteEncoder_ofFn, unpacked]
  exact agree q hq

/-- Literal initial K witness, SAME folded target, and every original public
claim. The committed root shape is an actual verifier initialization guard. -/
theorem initial_same_target (p : Profile) (lanes : Nat) (root : BaseOracle)
    (claims : Array Claim) (strategy : Strategy) (t : Tape (config p))
    (valid : oracleValid (liftRoot root) (length (config p) 0) lanes = true)
    (laneBound : lanes ≤ 2 ^ (config p).folds[0]!)
    (mca : ∀ j : Fin (config p).folds[0]!,
      ¬ RawMCA (Input p lanes root claims) strategy (initialLevel p) j t)
    (guard : ∀ j : Fin (config p).folds[0]!,
      ¬ ClaimEscape (Input p lanes root claims) strategy (initialLevel p) j t)
    (batchSafe : t.1 ∉ InitialBatching.candidateEscape
      (InitialCandidates.extensionCandidates (config p) lanes root) claims)
    (target : Array E)
    (member : target ∈ foldCandidates (Input p lanes root claims) strategy t 0 (config p).folds[0]!)
    (truth : dot target (CausalBoundary.boundary (Input p lanes root claims) strategy t (initialLevel p)).state.weight =
      (CausalBoundary.boundary (Input p lanes root claims) strategy t (initialLevel p)).state.claim) :
    ∃ w : Witness (config p) lanes,
      KnowledgeExtraction.Explains (Input p lanes root claims) w ∧
      foldFrom (Input p lanes root claims) t 0 0 (config p).folds[0]!
        (paddedWitness (config p) lanes w) = target := by
  obtain ⟨original, ho, hf, hc⟩ := InitialKnowledgeSchedule.same_target_lifts p lanes root claims strategy t
    (initialLevel p) 0 (config p).folds[0]! (by change 0 + (config p).folds[0]! ≤ (config p).folds[0]!; omega)
    (by intro j _ _; exact mca j) (by intro j _ _; exact guard j) target
    (by simpa only [initialLevel, Nat.zero_add] using member)
    (by simpa only [initialLevel, Nat.zero_add, CausalBoundary.boundary] using truth)
  rw [AcceptedShapes.initial_candidates p lanes root claims strategy t valid] at ho
  have reconstruct := InitialCandidates.production_reconstruction p lanes root laneBound original ho
  have originalSize : original.size = 2 ^ (config p).logN := by
    rw [reconstruct]
    simp [paddedWitness]
  refine ⟨InitialCandidates.project (config p) lanes original, ⟨?_, ?_⟩, ?_⟩
  · exact Finset.mem_image.mpr ⟨original, ho, rfl⟩
  · rw [← reconstruct]
    apply all_claims_of_safe_batch _ claims t.1 original ho batchSafe
    rw [originalSize]
    simpa only [initialLevel, foldAt_zero, levelAt_zero, initial] using hc
  · simpa only [← reconstruct] using hf

/-- The actual accepted execution supplies both initialization premises; its
pending-message table is not used as a candidate coefficient table. -/
theorem accepted_initial_same_target (p : Profile) (lanes : Nat) (root : BaseOracle)
    (claims : Array Claim) (strategy : Strategy) (t : Tape (config p))
    (accepted : experiment (Input p lanes root claims) strategy t = true)
    (mca : ∀ j : Fin (config p).folds[0]!,
      ¬ RawMCA (Input p lanes root claims) strategy (initialLevel p) j t)
    (guard : ∀ j : Fin (config p).folds[0]!,
      ¬ ClaimEscape (Input p lanes root claims) strategy (initialLevel p) j t)
    (batchSafe : t.1 ∉ InitialBatching.candidateEscape
      (InitialCandidates.extensionCandidates (config p) lanes root) claims)
    (target : Array E)
    (member : target ∈ foldCandidates (Input p lanes root claims) strategy t 0 (config p).folds[0]!)
    (truth : dot target (CausalBoundary.boundary (Input p lanes root claims) strategy t (initialLevel p)).state.weight =
      (CausalBoundary.boundary (Input p lanes root claims) strategy t (initialLevel p)).state.claim) :
    ∃ w : Witness (config p) lanes,
      KnowledgeExtraction.Explains (Input p lanes root claims) w ∧
      foldFrom (Input p lanes root claims) t 0 0 (config p).folds[0]!
        (paddedWitness (config p) lanes w) = target :=
  initial_same_target p lanes root claims strategy t
    (by simpa only [initialLevel, levelAt_zero, initial, beq_self_eq_true, ↓reduceIte] using
      AcceptedShapes.accepted_oracle p lanes root claims strategy t accepted (initialLevel p))
    (AcceptedShapes.accepted_lane_bound _ _ _ accepted) mca guard batchSafe target member truth

/-- Cancellation forces every full padded encoded lane at a fixed coordinate,
including occupied K leaves and zero padding. -/
theorem rowMatches_of_folded_equality (input : Public)
    (seed : Fin input.config.folds[0]! → E)
    (safe : ¬ initialRowCancellation input seed)
    (w : Witness input.config input.lanes)
    (member : w ∈ InitialCandidates.witnesses input.config input.lanes input.root)
    (q : Fin (blockLength input.config))
    (shape : input.root[q.val]!.size = input.lanes)
    (equal : Concrete.mle (committedRow input q) (Array.ofFn seed) =
      Concrete.mle (witnessRow input w q) (Array.ofFn seed)) :
    rowMatches input.config input.lanes (encodedLanes input.config (paddedWitness input.config input.lanes w))
      (q, input.root[q.val]!) = true := by
  have rows := rowEquality_of_not_cancellation input.config.folds[0]!
    (InitialCandidates.witnesses input.config input.lanes input.root)
    (committedRow input) (witnessRow input) seed safe w member q equal
  simp only [rowMatches, Bool.and_eq_true, beq_iff_eq, shape, true_and]
  apply List.all_eq_true.mpr
  intro lane _
  apply beq_iff_eq.mpr
  have entry := congrArg (fun row => row[lane.val]!) rows
  simpa [committedRow, witnessRow, encodedLanes, InitialCandidates.fullRow,
    recordLane, getElem!_pos, lane.isLt] using entry.symm

#print axioms initial_same_target
#print axioms accepted_initial_same_target
#print axioms rowMatches_of_folded_equality
end Whir.SupportedCandidateProtocol
