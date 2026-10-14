import Whir.CausalBadEvents
import Whir.AcceptedShapes

/-! End-to-end list-loss propagation for the actual causal WHIR verifier.
The initial candidate list is chosen from the commitment before public claims,
and each charged event is one of the concretely proved prefix events. -/
namespace Whir.InteractiveSoundness
open Concrete Protocol CausalGame CausalExecution ExecutionShapes ParameterBounds VerifierInvariant

/-- The fixed base-field witness list initializes the actual pending-state invariant. -/
theorem initial_lost (p : Profile) (lanes : Nat) (root : BaseOracle) (claims : Array Claim)
    (strategy : Strategy) (tape : Tape (config p))
    (accepted : experiment (Input p lanes root claims) strategy tape = true)
    (hfalse : ¬ ∃ w ∈ InitialCandidates.witnesses (config p) lanes root,
      ∀ claim ∈ claims.toList, dot (paddedWitness (config p) lanes w) claim.weight = claim.value)
    (outside : ¬ CausalInitial.Event (Input p lanes root claims) tape) :
    Lost (foldCandidates (Input p lanes root claims) strategy tape 0 0)
      (levelAt (Input p lanes root claims) strategy tape 0).state := by
  have valid := AcceptedShapes.accepted_oracle p lanes root claims strategy tape accepted
    ⟨0, (production_config_valid p).2.1⟩
  have rootValid : oracleValid (liftRoot root) (length (config p) 0) lanes = true := by
    simpa [initial] using valid
  rw [AcceptedShapes.initial_candidates p lanes root claims strategy tape rootValid]
  exact InitialSoundness.batching_preserves_lost p lanes root
    (AcceptedShapes.accepted_lane_bound _ _ _ accepted) claims hfalse tape.1
    (proof (Input p lanes root claims) strategy tape).initial outside

/-- Avoiding every concrete fold restoration preserves loss throughout the whole actual fold block. -/
theorem folds_preserve_lost (p : Profile) (lanes : Nat) (root : BaseOracle) (claims : Array Claim)
    (strategy : Strategy) (tape : Tape (config p)) (i : Fin (config p).folds.size)
    (incoming : Lost (foldCandidates (Input p lanes root claims) strategy tape i 0)
      (levelAt (Input p lanes root claims) strategy tape i).state)
    (outside : ∀ j : Fin (config p).folds[i.val]!,
      ¬ CausalFolds.Event (Input p lanes root claims) strategy i j tape) :
    Lost (foldCandidates (Input p lanes root claims) strategy tape i (config p).folds[i.val]!)
      (foldAt (Input p lanes root claims) strategy tape i (config p).folds[i.val]!).state := by
  have each (j : Nat) (hj : j ≤ (config p).folds[i.val]!) :
      Lost (foldCandidates (Input p lanes root claims) strategy tape i j)
        (foldAt (Input p lanes root claims) strategy tape i j).state := by
    induction j with
    | zero => exact incoming
    | succ j ih =>
      apply Classical.byContradiction
      intro restored
      have index : j < (config p).folds[i.val]! := by omega
      apply outside ⟨j, index⟩
      refine ⟨?_, ih (by omega), restored⟩
      rw [(foldAt_shape p lanes root claims strategy tape i j index.le).2]
      simp only [dimension, Nat.pow_add, Nat.mul_comm]
  exact each _ le_rfl

/-- The actual authentication and boundary guards turn absence of the grouped query event into loss of the next list. -/
theorem query_preserves_lost (p : Profile) (lanes : Nat) (root : BaseOracle) (claims : Array Claim)
    (strategy : Strategy) (tape : Tape (config p))
    (accepted : experiment (Input p lanes root claims) strategy tape = true)
    (i : Fin (config p).folds.size)
    (incoming : Lost (foldCandidates (Input p lanes root claims) strategy tape i (config p).folds[i.val]!)
      (foldAt (Input p lanes root claims) strategy tape i (config p).folds[i.val]!).state)
    (oodOutside : ∀ j : Fin (oodCount (config p) i),
      ¬ CausalBoundary.OodEvent (Input p lanes root claims) strategy i j tape)
    (queryOutside : ¬ CausalBoundary.QueryEvent (Input p lanes root claims) strategy i tape) :
    Lost (followingCandidates (Input p lanes root claims) strategy tape i)
      (levelAt (Input p lanes root claims) strategy tape (i.val + 1)).state := by
  classical
  apply Classical.byContradiction
  intro restored
  have dims := foldAt_shape p lanes root claims strategy tape i (config p).folds[i.val]! le_rfl
  simp only [Nat.sub_self, Nat.add_zero] at dims
  have close := AcceptedShapes.closeLost_of_terminal_lost p lanes root claims strategy tape accepted i incoming
  have checked := accepted_level (Input p lanes root claims) strategy tape accepted i i.isLt
  have result := OperationalRefinement.verifyLevel_success _ _ _ i _ _ checked
  dsimp only at result
  have endEq := foldAt_end (Input p lanes root claims) strategy tape i i.isLt
  dsimp only [block] at endEq
  rw [← endEq] at result
  rw [dims.1, foldAt_oracle] at result
  obtain ⟨_, oodLength, qs, sampled, rows, auth, _⟩ := result
  apply queryOutside
  dsimp only [CausalBoundary.QueryEvent, CausalBoundary.boundary]
  rw [sampled]
  refine ⟨dims.1, dims.2, close, ?_, rows,
    (OperationalRefinement.authentication_ok_iff _ _ _).mpr auth, restored⟩
  split_ifs with hasNext
  · have positive := ((CausalBoundary.production_boundary_facts p i).2.2 hasNext).2
    let j : Fin (oodCount (config p) i) := ⟨0, positive⟩
    have separated := oodOutside j
    unfold CausalBoundary.OodEvent at separated
    have count := (TapeValidity.level_shapes (config p) tape i i.isLt).2.1
    exact ⟨0, by omega, not_not.mp separated⟩
  · have boundaryGuard := boundary_shape (config p) (challenges (config p) tape)
      (proof (Input p lanes root claims) strategy tape) i _ _ checked
    dsimp only at boundaryGuard
    rw [← foldAt_end (Input p lanes root claims) strategy tape i i.isLt, dims.1] at boundaryGuard
    have finalShape : (proof (Input p lanes root claims) strategy tape).levels[i.val]!.nextOracle = none ∧
        (proof (Input p lanes root claims) strategy tape).residual.size = 2 ^ remaining (config p) i := by
      simpa only [hasNext, ↓reduceIte] using boundaryGuard
    exact finalShape.2

/-- Every accepted opening contradicting the commitment-time list encounters an actual bad challenge prefix. -/
theorem accepted_false_cover (p : Profile) (lanes : Nat) (root : BaseOracle) (claims : Array Claim)
    (strategy : Strategy) (tape : Tape (config p))
    (accepted : experiment (Input p lanes root claims) strategy tape = true)
    (hfalse : ¬ ∃ w ∈ InitialCandidates.witnesses (config p) lanes root,
      ∀ claim ∈ claims.toList, dot (paddedWitness (config p) lanes w) claim.weight = claim.value) :
    ∃ q, CausalBadEvents.Bad (Input p lanes root claims) strategy q tape := by
  classical
  apply Classical.byContradiction
  intro noBad
  have safe (q) : ¬ CausalBadEvents.Bad (Input p lanes root claims) strategy q tape :=
    fun h => noBad ⟨q, h⟩
  have initialLoss := initial_lost p lanes root claims strategy tape accepted hfalse (safe .initial)
  have entering (i : Nat) (hi : i < (config p).folds.size) :
      Lost (foldCandidates (Input p lanes root claims) strategy tape i 0)
        (levelAt (Input p lanes root claims) strategy tape i).state := by
    induction i with
    | zero => exact initialLoss
    | succ i ih =>
      have previous : i < (config p).folds.size := by omega
      let index : Fin (config p).folds.size := ⟨i, previous⟩
      have folded := folds_preserve_lost p lanes root claims strategy tape index (ih previous)
        (fun j => safe (.fold index j))
      have queried := query_preserves_lost p lanes root claims strategy tape accepted index folded
        (fun j => safe (.ood index j)) (safe (.query index))
      rw [following_eq_next _ _ _ i hi] at queried
      exact queried
  have positive := (production_config_valid p).2.1
  let last : Fin (config p).folds.size := ⟨(config p).folds.size - 1, by omega⟩
  have lastEnd : last.val + 1 = (config p).folds.size := by dsimp [last]; omega
  have noNext : ¬ last.val + 1 < (config p).folds.size := by omega
  have folded := folds_preserve_lost p lanes root claims strategy tape last (entering last last.isLt)
    (fun j => safe (.fold last j))
  have queried := query_preserves_lost p lanes root claims strategy tape accepted last folded
    (fun j => safe (.ood last j)) (safe (.query last))
  have beforeState := (accepted_execution (Input p lanes root claims) strategy tape accepted).2.2
  have incoming : dot (proof (Input p lanes root claims) strategy tape).residual
      (CausalTerminal.before (Input p lanes root claims) strategy tape).weight ≠
        (CausalTerminal.before (Input p lanes root claims) strategy tape).claim := by
    have member : (proof (Input p lanes root claims) strategy tape).residual ∈
        followingCandidates (Input p lanes root claims) strategy tape last := by
      simp only [followingCandidates, noNext, ↓reduceIte, Finset.mem_singleton]
    have lost := queried _ member
    simpa only [lastEnd, beforeState] using lost
  have checked := accepted_level (Input p lanes root claims) strategy tape accepted last last.isLt
  have terminalShape := boundary_shape (config p) (challenges (config p) tape)
    (proof (Input p lanes root claims) strategy tape) last _ _ checked
  dsimp only at terminalShape
  rw [← foldAt_end (Input p lanes root claims) strategy tape last last.isLt] at terminalShape
  have dims := (foldAt_shape p lanes root claims strategy tape last (config p).folds[last.val]! le_rfl).1
  simp only [Nat.sub_self, Nat.add_zero] at dims
  rw [dims] at terminalShape
  have shapeLast : (proof (Input p lanes root claims) strategy tape).residual.size =
      2 ^ remaining (config p) last := by
    have pair : (proof (Input p lanes root claims) strategy tape).levels[last.val]!.nextOracle = none ∧
        (proof (Input p lanes root claims) strategy tape).residual.size = 2 ^ remaining (config p) last := by
      simpa only [noNext, ↓reduceIte] using terminalShape
    exact pair.2
  have remainingLast : remaining (config p) last = (config p).logN - (config p).folds.toList.sum := by
    unfold remaining
    rw [lastEnd, ← Array.length_toList, List.take_length]
  rw [remainingLast] at shapeLast
  have weight := (levelAt_shape p lanes root claims strategy tape (config p).folds.size le_rfl).2
  rw [beforeState] at weight
  simp only [before] at weight
  have takeAll : (config p).folds.toList.take (config p).folds.size = (config p).folds.toList := by
    rw [← Array.length_toList, List.take_length]
  rw [takeAll] at weight
  have weightShape : (CausalTerminal.before (Input p lanes root claims) strategy tape).weight.size =
      (proof (Input p lanes root claims) strategy tape).residual.size := weight.trans shapeLast.symm
  obtain ⟨j, escaped⟩ := CausalTerminal.event_has_collision (Input p lanes root claims) strategy tape
    ⟨accepted, shapeLast, weightShape, incoming⟩
  exact safe (.tail j) escaped

/-- Public claim shape is checked before any causal proof response is considered. -/
theorem accepted_claim_shapes (input : Public) (strategy : Strategy) (tape : Tape input.config)
    (accepted : experiment input strategy tape = true) :
    ∀ j : Fin input.claims.size, input.claims[j].weight.size = 2 ^ input.config.logN := by
  intro j
  have all := (CausalRefinement.experiment_iff input strategy tape).mp accepted |>.1
  rw [Array.all_eq_true] at all
  have valid := all j.val j.isLt
  simp only [shapeValid, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at valid
  exact valid.1.2

/-- The concrete conservative ledger is nonnegative, including rejected public inputs. -/
theorem error_nonneg (c : Config) (claims : Nat) :
    0 ≤ GroupedChallenges.interactiveError c (estimates c) claims := by
  unfold GroupedChallenges.interactiveError
  refine add_nonneg (add_nonneg ?_ (Finset.sum_nonneg fun i _ => ?_)) ?_
  · simp only [GroupedChallenges.initialBatch, estimates, GroupedChallenges.fieldSize]
    split_ifs <;> positivity
  · have field : (0 : ℚ) ≤ GroupedChallenges.fieldSize := by norm_num [GroupedChallenges.fieldSize]
    have fold : 0 ≤ GroupedChallenges.foldError c (estimates c) i := by
      norm_num [GroupedChallenges.foldError, estimates, GroupedChallenges.fieldSize]
    have ood : 0 ≤ GroupedChallenges.oodError c (estimates c) i := by
      unfold GroupedChallenges.oodError
      split_ifs
      · exact div_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
          (Nat.cast_nonneg _)) field
      · exact le_rfl
    have fraction : 0 ≤ (estimates c i).agreementFraction := by
      dsimp only [estimates, alpha, upper]
      apply mul_nonneg (by norm_num) (div_nonneg ?_ (by positivity))
      split_ifs <;> norm_num
    have query : 0 ≤ GroupedChallenges.queryBatchError c (estimates c) i := by
      unfold GroupedChallenges.queryBatchError
      apply add_nonneg (pow_nonneg fraction _)
      split_ifs
      · exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) field
      · exact div_nonneg (Nat.cast_nonneg _) field
    exact add_nonneg (add_nonneg (mul_nonneg (Nat.cast_nonneg _) fold) ood) query
  · dsimp only [GroupedChallenges.fieldSize]
    positivity

private theorem filtered_mono {Ω : Type*} [Fintype Ω] (P Q : Ω → Prop)
    [DecidablePred P] [DecidablePred Q] (h : ∀ ω, P ω → Q ω) :
    Soundness.uniformProb (Finset.univ.filter P) ≤ Soundness.uniformProb (Finset.univ.filter Q) := by
  have sub : Finset.univ.filter P ⊆ Finset.univ.filter Q := by
    intro ω hω
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h ω (Finset.mem_filter.mp hω).2⟩
  unfold Soundness.uniformProb
  exact div_le_div_of_nonneg_right (by exact_mod_cast Finset.card_le_card sub) (by positivity)

private theorem impossible_event {Ω : Type*} [Fintype Ω] (P : Ω → Prop)
    [DecidablePred P] (h : ∀ ω, ¬ P ω) :
    Soundness.uniformProb (Finset.univ.filter P) = 0 := by
  rw [Finset.filter_eq_empty_iff.mpr (fun ω _ => h ω)]
  simp [Soundness.uniformProb]

open Classical

/-- Concrete probability bound for arbitrary public claims and arbitrary causal proof strategies. -/
theorem opening_probability (p : Profile) (lanes : Nat) (root : BaseOracle)
    (claims : Array Claim) (strategy : Strategy) :
    Soundness.uniformProb (Finset.univ.filter fun tape : Tape (config p) =>
      experiment (Input p lanes root claims) strategy tape = true ∧
      ¬ ∃ w ∈ InitialCandidates.witnesses (config p) lanes root,
        ∀ claim ∈ claims.toList, dot (paddedWitness (config p) lanes w) claim.weight = claim.value) ≤
      GroupedChallenges.interactiveError (config p) (estimates (config p)) claims.size := by
  by_cases possible : ∃ tape, experiment (Input p lanes root claims) strategy tape = true
  · obtain ⟨tape, accepted⟩ := possible
    apply le_trans (filtered_mono _ _ fun t h =>
      accepted_false_cover p lanes root claims strategy t h.1 h.2)
    exact CausalBadEvents.bad_probability p lanes root claims strategy
      (AcceptedShapes.accepted_lane_bound _ _ _ accepted)
      (accepted_claim_shapes _ _ _ accepted)
  · rw [impossible_event _ (fun tape h => possible ⟨tape, h.1⟩)]
    exact error_nonneg _ _

/-- Full ideal-interactive adaptive list binding for every production size/rate profile.
The witness list is fixed before claims and strategy, and the quantified experiment
is the actual causal verifier, not a replacement arithmetic acceptance predicate. -/
theorem adaptive_list_binding (p : Profile) :
    AdaptiveListBinding (config p) (2 ^ 32)
      (GroupedChallenges.interactiveError (config p) (estimates (config p))) := by
  intro lanes root
  exact ⟨InitialCandidates.witnesses (config p) lanes root,
    InitialCandidates.production_witnesses_card p lanes root,
    fun claims strategy => opening_probability p lanes root claims strategy⟩

/-- An unground bound. This does not claim a grinding amplifier or 128-bit security. -/
theorem production_probability (p : Profile) (lanes : Nat) (root : BaseOracle)
    (claims : Array Claim) (strategy : Strategy) (claim_cap : claims.size ≤ 2 ^ 64) :
    Soundness.uniformProb (Finset.univ.filter fun tape : Tape (config p) =>
      experiment (Input p lanes root claims) strategy tape = true ∧
      ¬ ∃ w ∈ InitialCandidates.witnesses (config p) lanes root,
        ∀ claim ∈ claims.toList, dot (paddedWitness (config p) lanes w) claim.weight = claim.value) ≤
      (1 / 2 ^ 73 : ℚ) :=
  (opening_probability p lanes root claims strategy).trans
    (production_interactive p claims.size claim_cap)

end Whir.InteractiveSoundness
