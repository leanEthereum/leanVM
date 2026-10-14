import Whir.PCSRoundByRoundKnowledgeQuery
import Whir.PCSRoundByRoundCancellation
import Whir.PCSRoundByRoundEnvelope

/-! Strict incoming-history envelopes for the actual additive characteristic-two
events. Current query replies cannot toggle the state. The six-fold row
cancellation is localized at its first collapsing scalar. -/
namespace Whir.PCSRoundByRoundKnowledge
open Concrete Protocol CausalGame CausalExecution CausalProbability ExecutionShapes
open ParameterBounds SupportedCandidateProtocol RewindBatchTarget InitialKnowledgeSchedule
open PCSRewindExtractor (heavyQueryLoss)
open SupportedCandidateExtraction (blockLength)
open Classical

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
attribute [local irreducible] ParameterBounds.config
attribute [local irreducible] RawMCA ClaimEscape PCSRoundByRoundEnvelope.core

private theorem uniform_false {A : Type} [Fintype A] :
    Soundness.uniformProb (Finset.univ.filter fun _ : A => False) = 0 := by
  have empty : (Finset.univ.filter fun _ : A => False) = ∅ :=
    Finset.filter_eq_empty_iff.mpr (by intro x hx impossible; exact impossible)
  rw [empty]
  simp only [Soundness.uniformProb, Finset.card_empty, Nat.cast_zero, zero_div]


noncomputable def extraBad (p : Profile) (lanes : Nat) (root : BaseOracle)
    (claims : Array Claim) (strategy : Strategy) (q : Coordinate (config p))
    (t : Tape (config p)) : Prop :=
  match q with
  | .fold i j =>
    if h : i = initialLevel p then
      let j0 : Fin (config p).folds[0]! := ⟨j.val, by simpa only [h, initialLevel] using j.isLt⟩
      RawMCA (Input p lanes root claims) strategy (initialLevel p) j0 t ∨
        ClaimEscape (Input p lanes root claims) strategy (initialLevel p) j0 t ∨
        PCSRoundByRoundCancellation.Event p lanes root claims j0 t
    else False
  | .query i => i = initialLevel p ∧
      (CollisionEvent p lanes root claims strategy t ∨ LowSupportQuery p lanes root claims strategy t)
  | _ => False

noncomputable def roundBad (p : Profile) (lanes : Nat) (root : BaseOracle)
    (claims : Array Claim) (strategy : Strategy) (q : Coordinate (config p))
    (t : Tape (config p)) : Prop :=
  PCSRoundByRoundEnvelope.core (Input p lanes root claims) strategy q t ∨
    extraBad p lanes root claims strategy q t
attribute [local irreducible] extraBad roundBad


def extraLoss (p : Profile) (q : Coordinate (config p)) : ℚ :=
  match q with
  | .fold i _ => if i = initialLevel p then
      (2^108 : ℚ)/2^192 + (2^33 : ℚ)/2^192 + (2^32 : ℚ)*blockLength (config p)/2^192
      else 0
  | .query i => if i = initialLevel p then
      (2^32 : ℚ) * ((oodCount (config p) 0 + (config p).queries[0]! : Nat)/2^192) + heavyQueryLoss p
      else 0
  | _ => 0

def epsilon (p : Profile) (lanes : Nat) (root : BaseOracle) (claims : Array Claim)
    (q : Coordinate (config p)) : ℚ :=
  CausalBadEvents.localError (Input p lanes root claims) q + extraLoss p q

open Classical in
theorem extraBad_fiber_bound (p : Profile) (lanes : Nat) (root : BaseOracle)
    (claims : Array Claim) (strategy : Strategy) (q : Coordinate (config p)) (t : Tape (config p)) :
    Soundness.uniformProb (Finset.univ.filter fun x : Sample q =>
      extraBad p lanes root claims strategy q (set q t x)) ≤ extraLoss p q := by
  cases q with
  | fold i j =>
    by_cases same : i = initialLevel p
    · subst i
      simp only [extraBad, extraLoss, dite_true, ite_true]
      apply (uniform_or_bound _ _ _ _
        (rawMCA_fiber_bound p lanes root claims strategy t (initialLevel p) j)
        (uniform_or_bound _ _ _ _
          (claimEscape_fiber_bound p lanes root claims strategy t (initialLevel p) j)
          (PCSRoundByRoundCancellation.fiber_bound p lanes root claims j t))).trans_eq
      ring
    · simp only [extraBad, extraLoss, same, dite_false, ite_false]
      rw [uniform_false]
  | query i =>
    by_cases same : i = initialLevel p
    · subst i
      simpa only [extraBad, extraLoss, true_and, ite_true] using
        uniform_or_bound _ _ _ _
          (collisionEvent_fiber_bound p lanes root claims strategy t)
          (lowSupportQuery_fiber_bound p lanes root claims strategy t)
    · simp only [extraBad, extraLoss, same, false_and, ite_false]
      rw [uniform_false]
  | initial =>
    simp only [extraBad, extraLoss]
    rw [uniform_false]
  | ood i j =>
    simp only [extraBad, extraLoss]
    rw [uniform_false]
  | tail j =>
    simp only [extraBad, extraLoss]
    rw [uniform_false]

open Classical in
/-- Exact local loss on every arbitrary fixed incoming execution history. -/
theorem roundBad_fiber_bound (p : Profile) (lanes : Nat) (root : BaseOracle)
    (claims : Array Claim) (strategy : Strategy)
    (laneBound : lanes ≤ 2 ^ (config p).folds[0]!)
    (shape : ∀ j : Fin claims.size, claims[j].weight.size = 2 ^ (config p).logN)
    (q : Coordinate (config p)) (t : Tape (config p)) :
    Soundness.uniformProb (Finset.univ.filter fun x : Sample q =>
      roundBad p lanes root claims strategy q (set q t x)) ≤ epsilon p lanes root claims q := by
  let A := Finset.univ.filter fun x : Sample q =>
    roundBad p lanes root claims strategy q (set q t x)
  let B := Finset.univ.filter fun x : Sample q =>
    PCSRoundByRoundEnvelope.core (Input p lanes root claims) strategy q (set q t x)
  let C := Finset.univ.filter fun x : Sample q =>
    extraBad p lanes root claims strategy q (set q t x)
  have cover : A ⊆ B ∪ C := by
    intro x member
    have event := (Finset.mem_filter.mp member).2
    unfold roundBad at event
    rcases event with core | extra
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, core⟩))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, extra⟩))
  have card : A.card ≤ B.card + C.card :=
    (Finset.card_le_card cover).trans (Finset.card_union_le B C)
  have unionBound : Soundness.uniformProb A ≤ Soundness.uniformProb B + Soundness.uniformProb C := by
    unfold Soundness.uniformProb
    rw [← add_div]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast card
  exact unionBound.trans (add_le_add
    (PCSRoundByRoundEnvelope.fiber_bound p lanes root claims laneBound shape strategy q t)
    (extraBad_fiber_bound p lanes root claims strategy q t))

theorem knowledgeBad_cover (p : Profile) (lanes : Nat) (root : BaseOracle)
    (claims : Array Claim) (strategy : Strategy) (t : Tape (config p))
    (bad : KnowledgeBad p lanes root claims strategy t) :
    ∃ q, roundBad p lanes root claims strategy q t := by
  unfold roundBad
  rcases bad with causal | folds | cancellation | collision
  · obtain ⟨q, event⟩ := causal
    exact ⟨q, Or.inl (PCSRoundByRoundEnvelope.bad_cover p lanes root claims strategy q t event)⟩
  · obtain ⟨j, event⟩ := folds
    refine ⟨.fold (initialLevel p) j, Or.inr ?_⟩
    simp only [extraBad, dite_true]
    rcases event with raw | claim
    · exact Or.inl raw
    · exact Or.inr (Or.inl claim)
  · obtain ⟨j, event⟩ := PCSRoundByRoundCancellation.cover p lanes root claims t cancellation
    exact ⟨.fold (initialLevel p) j, Or.inr (by simp only [extraBad, dite_true]; exact Or.inr (Or.inr event))⟩
  · refine ⟨.query (initialLevel p), Or.inr ?_⟩
    unfold extraBad
    exact ⟨rfl, Or.inl collision⟩

theorem lowSupport_cover (p : Profile) (lanes : Nat) (root : BaseOracle)
    (claims : Array Claim) (strategy : Strategy) (t : Tape (config p))
    (low : LowSupportQuery p lanes root claims strategy t) :
    roundBad p lanes root claims strategy (.query (initialLevel p)) t := by
  unfold roundBad extraBad
  exact Or.inr ⟨rfl, Or.inr low⟩

theorem collisionEvent_set_future (p : Profile) (lanes : Nat) (root : BaseOracle)
    (claims : Array Claim) (strategy : Strategy) (t : Tape (config p))
    (q : Coordinate (config p)) (x : Sample q)
    (later : position (.query (initialLevel p)) < position q) :
    CollisionEvent p lanes root claims strategy (set q t x) ↔
      CollisionEvent p lanes root claims strategy t := by
  have fixed := Root0FixedTarget.snapshot_set (Input p lanes root claims) strategy t
    (initialLevel p) q x later.le
  have list := congrArg (fun s => s.1) fixed
  have boundary := congrArg (fun s => s.2.1) fixed
  have oracle := congrArg (fun s => s.2.2.1) fixed
  have answers := congrArg (fun s => s.2.2.2.1) fixed
  have folds := congrArg (fun s => s.2.2.2.2.1) fixed
  have points := congrArg (fun s => s.2.2.2.2.2) fixed
  dsimp only [Root0FixedTarget.snapshot, initialLevel] at list boundary oracle answers folds points
  have draw := get_set_ne q (.query (initialLevel p)) t x (by
    intro same
    rw [same] at later
    exact lt_irrefl _ later)
  unfold CollisionEvent Collision QueryBatchSoundness.polynomial BatchingRefinement.errorPolynomial
    BatchingRefinement.oodError BatchingRefinement.queryError
  rw [draw, list, boundary, oracle, answers, folds, points]

theorem extraBad_set_future (p : Profile) (lanes : Nat) (root : BaseOracle)
    (claims : Array Claim) (strategy : Strategy) (r q : Coordinate (config p))
    (t : Tape (config p)) (x : Sample q) (later : position r < position q) :
    extraBad p lanes root claims strategy r (set q t x) ↔
      extraBad p lanes root claims strategy r t := by
  cases r with
  | fold i j =>
    by_cases same : i = initialLevel p
    · subst i
      have before : levelStart (challenges (config p) t) 0 + j.val + 1 ≤ position q := by
        rw [CausalPositions.position_fold _ _ t] at later
        exact later
      have guards := knowledgeEvents_set_future (Input p lanes root claims) strategy t
        (initialLevel p) j q x before
      simp only [extraBad, dite_true]
      rw [guards.1, guards.2, PCSRoundByRoundCancellation.future_invariant p lanes root claims j q t x later]
    · simp [extraBad, same]
  | query i =>
    by_cases same : i = initialLevel p
    · subst i
      simp only [extraBad, true_and]
      rw [collisionEvent_set_future p lanes root claims strategy t q x later,
        lowSupportQuery_set_future p lanes root claims strategy t q x later]
    · simp [extraBad, same]
  | initial => simp only [extraBad]
  | ood i j => simp only [extraBad]
  | tail j => simp only [extraBad]

/-- Every stored event is determined by the actual already completed causal
history, even for malformed strategies and arbitrary future challenge tapes. -/
theorem roundBad_set_future (p : Profile) (lanes : Nat) (root : BaseOracle)
    (claims : Array Claim) (strategy : Strategy) (r q : Coordinate (config p))
    (t : Tape (config p)) (x : Sample q) (later : position r < position q) :
    roundBad p lanes root claims strategy r (set q t x) ↔
      roundBad p lanes root claims strategy r t := by
  unfold roundBad
  rw [PCSRoundByRoundEnvelope.future_invariant p lanes root claims strategy r q t x later,
    extraBad_set_future p lanes root claims strategy r q t x later]

/-- A conservative uniform per-message envelope, derived only after the
conditional fibers have been proved. It is not the q56 extraction cutoff. -/
def rbrError : ℚ := SupportedCandidateExtraction.radiusEnvelope + 1 / 2^78

theorem extraLoss_le (p : Profile) (q : Coordinate (config p)) :
    extraLoss p q ≤ heavyQueryLoss p + 1 / 2^80 := by
  have hnonnegative : (0 : ℚ) ≤ heavyQueryLoss p := by
    unfold heavyQueryLoss
    positivity
  have cnonnegative : (0 : ℚ) ≤ (2^32 : ℚ) * blockLength (config p) / 2^192 := by positivity
  have bnonnegative : (0 : ℚ) ≤ (2^32 : ℚ) *
      ((oodCount (config p) 0 + (config p).queries[0]! : Nat) / 2^192) := by positivity
  have budget := production_extra_ledger p
  cases q with
  | fold i j =>
    by_cases same : i = initialLevel p
    · simp only [extraLoss, same, ite_true]
      linarith
    · simp only [extraLoss, same, ite_false]
      positivity
  | query i =>
    by_cases same : i = initialLevel p
    · simp only [extraLoss, same, ite_true]
      linarith
    · simp only [extraLoss, same, ite_false]
      positivity
  | initial => simp only [extraLoss]; positivity
  | ood i j => simp only [extraLoss]; positivity
  | tail j => simp only [extraLoss]; positivity

theorem epsilon_le_rbrError (p : Profile) (lanes : Nat) (root : BaseOracle)
    (claims : Array Claim) (cap : claims.size ≤ 2^64) (q : Coordinate (config p)) :
    epsilon p lanes root claims q ≤ rbrError := by
  have localBound := (CausalBadEvents.localError_le_groupedMaximum
    (Input p lanes root claims) q).trans (production_grouped p claims.size cap)
  have extra := extraLoss_le p q
  have heavy := PCSRewindExtractor.production_heavyQueryLoss p
  unfold epsilon rbrError
  linarith

#print axioms extraBad_fiber_bound
#print axioms roundBad_fiber_bound
#print axioms knowledgeBad_cover
#print axioms roundBad_set_future
#print axioms epsilon_le_rbrError

end Whir.PCSRoundByRoundKnowledge
