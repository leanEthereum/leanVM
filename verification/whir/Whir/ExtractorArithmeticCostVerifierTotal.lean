import Whir.ExtractorArithmeticCostVerifierBounds

namespace Whir.ExtractorArithmeticCost
open Concrete Protocol CausalGame CountedCandidateCheck AuthenticatedResetSupport

private theorem countedChecked_bound {S : Type*} (step : Nat → S → Except String S × Nat)
    (P : S → Prop) (bound count start : Nat)
    (valid : ∀ i, start ≤ i → i < start + count → ∀ s, P s →
      (∀ after, (step i s).1 = .ok after → P after) ∧ (step i s).2 ≤ bound)
    (s : S) (hs : P s) :
    (∀ after, (countedChecked step count start s).1 = .ok after → P after) ∧
      (countedChecked step count start s).2 ≤ count * bound := by
  induction count generalizing start s with
  | zero =>
    refine ⟨?_, by simp [countedChecked]⟩
    intro after h
    have equal : s = after := Except.ok.inj h
    simpa [← equal] using hs
  | succ count ih =>
    have current := valid start le_rfl (by omega) s hs
    cases h : (step start s).1 with
    | error error =>
      simp only [countedChecked, h]
      refine ⟨by intro after h; contradiction, ?_⟩
      rw [Nat.succ_mul]
      omega
    | ok after =>
      have tail := ih (start + 1)
        (by intro i lower upper s hs; exact valid i (by omega) (by omega) s hs)
        after (current.1 after h)
      simp only [countedChecked, h]
      refine ⟨tail.1, ?_⟩
      rw [Nat.succ_mul]
      omega

def verifierPolynomial (levels dimension folds oods queries tail : Nat) : Nat :=
  levels * levelPolynomial dimension folds oods queries +
    tail * (3 * 2 ^ dimension + 6) + 5 * 2 ^ dimension + 1

theorem countedVerify_bound (c : Config) (ch : Challenges) (lanes : Nat) (root : Oracle)
    (weight : Array E) (target : E) (proof : Opening)
    (dimension folds oods queries tail : Nat)
    (input : ChallengeInput c ch dimension folds oods queries tail)
    (weightBound : weight.size ≤ 2 ^ dimension) :
    (countedVerify c ch lanes root weight target proof).2 ≤
      verifierPolynomial c.folds.size dimension folds oods queries tail := by
  unfold countedVerify
  cases initialized : initializeVerifier c ch lanes root weight target proof with
  | error error => exact Nat.zero_le _
  | ok initial =>
    have initialBound : StateBound dimension initial := by
      have shape := (CausalExecution.initialize_success _ _ _ _ _ _ _ _ initialized).2.2
      rw [shape]
      exact ⟨input.dimensionBound, weightBound⟩
    have levels := countedChecked_bound (countedVerifyLevel c ch proof) (StateBound dimension)
      (levelPolynomial dimension folds oods queries) c.folds.size 0
      (by
        intro i _ hi state valid
        exact countedVerifyLevel_bound c ch proof
          dimension folds oods queries tail i input (by omega) state valid)
      initial initialBound
    cases replayed : (countedChecked (countedVerifyLevel c ch proof) c.folds.size 0 initial).1 with
    | error error =>
      dsimp only
      simp only [replayed]
      unfold verifierPolynomial
      omega
    | ok final =>
      have finalBound := levels.1 final replayed
      have close := countedSteps_bound
        (fun j state => (tailStep ch proof j state, foldCharge state.weight))
        (fun state : VerifierState E => state.weight.size ≤ 2 ^ dimension)
        (3 * 2 ^ dimension + 6)
        (by
          intro j state valid
          dsimp [tailStep, VerifierState.fold]
          simp only [foldValues]
          split <;> simp only [ArrayLayout.size_foldLow, ArrayLayout.size_foldLane] <;> omega)
        (by intro j state valid; dsimp [foldCharge]; omega)
        ch.tail.size 0 (final.state, 0) finalBound.2
      have tailCost : (countedCloseTail ch proof final.state).2 ≤
          tail * (3 * 2 ^ dimension + 6) := by
        have localCost : (countedCloseTail ch proof final.state).2 ≤
            ch.tail.size * (3 * 2 ^ dimension + 6) := by
          simpa [countedCloseTail] using close.2
        exact localCost.trans (Nat.mul_le_mul_right _ input.tailLoops)
      have tableBound : 2 ^ ch.tail.size ≤ 2 ^ dimension :=
        Nat.pow_le_pow_right (by decide) input.tailDimension
      have dotBound : min proof.residual.size (2 ^ ch.tail.size) ≤ 2 ^ dimension :=
        (Nat.min_le_right _ _).trans tableBound
      dsimp only
      simp only [replayed]
      unfold verifierPolynomial tableCharge
      omega

private theorem batch_weight (width : Nat) (claims : Array Claim) (lambda : E) :
    (batchClaims width claims lambda).weight.size = width := by
  unfold batchClaims
  simp only [Array.forIn_pure_yield_eq_foldl, pure_bind]
  rw [← Array.foldl_toList]
  have h : ∀ (xs : List Claim) (s : Claim × E),
      (xs.foldl (fun state claim =>
        (⟨weightGlue state.1.weight claim.weight state.2,
          state.1.value + state.2 * claim.value⟩, state.2 * lambda)) s).1.weight.size =
          s.1.weight.size := by
    intro xs
    induction xs with
    | nil => intro s; rfl
    | cons x xs ih =>
      intro s
      simpa [List.foldl_cons, ArrayAlgebra.size_weightGlue] using
        (ih (⟨weightGlue s.1.weight x.weight s.2, s.1.value + s.2 * x.value⟩, s.2 * lambda))
  simpa [ArrayLayout.size_tab] using
    (h claims.toList (⟨tab width fun _ => E.zero, E.zero⟩, E.one))

def trialPolynomial (claims levels dimension folds oods queries tail : Nat) : Nat :=
  claims * (2 * 2 ^ dimension + 3) +
    verifierPolynomial levels dimension folds oods queries tail

theorem countedAcceptedReplies_bound (input : Public) (tape : Tape input.config)
    (answers : List Reply) (dimension folds oods queries tail : Nat)
    (consumer : ChallengeInput input.config (challenges input.config tape)
      dimension folds oods queries tail) :
    (countedAcceptedReplies input tape answers).2 ≤
      trialPolynomial input.claims.size input.config.folds.size dimension folds oods queries tail := by
  have widthBound : 2 ^ input.config.logN ≤ 2 ^ dimension :=
    Nat.pow_le_pow_right (by decide) consumer.dimensionBound
  unfold countedAcceptedReplies
  dsimp only
  split
  · exact Nat.zero_le _
  · try dsimp only
    cases parsed : opening input.config (challenges input.config tape) answers.toArray with
    | error error =>
      dsimp [countedBatchClaims]
      unfold trialPolynomial
      nlinarith
    | ok proof =>
      have verified := countedVerify_bound input.config (challenges input.config tape) input.lanes
        (liftRoot input.root) (batchClaims (2 ^ input.config.logN) input.claims tape.1).weight
        (batchClaims (2 ^ input.config.logN) input.claims tape.1).value proof
        dimension folds oods queries tail consumer (by rw [batch_weight]; exact widthBound)
      dsimp [countedBatchClaims]
      unfold trialPolynomial
      nlinarith

end Whir.ExtractorArithmeticCost
