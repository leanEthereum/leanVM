import Whir.ExtractorArithmeticCostVerifier

namespace Whir.ExtractorArithmeticCost
open Concrete Protocol CausalGame CountedCandidateCheck AuthenticatedResetSupport

/-- Strict challenge consumer restrictions. These are imposed before running any trial, and apply to rejected as well as accepted replies. Public tapes from production configurations have exactly these finite dimensions. -/
structure ChallengeInput (c : Config) (ch : Challenges) (dimension folds oods queries tail : Nat) : Prop where
  dimensionBound : c.logN ≤ dimension
  noWrap : dimension ≤ 64
  foldDimensions : ∀ i < c.folds.size, ch.levels[i]!.folds.size ≤ dimension
  foldLoops : ∀ i < c.folds.size, ch.levels[i]!.folds.size ≤ folds
  oodLoops : ∀ i < c.folds.size, ch.levels[i]!.oodPoints.size ≤ oods
  oodDimensions : ∀ i < c.folds.size, ∀ point ∈ ch.levels[i]!.oodPoints.toList, point.size ≤ dimension
  queryLoops : ∀ i < c.folds.size, c.queries[i]! ≤ queries
  tailDimension : ch.tail.size ≤ dimension
  tailLoops : ch.tail.size ≤ tail

def StateBound (dimension : Nat) (s : CheckedState) : Prop :=
  s.n ≤ dimension ∧ s.state.weight.size ≤ 2 ^ dimension

theorem countedSteps_bound {S : Type*} (step : Nat → S → S × Nat) (P : S → Prop)
    (bound : Nat) (preserve : ∀ i s, P s → P (step i s).1)
    (charge : ∀ i s, P s → (step i s).2 ≤ bound)
    (count start : Nat) (s : S × Nat) (valid : P s.1) :
    P (countedSteps step count start s).1 ∧
      (countedSteps step count start s).2 ≤ s.2 + count * bound := by
  induction count generalizing start s with
  | zero => exact ⟨valid, by simp [countedSteps]⟩
  | succ count ih =>
    obtain ⟨hp, hc⟩ := ih (start + 1) ((step start s.1).1, s.2 + (step start s.1).2)
      (preserve _ _ valid)
    refine ⟨hp, ?_⟩
    have hs := charge start s.1 valid
    simp only [countedSteps]
    simp only [Nat.succ_mul]
    omega

private theorem fold_preserves (block : Nat) (cs : LevelChallenges) (p : LevelProof)
    (dimension i : Nat) (s : CheckedState) (h : StateBound dimension s) :
    StateBound dimension (foldStep block cs p i s) := by
  obtain ⟨hn, hw⟩ := h
  dsimp [StateBound, foldStep, VerifierState.fold]
  constructor
  · omega
  · simp only [foldValues]
    split <;> simp only [ArrayLayout.size_foldLow, ArrayLayout.size_foldLane] <;> omega

theorem countedFoldBlock_bound (block : Nat) (cs : LevelChallenges) (p : LevelProof)
    (dimension : Nat) (s : CheckedState) (valid : StateBound dimension s) :
    StateBound dimension (countedFoldBlock block cs p s).1 ∧
      (countedFoldBlock block cs p s).2 ≤ cs.folds.size * (3 * 2 ^ dimension + 6) := by
  have h := countedSteps_bound
    (fun j state => (foldStep block cs p j state, foldCharge state.state.weight))
    (StateBound dimension) (3 * 2 ^ dimension + 6)
    (fun i s hs => fold_preserves block cs p dimension i s hs)
    (by intro i s hs; dsimp [foldCharge]; have hw := hs.2; omega)
    cs.folds.size 0 (s, 0) valid
  simpa [countedFoldBlock] using h

private theorem default_point_bound (cs : LevelChallenges) (dimension : Nat)
    (points : ∀ point ∈ cs.oodPoints.toList, point.size ≤ dimension) (j : Nat) :
    cs.oodPoints[j]!.size ≤ dimension := by
  by_cases h : j < cs.oodPoints.size
  · apply points
    simp only [getElem!_pos, h]
    exact Array.getElem_mem_toList h
  · rw [getElem!_neg cs.oodPoints j h]
    change 0 ≤ dimension
    omega

theorem countedOodBatch_bound (cs : LevelChallenges) (p : LevelProof)
    (dimension : Nat) (s : VerifierState E) (weight : s.weight.size ≤ 2 ^ dimension)
    (points : ∀ point ∈ cs.oodPoints.toList, point.size ≤ dimension) :
    (countedOodBatch cs p s).1.1.weight.size ≤ 2 ^ dimension ∧
      (countedOodBatch cs p s).2 ≤ p.oods.size * (5 * 2 ^ dimension + 7) := by
  have h := countedSteps_bound
    (fun j state => (oodStep cs p j state,
      tableCharge cs.oodPoints[j]! + 2 * state.1.weight.size + 7))
    (fun state : VerifierState E × E => state.1.weight.size ≤ 2 ^ dimension)
    (5 * 2 ^ dimension + 7)
    (by intro i state hs; simpa [oodStep, VerifierState.batch, ArrayAlgebra.size_weightGlue] using hs)
    (by
      intro i state hs
      dsimp [tableCharge]
      have hd := default_point_bound cs dimension points i
      have hp : 2 ^ cs.oodPoints[i]!.size ≤ 2 ^ dimension :=
        Nat.pow_le_pow_right (by decide) hd
      omega)
    p.oods.size 0 ((s, E.one), 0) weight
  simpa [countedOodBatch] using h

theorem columnCharge_bound (dimension n : Nat) (noWrap : dimension ≤ 64) (hn : n ≤ dimension) :
    columnCharge n ≤ 16576 + 3 * 2 ^ dimension := by
  have hp : 2 ^ n ≤ 2 ^ dimension := Nat.pow_le_pow_right (by decide) hn
  have small : n ≤ 64 := hn.trans noWrap
  dsimp [columnCharge]
  nlinarith

private theorem derived_size (depth count : Nat) (squeezes : Array E) (qs : Array Nat)
    (success : deriveQueries depth count squeezes = some qs) : qs.size = count := by
  unfold deriveQueries at success
  split at success <;> simp_all
  rw [← success.2]
  simp [ArrayLayout.size_tab]

theorem queryCharge_bound (dimension n : Nat) (cs : LevelChallenges) (p : LevelProof)
    (qs : Array Nat) (s : VerifierState E × E) (noWrap : dimension ≤ 64)
    (nBound : n ≤ dimension) (folds : cs.folds.size ≤ dimension)
    (weight : s.1.weight.size ≤ 2 ^ dimension) (rows : p.rows.size = qs.size) :
    queryCharge n cs p qs s ≤ (qs.size + 1) * (16586 + 12 * 2 ^ dimension) := by
  have column := columnCharge_bound dimension n noWrap nBound
  have hp : 2 ^ n ≤ 2 ^ dimension := Nat.pow_le_pow_right (by decide) nBound
  have hf : 2 ^ cs.folds.size ≤ 2 ^ dimension := Nat.pow_le_pow_right (by decide) folds
  have induced : qs.size * (columnCharge n + 2 * 2 ^ n) ≤
      qs.size * (16576 + 5 * 2 ^ dimension) :=
    Nat.mul_le_mul_left _ (by omega)
  have enforced : qs.size * (2 * 2 ^ cs.folds.size + 2) ≤ qs.size * (2 * 2 ^ dimension + 2) :=
    Nat.mul_le_mul_left _ (by omega)
  have table : 2 ^ cs.folds.size - 1 ≤ 2 ^ dimension := by omega
  dsimp [queryCharge, tableCharge]
  rw [rows]
  nlinarith

/-- Explicit per-level polynomial in actual challenge loop dimensions and the dense physical input width. -/
def levelPolynomial (dimension folds oods queries : Nat) : Nat :=
  folds * (3 * 2 ^ dimension + 6) + oods * (5 * 2 ^ dimension + 7) +
    (queries + 1) * (16586 + 12 * 2 ^ dimension)

theorem countedVerifyLevel_bound (c : Config) (ch : Challenges) (proof : Opening)
    (dimension folds oods queries tail i : Nat)
    (input : ChallengeInput c ch dimension folds oods queries tail)
    (hi : i < c.folds.size) (s : CheckedState) (valid : StateBound dimension s) :
    (∀ after, (countedVerifyLevel c ch proof i s).1 = .ok after → StateBound dimension after) ∧
      (countedVerifyLevel c ch proof i s).2 ≤ levelPolynomial dimension folds oods queries := by
  have fold := countedFoldBlock_bound
    (if i == 0 then 2 ^ (c.logN - c.folds[0]!) else 1) ch.levels[i]! proof.levels[i]! dimension s valid
  have foldCost : (countedFoldBlock
      (if i == 0 then 2 ^ (c.logN - c.folds[0]!) else 1) ch.levels[i]! proof.levels[i]! s).2 ≤
      folds * (3 * 2 ^ dimension + 6) :=
    fold.2.trans (Nat.mul_le_mul_right _ (input.foldLoops i hi))
  unfold countedVerifyLevel
  dsimp only
  split
  · exact ⟨by intro after h; contradiction, Nat.zero_le _⟩
  · rename_i lengths
    have equalLengths : proof.levels[i]!.afterFold.size = ch.levels[i]!.folds.size ∧
        proof.levels[i]!.oods.size = ch.levels[i]!.oodPoints.size := by
      simpa only [Bool.or_eq_true, bne_iff_ne, not_or, not_not] using lengths
    have oodsEqual := equalLengths.2
    split
    · exact ⟨by intro after h; contradiction, by unfold levelPolynomial; omega⟩
    · try dsimp only
      split
      · exact ⟨by intro after h; contradiction, by unfold levelPolynomial; omega⟩
      · rename_i qs derived
        have querySize := derived_size _ _ _ qs derived
        split
        · exact ⟨by intro after h; contradiction, by unfold levelPolynomial; omega⟩
        · rename_i rowSize
          have rowSize : proof.levels[i]!.rows.size = qs.size := by simpa using rowSize
          split
          · exact ⟨by intro after h; contradiction, by unfold levelPolynomial; omega⟩
          · have ood := countedOodBatch_bound ch.levels[i]! proof.levels[i]! dimension
              (countedFoldBlock (if i == 0 then 2 ^ (c.logN - c.folds[0]!) else 1)
                ch.levels[i]! proof.levels[i]! s).1.state fold.1.2 (input.oodDimensions i hi)
            have oodCost := ood.2.trans (Nat.mul_le_mul_right _
              (oodsEqual.trans_le (input.oodLoops i hi)))
            have query := queryCharge_bound dimension _ ch.levels[i]! proof.levels[i]! qs
              (countedOodBatch ch.levels[i]! proof.levels[i]!
                (countedFoldBlock (if i == 0 then 2 ^ (c.logN - c.folds[0]!) else 1)
                  ch.levels[i]! proof.levels[i]! s).1.state).1
              input.noWrap fold.1.1 (input.foldDimensions i hi) ood.1 rowSize
            have queryCost := query.trans (Nat.mul_le_mul_right _
              (Nat.add_le_add_right (querySize.trans_le (input.queryLoops i hi)) 1))
            constructor
            · intro after success
              have equal := Except.ok.inj success
              subst after
              refine ⟨fold.1.1, ?_⟩
              simpa [countedQueryBatch, queryBatch, VerifierState.batch,
                ArrayAlgebra.size_weightGlue] using ood.1
            · dsimp [countedQueryBatch]
              unfold levelPolynomial
              omega

end Whir.ExtractorArithmeticCost
