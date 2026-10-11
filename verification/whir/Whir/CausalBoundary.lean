import Whir.CausalExecution
import Whir.CausalProbability
import Whir.QueryBatchSoundness
import Whir.ConcreteCandidates
import Whir.CausalPositions
import Whir.CausalStateCausality

namespace Whir.CausalBoundary
open Concrete Protocol CausalGame CausalExecution CausalProbability
open Classical
open scoped BigOperators

set_option maxRecDepth 4096
set_option maxHeartbeats 800000

/-- The list is fixed by the last fold response, not by an OOD answer. -/
def OodEvent (input : Public) (strategy : Strategy)
    (i : Fin input.config.folds.size) (j : Fin (oodCount input.config i))
    (tape : Tape input.config) : Prop :=
  ¬ LevelBoundary.Separated (followingCandidates input strategy tape i)
    (challenges input.config tape).levels[i.val]!.oodPoints[j.val]!

/-- The actual incoming state immediately after the complete fold block. -/
def boundary (input : Public) (strategy : Strategy) (tape : Tape input.config)
    (i : Nat) : CheckedState :=
  foldAt input strategy tape i input.config.folds[i]!

/-- All shape, separation, and authentication conditions are guards of this
prefix event. No acceptance test or future response occurs in the event. -/
def QueryEvent (input : Public) (strategy : Strategy)
    (i : Fin input.config.folds.size) (tape : Tape input.config) : Prop :=
  let c := input.config
  let cs := (challenges c tape).levels[i.val]!
  let p := (proof input strategy tape).levels[i.val]!
  let s := boundary input strategy tape i
  let n := remaining c i
  let qs := (deriveQueries (n + c.rates[i.val]!) c.queries[i.val]! cs.querySqueezes).getD #[]
  s.n = n ∧ s.state.weight.size = 2 ^ n ∧
  LevelBoundary.CloseLost n c.rates[i.val]! (ParameterBounds.threshold c i)
    (QueryBatchSoundness.oldWord n c.rates[i.val]!
      (levelAt input strategy tape i).oracle (i.val == 0) cs.folds) s.state ∧
  (if i.val + 1 < c.folds.size then
    ∃ j < p.oods.size, LevelBoundary.Separated (followingCandidates input strategy tape i)
      cs.oodPoints[j]!
   else (proof input strategy tape).residual.size = 2 ^ n) ∧
  p.rows.size = qs.size ∧
  runChecked (authenticateRow (levelAt input strategy tape i).oracle qs p) qs.size 0 () = .ok () ∧
  ¬ VerifierInvariant.Lost (followingCandidates input strategy tape i)
    (levelAt input strategy tape (i.val + 1)).state

set_option maxHeartbeats 0 in
/-- Arithmetic of the supported production ladder, including the genuine
zero-OOD last level and the next commitment's coefficient dimension. -/
theorem production_boundary_facts : ∀ p : ParameterBounds.Profile,
    ∀ i : Fin (ParameterBounds.config p).folds.size,
    0 < remaining (ParameterBounds.config p) i + (ParameterBounds.config p).rates[i.val]! ∧
    remaining (ParameterBounds.config p) i + (ParameterBounds.config p).rates[i.val]! ≤ 64 ∧
    (i.val + 1 < (ParameterBounds.config p).folds.size →
      remaining (ParameterBounds.config p) (i.val + 1) +
          (ParameterBounds.config p).folds[i.val + 1]! =
        remaining (ParameterBounds.config p) i ∧
      0 < oodCount (ParameterBounds.config p) i) := by
  decide +kernel

 theorem followingCandidates_card (input : Public) (strategy : Strategy)
    (tape : Tape input.config) (p : ParameterBounds.Profile)
    (hc : input.config = ParameterBounds.config p) (i : Fin input.config.folds.size) :
    (followingCandidates input strategy tape i).card ≤ 2 ^ 32 := by
  unfold followingCandidates
  split_ifs with hn
  · have cap := ConcreteCandidates.production_arrayCandidates_card false p
      ⟨i.val + 1, by simpa [← hc] using hn⟩
      (lanes := 2 ^ (input.config.folds[i.val + 1]! - 0))
    simp only [Fin.val_mk] at cap
    rw [← hc] at cap
    exact cap _
  · simp

 theorem followingCandidates_sizes (input : Public) (strategy : Strategy)
    (tape : Tape input.config) (p : ParameterBounds.Profile)
    (hc : input.config = ParameterBounds.config p) (i : Fin input.config.folds.size)
    (shape : ¬ i.val + 1 < input.config.folds.size →
      (proof input strategy tape).residual.size = 2 ^ remaining input.config i) :
    ∀ f ∈ followingCandidates input strategy tape i, f.size = 2 ^ remaining input.config i := by
  intro f hf
  unfold followingCandidates at hf
  split_ifs at hf with hn
  · have size := OracleReplay.candidate_size false input.config.folds[i.val + 1]!
      (remaining input.config (i.val + 1)) input.config.rates[i.val + 1]! 0
      (ParameterBounds.threshold input.config (i.val + 1))
      ((proof input strategy tape).levels[i.val]!.nextOracle.getD #[])
      (challenges input.config tape).levels[i.val + 1]!.folds f hf
    have dim := (production_boundary_facts p ⟨i.val, by simp [← hc]⟩).2.2
      (by simpa [← hc] using hn)
    have hd : remaining input.config (i.val + 1) + input.config.folds[i.val + 1]! =
        remaining input.config i := by simpa only [← hc] using dim.1
    simpa only [Nat.sub_zero, hd] using size
  · exact (congrArg Array.size (Finset.mem_singleton.mp hf)).trans (shape hn)

theorem decoded_oods_size (input : Public) (strategy : Strategy) (tape : Tape input.config)
    (i : Fin input.config.folds.size) :
    (proof input strategy tape).levels[i.val]!.oods.size = oodCount input.config i := by
  simp [proof, CausalTerminal.proof, decodedOpening, decodedLevel, challenges,
    _root_.getElem!_pos, i.isLt]

theorem point_size (input : Public) (tape : Tape input.config)
    (i : Fin input.config.folds.size) (j : Nat) (hj : j < oodCount input.config i) :
    (eqTable (challenges input.config tape).levels[i.val]!.oodPoints[j]!).size =
      2 ^ remaining input.config i := by
  simp [challenges, _root_.getElem!_pos, i.isLt, hj, TerminalRefinement.size_eqTable]

/-- Fixed-prefix transition bound for the real list, state and commitment.
Only the arbitrary rows and intro range over the indivisible query draw. -/
theorem actual_transition (input : Public) (strategy : Strategy) (tape : Tape input.config)
    (profile : ParameterBounds.Profile) (hc : input.config = ParameterBounds.config profile)
    (i : Fin input.config.folds.size)
    (rowsAt : LevelBoundary.QueryTape (remaining input.config i + input.config.rates[i.val]!)
      input.config.queries[i.val]! → E → Oracle)
    (introAt : LevelBoundary.QueryTape (remaining input.config i + input.config.rates[i.val]!)
      input.config.queries[i.val]! → E → Message E)
    (weight : (boundary input strategy tape i).state.weight.size = 2 ^ remaining input.config i)
    (lost : LevelBoundary.CloseLost (remaining input.config i) input.config.rates[i.val]!
      (ParameterBounds.threshold input.config i)
      (QueryBatchSoundness.oldWord (remaining input.config i) input.config.rates[i.val]!
        (levelAt input strategy tape i).oracle (i.val == 0)
        (challenges input.config tape).levels[i.val]!.folds)
      (boundary input strategy tape i).state)
    (prior : if i.val + 1 < input.config.folds.size then
      ∃ j < (proof input strategy tape).levels[i.val]!.oods.size,
        LevelBoundary.Separated (followingCandidates input strategy tape i)
          (challenges input.config tape).levels[i.val]!.oodPoints[j]!
      else (proof input strategy tape).residual.size = 2 ^ remaining input.config i) :
    Soundness.uniformProb (Finset.univ.filter
      (QueryBatchSoundness.Restores (remaining input.config i) input.config.rates[i.val]!
        input.config.queries[i.val]! i (levelAt input strategy tape i).oracle
        (challenges input.config tape).levels[i.val]! (proof input strategy tape).levels[i.val]!
        (boundary input strategy tape i).state (followingCandidates input strategy tape i)
        rowsAt introAt)) ≤
      GroupedChallenges.queryBatchError input.config (ParameterBounds.estimates input.config) i := by
  have facts := production_boundary_facts profile ⟨i.val, by simp [← hc]⟩
  dsimp only at facts
  rw [← hc] at facts
  have alpha := (ParameterBounds.production_level_facts profile
    ⟨i.val, by simp [← hc]⟩).2.2.2.2.2.2.1
  dsimp only at alpha
  rw [← hc] at alpha
  have threshold : ParameterBounds.threshold input.config i =
      ⌈(2 ^ (remaining input.config i + input.config.rates[i.val]!) : ℚ) *
        ParameterBounds.alpha input.config.rates[i.val]!⌉₊ := by
    simp [ParameterBounds.threshold, ParameterBounds.length]
  by_cases hn : i.val + 1 < input.config.folds.size
  · simp only [hn, ↓reduceIte] at prior
    obtain ⟨j, hj, sep⟩ := prior
    have bound := QueryBatchSoundness.grouped_transition
      (remaining input.config i) input.config.rates[i.val]! input.config.queries[i.val]! i
      (ParameterBounds.threshold input.config i) (levelAt input strategy tape i).oracle
      (challenges input.config tape).levels[i.val]! (proof input strategy tape).levels[i.val]!
      (boundary input strategy tape i).state (followingCandidates input strategy tape i)
      rowsAt introAt (ParameterBounds.alpha input.config.rates[i.val]!) alpha.le threshold
      facts.1 facts.2.1
      (followingCandidates_sizes input strategy tape profile hc i (by simp [hn]))
      weight (by intro k hk; exact point_size input tape i k (by
        simpa only [decoded_oods_size] using hk)) lost j hj sep
    apply bound.trans
    have cap : ((followingCandidates input strategy tape i).card : ℚ) ≤ 2 ^ 32 := by
      exact_mod_cast followingCandidates_card input strategy tape profile hc i
    simp only [GroupedChallenges.queryBatchError, ParameterBounds.estimates, hn,
      ↓reduceDIte, GroupedChallenges.fieldSize, decoded_oods_size]
    have mul := mul_le_mul_of_nonneg_right cap
      (by positivity : (0 : ℚ) ≤
        ((oodCount input.config i + input.config.queries[i.val]! : Nat) : ℚ) / 2 ^ 192)
    push_cast at mul ⊢
    nlinarith
  · simp only [hn, ↓reduceIte] at prior
    have last : followingCandidates input strategy tape i =
        {(proof input strategy tape).residual} := by simp [followingCandidates, hn]
    rw [last]
    have zero : (proof input strategy tape).levels[i.val]!.oods.size = 0 := by
      rw [decoded_oods_size]
      simp [oodCount, hn]
    have bound := QueryBatchSoundness.final_transition
      (remaining input.config i) input.config.rates[i.val]! input.config.queries[i.val]! i
      (ParameterBounds.threshold input.config i) (levelAt input strategy tape i).oracle
      (challenges input.config tape).levels[i.val]! (proof input strategy tape).levels[i.val]!
      (boundary input strategy tape i).state (proof input strategy tape).residual
      rowsAt introAt (ParameterBounds.alpha input.config.rates[i.val]!) alpha.le threshold
      facts.1 facts.2.1 prior weight zero lost
    simpa only [GroupedChallenges.queryBatchError, ParameterBounds.estimates, hn,
      ↓reduceDIte, GroupedChallenges.fieldSize] using bound

theorem decoded_level (input : Public) (strategy : Strategy) (tape : Tape input.config)
    (i : Fin input.config.folds.size) :
    (proof input strategy tape).levels[i.val]! =
      decodedLevel input.config (challenges input.config tape)
        (run strategy input [] (visibleBatches input.config tape.1
          (challenges input.config tape))).toArray i.val := by
  simp [proof, CausalTerminal.proof, decodedOpening, _root_.getElem!_pos, i.isLt]

theorem nextOracle_set (input : Public) (strategy : Strategy) (tape : Tape input.config)
    (q : Coordinate input.config) (x : Sample q) (i : Fin input.config.folds.size)
    (before : levelStart (challenges input.config tape) i.val + input.config.folds[i.val]! ≤
      position q) :
    (proof input strategy (set q tape x)).levels[i.val]!.nextOracle =
      (proof input strategy tape).levels[i.val]!.nextOracle := by
  have sizes (t : Tape input.config) :
      (challenges input.config t).levels[i.val]!.folds.size = input.config.folds[i.val]! := by
    simp [challenges, _root_.getElem!_pos, i.isLt]
  simp only [decoded_level, decodedLevel, sizes, CausalPositions.levelStart_set]
  split_ifs with h
  · simpa using field_before q tape x strategy input rootField
      (levelStart (challenges input.config tape) i.val + input.config.folds[i.val]! - 1)
      (by omega)
  · rfl

theorem residual_set (input : Public) (strategy : Strategy) (tape : Tape input.config)
    (q : Coordinate input.config) (x : Sample q) (i : Fin input.config.folds.size)
    (last : ¬ i.val + 1 < input.config.folds.size)
    (before : levelStart (challenges input.config tape) i.val + input.config.folds[i.val]! ≤
      position q) :
    (proof input strategy (set q tape x)).residual = (proof input strategy tape).residual := by
  have hi : input.config.folds.size - 1 = i.val := by omega
  have sizes (t : Tape input.config) :
      (challenges input.config t).levels[i.val]!.folds.size = input.config.folds[i.val]! := by
    simp [challenges, _root_.getElem!_pos, i.isLt]
  simp only [proof, CausalTerminal.proof, decodedOpening, hi, sizes,
    CausalPositions.levelStart_set]
  split_ifs with h
  · simpa using field_before q tape x strategy input residualField
      (levelStart (challenges input.config tape) i.val + input.config.folds[i.val]! - 1)
      (by omega)
  · rfl

theorem followingCandidates_set (input : Public) (strategy : Strategy) (tape : Tape input.config)
    (q : Coordinate input.config) (x : Sample q) (i : Fin input.config.folds.size)
    (before : levelStart (challenges input.config tape) i.val + input.config.folds[i.val]! ≤
      position q) :
    followingCandidates input strategy (set q tape x) i =
      followingCandidates input strategy tape i := by
  unfold followingCandidates
  split_ifs with hn
  · apply congrArg (fun oracle : Fin (2 ^ (input.config.folds[i.val + 1]! - 0)) →
        Fin (2 ^ (remaining input.config (i.val + 1) + input.config.rates[i.val + 1]!)) → E =>
      CandidateFolding.arrayCandidates false
        (CandidateFolding.concreteEncoder (remaining input.config (i.val + 1))
          input.config.rates[i.val + 1]!) oracle
        (ParameterBounds.threshold input.config (i.val + 1)))
    funext lane col
    simp only [OracleReplay.oracleAt, OracleReplay.rowAt_zero]
    rw [nextOracle_set input strategy tape q x i before]
  · rw [residual_set input strategy tape q x i hn before]

theorem ood_fiber_bound (input : Public) (strategy : Strategy)
    (profile : ParameterBounds.Profile) (hc : input.config = ParameterBounds.config profile)
    (i : Fin input.config.folds.size) (j : Fin (oodCount input.config i))
    (rest : Rest (.ood i j)) :
    Soundness.uniformProb (Finset.univ.filter fun x : Sample (.ood i j) =>
      OodEvent input strategy i j (set (.ood i j) rest.val x)) ≤
      ((2 ^ 32).choose 2 : ℚ) * (remaining input.config i : ℚ) / 2 ^ 192 := by
  have hn : i.val + 1 < input.config.folds.size := by
    by_contra h
    have := j.isLt
    simp [oodCount, h] at this
  have event : (fun x : Sample (.ood i j) =>
      OodEvent input strategy i j (set (.ood i j) rest.val x)) =
      (fun x : Fin (remaining input.config i) → E =>
        ¬ LevelBoundary.Separated (followingCandidates input strategy rest.val i)
          (Array.ofFn x)) := by
    funext x
    unfold OodEvent
    rw [followingCandidates_set input strategy rest.val (.ood i j) x i (by
      rw [CausalPositions.position_ood i j rest.val]; omega)]
    have h := challengeBatch_eq (.ood i j) (set (.ood i j) rest.val x)
    rw [get_set] at h
    exact congrArg (fun point => ¬ LevelBoundary.Separated
      (followingCandidates input strategy rest.val i) point) (Batch.ood.inj h).2.2
  simp only [event]
  have bound := LevelBoundary.separation_probability (remaining input.config i)
    (followingCandidates input strategy rest.val i)
    (followingCandidates_sizes input strategy rest.val profile hc i (by simp [hn]))
  have cap : ((followingCandidates input strategy rest.val i).card.choose 2 : ℚ) ≤
      (2 ^ 32).choose 2 := by
    exact_mod_cast Nat.choose_le_choose 2 (followingCandidates_card input strategy rest.val profile hc i)
  have enlarged := bound.trans (mul_le_mul_of_nonneg_right cap
    (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
  rw [ParameterBounds.field_cardinality] at enlarged
  exact enlarged.trans_eq (mul_div_assoc _ _ _).symm

theorem ood_coordinate_probability (input : Public) (strategy : Strategy)
    (profile : ParameterBounds.Profile) (hc : input.config = ParameterBounds.config profile)
    (i : Fin input.config.folds.size) (j : Fin (oodCount input.config i)) :
    Soundness.uniformProb (Finset.univ.filter (OodEvent input strategy i j)) ≤
      ((2 ^ 32).choose 2 : ℚ) * (remaining input.config i : ℚ) / 2 ^ 192 :=
  fiber_event_bound (.ood i j) _ _ (ood_fiber_bound input strategy profile hc i j)

theorem ood_probability (input : Public) (strategy : Strategy)
    (profile : ParameterBounds.Profile) (hc : input.config = ParameterBounds.config profile)
    (i : Fin input.config.folds.size) :
    Soundness.uniformProb (Finset.univ.biUnion fun j : Fin (oodCount input.config i) =>
      Finset.univ.filter (OodEvent input strategy i j)) ≤
      GroupedChallenges.oodError input.config (ParameterBounds.estimates input.config) i := by
  apply (Soundness.union_bound _).trans
  calc
    _ ≤ ∑ _j : Fin (oodCount input.config i),
        ((2 ^ 32).choose 2 : ℚ) * (remaining input.config i : ℚ) / 2 ^ 192 :=
      Finset.sum_le_sum fun j _ => ood_coordinate_probability input strategy profile hc i j
    _ ≤ _ := by
      by_cases hn : i.val + 1 < input.config.folds.size
      · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          GroupedChallenges.oodError, ParameterBounds.estimates, hn, ↓reduceDIte,
          GroupedChallenges.fieldSize, mul_div_assoc, mul_assoc, le_refl]
      · have hz : oodCount input.config i = 0 := by simp only [oodCount, hn, ↓reduceIte]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, hz, zero_nsmul,
          GroupedChallenges.oodError, hn, ↓reduceDIte, le_refl]

theorem oods_set (input : Public) (strategy : Strategy) (tape : Tape input.config)
    (q : Coordinate input.config) (x : Sample q) (i : Fin input.config.folds.size)
    (before : levelStart (challenges input.config tape) i.val + input.config.folds[i.val]! +
      oodCount input.config i ≤ position q) :
    (proof input strategy (set q tape x)).levels[i.val]!.oods =
      (proof input strategy tape).levels[i.val]!.oods := by
  have fs (t : Tape input.config) :
      (challenges input.config t).levels[i.val]!.folds.size = input.config.folds[i.val]! := by
    simp [challenges, _root_.getElem!_pos, i.isLt]
  have os (t : Tape input.config) :
      (challenges input.config t).levels[i.val]!.oodPoints.size = oodCount input.config i := by
    simp [challenges, _root_.getElem!_pos, i.isLt]
  simp only [decoded_level, decodedLevel, fs, os, CausalPositions.levelStart_set]
  apply Array.ext
  · simp only [Array.size_ofFn, os]
  · intro j hj hj'
    simp only [Array.getElem_ofFn]
    simpa using field_before q tape x strategy input oodField
      (levelStart (challenges input.config tape) i.val + input.config.folds[i.val]! + j)
      (by simp only [Array.size_ofFn, os] at hj; omega)

theorem query_challenges (input : Public) (tape : Tape input.config)
    (i : Fin input.config.folds.size) (x : Sample (.query i)) :
    (challenges input.config (set (.query i) tape x)).levels[i.val]! =
      { (challenges input.config tape).levels[i.val]! with querySqueezes := Array.ofFn x.1, lambda := x.2 } := by
  have folds : (challenges input.config (set (.query i) tape x)).levels[i.val]!.folds =
      (challenges input.config tape).levels[i.val]!.folds := by
    simp only [challenges, _root_.getElem!_pos, Array.size_ofFn, i.isLt, Array.getElem_ofFn]
    apply congrArg Array.ofFn
    funext j
    exact get_set_ne (.query i) (.fold i j) tape x (by intro h; cases h)
  have oods : (challenges input.config (set (.query i) tape x)).levels[i.val]!.oodPoints =
      (challenges input.config tape).levels[i.val]!.oodPoints := by
    simp only [challenges, _root_.getElem!_pos, Array.size_ofFn, i.isLt, Array.getElem_ofFn]
    apply congrArg Array.ofFn
    funext j
    apply congrArg Array.ofFn
    exact get_set_ne (.query i) (.ood i j) tape x (by intro h; cases h)
  have query := challengeBatch_eq (.query i) (set (.query i) tape x)
  rw [get_set] at query
  have values := Batch.query.inj query
  cases left : (challenges input.config (set (.query i) tape x)).levels[i.val]!
  cases right : (challenges input.config tape).levels[i.val]!
  simp_all only

theorem boundary_eq_foldBlock (input : Public) (strategy : Strategy)
    (tape : Tape input.config) (i : Fin input.config.folds.size) :
    boundary input strategy tape i =
      Protocol.foldBlock (block input.config i) (challenges input.config tape).levels[i.val]!
        (proof input strategy tape).levels[i.val]! (levelAt input strategy tape i) := by
  have sizes : (challenges input.config tape).levels[i.val]!.folds.size =
      input.config.folds[i.val]! := by
    simp [challenges, _root_.getElem!_pos, i.isLt]
  simp only [boundary, foldAt, Protocol.foldBlock, sizes]

theorem next_state (input : Public) (strategy : Strategy)
    (tape : Tape input.config) (i : Fin input.config.folds.size) :
    (levelAt input strategy tape (i.val + 1)).state =
      queryBatch (boundary input strategy tape i).n i
        (challenges input.config tape).levels[i.val]! (proof input strategy tape).levels[i.val]!
        ((deriveQueries ((boundary input strategy tape i).n + input.config.rates[i.val]!)
          input.config.queries[i.val]! (challenges input.config tape).levels[i.val]!.querySqueezes).getD #[])
        (oodBatch (challenges input.config tape).levels[i.val]!
          (proof input strategy tape).levels[i.val]! (boundary input strategy tape i).state) := by
  rw [levelAt_succ]
  simp only [next, boundary_eq_foldBlock]

def QueryPrior (input : Public) (strategy : Strategy)
    (i : Fin input.config.folds.size) (tape : Tape input.config) : Prop :=
  let c := input.config
  let cs := (challenges c tape).levels[i.val]!
  let p := (proof input strategy tape).levels[i.val]!
  let s := boundary input strategy tape i
  let n := remaining c i
  s.n = n ∧ s.state.weight.size = 2 ^ n ∧
  LevelBoundary.CloseLost n c.rates[i.val]! (ParameterBounds.threshold c i)
    (QueryBatchSoundness.oldWord n c.rates[i.val]!
      (levelAt input strategy tape i).oracle (i.val == 0) cs.folds) s.state ∧
  (if i.val + 1 < c.folds.size then
    ∃ j < p.oods.size, LevelBoundary.Separated (followingCandidates input strategy tape i)
      cs.oodPoints[j]!
   else (proof input strategy tape).residual.size = 2 ^ n)

theorem query_level_set (input : Public) (strategy : Strategy) (tape : Tape input.config)
    (i : Fin input.config.folds.size) (x : Sample (.query i)) :
    levelAt input strategy (set (.query i) tape x) i = levelAt input strategy tape i :=
  CausalStateCausality.levelAt_set input strategy (.query i) tape x i i.isLt.le
    (by rw [CausalPositions.position_query i tape]; omega)

theorem query_boundary_set (input : Public) (strategy : Strategy) (tape : Tape input.config)
    (i : Fin input.config.folds.size) (x : Sample (.query i)) :
    boundary input strategy (set (.query i) tape x) i = boundary input strategy tape i :=
  CausalStateCausality.foldAt_set input strategy (.query i) tape x i _ le_rfl
    (by rw [CausalPositions.position_query i tape]; omega)

theorem query_prior_set (input : Public) (strategy : Strategy) (tape : Tape input.config)
    (i : Fin input.config.folds.size) (x : Sample (.query i)) :
    QueryPrior input strategy i (set (.query i) tape x) = QueryPrior input strategy i tape := by
  dsimp only [QueryPrior]
  rw [query_challenges, query_level_set, query_boundary_set,
    followingCandidates_set input strategy tape (.query i) x i (by
      rw [CausalPositions.position_query i tape]; omega)]
  simp only
  by_cases hn : i.val + 1 < input.config.folds.size
  · rw [ite_eq_left hn, ite_eq_left hn, oods_set input strategy tape (.query i) x i (by
      rw [CausalPositions.position_query])]
  · rw [ite_eq_right hn, ite_eq_right hn, residual_set input strategy tape (.query i) x i hn (by
      rw [CausalPositions.position_query i tape]; omega)]

def queryRows (input : Public) (strategy : Strategy) (tape : Tape input.config)
    (i : Fin input.config.folds.size)
    (squeezes : LevelBoundary.QueryTape (remaining input.config i + input.config.rates[i.val]!)
      input.config.queries[i.val]!) (lambda : E) : Oracle :=
  (proof input strategy (set (.query i) tape (squeezes, lambda))).levels[i.val]!.rows

def queryIntro (input : Public) (strategy : Strategy) (tape : Tape input.config)
    (i : Fin input.config.folds.size)
    (squeezes : LevelBoundary.QueryTape (remaining input.config i + input.config.rates[i.val]!)
      input.config.queries[i.val]!) (lambda : E) : Message E :=
  (proof input strategy (set (.query i) tape (squeezes, lambda))).levels[i.val]!.intro

private theorem batch_fields_congr (n i : Nat) (cs : LevelChallenges)
    (p q : LevelProof) (qs : Array Nat) (s : VerifierState E)
    (oods : p.oods = q.oods) (rows : p.rows = q.rows) (intro : p.intro = q.intro) :
    queryBatch n i cs p qs (oodBatch cs p s) =
      queryBatch n i cs q qs (oodBatch cs q s) := by
  cases p
  cases q
  cases oods
  cases rows
  cases intro
  rfl

theorem query_event_fiber (input : Public) (strategy : Strategy) (tape : Tape input.config)
    (i : Fin input.config.folds.size) (x : Sample (.query i))
    (hd : 0 < remaining input.config i + input.config.rates[i.val]!)
    (hb : remaining input.config i + input.config.rates[i.val]! ≤ 64)
    (h : QueryEvent input strategy i (set (.query i) tape x)) :
    QueryPrior input strategy i tape ∧
    QueryBatchSoundness.Restores (remaining input.config i) input.config.rates[i.val]!
      input.config.queries[i.val]! i (levelAt input strategy tape i).oracle
      (challenges input.config tape).levels[i.val]! (proof input strategy tape).levels[i.val]!
      (boundary input strategy tape i).state (followingCandidates input strategy tape i)
      (queryRows input strategy tape i) (queryIntro input strategy tape i) x := by
  rcases h with ⟨dimension, weight, lost, prior, rows, auth, failure⟩
  have hp : QueryPrior input strategy i (set (.query i) tape x) :=
    ⟨dimension, weight, lost, prior⟩
  refine ⟨by rwa [query_prior_set] at hp, ?_⟩
  have sampled :
      (deriveQueries (remaining input.config i + input.config.rates[i.val]!)
        input.config.queries[i.val]!
        (challenges input.config (set (.query i) tape x)).levels[i.val]!.querySqueezes).getD #[] =
      QueryBatchSoundness.queries (remaining input.config i + input.config.rates[i.val]!)
        input.config.queries[i.val]! x.1 := by
    rw [query_challenges]
    dsimp only
    erw [QueryBatchSoundness.queries_actual _ _ x.1 hd hb]
    rfl
  have fixed := followingCandidates_set input strategy tape (.query i) x i (by
    rw [CausalPositions.position_query i tape]; omega)
  have answers := oods_set input strategy tape (.query i) x i (by
    rw [CausalPositions.position_query])
  rw [next_state, dimension, sampled, fixed, query_boundary_set, query_challenges] at failure
  rw [sampled] at rows auth
  rw [query_level_set] at auth
  unfold QueryBatchSoundness.Restores
  dsimp only [queryRows, queryIntro]
  refine ⟨rows, ?_, ?_⟩
  · exact auth
  · have kernel := batch_fields_congr (remaining input.config i) i
      { (challenges input.config tape).levels[i.val]! with querySqueezes := Array.ofFn x.1, lambda := x.2 }
      (proof input strategy (set (.query i) tape x)).levels[i.val]!
      { (proof input strategy tape).levels[i.val]! with
        rows := (proof input strategy (set (.query i) tape x)).levels[i.val]!.rows
        intro := (proof input strategy (set (.query i) tape x)).levels[i.val]!.intro }
      (QueryBatchSoundness.queries (remaining input.config i + input.config.rates[i.val]!)
        input.config.queries[i.val]! x.1)
      (boundary input strategy tape i).state answers rfl rfl
    erw [kernel] at failure
    exact failure

private theorem probability_mono {A : Type*} [Fintype A] (P Q : A → Prop)
    (h : ∀ x, P x → Q x) :
    Soundness.uniformProb (Finset.univ.filter P) ≤
      Soundness.uniformProb (Finset.univ.filter Q) := by
  classical
  unfold Soundness.uniformProb
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast Finset.card_le_card (by
    intro x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h x (Finset.mem_filter.mp hx).2⟩)

theorem query_fiber_bound (input : Public) (strategy : Strategy)
    (profile : ParameterBounds.Profile) (hc : input.config = ParameterBounds.config profile)
    (i : Fin input.config.folds.size) (rest : Rest (.query i)) :
    Soundness.uniformProb (Finset.univ.filter fun x : Sample (.query i) =>
      QueryEvent input strategy i (set (.query i) rest.val x)) ≤
      GroupedChallenges.queryBatchError input.config (ParameterBounds.estimates input.config) i := by
  classical
  have facts := production_boundary_facts profile ⟨i.val, by simp [← hc]⟩
  dsimp only at facts
  rw [← hc] at facts
  by_cases prior : QueryPrior input strategy i rest.val
  · have localBound := actual_transition input strategy rest.val profile hc i
      (queryRows input strategy rest.val i) (queryIntro input strategy rest.val i)
      prior.2.1 prior.2.2.1 prior.2.2.2
    apply le_trans _ localBound
    apply probability_mono
    intro x hx
    exact (query_event_fiber input strategy rest.val i x facts.1 facts.2.1 hx).2
  · have empty : (Finset.univ.filter fun x : Sample (.query i) =>
        QueryEvent input strategy i (set (.query i) rest.val x)) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact prior (query_event_fiber input strategy rest.val i x facts.1 facts.2.1
        (Finset.mem_filter.mp hx).2).1
    rw [empty]
    simp only [Soundness.uniformProb, Finset.card_empty, Nat.cast_zero, zero_div]
    have alpha := (ParameterBounds.production_level_facts profile
      ⟨i.val, by simp [← hc]⟩).2.2.2.2.2.2.1
    dsimp only at alpha
    rw [← hc] at alpha
    unfold GroupedChallenges.queryBatchError ParameterBounds.estimates GroupedChallenges.fieldSize
    split_ifs <;> positivity

theorem query_probability (input : Public) (strategy : Strategy)
    (profile : ParameterBounds.Profile) (hc : input.config = ParameterBounds.config profile)
    (i : Fin input.config.folds.size) :
    Soundness.uniformProb (Finset.univ.filter (QueryEvent input strategy i)) ≤
      GroupedChallenges.queryBatchError input.config (ParameterBounds.estimates input.config) i :=
  fiber_event_bound (.query i) _ _ (query_fiber_bound input strategy profile hc i)

/-- A later random-oracle message cannot change an already exposed OOD event. -/
theorem oodEvent_set_future (input : Public) (strategy : Strategy) (tape : Tape input.config)
    (i : Fin input.config.folds.size) (j : Fin (oodCount input.config i))
    (q : Coordinate input.config) (x : Sample q) (later : position (.ood i j) < position q) :
    OodEvent input strategy i j (set q tape x) = OodEvent input strategy i j tape := by
  have before : levelStart (challenges input.config tape) i.val +
      input.config.folds[i.val]! ≤ position q := by
    rw [CausalPositions.position_ood i j tape] at later
    omega
  simp only [OodEvent, followingCandidates_set input strategy tape q x i before,
    CausalStateCausality.challenge_ood]
  rw [get_set_ne q (.ood i j) tape x (by intro h; rw [h] at later; omega)]

/-- The query event is measurable immediately after the one query/lambda reply;
future proof validity or future challenges do not appear in its definition. -/
theorem queryEvent_set_future (input : Public) (strategy : Strategy) (tape : Tape input.config)
    (i : Fin input.config.folds.size) (q : Coordinate input.config) (x : Sample q)
    (later : levelStart (challenges input.config tape) (i.val + 1) ≤ position q) :
    QueryEvent input strategy i (set q tape x) = QueryEvent input strategy i tape := by
  have before : levelStart (challenges input.config tape) i.val +
      input.config.folds[i.val]! ≤ position q := by
    rw [CausalRefinement.levelStart_succ, CausalStateCausality.challenge_folds_size,
      CausalStateCausality.challenge_oods_size] at later
    omega
  have state := CausalStateCausality.foldAt_set input strategy q tape x i
    input.config.folds[i.val]! le_rfl before
  change boundary input strategy (set q tape x) i = boundary input strategy tape i at state
  have level := CausalStateCausality.levelAt_set input strategy q tape x i i.isLt.le (by omega)
  have after := CausalStateCausality.levelAt_set input strategy q tape x (i.val + 1)
    (by omega) later
  simp only [QueryEvent, state, level, after,
    CausalStateCausality.challenge_level_set input.config q tape x i later,
    CausalStateCausality.proof_level_set input strategy q tape x i later,
    followingCandidates_set input strategy tape q x i before]
  by_cases hn : i.val + 1 < input.config.folds.size
  · simp only [hn, ↓reduceIte]
  · rw [ite_eq_right hn, ite_eq_right hn, residual_set input strategy tape q x i hn before]

end Whir.CausalBoundary
