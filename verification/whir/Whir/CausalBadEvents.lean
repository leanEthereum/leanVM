import Whir.CausalInitial
import Whir.CausalFolds
import Whir.CausalBoundary

/-! One dependent-alphabet bad-prefix relation for the actual WHIR execution.
Every constructor corresponds to one indivisible random challenge message. -/
namespace Whir.CausalBadEvents
open Concrete Protocol CausalGame CausalProbability

/-- The final tail coordinate is included although it has no following prover response. -/
def Bad (input : Public) (strategy : Strategy) (q : Coordinate input.config)
    (tape : Tape input.config) : Prop :=
  match q with
  | .initial => CausalInitial.Event input tape
  | .fold i j => CausalFolds.Event input strategy i j tape
  | .ood i j => CausalBoundary.OodEvent input strategy i j tape
  | .query i => CausalBoundary.QueryEvent input strategy i tape
  | .tail j =>
      dot (CausalTerminal.candidate input strategy tape j)
        (CausalTerminal.pending input strategy tape j).weight ≠
          (CausalTerminal.pending input strategy tape j).claim ∧
      tape.2.2 j ∈ TerminalSoundness.collision (CausalTerminal.candidate input strategy tape j)
        (CausalTerminal.pending input strategy tape j)

/-- Conservative unground production envelopes, before any hash or ROM losses. -/
def localError (input : Public) (q : Coordinate input.config) : ℚ :=
  match q with
  | .initial => GroupedChallenges.initialBatch input.config
      (ParameterBounds.estimates input.config) input.claims.size
  | .fold i _ => GroupedChallenges.foldError input.config
      (ParameterBounds.estimates input.config) i
  | .ood i _ => ((2 ^ 32).choose 2 : ℚ) * (remaining input.config i : ℚ) / 2 ^ 192
  | .query i => GroupedChallenges.queryBatchError input.config
      (ParameterBounds.estimates input.config) i
  | .tail _ => 2 / 2 ^ 192

open ParameterBounds GroupedChallenges
open scoped BigOperators
open Classical
set_option maxHeartbeats 800000
set_option maxRecDepth 100000
attribute [local irreducible] CausalTerminal.candidate CausalTerminal.pending TerminalSoundness.collision

theorem initial_fiber (p : Profile) (lanes : Nat) (root : BaseOracle) (claims : Array Claim)
    (lane_bound : lanes ≤ 2 ^ (config p).folds[0]!)
    (shape : ∀ j : Fin claims.size, claims[j].weight.size = 2 ^ (config p).logN)
    (strategy : Strategy) (t : Tape (config p)) :
    Soundness.uniformProb (Finset.univ.filter fun x : E =>
      Bad ⟨config p, lanes, root, claims⟩ strategy .initial (set .initial t x)) ≤
      initialBatch (config p) (estimates (config p)) claims.size := by
  have he : (Finset.univ.filter fun x : E =>
      Bad ⟨config p, lanes, root, claims⟩ strategy .initial (set .initial t x)) =
      InitialBatching.candidateEscape
        (InitialCandidates.extensionCandidates (config p) lanes root) claims := by
    have hs : (Finset.univ.filter fun x : E =>
        Bad ⟨config p, lanes, root, claims⟩ strategy .initial (set .initial t x)) =
        (Finset.univ.filter fun x : E => x ∈ InitialBatching.candidateEscape
          (InitialCandidates.extensionCandidates (config p) lanes root) claims) := by
      apply Finset.filter_congr
      intro x _
      change (get .initial (set .initial t x) ∈ _) ↔ _
      rw [get_set]
    rw [hs, Finset.filter_mem_eq_inter, Finset.univ_inter]
  rw [he]
  apply (InitialSoundness.initial_escape_probability p lanes root lane_bound claims shape).trans_eq
  unfold initialBatch
  rw [dite_eq_left (production_config_valid p).2.1]
  simp only [estimates, fieldSize, Nat.cast_pow, Nat.cast_ofNat]
  ring

theorem tail_fiber (input : Public) (strategy : Strategy) (valid : input.config.valid = true)
    (j : Fin (input.config.logN - input.config.folds.toList.sum)) (t : Tape input.config) :
    Soundness.uniformProb (Finset.univ.filter fun x : Sample (.tail j) =>
      Bad input strategy (.tail j) (set (.tail j) t x)) ≤ 2 / fieldSize := by
  have eq (x : E) : Bad input strategy (.tail j) (set (.tail j) t x) ↔
      dot (CausalTerminal.candidate input strategy t j)
          (CausalTerminal.pending input strategy t j).weight ≠
        (CausalTerminal.pending input strategy t j).claim ∧
      x ∈ TerminalSoundness.collision (CausalTerminal.candidate input strategy t j)
        (CausalTerminal.pending input strategy t j) := by
    obtain ⟨ha, hs⟩ := CausalTerminal.kernels_set input strategy valid j t x
    dsimp only [Bad]
    rw [ha, hs]
    simp only [set_tail, Function.update_self]
  simp_rw [eq]
  by_cases lost : dot (CausalTerminal.candidate input strategy t j)
      (CausalTerminal.pending input strategy t j).weight ≠
      (CausalTerminal.pending input strategy t j).claim
  · have he : (Finset.univ.filter fun x : E =>
        dot (CausalTerminal.candidate input strategy t j)
            (CausalTerminal.pending input strategy t j).weight ≠
          (CausalTerminal.pending input strategy t j).claim ∧
        x ∈ TerminalSoundness.collision (CausalTerminal.candidate input strategy t j)
          (CausalTerminal.pending input strategy t j)) =
        TerminalSoundness.collision (CausalTerminal.candidate input strategy t j)
          (CausalTerminal.pending input strategy t j) := by
      apply Finset.ext
      intro x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨And.right, fun h => ⟨lost, h⟩⟩
    rw [he]
    have h := TerminalSoundness.collision_probability _ _ lost
    rw [field_cardinality] at h
    exact h
  · simp only [lost, false_and, Finset.filter_false, Soundness.uniformProb,
      Finset.card_empty, Nat.cast_zero, zero_div]
    norm_num [fieldSize]

/-- No acceptance or local-escape hypothesis: each case is the checked actual
strategy fiber bound, including arbitrary current replies and authenticated rows. -/
theorem fiber_bound (p : Profile) (lanes : Nat) (root : BaseOracle) (claims : Array Claim)
    (lane_bound : lanes ≤ 2 ^ (config p).folds[0]!)
    (shape : ∀ j : Fin claims.size, claims[j].weight.size = 2 ^ (config p).logN)
    (strategy : Strategy) (q : Coordinate (config p)) (t : Tape (config p)) :
    Soundness.uniformProb (Finset.univ.filter fun x : Sample q =>
      Bad ⟨config p, lanes, root, claims⟩ strategy q (set q t x)) ≤
      localError ⟨config p, lanes, root, claims⟩ q := by
  cases q with
  | initial => exact initial_fiber p lanes root claims lane_bound shape strategy t
  | fold i j => exact CausalFolds.fiber_bound p lanes root claims strategy i j t
  | ood i j =>
    have h := CausalBoundary.ood_fiber_bound ⟨config p, lanes, root, claims⟩ strategy p rfl i j
      ⟨set (.ood i j) t 0, get_set _ _ _⟩
    change Soundness.uniformProb (Finset.univ.filter fun x : Sample (.ood i j) =>
      CausalBoundary.OodEvent ⟨config p, lanes, root, claims⟩ strategy i j (set (.ood i j) t x)) ≤ _
    convert h using 1 <;> simp only [set_set, localError]
  | query i =>
    have h := CausalBoundary.query_fiber_bound ⟨config p, lanes, root, claims⟩ strategy p rfl i
      ⟨set (.query i) t 0, get_set _ _ _⟩
    change Soundness.uniformProb (Finset.univ.filter fun x : Sample (.query i) =>
      CausalBoundary.QueryEvent ⟨config p, lanes, root, claims⟩ strategy i (set (.query i) t x)) ≤ _
    convert h using 1 <;> simp only [set_set, localError]
  | tail j =>
    change _ ≤ 2 / fieldSize
    exact tail_fiber ⟨config p, lanes, root, claims⟩ strategy (production_config_valid p).1 j t

theorem coordinate_bound (p : Profile) (lanes : Nat) (root : BaseOracle) (claims : Array Claim)
    (lane_bound : lanes ≤ 2 ^ (config p).folds[0]!)
    (shape : ∀ j : Fin claims.size, claims[j].weight.size = 2 ^ (config p).logN)
    (strategy : Strategy) (q : Coordinate (config p)) :
    Soundness.uniformProb (Finset.univ.filter (Bad ⟨config p, lanes, root, claims⟩ strategy q)) ≤
      localError ⟨config p, lanes, root, claims⟩ q :=
  fiber_event_bound q _ _ (fun rest => fiber_bound p lanes root claims lane_bound shape strategy q rest.val)

private theorem le_foldl_max_start (xs : List ℚ) (a : ℚ) :
    a ≤ xs.foldl max a := by
  induction xs generalizing a with
  | nil => exact le_rfl
  | cons x xs ih => exact (le_max_left a x).trans (ih _)

private theorem le_foldl_max_of_mem (xs : List ℚ) (a x : ℚ) (hx : x ∈ xs) :
    x ≤ xs.foldl max a := by
  induction xs generalizing a with
  | nil => simp at hx
  | cons y ys ih =>
    rcases List.mem_cons.mp hx with rfl | h
    · exact (le_max_right a x).trans (le_foldl_max_start ys _)
    · exact ih _ h

theorem level_le_groupedMaximum (c : Config) (claims : Nat) (i : Fin c.folds.size) :
    max (foldError c (estimates c) i)
      (max (oodError c (estimates c) i) (queryBatchError c (estimates c) i)) ≤
      groupedMaximum c (estimates c) claims := by
  apply le_trans (le_foldl_max_of_mem _ 0 _ (List.mem_ofFn.mpr ⟨i, rfl⟩))
  exact (le_max_right _ _).trans (le_max_right _ _)

theorem localError_le_groupedMaximum (input : Public) (q : Coordinate input.config) :
    localError input q ≤ groupedMaximum input.config (estimates input.config) input.claims.size := by
  cases q with
  | initial => exact le_max_left _ _
  | fold i j => exact (le_max_left _ _).trans (level_le_groupedMaximum _ _ i)
  | query i => exact (le_max_right _ _).trans ((le_max_right _ _).trans (level_le_groupedMaximum _ _ i))
  | tail j => exact (le_max_left _ _).trans (le_max_right _ _)
  | ood i j =>
    apply le_trans _ ((le_max_left _ _).trans ((le_max_right _ _).trans
      (level_le_groupedMaximum _ _ i)))
    have hn : i.val + 1 < input.config.folds.size := by
      by_contra h
      have := j.isLt
      simp [oodCount, h] at this
    have hj : (1 : ℚ) ≤ oodCount input.config i := by
      exact_mod_cast (Nat.zero_lt_of_lt j.isLt)
    simp only [localError, oodError, hn, ↓reduceDIte, estimates, fieldSize]
    have hm := mul_le_mul_of_nonneg_right hj
      (show (0 : ℚ) ≤ ((2^32).choose 2 : ℚ) * remaining input.config i / 2^192 from
        div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (by norm_num))
    simpa only [one_mul, mul_div_assoc, mul_assoc] using hm

/-- Exact dependent-coordinate ledger, including all individual OOD vectors. -/
theorem localError_sum (input : Public) :
    (∑ q : Coordinate input.config, localError input q) =
      interactiveError input.config (estimates input.config) input.claims.size := by
  rw [← Equiv.sum_comp (Coordinate.proxyTypeEquiv input.config)]
  simp only [Fintype.sum_sum_type, Fintype.sum_sigma, Fintype.sum_unique]
  change initialBatch input.config (estimates input.config) input.claims.size +
    ((∑ i : Fin input.config.folds.size, ∑ _j : Fin input.config.folds[i.val]!,
        foldError input.config (estimates input.config) i) +
    ((∑ i : Fin input.config.folds.size, ∑ _j : Fin (oodCount input.config i),
        ((2^32).choose 2 : ℚ) * (remaining input.config i : ℚ) / 2^192) +
    ((∑ i : Fin input.config.folds.size, queryBatchError input.config (estimates input.config) i) +
      ∑ _j : Fin (input.config.logN - input.config.folds.toList.sum), (2 / 2^192 : ℚ)))) = _
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have ood (i : Fin input.config.folds.size) :
      (oodCount input.config i : ℚ) *
        (((2 ^ 32).choose 2 : ℚ) * (remaining input.config i : ℚ) / 2 ^ 192) =
      oodError input.config (estimates input.config) i := by
    unfold oodError
    split_ifs with h
    · simp only [estimates, fieldSize]
      ring
    · simp only [oodCount, h, ↓reduceIte, Nat.cast_zero, zero_mul]
  simp_rw [ood]
  simp only [interactiveError, Finset.sum_add_distrib, fieldSize]
  ring

/-- The concrete accepted-cover consumer needs only deterministic public syntax.
The event probability itself contains no acceptance condition. -/
theorem bad_probability (p : Profile) (lanes : Nat) (root : BaseOracle) (claims : Array Claim)
    (strategy : Strategy) (lane_bound : lanes ≤ 2 ^ (config p).folds[0]!)
    (shape : ∀ j : Fin claims.size, claims[j].weight.size = 2 ^ (config p).logN) :
    Soundness.uniformProb (Finset.univ.filter fun tape : Tape (config p) =>
      ∃ q, Bad ⟨config p, lanes, root, claims⟩ strategy q tape) ≤
      interactiveError (config p) (estimates (config p)) claims.size := by
  have he : (Finset.univ.filter fun tape : Tape (config p) =>
      ∃ q, Bad ⟨config p, lanes, root, claims⟩ strategy q tape) =
      Finset.univ.biUnion (fun q => Finset.univ.filter
        (Bad ⟨config p, lanes, root, claims⟩ strategy q)) := by
    ext tape
    simp
  rw [he, ← localError_sum (⟨config p, lanes, root, claims⟩ : Public)]
  exact (Soundness.union_bound _).trans (Finset.sum_le_sum fun q _ =>
    coordinate_bound p lanes root claims lane_bound shape strategy q)

end Whir.CausalBadEvents
