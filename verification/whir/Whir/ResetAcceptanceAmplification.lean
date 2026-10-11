import Whir.AuthenticatedResetProbability
import Whir.KnowledgeExtraction
import Whir.AuthenticatedResetLaw

/-! Prefix averaging and amplification over independent FULL attempts. The
stopping event is a verified explaining output, never a first accepted prefix.
Acceptance may depend arbitrarily on the entire suffix. -/
namespace Whir.ResetAcceptanceAmplification
open SamplingProbability AuthenticatedResetProbability KnowledgeExtraction
open Concrete Protocol CausalGame
open scoped BigOperators

variable {Prefix Suffix : Type*} [Fintype Prefix] [Nonempty Prefix]
  [Fintype Suffix] [Nonempty Suffix]

noncomputable def prefixAcceptance (accept : Prefix × Suffix → Prop) (p : Prefix) : ℝ :=
  probability (fun suffix => accept (p, suffix))

noncomputable def GoodPrefix (accept : Prefix × Suffix → Prop) (p : Prefix) : Prop :=
  probability accept / 2 ≤ prefixAcceptance accept p

/-- Bounded averaging supplies unconditional good-prefix mass at least κ/2.
This does not claim that the first accepted prefix is good with overwhelming
probability. It can give only a conditional constant, so attempts must repeat. -/
theorem good_prefix_mass (accept : Prefix × Suffix → Prop) :
    probability accept / 2 ≤ probability (GoodPrefix accept) := by
  classical
  let κ := probability accept
  have positive : (0 : ℝ) < Fintype.card Prefix := by exact_mod_cast Fintype.card_pos
  have κnonneg : 0 ≤ κ := nonneg accept
  have pointwise : ∀ p, prefixAcceptance accept p ≤
      κ / 2 + if GoodPrefix accept p then (1 : ℝ) else 0 := by
    intro p
    by_cases good : GoodPrefix accept p
    · rw [ite_eq_left good]
      exact (le_one _).trans (by linarith)
    · rw [ite_eq_right good]
      have low : prefixAcceptance accept p < κ / 2 := lt_of_not_ge good
      linarith
  have total := Finset.sum_le_sum (fun p (_ : p ∈ (Finset.univ : Finset Prefix)) => pointwise p)
  have mean : κ * Fintype.card Prefix = ∑ p, prefixAcceptance accept p := by
    exact (eq_div_iff (ne_of_gt positive)).mp (probability_average accept)
  have goodCard : (∑ p : Prefix, if GoodPrefix accept p then (1 : ℝ) else 0) =
      ((Finset.univ.filter (GoodPrefix accept)).card : ℝ) := by simp
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    goodCard] at total
  rw [← mean] at total
  rw [probability_eq_uniformProb (GoodPrefix accept)]
  simp only [Soundness.uniformProb, Rat.cast_div, Rat.cast_natCast]
  dsimp only [κ] at total
  apply (le_div_iff₀ positive).mpr
  nlinarith

/-- Good prefixes carry at least half the accepted mass as well. In particular,
conditioning on acceptance yields only a constant guarantee, not exponential
failure reduction. -/
theorem good_accepted_mass (accept : Prefix × Suffix → Prop) :
    probability accept / 2 ≤ probability (fun t => accept t ∧ GoodPrefix accept t.1) := by
  classical
  have bad : probability (fun t => accept t ∧ ¬ GoodPrefix accept t.1) ≤ probability accept / 2 := by
    rw [probability_average]
    have positive : (0 : ℝ) < Fintype.card Prefix := by exact_mod_cast Fintype.card_pos
    apply (div_le_iff₀ positive).mpr
    calc
      _ ≤ ∑ _ : Prefix, probability accept / 2 := by
        apply Finset.sum_le_sum
        intro p _
        by_cases good : GoodPrefix accept p
        · simp [good, probability]
          positivity
        · have low : prefixAcceptance accept p < probability accept / 2 := lt_of_not_ge good
          simpa only [good, not_false_eq_true, and_true, prefixAcceptance] using low.le
      _ = _ := by simp [mul_comm]
  let events : Bool → Prefix × Suffix → Prop
    | false => fun t => accept t ∧ ¬ GoodPrefix accept t.1
    | true => fun t => accept t ∧ GoodPrefix accept t.1
  have included : ∀ t, accept t → ∃ b, events b t := by
    intro t h
    by_cases good : GoodPrefix accept t.1
    · exact ⟨true, h, good⟩
    · exact ⟨false, h, good⟩
  have bound := (mono _ _ included).trans (union_le events)
  simp only [Fintype.sum_bool, events] at bound
  linarith

/-- Complete attempts use independent product seeds. The event here must be
actual verified-output success; mere acceptance is not a stopping condition. -/
theorem repeated_attempt_failure {Attempt : Type*} [Fintype Attempt] [Nonempty Attempt]
    (success : Attempt → Prop) (chance : ℝ) (_chanceNonneg : 0 ≤ chance)
    (lower : chance ≤ probability success) (attempts : Nat) :
    probability (fun seed : Fin attempts → Attempt => ∀ i, ¬ success (seed i)) ≤
      (1 - chance) ^ attempts := by
  rw [independent_misses success attempts]
  exact pow_le_pow_left₀ (sub_nonneg.mpr (le_one success)) (by linarith) attempts

/-- Success is the actual reset-machine output together with Explains. -/
theorem repeated_extraction_failure {Seed : Type*} [Fintype Seed] [Nonempty Seed]
    (extractor : Extractor Seed) (prover : CommittedProver) (chance : ℝ)
    (chanceNonneg : 0 ≤ chance)
    (lower : chance ≤ probability (extractionSuccess extractor prover)) (attempts : Nat) :
    probability (fun seed : Fin attempts → Seed =>
      ∀ i, ¬ extractionSuccess extractor prover (seed i)) ≤ (1 - chance) ^ attempts :=
  repeated_attempt_failure _ chance chanceNonneg lower attempts

/-- A fresh prefix and fresh extraction seed form one attempt. Bounded-average
good-prefix mass combines with the actual per-good-prefix output guarantee. -/
theorem prefix_attempt_chance {Seed : Type*} [Fintype Seed] [Nonempty Seed]
    (accept : Prefix × Suffix → Prop) (success : Prefix × Seed → Prop)
    (δ : ℝ) (_δnonneg : 0 ≤ δ) (δle : δ ≤ 1)
    (goodSuccess : ∀ p, GoodPrefix accept p →
      1 - δ ≤ probability (fun seed => success (p, seed))) :
    probability accept / 2 * (1 - δ) ≤ probability success := by
  classical
  have positive : (0 : ℝ) < Fintype.card Prefix := by exact_mod_cast Fintype.card_pos
  have per : ∀ p, (if GoodPrefix accept p then (1 : ℝ) else 0) * (1 - δ) ≤
      probability (fun seed => success (p, seed)) := by
    intro p
    by_cases good : GoodPrefix accept p
    · simpa [good] using goodSuccess p good
    · simpa [good] using nonneg (fun seed => success (p, seed))
  have sum := Finset.sum_le_sum (fun p (_ : p ∈ (Finset.univ : Finset Prefix)) => per p)
  have weighted : probability (GoodPrefix accept) * (1 - δ) ≤ probability success := by
    rw [probability_average]
    rw [probability_eq_uniformProb (GoodPrefix accept)]
    simp only [Soundness.uniformProb, Rat.cast_div, Rat.cast_natCast]
    apply (le_div_iff₀ positive).mpr
    have boole : (∑ p : Prefix, if GoodPrefix accept p then (1 : ℝ) else 0) =
      ((Finset.univ.filter (GoodPrefix accept)).card : ℝ) := by simp
    rw [← Finset.sum_mul, boole] at sum
    simpa only [div_mul_eq_mul_div, div_mul_cancel₀ _ (ne_of_gt positive)] using sum
  exact (mul_le_mul_of_nonneg_right (good_prefix_mass accept) (sub_nonneg.mpr δle)).trans weighted

def firstVerified {W : Type*} (check : W → Bool) : List (Option W) → Option W
  | [] => none
  | none :: rest => firstVerified check rest
  | some w :: rest => if check w then some w else firstVerified check rest

theorem firstVerified_none_iff {W : Type*} (check : W → Bool) (candidates : List (Option W)) :
    firstVerified check candidates = none ↔
      ∀ candidate ∈ candidates, ¬ ∃ w, candidate = some w ∧ check w = true := by
  induction candidates with
  | nil => simp [firstVerified]
  | cons candidate rest ih =>
    cases candidate with
    | none => simp [firstVerified, ih]
    | some w =>
      cases h : check w <;> simp [firstVerified, h, ih]

theorem firstVerified_sound {W : Type*} (check : W → Bool) (relation : W → Prop)
    (sound : ∀ w, check w = true → relation w) (candidates : List (Option W))
    (w : W) (output : firstVerified check candidates = some w) : relation w := by
  induction candidates with
  | nil => simp [firstVerified] at output
  | cons candidate rest ih =>
    cases candidate with
    | none => exact ih output
    | some x =>
      simp only [firstVerified] at output
      split at output
      · rename_i checked
        have same : x = w := Option.some.inj output
        subst w
        exact sound x checked
      · exact ih output

section Attempts
variable {Seed : Type*} [Fintype Seed] [Nonempty Seed]
    (extractor : Extractor Seed) (prover : CommittedProver)
    (check : Witness prover.input.config prover.input.lanes → Bool)

def checkedSuccess (seed : Seed) : Prop :=
  ∃ w, (runRewind prover.input prover.respond extractor.maxReplay extractor.rewindRounds
    (extractor.program prover.input seed)).output = some w ∧ check w = true

/-- Every candidate comes from the actual black box. The algorithm tests output\n+certificates and does NOT stop at an accepted prefix or unchecked candidate. -/
def attemptOutput (attempts : Nat) (seed : Fin attempts → Seed) :
    Option (Witness prover.input.config prover.input.lanes) :=
  firstVerified check (List.ofFn fun i =>
    (runRewind prover.input prover.respond extractor.maxReplay extractor.rewindRounds
      (extractor.program prover.input (seed i))).output)

def attemptCalls (attempts : Nat) (seed : Fin attempts → Seed) : Nat :=
  ∑ i, (runRewind prover.input prover.respond extractor.maxReplay extractor.rewindRounds
    (extractor.program prover.input (seed i))).responseCalls

omit [Fintype Seed] [Nonempty Seed] in
theorem attemptCalls_le (attempts : Nat) (seed : Fin attempts → Seed) :
    attemptCalls extractor prover attempts seed ≤
      attempts * (extractor.rewindRounds * (extractor.maxReplay + 1)) := by
  calc
    _ ≤ ∑ _ : Fin attempts, extractor.rewindRounds * (extractor.maxReplay + 1) :=
      Finset.sum_le_sum (fun i _ => responseCalls_le _ _ _ _ _)
    _ = _ := by simp

omit [Fintype Seed] [Nonempty Seed] in
theorem attemptOutput_explains
    (sound : ∀ w, check w = true → Explains prover.input w)
    (attempts : Nat) (seed : Fin attempts → Seed) (w)
    (output : attemptOutput extractor prover check attempts seed = some w) : Explains prover.input w :=
  firstVerified_sound check _ sound _ w output

theorem attemptOutput_failure (chance : ℝ) (chanceNonneg : 0 ≤ chance)
    (lower : chance ≤ probability (checkedSuccess extractor prover check)) (attempts : Nat) :
    probability (fun seed : Fin attempts → Seed =>
      attemptOutput extractor prover check attempts seed = none) ≤ (1 - chance) ^ attempts := by
  have failure : ∀ seed, attemptOutput extractor prover check attempts seed = none ↔
      ∀ i, ¬ checkedSuccess extractor prover check (seed i) := by
    intro seed
    simp only [attemptOutput, firstVerified_none_iff, List.forall_mem_ofFn_iff, checkedSuccess]
  convert repeated_attempt_failure (checkedSuccess extractor prover check) chance chanceNonneg lower attempts using 1
  congr 1
  funext seed
  exact propext (failure seed)
end Attempts

section ActualPrefix
open AuthenticatedResetSupport
variable (prover : CommittedProver) (level : Fin prover.input.config.folds.size)
    (depth : Nat)
    (chunks : CausalGame.queryChunks prover.input.config level =
      ((prover.input.config.queries[level.val]! + 192 / depth - 1) / (192 / depth)))

def fullPrefixAccept (p : CausalGame.Tape prover.input.config ×
    (RewindCoverage.QueryTape depth prover.input.config.queries[level.val]! ×
      (Concrete.E × CausalGame.Tape prover.input.config))) : Prop :=
  CausalGame.experiment prover.input prover.respond
    (fullResetTape prover.input p.1 level depth chunks p.2.1 p.2.2) = true

theorem actual_good_prefix_mass :
    probability (fun t => CausalGame.experiment prover.input prover.respond t = true) / 2 ≤
      probability (GoodPrefix (fullPrefixAccept prover level depth chunks)) := by
  have bound := good_prefix_mass (fullPrefixAccept prover level depth chunks)
  have law := fullResetTape_probability prover.input level depth chunks
    (fun t => CausalGame.experiment prover.input prover.respond t = true)
  change probability (fullPrefixAccept prover level depth chunks) = _ at law
  rwa [law] at bound

theorem actual_prefix_attempt_chance {Seed : Type*} [Fintype Seed] [Nonempty Seed]
    (success : CausalGame.Tape prover.input.config × Seed → Prop)
    (δ : ℝ) (δnonneg : 0 ≤ δ) (δle : δ ≤ 1)
    (goodSuccess : ∀ p, GoodPrefix (fullPrefixAccept prover level depth chunks) p →
      1 - δ ≤ probability (fun seed => success (p, seed))) :
    probability (fun t => CausalGame.experiment prover.input prover.respond t = true) / 2 * (1 - δ) ≤
      probability success := by
  have bound := prefix_attempt_chance (fullPrefixAccept prover level depth chunks)
    success δ δnonneg δle goodSuccess
  have law := fullResetTape_probability prover.input level depth chunks
    (fun t => CausalGame.experiment prover.input prover.respond t = true)
  change probability (fullPrefixAccept prover level depth chunks) = _ at law
  rwa [law] at bound
/-- Complete fresh prefix+extraction attempts amplify only VERIFIED output
success. This is the exponential statement a first accepted prefix cannot give. -/
theorem actual_repeated_prefix_failure {Seed : Type*} [Fintype Seed] [Nonempty Seed]
    (success : CausalGame.Tape prover.input.config × Seed → Prop)
    (δ : ℝ) (δnonneg : 0 ≤ δ) (δle : δ ≤ 1)
    (goodSuccess : ∀ p, GoodPrefix (fullPrefixAccept prover level depth chunks) p →
      1 - δ ≤ probability (fun seed => success (p, seed))) (attempts : Nat) :
    probability (fun seed : Fin attempts → CausalGame.Tape prover.input.config × Seed =>
      ∀ i, ¬ success (seed i)) ≤
      (1 - probability (fun t => CausalGame.experiment prover.input prover.respond t = true) / 2 *
        (1 - δ)) ^ attempts := by
  apply repeated_attempt_failure
  · exact mul_nonneg (div_nonneg (nonneg _) (by norm_num)) (sub_nonneg.mpr δle)
  · exact actual_prefix_attempt_chance prover level depth chunks success δ δnonneg δle goodSuccess

#print axioms actual_repeated_prefix_failure
end ActualPrefix

#print axioms actual_good_prefix_mass
#print axioms actual_prefix_attempt_chance

#print axioms prefix_attempt_chance
#print axioms attemptCalls_le
#print axioms attemptOutput_explains
#print axioms attemptOutput_failure

#print axioms good_prefix_mass
#print axioms good_accepted_mass
#print axioms repeated_attempt_failure
#print axioms repeated_extraction_failure
end Whir.ResetAcceptanceAmplification
