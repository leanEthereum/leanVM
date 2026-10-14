import Whir.RewindRowExtraction
import Whir.AuthenticatedResetProbability
import Whir.AuthenticatedResetSuffix

/-! Acceptance-dependent support of the actual stratified query sampler. Full
trials, including lambda and the remaining suffix, are repeated independently.
Rejected or malformed verifier trials supply no data. -/
namespace Whir.AuthenticatedResetSupport
open Concrete Protocol CausalGame CausalProbability KnowledgeExtraction
open SamplingProbability RewindCoverage AuthenticatedResetProbability
open scoped BigOperators

section Support
variable (depth count : Nat) (positive : 0 < depth) (noWrap : depth ≤ 64)
variable {Suffix : Type*} [Fintype Suffix] [Nonempty Suffix]

abbrev Trial := QueryTape depth count × Suffix

def Occurs (target : Fin (2 ^ depth)) (trial : Trial depth count (Suffix := Suffix)) : Prop :=
  ∃ i, sampledPosition depth count positive noWrap trial.1 i = target

noncomputable def availability (accept : Trial depth count (Suffix := Suffix) → Prop)
    (target : Fin (2 ^ depth)) : ℝ :=
  probability (fun trial => accept trial ∧ Occurs depth count positive noWrap target trial)

noncomputable def heavy (accept : Trial depth count (Suffix := Suffix) → Prop) (η : ℝ) :
    Finset (Fin (2 ^ depth)) :=
  @Finset.filter _ (fun q => η ≤ availability depth count positive noWrap accept q)
    (Classical.decPred _) Finset.univ

theorem allQueriesHit_iff (A : Finset (Fin (2 ^ depth))) (tape : QueryTape depth count) :
    allQueriesHit depth count A tape ↔
      ∀ i, sampledPosition depth count positive noWrap tape i ∈ A := by
  classical
  unfold allQueriesHit
  rw [deriveQueries_eq depth count positive noWrap]
  simp only [Option.some.injEq]
  constructor
  · rintro ⟨qs, rfl, hit⟩ i
    have member := hit i
    rw [ArrayLayout.getElem!_tab _ _ _ i.isLt,
      ← sampledPosition_actual depth count positive noWrap tape i] at member
    obtain ⟨q, hq, same⟩ := Finset.mem_image.mp member
    have eq : q = sampledPosition depth count positive noWrap tape i := Fin.ext same
    simpa [eq] using hq
  · intro hit
    refine ⟨_, rfl, ?_⟩
    intro i
    rw [ArrayLayout.getElem!_tab _ _ _ i.isLt,
      ← sampledPosition_actual depth count positive noWrap tape i]
    exact Finset.mem_image.mpr ⟨_, hit i, rfl⟩

/-- κ is the actual acceptance probability, even when the prover withholds
precisely on particular coordinates or suffixes. No answer independence is used. -/
theorem acceptance_le_heavy_probability (accept : Trial depth count (Suffix := Suffix) → Prop)
    (η : ℝ) (ηnonneg : 0 ≤ η) :
    probability accept ≤
      probability (allQueriesHit depth count (heavy depth count positive noWrap accept η)) +
        (2 ^ depth : Nat) * η := by
  classical
  let H := heavy depth count positive noWrap accept η
  let events : Option (Fin (2 ^ depth)) → Trial depth count (Suffix := Suffix) → Prop
    | none => fun t => allQueriesHit depth count H t.1
    | some q => fun t => accept t ∧ Occurs depth count positive noWrap q t ∧ q ∉ H
  have included : ∀ t, accept t → ∃ j, events j t := by
    intro t accepted
    by_cases all : allQueriesHit depth count H t.1
    · exact ⟨none, all⟩
    · rw [allQueriesHit_iff depth count positive noWrap] at all
      push Not at all
      obtain ⟨i, outside⟩ := all
      exact ⟨some _, accepted, ⟨i, rfl⟩, outside⟩
  have lightBound : ∀ q, probability (events (some q)) ≤ η := by
    intro q
    by_cases member : q ∈ H
    · have empty : events (some q) = fun _ => False := by funext t; simp [events, member]
      rw [empty]
      simpa [probability] using ηnonneg
    · have light : availability depth count positive noWrap accept q < η := by
        simpa [H, heavy] using member
      exact (mono _ _ (fun t h => ⟨h.1, h.2.1⟩)).trans light.le
  calc
    probability accept ≤ probability (fun t => ∃ j, events j t) := mono _ _ included
    _ ≤ ∑ j, probability (events j) := union_le events
    _ = probability (events none) + ∑ q, probability (events (some q)) := by
      rw [Fintype.sum_option]
    _ ≤ probability (allQueriesHit depth count H) + ∑ _ : Fin (2 ^ depth), η := by
      dsimp only [events]
      rw [product_left]
      exact add_le_add le_rfl (Finset.sum_le_sum fun q _ => lightBound q)
    _ = probability (allQueriesHit depth count H) + (2 ^ depth : Nat) * η := by simp

/-- The density envelope uses the actual stratified law, not iid uniform
replacement queries. -/
theorem acceptance_le_heavy (accept : Trial depth count (Suffix := Suffix) → Prop)
    (η : ℝ) (ηnonneg : 0 ≤ η) :
    probability accept ≤
      ((heavy depth count positive noWrap accept η).card / (2 ^ depth : Nat) : ℝ) ^ count +
        (2 ^ depth : Nat) * η := by
  refine (acceptance_le_heavy_probability depth count positive noWrap accept η ηnonneg).trans ?_
  simpa [StratifiedDensity.globalDensity] using
    add_le_add_right (actual_query_bound depth count positive noWrap
      (heavy depth count positive noWrap accept η)) ((2 ^ depth : Nat) * η)

/-- Strict acceptance above the light-support envelope forces genuinely
available coordinates, not merely coordinates occurring in rejected transcripts. -/
theorem heavy_card_gt (accept : Trial depth count (Suffix := Suffix) → Prop)
    (η : ℝ) (ηnonneg : 0 ≤ η) (B : Nat)
    (large : ((B : ℝ) / (2 ^ depth : Nat)) ^ count + (2 ^ depth : Nat) * η < probability accept) :
    B < (heavy depth count positive noWrap accept η).card := by
  by_contra notLarge
  have card : (heavy depth count positive noWrap accept η).card ≤ B := by omega
  have powers : ((heavy depth count positive noWrap accept η).card / (2 ^ depth : Nat) : ℝ) ^ count ≤
      ((B : ℝ) / (2 ^ depth : Nat)) ^ count := by
    apply pow_le_pow_left₀ (by positivity)
    exact div_le_div_of_nonneg_right (by exact_mod_cast card) (by positivity)
  have bound := acceptance_le_heavy depth count positive noWrap accept η ηnonneg
  linarith

def CoversHeavy (accept : Trial depth count (Suffix := Suffix) → Prop) (η : ℝ)
    (fuel : Nat) (seed : Fin fuel → Trial depth count (Suffix := Suffix)) : Prop :=
  ∀ target ∈ heavy depth count positive noWrap accept η,
    ∃ r, accept (seed r) ∧ Occurs depth count positive noWrap target (seed r)

/-- Fresh FULL suffixes are repeated; there is no resampling of just coordinates
while leaving a maliciously selected suffix fixed. -/
theorem coverage_failure_le (accept : Trial depth count (Suffix := Suffix) → Prop)
    (η : ℝ) (_ηnonneg : 0 ≤ η) (ηle : η ≤ 1) (fuel : Nat) :
    probability (fun seed => ¬ CoversHeavy depth count positive noWrap accept η fuel seed) ≤
      (2 ^ depth : Nat) * (1 - η) ^ fuel := by
  classical
  let events := fun target : Fin (2 ^ depth) => fun seed : Fin fuel → Trial depth count (Suffix := Suffix) =>
    target ∈ heavy depth count positive noWrap accept η ∧
      ∀ r, ¬ (accept (seed r) ∧ Occurs depth count positive noWrap target (seed r))
  have included : ∀ seed, ¬ CoversHeavy depth count positive noWrap accept η fuel seed →
      ∃ target, events target seed := by
    intro seed failure
    simpa [CoversHeavy, events, not_forall, not_imp, not_exists] using failure
  have each : ∀ target, probability (events target) ≤ (1 - η) ^ fuel := by
    intro target
    by_cases member : target ∈ heavy depth count positive noWrap accept η
    · have available : η ≤ availability depth count positive noWrap accept target := by
        simpa [heavy] using member
      refine (mono _ _ (fun seed h => h.2)).trans ?_
      rw [independent_misses (fun t : Trial depth count (Suffix := Suffix) =>
        accept t ∧ Occurs depth count positive noWrap target t) fuel]
      apply pow_le_pow_left₀
      · exact sub_nonneg.mpr (le_one _)
      · dsimp [availability] at available
        linarith
    · have empty : events target = fun _ => False := by funext seed; simp [events, member]
      rw [empty]
      simp only [probability, Fintype.card_subtype]
      simp
      exact pow_nonneg (sub_nonneg.mpr ηle) _
  calc
    _ ≤ probability (fun seed => ∃ target, events target seed) := mono _ _ included
    _ ≤ ∑ target, probability (events target) := union_le events
    _ ≤ ∑ _ : Fin (2 ^ depth), (1 - η) ^ fuel := Finset.sum_le_sum fun q _ => each q
    _ = _ := by simp
end Support

section Actual
variable (prover : CommittedProver) (base : Tape prover.input.config)
    (level : Fin prover.input.config.folds.size) (depth : Nat)
    (positive : 0 < depth) (noWrap : depth ≤ 64)
    (chunks : queryChunks prover.input.config level =
      ((prover.input.config.queries[level.val]! + 192 / depth - 1) / (192 / depth)))

abbrev FullTrial := Trial depth prover.input.config.queries[level.val]!
  (Suffix := E × Tape prover.input.config)

def resetAccept (trial : FullTrial prover level depth) : Prop :=
  experiment prover.input prover.respond
    (fullResetTape prover.input base level depth chunks trial.1 trial.2) = true

def resetTapes (fuel : Nat) (seed : Fin fuel → FullTrial prover level depth) :
    List (Tape prover.input.config) :=
  List.ofFn fun r => fullResetTape prover.input base level depth chunks (seed r).1 (seed r).2

def HasHeavyRecords (η : ℝ) (fuel : Nat) (seed : Fin fuel → FullTrial prover level depth) : Prop :=
  ∀ q ∈ heavy depth prover.input.config.queries[level.val]! positive noWrap
      (resetAccept prover base level depth chunks) η,
    ∃ record ∈ collectedRecords prover level depth (resetTapes prover base level depth chunks fuel seed),
      record.1 = q

theorem heavy_records_of_coverage (η : ℝ) (fuel : Nat) (seed : Fin fuel → FullTrial prover level depth)
    (coverage : CoversHeavy depth prover.input.config.queries[level.val]! positive noWrap
      (resetAccept prover base level depth chunks) η fuel seed) :
    HasHeavyRecords prover base level depth positive noWrap chunks η fuel seed := by
  intro q heavyQ
  obtain ⟨r, accepted, i, hit⟩ := coverage q heavyQ
  obtain ⟨record, member, coordinate⟩ := trialRecords_contains prover
    (fullResetTape prover.input base level depth chunks (seed r).1 (seed r).2)
    level depth positive noWrap (seed r).1 (fullResetTape_squeezes _ _ _ _ _ _ _) accepted i
  refine ⟨record, List.mem_flatMap.mpr ⟨_, ?_, member⟩, coordinate.trans hit⟩
  exact List.mem_ofFn.mpr ⟨r, rfl⟩

/-- End-to-end heavy-coordinate availability of the real acceptance-guarded
collector, including arbitrary withholding and malformed answers. -/
theorem actual_collector_coverage_failure (η : ℝ) (ηnonneg : 0 ≤ η) (ηle : η ≤ 1) (fuel : Nat) :
    probability (fun seed : Fin fuel → FullTrial prover level depth =>
      ¬ HasHeavyRecords prover base level depth positive noWrap chunks η fuel seed) ≤
        (2 ^ depth : Nat) * (1 - η) ^ fuel := by
  refine (mono _ _ (fun seed failure covered =>
    failure (heavy_records_of_coverage prover base level depth positive noWrap chunks η fuel seed covered))).trans ?_
  exact coverage_failure_le depth prover.input.config.queries[level.val]! positive noWrap
    (resetAccept prover base level depth chunks) η ηnonneg ηle fuel

theorem actual_collected_authenticated (fuel : Nat) (seed : Fin fuel → FullTrial prover level depth)
    (shape : ∀ r, (CausalExecution.foldAt prover.input prover.respond
      (fullResetTape prover.input base level depth chunks (seed r).1 (seed r).2) level
      prover.input.config.folds[level.val]!).n + prover.input.config.rates[level.val]! = depth) :
    ∀ record ∈ collectedRecords prover level depth (resetTapes prover base level depth chunks fuel seed),
      record.2 = (CausalExecution.levelAt prover.input prover.respond base level).oracle[record.1.val]! := by
  intro record member
  obtain ⟨tape, inTapes, inRecords⟩ := List.mem_flatMap.mp member
  change tape ∈ List.ofFn _ at inTapes
  obtain ⟨r, rfl⟩ := List.mem_ofFn.mp inTapes
  have auth := trialRecords_authenticated prover _ level depth (shape r) record inRecords
  rwa [fullResetTape_oracle] at auth

#print axioms actual_collector_coverage_failure
#print axioms actual_collected_authenticated
end Actual

/-- One inverse-availability block reduces each heavy-coordinate miss to 1/2.
The caller supplies a natural block with block·η≥1; taking ceil(1/η) works. -/
theorem inverse_availability_block (η : ℝ) (ηpositive : 0 < η) (ηle : η ≤ 1)
    (block : Nat) (enough : 1 ≤ (block : ℝ) * η) :
    (1 - η) ^ block ≤ (1 / 2 : ℝ) := by
  have blockPositive : 0 < block := by
    by_contra h
    have zero : block = 0 := by omega
    norm_num [zero] at enough
  by_cases endpoint : η = 1
  · simp [endpoint, Nat.ne_of_gt blockPositive]
  have strict : η < 1 := lt_of_le_of_ne ηle endpoint
  have gap : 0 < 1 - η := by linarith
  have nonneg : 0 ≤ 1 - η := gap.le
  have ratioNonneg : 0 ≤ η / (1 - η) := div_nonneg ηpositive.le gap.le
  have ratio : η ≤ η / (1 - η) := by
    apply (le_div_iff₀ gap).mpr
    nlinarith
  have bernoulli := one_add_mul_le_pow (by linarith : (-2 : ℝ) ≤ η / (1 - η)) block
  have two : 2 ≤ (1 + η / (1 - η)) ^ block := by
    have mul := mul_le_mul_of_nonneg_left ratio (by positivity : (0 : ℝ) ≤ block)
    linarith
  have reciprocal : (1 - η) * (1 + η / (1 - η)) = 1 := by
    field_simp [ne_of_gt gap]
    ring
  have product : (1 - η) ^ block * (1 + η / (1 - η)) ^ block = 1 := by
    rw [← mul_pow, reciprocal, one_pow]
  have bound := mul_le_mul_of_nonneg_left two (pow_nonneg nonneg block)
  rw [product] at bound
  linarith

theorem polynomial_availability_schedule (depth count : Nat) (positive : 0 < depth)
    (noWrap : depth ≤ 64) {Suffix : Type*} [Fintype Suffix] [Nonempty Suffix]
    (accept : Trial depth count (Suffix := Suffix) → Prop)
    (η : ℝ) (ηpositive : 0 < η) (ηle : η ≤ 1) (block security : Nat)
    (enough : 1 ≤ (block : ℝ) * η) :
    probability (fun seed => ¬ CoversHeavy depth count positive noWrap accept η (block * security) seed) ≤
      (2 ^ depth : Nat) * (1 / 2 : ℝ) ^ security := by
  refine (coverage_failure_le depth count positive noWrap accept η ηpositive.le ηle _).trans ?_
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [pow_mul]
  exact pow_le_pow_left₀ (pow_nonneg (sub_nonneg.mpr ηle) block)
    (inverse_availability_block η ηpositive ηle block enough) security

#print axioms inverse_availability_block
#print axioms polynomial_availability_schedule

#print axioms acceptance_le_heavy_probability
#print axioms acceptance_le_heavy
#print axioms heavy_card_gt
#print axioms coverage_failure_le
end Whir.AuthenticatedResetSupport
