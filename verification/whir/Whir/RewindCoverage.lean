import Whir.SamplingProbability

/-! Coverage of actual stratified query positions across fresh independent reset tapes. These tapes do not change the committed statement or fixed prover coins. Coordinate coverage is not authenticated response availability: a malicious prover can withhold or malform its answer. No Fiat-Shamir reset interface is inferred. -/
namespace Whir.RewindCoverage
open Concrete SamplingProbability
open scoped BigOperators

abbrev QueryTape (depth count : Nat) := Fin ((count + 192 / depth - 1) / (192 / depth)) → E

/-- The actual sampler misses a coordinate precisely when every sampled position lies in its complement. -/
def Misses (depth count : Nat) (target : Fin (2 ^ depth)) (tape : QueryTape depth count) : Prop :=
  allQueriesHit depth count (Finset.univ.erase target) tape

def MissesAll (depth count rounds : Nat) (target : Fin (2 ^ depth))
    (seed : Fin rounds → QueryTape depth count) : Prop :=
  ∀ round, Misses depth count target (seed round)

private def splitUnit (A : Type*) : A ≃ Unit × A where
  toFun a := ((), a)
  invFun a := a.2
  left_inv _ := rfl
  right_inv a := by cases a with | mk unitValue a => cases unitValue; rfl

/-- Independence is proved from the product seed space, rather than asserted for adaptive prover replies. -/
theorem missesAll_probability (depth count rounds : Nat) (target : Fin (2 ^ depth)) :
    probability (MissesAll depth count rounds target) =
      probability (Misses depth count target) ^ rounds := by
  have product := coordinateEvent_probability
    (splitUnit (Fin rounds → QueryTape depth count))
    (fun _ tape => Misses depth count target tape)
  change probability (MissesAll depth count rounds target) =
    ∏ _ : Fin rounds, probability (Misses depth count target) at product
  simpa using product

/-- Exact finite-size miss fraction for the AM-GM envelope of the actual stratified law. -/
noncomputable def missFraction (depth : Nat) : ℝ :=
  ((2 ^ depth - 1 : Nat) : ℝ) / (2 ^ depth : Nat)

theorem misses_probability_le (depth count : Nat) (positive : 0 < depth) (noWrap : depth ≤ 64)
    (target : Fin (2 ^ depth)) :
    probability (Misses depth count target) ≤ missFraction depth ^ count := by
  have bound := actual_query_bound depth count positive noWrap (Finset.univ.erase target)
  change probability (allQueriesHit depth count (Finset.univ.erase target)) ≤ _
  simpa only [Misses, StratifiedDensity.globalDensity, missFraction,
    Finset.card_erase_of_mem (Finset.mem_univ target), Finset.card_univ, Fintype.card_fin] using bound

/-- The response-call schedule can use these exact fresh tape shapes at the same prefix. This proves only coordinate coverage of the messages. -/
theorem missesAll_probability_le (depth count rounds : Nat) (positive : 0 < depth)
    (noWrap : depth ≤ 64) (target : Fin (2 ^ depth)) :
    probability (MissesAll depth count rounds target) ≤ missFraction depth ^ (count * rounds) := by
  rw [missesAll_probability]
  calc
    probability (Misses depth count target) ^ rounds ≤ (missFraction depth ^ count) ^ rounds :=
      pow_le_pow_left₀ (by unfold probability; positivity)
        (misses_probability_le depth count positive noWrap target) rounds
    _ = missFraction depth ^ (count * rounds) := by rw [pow_mul]

/-- A finite-domain query position from the same chunk and stratum used by the actual sampler. -/
def sampledPosition (depth count : Nat) (positive : 0 < depth) (noWrap : depth ≤ 64)
    (tape : QueryTape depth count) (i : Fin count) : Fin (2 ^ depth) :=
  StratifiedDensity.placed (queryStratum count depth i)
    ((queryEquiv depth _ count
      (squeezeCount_capacity depth count positive (by omega)) tape).2 i)

theorem sampledPosition_actual (depth count : Nat) (positive : 0 < depth)
    (noWrap : depth ≤ 64) (tape : QueryTape depth count) (i : Fin count) :
    (sampledPosition depth count positive noWrap tape i).val =
      concretePlace count depth i.val
        (Layout.rawQuery depth (fun j => (Array.ofFn tape)[j]!.toNat) i.val) := by
  rw [concretePlace_eq]
  change Layout.placeQuery (queryStratum count depth i)
    (((queryEquiv depth _ count
      (squeezeCount_capacity depth count positive (by omega)) tape).2 i).val) = _
  rw [queryEquiv_rawQuery]

theorem misses_iff (depth count : Nat) (positive : 0 < depth) (noWrap : depth ≤ 64)
    (target : Fin (2 ^ depth)) (tape : QueryTape depth count) :
    Misses depth count target tape ↔
      ∀ i, sampledPosition depth count positive noWrap tape i ≠ target := by
  classical
  unfold Misses allQueriesHit
  rw [deriveQueries_eq depth count positive noWrap]
  simp only [Option.some.injEq]
  constructor
  · rintro ⟨qs, rfl, hit⟩ i equal
    have member := hit i
    rw [ArrayLayout.getElem!_tab _ _ _ i.isLt] at member
    rw [← sampledPosition_actual depth count positive noWrap tape i, equal] at member
    obtain ⟨q, hq, same⟩ := Finset.mem_image.mp member
    have : q = target := Fin.ext same
    simp [this] at hq
  · intro misses
    refine ⟨_, rfl, ?_⟩
    intro i
    rw [ArrayLayout.getElem!_tab _ _ _ i.isLt]
    rw [← sampledPosition_actual depth count positive noWrap tape i]
    exact Finset.mem_image.mpr
      ⟨_, Finset.mem_erase.mpr ⟨misses i, Finset.mem_univ _⟩, rfl⟩

/-- This is coordinate coverage; it deliberately does not promise that the prover answers those coordinates. -/
def Covers (depth count rounds : Nat) (positive : 0 < depth) (noWrap : depth ≤ 64)
    (seed : Fin rounds → QueryTape depth count) : Prop :=
  ∀ target : Fin (2 ^ depth), ∃ round i,
    sampledPosition depth count positive noWrap (seed round) i = target

theorem not_covers_iff (depth count rounds : Nat) (positive : 0 < depth)
    (noWrap : depth ≤ 64) (seed : Fin rounds → QueryTape depth count) :
    ¬ Covers depth count rounds positive noWrap seed ↔
      ∃ target, MissesAll depth count rounds target seed := by
  classical
  simp only [Covers, MissesAll, misses_iff depth count positive noWrap]
  push Not
  rfl

/-- Domain-wide coverage loss for the real stratified sampler, with no iid substitution. -/
theorem coverage_failure_probability_le (depth count rounds : Nat) (positive : 0 < depth)
    (noWrap : depth ≤ 64) :
    probability (fun seed : Fin rounds → QueryTape depth count =>
      ¬ Covers depth count rounds positive noWrap seed) ≤
        (2 ^ depth : Nat) * missFraction depth ^ (count * rounds) := by
  classical
  have union := Soundness.union_bound (fun target : Fin (2 ^ depth) =>
    Finset.univ.filter (MissesAll depth count rounds target))
  have events :
      (Finset.univ.filter fun seed : Fin rounds → QueryTape depth count =>
        ¬ Covers depth count rounds positive noWrap seed) =
      Finset.univ.biUnion (fun target : Fin (2 ^ depth) =>
        Finset.univ.filter (MissesAll depth count rounds target)) := by
    ext seed
    simp [not_covers_iff]
  rw [probability_eq_uniformProb, events]
  calc
    _ ≤ ∑ target : Fin (2 ^ depth),
        (Soundness.uniformProb (Finset.univ.filter
          (MissesAll depth count rounds target)) : ℝ) := by exact_mod_cast union
    _ = ∑ target : Fin (2 ^ depth), probability (MissesAll depth count rounds target) := by
      simp only [probability_eq_uniformProb]
    _ ≤ ∑ _ : Fin (2 ^ depth), missFraction depth ^ (count * rounds) :=
      Finset.sum_le_sum fun target _ => missesAll_probability_le depth count rounds positive noWrap target
    _ = _ := by simp

theorem missFraction_domain_power_le (depth : Nat) (positive : 0 < depth) :
    missFraction depth ^ (2 ^ depth) ≤ (1 / 2 : ℝ) := by
  let N := 2 ^ depth
  have two : 2 ≤ N := by
    dsimp [N]
    simpa using Nat.pow_le_pow_right (by decide : 1 ≤ 2) positive
  have predPositive : (0 : ℝ) < (N - 1 : Nat) := by exact_mod_cast (by omega : 0 < N - 1)
  have predCast : ((N - 1 : Nat) : ℝ) = (N : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ N)]
    norm_num
  have nPositive : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have nonneg : 0 ≤ missFraction depth := by unfold missFraction; positivity
  have atMostOne : missFraction depth ≤ 1 := by
    unfold missFraction
    exact (div_le_one nPositive).mpr (by exact_mod_cast (Nat.sub_le N 1))
  have bernoulli := one_add_mul_le_pow
    (show (-2 : ℝ) ≤ 1 / (N - 1 : Nat) by
      have : (0 : ℝ) ≤ 1 / (N - 1 : Nat) := by positivity
      linarith) (N - 1)
  have lower : (2 : ℝ) ≤ (1 + 1 / (N - 1 : Nat)) ^ (N - 1) := by
    have cancelled : ((N - 1 : Nat) : ℝ) * (1 / (N - 1 : Nat)) = 1 := by
      field_simp [ne_of_gt predPositive]
    rw [cancelled] at bernoulli
    norm_num only [one_add_one_eq_two] at bernoulli
    exact bernoulli
  have reciprocal : missFraction depth * (1 + 1 / (N - 1 : Nat)) = 1 := by
    unfold missFraction
    change ((N - 1 : Nat) : ℝ) / (N : ℝ) * (1 + 1 / (N - 1 : Nat)) = 1
    rw [predCast]
    field_simp [ne_of_gt nPositive, show (N : ℝ) - 1 ≠ 0 by linarith]
    ring
  have multiplied := mul_le_mul_of_nonneg_left lower
    (pow_nonneg nonneg (N - 1))
  have product : missFraction depth ^ (N - 1) *
      (1 + 1 / (N - 1 : Nat)) ^ (N - 1) = 1 := by
    rw [← mul_pow, reciprocal, one_pow]
  rw [product] at multiplied
  have predecessor : missFraction depth ^ (N - 1) ≤ (1 / 2 : ℝ) := by linarith
  change missFraction depth ^ N ≤ _
  have successor : N = (N - 1) + 1 := by omega
  rw [successor, pow_succ]
  exact (mul_le_of_le_one_right (pow_nonneg nonneg _) atMostOne).trans predecessor

/-- A polynomial reset schedule: N·security trials suffice for exponentially small coordinate-coverage loss. Answer availability and decoding proximity are not included. -/
theorem polynomial_schedule_coverage (depth count security : Nat) (positive : 0 < depth)
    (noWrap : depth ≤ 64) :
    probability (fun seed : Fin (2 ^ depth * security) → QueryTape depth count =>
      ¬ Covers depth count (2 ^ depth * security) positive noWrap seed) ≤
        (2 ^ depth : Nat) * (1 / 2 : ℝ) ^ (count * security) := by
  refine (coverage_failure_probability_le depth count _ positive noWrap).trans ?_
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [show count * (2 ^ depth * security) = 2 ^ depth * (count * security) by ring, pow_mul]
  exact pow_le_pow_left₀ (by unfold missFraction; positivity)
    (missFraction_domain_power_le depth positive) _

#print axioms missesAll_probability
#print axioms misses_probability_le
#print axioms missesAll_probability_le
#print axioms sampledPosition_actual
#print axioms misses_iff
#print axioms not_covers_iff
#print axioms coverage_failure_probability_le
#print axioms missFraction_domain_power_le
#print axioms polynomial_schedule_coverage

end Whir.RewindCoverage
