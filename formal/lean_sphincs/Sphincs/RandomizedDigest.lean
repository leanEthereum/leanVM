import Sphincs.World
import Sphincs.Digest

/-! Grinding from a truly uniform start `ρ`, scanning `ρ, ρ + 1, ...`, including cache hits. -/

open OracleComp OracleSpec ENNReal Finset

namespace Sphincs.Completeness

open Concrete

variable [Params]

/-- Exact operational law of one step of the scan: the digest of the current randomizer is answered
by the consistent random oracle; on a miss the scan continues from the next randomizer. -/
theorem run_randomizedDigest_succ (sk : Seeded.SecretKey) (message : Message) (n : Nat)
    (ρ : Randomness) (cache : QueryCache HashSpec) :
    (simulateQ randomOracle (Randomized.scanLoop sk message (n + 1) ρ)).run cache =
      (randomOracle (spec := HashSpec) (msgInput sk message ρ)).run cache >>= fun r =>
        if Landed sk.parameter (blockIndex r.1) then pure (some ρ, r.2)
        else (simulateQ randomOracle (Randomized.scanLoop sk message n (ρ + 1))).run r.2 := by
  rw [Randomized.scanLoop]
  simp only [Seeded.signAttempt, messageDigestCall, oracleHash, HasQuery.query,
    simulateQ_bind, simulateQ_spec_query, StateT.run_bind, bind_assoc]
  apply bind_congr
  intro r
  split <;> simp [simulateQ_pure, StateT.run_pure]

/-- Exact operational law of the randomized grinding loop: the start is sampled for free, then the
scan runs against the shared random oracle. -/
theorem run_randomizedDigest_start (sk : Seeded.SecretKey) (message : Message) (n : Nat)
    (cache : QueryCache HashSpec) :
    (simulateQ romImpl (Randomized.signDigestLoop sk message n)).run cache =
      ($ᵗ Randomness : ProbComp Randomness) >>= fun ρ =>
        (simulateQ randomOracle (Randomized.scanLoop sk message n ρ)).run cache := by
  rw [Randomized.signDigestLoop, simulateQ_bind, StateT.run_bind, run_lift_prob]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
  apply bind_congr
  intro ρ
  rw [simulate_lift_hash]

omit [Params] in
theorem tsum_randomness_ite (P : Randomness → Prop) [DecidablePred P] (x y : ℝ≥0∞) :
    ∑' ρ : Randomness, (Fintype.card Randomness : ℝ≥0∞)⁻¹ * (if P ρ then x else y) =
      x * Pr{let x ← ($ᵗ Randomness : ProbComp Randomness)}[P x] +
        y * Pr{let ρ ← ($ᵗ Randomness : ProbComp Randomness)}[¬P ρ] := by
  rw [OracleComp.prEvent_eq_tsum_ite ($ᵗ Randomness : ProbComp Randomness) P,
    OracleComp.prEvent_eq_tsum_ite ($ᵗ Randomness : ProbComp Randomness) (fun ρ => ¬P ρ),
    ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
  refine tsum_congr fun ρ => ?_
  rw [SampleableType.prEvent_uniformSample_eq_singleton]
  by_cases h : P ρ <;> simp [h, mul_comm]

omit [Params] in
theorem randomness_add_succ (ρ : Randomness) (i : Nat) :
    ρ + 1 + BitVec.ofNat digestBits i = ρ + BitVec.ofNat digestBits (i + 1) := by
  rw [BitVec.ofNat_add, BitVec.add_assoc, BitVec.add_comm 1 _]
  rfl

omit [Params] in
theorem randomness_add_ne (ρ : Randomness) {i : Nat} (hpos : 0 < i) (hi : i < 2 ^ 128) :
    ρ + BitVec.ofNat digestBits i ≠ ρ := by
  intro h
  have hzero : BitVec.ofNat digestBits i = 0#digestBits := by
    have hsub := congrArg (fun x => x - ρ) h
    simpa [BitVec.add_comm ρ, BitVec.add_sub_cancel] using hsub
  have hnat := congrArg BitVec.toNat hzero
  rw [BitVec.toNat_ofNat, show (2 : Nat) ^ digestBits = 2 ^ 128 from rfl,
    Nat.mod_eq_of_lt hi] at hnat
  simp at hnat
  omega

omit [Params] in
/-- A uniform start puts one of its `n` scanned randomizers in a set `R` with probability at most
`n |R| / 2^128`. -/
theorem probEvent_randomness_mem_le (R : Finset Randomness) (n : Nat) :
    Pr{let ρ ← ($ᵗ Randomness : ProbComp Randomness)}[∃ i < n, ρ + BitVec.ofNat digestBits i ∈ R] ≤
      ((n * R.card : Nat) : ℝ≥0∞) / (2 : ℝ≥0∞) ^ 128 := by
  classical
  rw [SampleableType.prEvent_uniformSample,
    show Fintype.card Randomness = 2 ^ 128 by simp [digestBits], Nat.cast_pow, Nat.cast_ofNat]
  refine ENNReal.div_le_div_right (Nat.cast_le.mpr ?_) _
  calc (Finset.univ.filter fun ρ : Randomness => ∃ i < n, ρ + BitVec.ofNat digestBits i ∈ R).card
      ≤ ((Finset.range n ×ˢ R).image fun p : Nat × Randomness =>
          p.2 - BitVec.ofNat digestBits p.1).card := by
        refine Finset.card_le_card fun ρ hρ => ?_
        obtain ⟨i, hi, hmem⟩ := (Finset.mem_filter.mp hρ).2
        exact Finset.mem_image.mpr ⟨(i, ρ + BitVec.ofNat digestBits i),
          Finset.mem_product.mpr ⟨Finset.mem_range.mpr hi, hmem⟩, BitVec.add_sub_cancel _ _⟩
    _ ≤ (Finset.range n ×ˢ R).card := Finset.card_image_le
    _ = n * R.card := by rw [Finset.card_product, Finset.card_range]

/-- The scan from a start whose `n` randomizers have fresh digest inputs exhausts its budget with
probability at most the rejection share to the `n`. The cache hypothesis concerns digest inputs
only: `R` holds the randomizers whose digest may already be cached. -/
theorem probEvent_scanLoop (sk : Seeded.SecretKey) (message : Message) :
    ∀ (n : Nat) (ρ : Randomness) (cache : QueryCache HashSpec) (R : Finset Randomness),
      n ≤ 2 ^ 128 →
      (∀ ρ', ρ' ∉ R → cache (msgInput sk message ρ') = none) →
      (∀ i < n, ρ + BitVec.ofNat digestBits i ∉ R) →
      Pr{let r ← (simulateQ randomOracle (Randomized.scanLoop sk message n ρ)).run cache}[r.1 = none]
      ≤ digestReject sk.parameter ^ n := by
  intro n
  induction n with
  | zero => intro ρ cache R _ _ _; simp [Randomized.scanLoop]
  | succ n ih =>
      intro ρ cache R hbound hmsg havoid
      have hρ : ρ ∉ R := by simpa using havoid 0 (Nat.succ_pos n)
      rw [run_randomizedDigest_succ, fresh_run _ _ (hmsg ρ hρ)]
      refine (ENNReal.tsum_le_tsum (g := fun answer => (Fintype.card HashOutput : ℝ≥0∞)⁻¹ *
        (if Landed sk.parameter (blockIndex answer) then 0
          else digestReject sk.parameter ^ n))
        fun answer => mul_le_mul_right ?_ _).trans ?_
      · split
        · simp
        · refine ih (ρ + 1) _ (insert ρ R) (by omega) ?_ ?_
          · intro ρ' hρ'
            rw [Finset.mem_insert, not_or] at hρ'
            exact (QueryCache.cacheQuery_of_ne cache answer
              (fun h => hρ'.1 (msgInput_inj sk message h))).trans (hmsg ρ' hρ'.2)
          · intro i hi
            rw [randomness_add_succ, Finset.mem_insert, not_or]
            exact ⟨randomness_add_ne ρ (Nat.succ_pos i) (by omega), havoid (i + 1) (by omega)⟩
      · rw [tsum_uniform_ite]
        simp only [zero_mul, zero_add]
        change digestReject sk.parameter ^ n * digestReject sk.parameter ≤ _
        rw [pow_succ]

/-- The uniform start: the loop exhausts its budget with probability at most the rejection share
to the `n`, plus the chance `n |R| / 2^128` that the scan meets a randomizer whose digest input may
already be cached. -/
theorem probEvent_randomizedDigest (sk : Seeded.SecretKey) (message : Message)
    (n : Nat) (cache : QueryCache HashSpec) (R : Finset Randomness) (hn : n ≤ 2 ^ 128)
    (hmsg : ∀ ρ, ρ ∉ R → cache (msgInput sk message ρ) = none) :
    Pr{let r ← (simulateQ romImpl (Randomized.signDigestLoop sk message n)).run cache}[r.1 = none]
    ≤ digestReject sk.parameter ^ n + ((n * R.card : Nat) : ℝ≥0∞) / (2 : ℝ≥0∞) ^ 128 := by
  classical
  rw [run_randomizedDigest_start, OracleComp.prEvent_bind_eq_tsum]
  simp only [SampleableType.prEvent_uniformSample_eq_singleton]
  refine (ENNReal.tsum_le_tsum (g := fun ρ => (Fintype.card Randomness : ℝ≥0∞)⁻¹ *
    (if ∃ i < n, ρ + BitVec.ofNat digestBits i ∈ R then 1
      else digestReject sk.parameter ^ n))
    fun ρ => mul_le_mul_right ?_ _).trans ?_
  · split
    next => exact (prEvent_le_one _)
    next hfree =>
      exact probEvent_scanLoop sk message n ρ cache R hn hmsg
        (fun i hi hmem => hfree ⟨i, hi, hmem⟩)
  · rw [tsum_randomness_ite, one_mul, add_comm]
    exact add_le_add (mul_le_of_le_one_right' (prEvent_le_one _))
      (probEvent_randomness_mem_le R n)

/-- The randomized grinding loop exhausts its full budget with probability at most `2^(-2^(b+5))`
from a cache with no message-digest inputs. -/
theorem randomized_digest_exhaustion_bound (sk : Seeded.SecretKey) (message : Message)
    (cache : QueryCache HashSpec) (hfresh : ∀ ρ, cache (msgInput sk message ρ) = none) :
    Pr{let r ← (simulateQ romImpl (Randomized.signDigestLoop sk message digestAttemptLimit)).run cache}[r.1 = none]
      ≤ (2⁻¹ : ℝ≥0∞) ^ (2 ^ (subtreeHeight + 5)) := by
  refine (probEvent_randomizedDigest sk message digestAttemptLimit cache ∅
    (by simp [digestAttemptLimit]) (fun ρ _ => hfresh ρ)).trans ?_
  rw [Finset.card_empty, Nat.mul_zero, Nat.cast_zero, ENNReal.zero_div, add_zero]
  exact (pow_le_pow_left₀ (by positivity) le_self_add _).trans (digestFactor_pow_bound sk.parameter)

end Sphincs.Completeness
