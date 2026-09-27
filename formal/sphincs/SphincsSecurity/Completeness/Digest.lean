import SphincsSecurity.Completeness.Search
import SphincsSecurity.Completeness.Fresh
import SphincsSecurity.Proof.Ots.EncodingProbability
import SphincsSecurity.Proof.Fts.MessageDeficitHashMoments

/-!
# The randomizer search

Each trial derives a randomizer from a fresh input, then hashes the message with it and keeps the
digest if its last index group is zero, which a fresh answer does with probability `1/1024`. The
second query need not be fresh: a randomizer can repeat one an earlier trial drew, and then the
digest is the earlier, rejected one. So the induction carries the set `R` of randomizers drawn so
far. A trial lands in `R` with probability at most `|R| / 2 ^ 128`, and otherwise its digest query
is fresh; either way one trial fails with probability at most `1023/1024 + 2 ^ 32 / 2 ^ 128`.
-/

open OracleComp OracleSpec ENNReal Finset

namespace SphincsSecurity.Completeness

open Concrete

/-- The input a digest trial hashes to derive its randomizer. -/
abbrev randInput (secretKey : Seeded.SecretKey) (message : Message) (trial : Nat) : HashInput :=
  randomizerHashInput secretKey.parameter secretKey.seed message (BitVec.ofNat 32 trial)

/-- The input a digest trial hashes to test its randomizer. -/
abbrev msgInput (secretKey : Seeded.SecretKey) (message : Message) (randomness : Randomness) :
    HashInput :=
  tweakableHashInput secretKey.parameter .message
    (messageDigestPayload secretKey.root message randomness)

theorem randInput_inj (secretKey : Seeded.SecretKey) (message : Message) {t t' : Nat}
    (ht : t < 2 ^ 32) (ht' : t' < 2 ^ 32)
    (h : randInput secretKey message t = randInput secretKey message t') : t = t' := by
  simp only [randInput, randomizerHashInput] at h
  have hfields := SphincsSecurity.fieldBytes_injective
    (List.append_cancel_right (List.append_cancel_right (List.append_cancel_right h)))
  simp only [TweakFields.mk.injEq, true_and, and_true] at hfields
  have hv := congrArg BitVec.toNat hfields
  simp only [BitVec.toNat_ofNat] at hv
  rwa [Nat.mod_eq_of_lt ht, Nat.mod_eq_of_lt ht'] at hv

theorem msgInput_inj (secretKey : Seeded.SecretKey) (message : Message)
    {randomness randomness' : Randomness}
    (h : msgInput secretKey message randomness = msgInput secretKey message randomness') :
    randomness = randomness' := by
  simp only [msgInput, tweakableHashInput, messageDigestPayload] at h
  have hpayload := List.append_cancel_left h
  exact SphincsSecurity.bytesLE_injective
    (List.append_cancel_right (List.append_cancel_right hpayload))

theorem randInput_ne_msgInput (secretKey : Seeded.SecretKey) (message : Message) (trial : Nat)
    (randomness : Randomness) :
    randInput secretKey message trial ≠ msgInput secretKey message randomness := by
  intro h
  have h' : fieldBytes ⟨7#8, 0#8, 0#8, 0#32, BitVec.ofNat 32 trial, 0#32⟩ ++ bytesLE 16 secretKey.parameter
        ++ (bytesLE 32 secretKey.seed ++ bytesLE 32 message)
      = fieldBytes (hashDomainFields .message) ++ bytesLE 16 secretKey.parameter
        ++ messageDigestPayload secretKey.root message randomness := by
    simpa only [randInput, msgInput, randomizerHashInput, tweakableHashInput, tweakBytes,
      List.append_assoc] using h
  exact fieldInput_ne_of_tag_ne secretKey.parameter
    (fields1 := ⟨7#8, 0#8, 0#8, 0#32, BitVec.ofNat 32 trial, 0#32⟩)
    (fields2 := hashDomainFields .message) (by simp [hashDomainFields, tweakFields]) _ _ h'

theorem cached_run (input : HashInput) (cache : QueryCache HashSpec) (answer : HashOutput)
    (hcached : cache input = some answer) :
    (randomOracle (spec := HashSpec) input).run cache = pure (answer, cache) :=
  QueryImpl.withCaching_run_some _ hcached

/-- The share of fresh answers the admissibility test rejects. -/
noncomputable def digestReject : ℝ≥0∞ :=
  Pr[fun u : HashOutput => ¬ Admissible (truncateMessageDigest u) |
    ($ᵗ HashOutput : ProbComp HashOutput)]

theorem digestReject_add : digestReject + (1024 : ℝ≥0∞)⁻¹ = 1 := by
  have h := probEvent_compl ($ᵗ HashOutput : ProbComp HashOutput)
    (fun u => Admissible (truncateMessageDigest u))
  have hfail : Pr[⊥ | ($ᵗ HashOutput : ProbComp HashOutput)] = 0 := by simp
  rw [SphincsSecurity.probEvent_uniformHashOutput_admissible, hfail, tsub_zero] at h
  rw [add_comm]
  exact h

theorem digestReject_le_one : digestReject ≤ 1 := probEvent_le_one

/-- Averaging a two-valued function over one uniform answer. -/
theorem tsum_uniform_ite (P : HashOutput → Prop) [DecidablePred P] (x y : ℝ≥0∞) :
    ∑' u : HashOutput, (Fintype.card HashOutput : ℝ≥0∞)⁻¹ * (if P u then x else y)
      = x * Pr[P | ($ᵗ HashOutput : ProbComp HashOutput)]
        + y * Pr[fun u => ¬ P u | ($ᵗ HashOutput : ProbComp HashOutput)] := by
  rw [probEvent_eq_tsum_ite ($ᵗ HashOutput : ProbComp HashOutput) P,
    probEvent_eq_tsum_ite ($ᵗ HashOutput : ProbComp HashOutput) (fun u => ¬ P u),
    ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
  refine tsum_congr fun u => ?_
  rw [probOutput_uniformSample]
  by_cases hu : P u <;> simp [hu, mul_comm]

/-- One trial's failure share. -/
noncomputable def digestFactor : ℝ≥0∞ := digestReject + (2 : ℝ≥0∞) ^ 32 / (2 : ℝ≥0∞) ^ 128

theorem probEvent_truncate_mem_le (R : Finset Randomness) (hR : R.card ≤ 2 ^ 32) :
    Pr[fun u : HashOutput => truncateHash u ∈ R | ($ᵗ HashOutput : ProbComp HashOutput)]
      ≤ (2 : ℝ≥0∞) ^ 32 / (2 : ℝ≥0∞) ^ 128 := by
  rw [SphincsSecurity.probEvent_uniform_truncateHash_mem R,
    show Fintype.card Digest = 2 ^ 128 by simp [digestBits], Nat.cast_pow, Nat.cast_ofNat]
  have hcast : (R.card : ℝ≥0∞) ≤ (2 : ℝ≥0∞) ^ 32 := by exact_mod_cast hR
  gcongr

set_option maxHeartbeats 1000000 in
/-- The randomizer search exhausts `n` trials with probability at most `digestFactor ^ n`. -/
theorem probEvent_signDigestLoop (sk : Seeded.SecretKey) (message : Message) :
    ∀ (n t : Nat) (cache : QueryCache HashSpec) (R : Finset Randomness),
      t + n ≤ 2 ^ 32 → R.card ≤ t →
      (∀ s, t ≤ s → s < 2 ^ 32 → cache (randInput sk message s) = none) →
      (∀ ρ, ρ ∉ R → cache (msgInput sk message ρ) = none) →
      Pr[fun r => r.1 = none | (simulateQ randomOracle
          (Seeded.signDigestLoop sk message n t
            : OracleComp HashSpec (Option (Randomness × Index × (IndexGroup → FtsLeaf))))).run cache]
        ≤ digestFactor ^ n := by
  intro n
  induction n with
  | zero => intro t cache R _ _ _ _; simp [Seeded.signDigestLoop]
  | succ n ih =>
      intro t cache R hbound hcard hrand hmsg
      rw [Seeded.signDigestLoop]
      simp only [deriveRandomizer, Seeded.signAttempt, messageDigest, oracleHash, HasQuery.query,
        simulateQ_bind, simulateQ_spec_query, StateT.run_bind, bind_assoc, pure_bind]
      rw [fresh_run _ cache (hrand t le_rfl (by omega))]
      refine (ENNReal.tsum_le_tsum (g := fun u => (Fintype.card HashOutput : ℝ≥0∞)⁻¹
        * (if truncateHash u ∈ R then digestFactor ^ n else digestReject * digestFactor ^ n))
        fun u => mul_le_mul_right ?_ _).trans ?_
      · dsimp only
        have hc1rand : ∀ s, t + 1 ≤ s → s < 2 ^ 32 →
            (QueryCache.cacheQuery cache (randInput sk message t) u) (randInput sk message s)
              = none := by
          intro s hs hsb
          exact (QueryCache.cacheQuery_of_ne cache u (fun h => by
            have := randInput_inj sk message hsb (by omega) h
            omega)).trans (hrand s (by omega) hsb)
        have hc1msg : ∀ ρ', (QueryCache.cacheQuery cache (randInput sk message t) u)
            (msgInput sk message ρ') = cache (msgInput sk message ρ') := fun ρ' =>
          QueryCache.cacheQuery_of_ne cache u (fun h => randInput_ne_msgInput sk message t ρ' h.symm)
        cases hmc : (QueryCache.cacheQuery cache (randInput sk message t) u)
            (msgInput sk message (truncateHash u)) with
        | some v =>
            have hρR : truncateHash u ∈ R := by
              by_contra hρ
              have hnone := hmsg _ hρ
              rw [← hc1msg, hmc] at hnone
              simp at hnone
            rw [if_pos hρR, cached_run _ _ v hmc, pure_bind]
            by_cases hadm : Admissible (truncateMessageDigest v)
            · simp [hadm]
            · simp only [hadm, if_false, simulateQ_pure, StateT.run_pure, pure_bind]
              exact ih (t + 1) _ R (by omega) (by omega) hc1rand
                (fun ρ' hρ' => (hc1msg ρ').trans (hmsg ρ' hρ'))
        | none =>
            rw [fresh_run _ _ hmc]
            refine (ENNReal.tsum_le_tsum (g := fun v => (Fintype.card HashOutput : ℝ≥0∞)⁻¹
              * (if Admissible (truncateMessageDigest v) then 0 else digestFactor ^ n))
              fun v => mul_le_mul_right ?_ _).trans ?_
            · dsimp only
              by_cases hadm : Admissible (truncateMessageDigest v)
              · simp [hadm]
              · simp only [hadm, if_false, simulateQ_pure, StateT.run_pure, pure_bind]
                refine ih (t + 1) _ (insert (truncateHash u) R) (by omega)
                  ((Finset.card_insert_le _ _).trans (by omega)) (fun s hs hsb => ?_)
                  (fun ρ' hρ' => ?_)
                · exact (QueryCache.cacheQuery_of_ne
                    (QueryCache.cacheQuery cache (randInput sk message t) u) v
                    (fun h => randInput_ne_msgInput sk message s (truncateHash u) h)).trans
                    (hc1rand s hs hsb)
                · rw [Finset.mem_insert, not_or] at hρ'
                  exact ((QueryCache.cacheQuery_of_ne
                    (QueryCache.cacheQuery cache (randInput sk message t) u) v
                    (fun h => hρ'.1 (msgInput_inj sk message h))).trans (hc1msg ρ')).trans
                    (hmsg ρ' hρ'.2)
            · rw [tsum_uniform_ite]
              simp only [zero_mul, zero_add]
              change digestFactor ^ n * digestReject ≤ _
              by_cases hρR : truncateHash u ∈ R
              · rw [if_pos hρR]
                exact mul_le_of_le_one_right' digestReject_le_one
              · rw [if_neg hρR, mul_comm]
      · rw [tsum_uniform_ite]
        have hcoll := probEvent_truncate_mem_le R (by omega)
        calc digestFactor ^ n * Pr[fun u : HashOutput => truncateHash u ∈ R |
                ($ᵗ HashOutput : ProbComp HashOutput)]
              + digestReject * digestFactor ^ n * Pr[fun u : HashOutput => ¬ truncateHash u ∈ R |
                ($ᵗ HashOutput : ProbComp HashOutput)]
            ≤ digestFactor ^ n * ((2 : ℝ≥0∞) ^ 32 / (2 : ℝ≥0∞) ^ 128)
              + digestReject * digestFactor ^ n * 1 :=
              add_le_add (mul_le_mul_right hcoll _) (mul_le_mul_right probEvent_le_one _)
          _ = digestFactor ^ (n + 1) := by
              have hF : digestFactor = digestReject + (2 : ℝ≥0∞) ^ 32 / (2 : ℝ≥0∞) ^ 128 := rfl
              generalize (2 : ℝ≥0∞) ^ 32 / (2 : ℝ≥0∞) ^ 128 = C at hF ⊢
              rw [pow_succ, hF]
              ring

end SphincsSecurity.Completeness
