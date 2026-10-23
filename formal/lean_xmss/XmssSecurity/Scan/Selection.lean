import XmssSecurity.Proof.PrecomputedBoundedSignProbability
import XmssSecurity.Proof.CappedEncodingRejection
import XmssSecurity.Proof.RandomOracle
import XmssSecurity.Scan.LoopWalk

/-!
# The selection law of the scan signer

For one message and one cache, the scan `base, base + 1, ...` of
`Concrete.precomputedSignBoundedAttempts` returns a cached hit `y` with exactly the probability
`reach nextRand landing (scanStatus ...) y A base` of `LoopWalk`: a fresh position lands with
probability `landing`, and the cache grows only at positions the walk has left and, within
`2^128` attempts, never revisits.
-/

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.Scan

open LoopWalk

set_option maxRecDepth 100000

/-- The probability that a uniform oracle answer truncates to a valid digest. -/
noncomputable def landing : ℝ≥0∞ :=
  (TargetSum.validDigests.card : ℝ≥0∞) / 2 ^ digestBits

theorem probEvent_landing :
    Pr{let output ← $ᵗ HashOutput}[TargetSum.ValidDigest (truncateHash output)] =
      landing := by
  have h := Rom.evalDist_truncate_uniformHashOutput.prEvent_eq TargetSum.ValidDigest
  rw [prEvent_map] at h
  rw [h, SampleableType.prEvent_uniformSample]
  have hcard : Fintype.card Digest = 2 ^ digestBits := by simp
  rw [hcard, Nat.cast_pow, Nat.cast_ofNat]
  rfl

/-- What an attempt at `randomness` returns for the oracle answer `output`. -/
noncomputable def attemptResult (secretKey : SecretKey) (leafIndex : LeafIndex) (randomness : Randomness)
    (output : HashOutput) : Option Signature :=
  (TargetSum.decodeDigest (truncateHash output)).map
    (Concrete.precomputedSignWithEncoding secretKey leafIndex randomness)

theorem attempt_run (secretKey : SecretKey) (leafIndex : LeafIndex) (message : Message)
    (randomness : Randomness) (cache : QueryCache HashSpec) :
    (simulateQ randomOracle (Concrete.precomputedSignAttempt secretKey leafIndex message randomness :
      OracleComp HashSpec (Option Signature))).run cache =
      (fun z => (attemptResult secretKey leafIndex randomness z.1, z.2)) <$>
        (randomOracle (Concrete.CacheView.encodingInput secretKey.parameter leafIndex
          (message, randomness))).run cache := by
  unfold Concrete.precomputedSignAttempt Concrete.encodingHash Concrete.tweakableHash
    Concrete.oracleHash
  simp only [simulateQ_bind, StateT.run_bind, map_eq_bind_pure_comp, bind_assoc, pure_bind]
  simp [-QueryImpl.withCaching_apply, Concrete.CacheView.encodingInput]
  refine bind_congr fun z => ?_
  cases h : TargetSum.decodeDigest (truncateHash z.1) <;> simp [attemptResult, h]

theorem probEvent_not_landing :
    Pr{let output ← $ᵗ HashOutput}[¬TargetSum.ValidDigest (truncateHash output)] =
      1 - landing := by
  rw [OracleComp.prEvent_not_eq_one_sub, probEvent_landing]

theorem attemptResult_of_not_valid (secretKey : SecretKey) (leafIndex : LeafIndex)
    (randomness : Randomness) {output : HashOutput}
    (h : ¬TargetSum.ValidDigest (truncateHash output)) :
    attemptResult secretKey leafIndex randomness output = none := by
  unfold attemptResult
  cases hd : TargetSum.decodeDigest (truncateHash output) with
  | none => rfl
  | some encoding => exact absurd ⟨encoding, hd⟩ h

theorem attemptResult_of_valid (secretKey : SecretKey) (leafIndex : LeafIndex)
    (randomness : Randomness) {output : HashOutput}
    (h : TargetSum.ValidDigest (truncateHash output)) :
    ∃ signature, attemptResult secretKey leafIndex randomness output = some signature ∧
      signature.randomness = randomness := by
  obtain ⟨encoding, he⟩ := h
  exact ⟨Concrete.precomputedSignWithEncoding secretKey leafIndex randomness encoding,
    by simp [attemptResult, he], rfl⟩

/-- The status of the scan position `randomness` for one message in `cache`. -/
noncomputable def scanStatus (secretKey : SecretKey) (leafIndex : LeafIndex) (message : Message)
    (cache : QueryCache HashSpec) (randomness : Randomness) : St :=
  match cache (Concrete.CacheView.encodingInput secretKey.parameter leafIndex (message, randomness)) with
  | none => .fresh
  | some output => if TargetSum.ValidDigest (truncateHash output) then .hit else .miss

theorem scanStatus_cacheQuery_of_ne (secretKey : SecretKey) (leafIndex : LeafIndex)
    (message : Message) (cache : QueryCache HashSpec) {randomness other : Randomness}
    (h : other ≠ randomness) (output : HashOutput) :
    scanStatus secretKey leafIndex message
        (cache.cacheQuery (Concrete.CacheView.encodingInput secretKey.parameter leafIndex
          (message, randomness)) output) other =
      scanStatus secretKey leafIndex message cache other := by
  unfold scanStatus
  rw [QueryCache.cacheQuery_of_ne]
  intro heq
  exact h (congrArg Prod.snd (Concrete.CacheView.encodingInput_injective _ _ heq))

/-- The scan's successor `ρ ↦ ρ + 1`. -/
def nextRand : Equiv.Perm Randomness := Equiv.addRight 1

theorem nextRand_pow_apply (randomness : Randomness) (j : ℕ) :
    (nextRand ^ j) randomness = randomness + (j : Randomness) := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, ih]
      simp [nextRand, add_assoc]

theorem nextRand_trial (base : Randomness) (trial : ℕ) :
    nextRand (base + BitVec.ofNat randomnessBits trial) =
      base + BitVec.ofNat randomnessBits (trial + 1) := by
  simp [nextRand, BitVec.ofNat_add, add_assoc]

theorem trial_ne (base : Randomness) (trial k : ℕ) (hk : 0 < k) (hk' : k < 2 ^ randomnessBits) :
    base + BitVec.ofNat randomnessBits (trial + k) ≠ base + BitVec.ofNat randomnessBits trial := by
  intro h
  rw [BitVec.ofNat_add, ← add_assoc, add_eq_left] at h
  have := congrArg BitVec.toNat h
  simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk'] at this
  omega

theorem continuation_some (attempts trial : ℕ) (secretKey : SecretKey) (leafIndex : LeafIndex)
    (message : Message) (base : Randomness) (signature : Signature) (cache : QueryCache HashSpec) :
    Concrete.precomputedSignBoundedAttemptsContinuation attempts trial secretKey leafIndex message base
      (some signature, cache) = pure (some signature, cache) := by
  simp [Concrete.precomputedSignBoundedAttemptsContinuation]

theorem continuation_none (attempts trial : ℕ) (secretKey : SecretKey) (leafIndex : LeafIndex)
    (message : Message) (base : Randomness) (cache : QueryCache HashSpec) :
    Concrete.precomputedSignBoundedAttemptsContinuation attempts trial secretKey leafIndex message base
      (none, cache) = (simulateQ romImpl
        (Concrete.precomputedSignBoundedAttempts secretKey leafIndex message base attempts trial)).run
          cache := by
  simp [Concrete.precomputedSignBoundedAttemptsContinuation]

/-- **Selection law, from any trial.** The scan from trial `trial` returns the cached hit `y` with the
probability that the walk from `base + trial` reaches `y`, as long as the statuses `st` agree with the
cache on the positions it may visit. -/
theorem selection_eq_reach (secretKey : SecretKey) (leafIndex : LeafIndex) (message : Message)
    (base : Randomness) (st : Randomness → St) (y : Randomness) :
    ∀ (A trial : ℕ) (cache : QueryCache HashSpec), A ≤ 2 ^ randomnessBits →
      scanStatus secretKey leafIndex message cache y = .hit →
      (∀ j < A, scanStatus secretKey leafIndex message cache
          (base + BitVec.ofNat randomnessBits (trial + j)) =
        st (base + BitVec.ofNat randomnessBits (trial + j))) →
      Pr{let result ← ((simulateQ romImpl
          (Concrete.precomputedSignBoundedAttempts secretKey leafIndex message base A trial)).run
            cache)}[∃ s, result.1 = some s ∧ s.randomness = y] =
        reach nextRand landing st y A (base + BitVec.ofNat randomnessBits trial)
  | 0, trial, cache, _, _, _ => by
      simp [Concrete.precomputedSignBoundedAttempts, reach]
  | A + 1, trial, cache, hA, hy, hst => by
      set r := base + BitVec.ofNat randomnessBits trial with hr
      have hnext : nextRand r = base + BitVec.ofNat randomnessBits (trial + 1) :=
        nextRand_trial base trial
      have hstr : scanStatus secretKey leafIndex message cache r = st r := by
        simpa using hst 0 (Nat.succ_pos A)
      have hshift : ∀ j < A, scanStatus secretKey leafIndex message cache
          (base + BitVec.ofNat randomnessBits (trial + 1 + j)) =
            st (base + BitVec.ofNat randomnessBits (trial + 1 + j)) := fun j hj => by
        rw [show trial + 1 + j = trial + (j + 1) by omega]
        exact hst (j + 1) (by omega)
      have ih := selection_eq_reach secretKey leafIndex message base st y A (trial + 1)
      rw [Concrete.precomputedSignBoundedAttempts_run_succ_eq, attempt_run]
      cases hc : cache (Concrete.CacheView.encodingInput secretKey.parameter leafIndex (message, r)) with
      | some output =>
          rw [randomOracle, QueryImpl.withCaching_run_some _ hc, map_pure, pure_bind]
          by_cases hv : TargetSum.ValidDigest (truncateHash output)
          · obtain ⟨signature, hsig, hrand⟩ := attemptResult_of_valid secretKey leafIndex r hv
            rw [hsig, continuation_some, prEvent_pure]
            by_cases hry : r = y
            · subst hry
              rw [reach_self, ite_eq_left ⟨signature, rfl, hrand⟩]
            · have hhit : st r = .hit := by
                rw [← hstr]
                simp [scanStatus, hc, hv]
              rw [reach_succ_hit A hry hhit, ite_eq_right]
              rintro ⟨s, hs, hsy⟩
              cases hs
              exact hry (hrand.symm.trans hsy)
          · have hmiss : st r = .miss := by
              rw [← hstr]
              simp [scanStatus, hc, hv]
            have hry : r ≠ y := by
              rintro rfl
              rw [hy] at hstr
              rw [← hstr] at hmiss
              cases hmiss
            rw [attemptResult_of_not_valid secretKey leafIndex r hv, continuation_none,
              reach_succ_miss A hry hmiss, hnext]
            exact ih cache (by omega) hy hshift
      | none =>
          have hfresh : st r = .fresh := by
            rw [← hstr]
            simp [scanStatus, hc]
          have hry : r ≠ y := by
            rintro rfl
            rw [hy] at hstr
            rw [← hstr] at hfresh
            cases hfresh
          rw [randomOracle_run_none_eq_uniformHashOutput _ _ hc, Functor.map_map, bind_map_left]
          rw [OracleComp.prEvent_bind_eq_tsum, reach_succ_fresh A hry hfresh, hnext,
            ← probEvent_not_landing, OracleComp.prEvent_eq_tsum_ite, ← ENNReal.tsum_mul_right]
          refine tsum_congr fun output => ?_
          by_cases hv : TargetSum.ValidDigest (truncateHash output)
          · obtain ⟨signature, hsig, hrand⟩ := attemptResult_of_valid secretKey leafIndex r hv
            rw [hsig, continuation_some, prEvent_pure, ite_eq_right, ite_eq_right (not_not.mpr hv), zero_mul,
              mul_zero]
            rintro ⟨s, hs, hsy⟩
            cases hs
            exact hry (hrand.symm.trans hsy)
          · rw [attemptResult_of_not_valid secretKey leafIndex r hv, continuation_none, ite_eq_left hv,
              uniformHashOutput, ih _ (by omega)]
            · rw [scanStatus_cacheQuery_of_ne _ _ _ _ (Ne.symm hry)]
              exact hy
            · intro j hj
              rw [scanStatus_cacheQuery_of_ne _ _ _ _ ?_]
              · exact hshift j hj
              · rw [hr, show trial + 1 + j = trial + (j + 1) by omega]
                exact trial_ne base trial (j + 1) (by omega) (by omega)

/-- **Selection law.** The scan from `base` returns a cached hit `y` with the probability that the walk
over the cache's statuses reaches `y` from `base`. -/
theorem selection_eq (secretKey : SecretKey) (leafIndex : LeafIndex) (message : Message)
    (cache : QueryCache HashSpec) (base y : Randomness) {A : ℕ} (hA : A ≤ 2 ^ randomnessBits)
    (hy : scanStatus secretKey leafIndex message cache y = .hit) :
    Pr{let result ← ((simulateQ romImpl
        (Concrete.precomputedSignBoundedAttempts secretKey leafIndex message base A 0)).run cache)}[∃ s, result.1 = some s ∧ s.randomness = y] =
      reach nextRand landing (scanStatus secretKey leafIndex message cache) y A base := by
  simpa using selection_eq_reach secretKey leafIndex message base
    (scanStatus secretKey leafIndex message cache) y A 0 cache hA hy (fun _ _ => rfl)

theorem signingAttemptLimit_le : signingAttemptLimit ≤ 2 ^ randomnessBits := by
  unfold signingAttemptLimit randomnessBits
  exact Nat.pow_le_pow_right (by norm_num) (by norm_num)

noncomputable local instance : SampleableType Randomness :=
  SampleableType.ofFintype Randomness

/-- **Selection law, averaged over the start.** -/
theorem selection_uniform_eq (secretKey : SecretKey) (leafIndex : LeafIndex) (message : Message)
    (cache : QueryCache HashSpec) (y : Randomness)
    (hy : scanStatus secretKey leafIndex message cache y = .hit) :
    Pr{let result ← (do
      let base ← $ᵗ Randomness
      (simulateQ romImpl (Concrete.precomputedSignBoundedAttempts secretKey leafIndex message base
        signingAttemptLimit 0)).run cache)}[∃ s, result.1 = some s ∧ s.randomness = y] =
      (∑ r, reach nextRand landing (scanStatus secretKey leafIndex message cache) y
        signingAttemptLimit r) * ((2 ^ randomnessBits : ℕ) : ℝ≥0∞)⁻¹ := by
  rw [OracleComp.prEvent_bind_eq_tsum, tsum_fintype, Finset.sum_mul]
  refine Finset.sum_congr rfl fun base _ => ?_
  rw [selection_eq secretKey leafIndex message cache base y signingAttemptLimit_le hy,
    SampleableType.prEvent_uniformSample_eq_singleton, card_randomness, mul_comm]

end XmssSecurity.Scan