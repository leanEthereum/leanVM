import XmssSecurity.Proof.AdaptiveFreshTarget
import XmssSecurity.Proof.StatementLemmas
import XmssSecurity.Proof.ExpectedQueryCount

open OracleComp ENNReal

namespace XmssSecurity.Rom

open OracleSpec

noncomputable local instance : IsUniformSpec HashSpec :=
  IsUniformSpec.ofFintypeInhabited _

def IsRelevantHashQuery (relevant : HashInput → Prop) : OracleWorld.Domain → Prop
  | .inr input => relevant input
  | .inl _ => False

noncomputable instance (relevant : HashInput → Prop) :
    DecidablePred (IsRelevantHashQuery relevant) :=
  Classical.decPred _

/-- Only fresh hits at relevant hash inputs are charged, so unrelated hash domains consume no
collision budget. -/
theorem mixed_adaptive_truncated_output_fresh_relevant_hit_from_cache_le_expected
    {α : Type} (computation : OracleComp OracleWorld α)
    (relevant : HashInput → Prop) (target : HashInput → Digest)
    (cache : QueryCache HashSpec) :
    Pr[fun result => ∃ input output,
        result.2 input = some output ∧ cache input = none ∧ relevant input ∧
          truncateHash output = target input |
      (simulateQ romImpl computation).run cache] ≤
      expectedSimulatedQueryCount romImpl (IsRelevantHashQuery relevant)
        computation cache / ((2 ^ digestBits : Nat) : ENNReal) := by
  classical
  let digestCard : ENNReal := ((2 ^ digestBits : Nat) : ENNReal)
  induction computation using OracleComp.inductionOn generalizing cache with
  | pure value =>
      refine le_of_eq_of_le (b := 0) ?_ zero_le
      rw [simulateQ_pure]
      refine probEvent_eq_zero fun result hresult hhit => ?_
      change result ∈ support (pure (value, cache) : ProbComp _) at hresult
      rw [support_pure, Set.mem_singleton_iff] at hresult
      subst result
      obtain ⟨input, output, hcache, hnone, _⟩ := hhit
      simp [hnone] at hcache
  | query_bind query next ih =>
      rcases query with uniformIndex | hashInput
      · change Fin (uniformIndex + 1) → OracleComp OracleWorld α at next
        have hrun :
            (simulateQ romImpl
              (liftM (OracleWorld.query (.inl uniformIndex)) >>= next)).run cache =
            ((unifSpec.query uniformIndex : ProbComp _) >>= fun sampled =>
              (simulateQ romImpl (next sampled)).run cache) := by
          simp [StateT.run_bind, romImpl, unifFwdImpl,
            QueryImpl.liftTarget_apply, HasQuery.toQueryImpl_apply]
        have hcount :
            expectedSimulatedQueryCount romImpl (IsRelevantHashQuery relevant)
                (liftM (OracleWorld.query (.inl uniformIndex)) >>= next) cache =
              ∑' sampled, Pr[= sampled | (unifSpec.query uniformIndex : ProbComp _)] *
                expectedSimulatedQueryCount romImpl (IsRelevantHashQuery relevant)
                  (next sampled) cache := by
          rw [expectedSimulatedQueryCount_query_bind]
          simp only [IsRelevantHashQuery, ↓reduceIte, zero_add]
          change (∑' result, Pr[= result |
              (fun sampled => (sampled, cache)) <$>
                (unifSpec.query uniformIndex : ProbComp _)] *
                expectedSimulatedQueryCount romImpl (IsRelevantHashQuery relevant)
                  (next result.1) result.2) = _
          rw [tsum_probOutput_map_mul]
        rw [hrun, probEvent_bind_eq_tsum, hcount, div_eq_mul_inv,
          ← ENNReal.tsum_mul_right]
        apply ENNReal.tsum_le_tsum
        intro sampled
        rw [mul_assoc]
        gcongr
        exact ih sampled cache
      · change HashOutput → OracleComp OracleWorld α at next
        by_cases hcached : ∃ output, cache hashInput = some output
        · obtain ⟨output, houtput⟩ := hcached
          have hquery :
              (simulateQ romImpl
                (liftM (OracleWorld.query (.inr hashInput)))).run cache =
              pure ((show OracleWorld.Range (.inr hashInput) from output), cache) := by
            rw [simulateQ_spec_query]
            change (randomOracle (spec := HashSpec) hashInput).run cache = pure (output, cache)
            rw [QueryImpl.withCaching_run_some _ houtput]
          have hrun :
              (simulateQ romImpl
                (liftM (OracleWorld.query (.inr hashInput)) >>= next)).run cache =
              (simulateQ romImpl (next output)).run cache := by
            rw [simulateQ_bind, StateT.run_bind, hquery, pure_bind]
          have hcount :
              expectedSimulatedQueryCount romImpl (IsRelevantHashQuery relevant)
                  (liftM (OracleWorld.query (.inr hashInput)) >>= next) cache =
                (if relevant hashInput then 1 else 0) +
                  expectedSimulatedQueryCount romImpl
                    (IsRelevantHashQuery relevant) (next output) cache := by
            rw [expectedSimulatedQueryCount_query_bind]
            simp only [IsRelevantHashQuery]
            have hhandler :
                (romImpl (.inr hashInput)).run cache =
                  pure ((show OracleWorld.Range (.inr hashInput) from output), cache) := by
              change (randomOracle (spec := HashSpec) hashInput).run cache = _
              rw [QueryImpl.withCaching_run_some _ houtput]
              simp
            rw [hhandler, tsum_probOutput_pure_mul]
            convert rfl
          rw [hrun, hcount]
          by_cases hrelevant : relevant hashInput
          · simp only [hrelevant, if_true]
            exact (ih output cache).trans (by gcongr; exact le_add_left le_rfl)
          · simpa only [hrelevant, if_false, zero_add] using ih output cache
        · push Not at hcached
          have hnone : cache hashInput = none := Option.eq_none_iff_forall_ne_some.mpr hcached
          have hquery :
              (simulateQ romImpl
                (liftM (OracleWorld.query (.inr hashInput)))).run cache =
              (($ᵗ HashOutput) >>= fun output =>
                pure (output, cache.cacheQuery hashInput output) : ProbComp _) := by
            rw [simulateQ_spec_query]
            change (randomOracle (spec := HashSpec) hashInput).run cache = _
            rw [QueryImpl.withCaching_run_none _ hnone]
            simp [uniformSampleImpl, map_eq_bind_pure_comp]
          have hrun :
              (simulateQ romImpl
                (liftM (OracleWorld.query (.inr hashInput)) >>= next)).run cache =
              (($ᵗ HashOutput) >>= fun output =>
                (simulateQ romImpl (next output)).run
                  (cache.cacheQuery hashInput output)) := by
            rw [simulateQ_bind, StateT.run_bind, hquery]
            simp [monad_norm]
          have hcount :
              expectedSimulatedQueryCount romImpl (IsRelevantHashQuery relevant)
                  (liftM (OracleWorld.query (.inr hashInput)) >>= next) cache =
                (if relevant hashInput then 1 else 0) +
                  ∑' output, Pr[= output | $ᵗ HashOutput] *
                    expectedSimulatedQueryCount romImpl
                      (IsRelevantHashQuery relevant) (next output)
                        (cache.cacheQuery hashInput output) := by
            rw [expectedSimulatedQueryCount_query_bind]
            simp only [IsRelevantHashQuery]
            have hhandler : (romImpl (.inr hashInput)).run cache =
                (fun output : HashOutput =>
                  ((show OracleWorld.Range (.inr hashInput) from output),
                    cache.cacheQuery hashInput output)) <$>
                  ($ᵗ HashOutput) := by
              change (randomOracle (spec := HashSpec) hashInput).run cache = _
              rw [QueryImpl.withCaching_run_none _ hnone]
              simp [uniformSampleImpl]
            rw [hhandler, tsum_probOutput_map_mul]
            convert rfl
          rw [hrun, probEvent_bind_eq_tsum]
          by_cases hrelevant : relevant hashInput
          · have hrest : ∀ output : HashOutput,
                truncateHash output ≠ target hashInput →
                Pr[fun result => ∃ input candidateOutput,
                      result.2 input = some candidateOutput ∧ cache input = none ∧
                        relevant input ∧ truncateHash candidateOutput = target input |
                  (simulateQ romImpl (next output)).run
                    (cache.cacheQuery hashInput output)] ≤
                  expectedSimulatedQueryCount romImpl
                      (IsRelevantHashQuery relevant) (next output)
                        (cache.cacheQuery hashInput output) / digestCard := by
              intro output hmiss
              calc
                Pr[fun result => ∃ input candidateOutput,
                      result.2 input = some candidateOutput ∧ cache input = none ∧
                        relevant input ∧ truncateHash candidateOutput = target input |
                    (simulateQ romImpl (next output)).run
                      (cache.cacheQuery hashInput output)] ≤
                  Pr[fun result => ∃ input candidateOutput,
                      result.2 input = some candidateOutput ∧
                        (cache.cacheQuery hashInput output) input = none ∧
                        relevant input ∧ truncateHash candidateOutput = target input |
                    (simulateQ romImpl (next output)).run
                      (cache.cacheQuery hashInput output)] := by
                    apply probEvent_mono
                    intro result hresult
                    rintro ⟨input, candidateOutput, hfinal, hinitial,
                      hinputRelevant, htarget⟩
                    by_cases heq : input = hashInput
                    · subst input
                      have hle := xmssRom_cache_le (next output)
                        (cache.cacheQuery hashInput output) result hresult
                      have hcurrent := hle
                        (QueryCache.cacheQuery_self cache hashInput output)
                      rw [hcurrent] at hfinal
                      cases hfinal
                      exact (hmiss htarget).elim
                    · exact ⟨input, candidateOutput, hfinal, by
                        rw [QueryCache.cacheQuery_of_ne _ _ heq]
                        exact hinitial, hinputRelevant, htarget⟩
                _ ≤ _ := ih output (cache.cacheQuery hashInput output)
            calc
              ∑' output, Pr[= output | ($ᵗ HashOutput)] *
                  Pr[fun result => ∃ input candidateOutput,
                      result.2 input = some candidateOutput ∧ cache input = none ∧
                        relevant input ∧ truncateHash candidateOutput = target input |
                    (simulateQ romImpl (next output)).run
                      (cache.cacheQuery hashInput output)] ≤
                ∑' output, ((if truncateHash output = target hashInput then
                    Pr[= output | ($ᵗ HashOutput)] else 0) +
                  Pr[= output | ($ᵗ HashOutput)] *
                    (expectedSimulatedQueryCount romImpl
                      (IsRelevantHashQuery relevant) (next output)
                        (cache.cacheQuery hashInput output) / digestCard)) := by
                  apply ENNReal.tsum_le_tsum
                  intro output
                  by_cases heq : truncateHash output = target hashInput
                  · simp only [heq, ite_true]
                    calc
                      Pr[= output | ($ᵗ HashOutput)] * _ ≤
                          Pr[= output | ($ᵗ HashOutput)] * 1 :=
                        mul_le_mul' le_rfl probEvent_le_one
                      _ = Pr[= output | ($ᵗ HashOutput)] := mul_one _
                      _ ≤ Pr[= output | ($ᵗ HashOutput)] + _ := le_add_right le_rfl
                  · simp only [heq, ite_false, zero_add]
                    exact mul_le_mul' le_rfl (hrest output heq)
              _ = (∑' output : HashOutput,
                    if truncateHash output = target hashInput then
                      Pr[= output | ($ᵗ HashOutput)] else 0) +
                  (∑' output, Pr[= output | ($ᵗ HashOutput)] *
                    expectedSimulatedQueryCount romImpl
                      (IsRelevantHashQuery relevant) (next output)
                        (cache.cacheQuery hashInput output)) / digestCard := by
                rw [ENNReal.tsum_add]
                congr 1
                rw [div_eq_mul_inv, ← ENNReal.tsum_mul_right]
                apply tsum_congr
                intro output
                rw [div_eq_mul_inv, mul_assoc]
              _ ≤ digestCard⁻¹ +
                  (∑' output, Pr[= output | ($ᵗ HashOutput)] *
                    expectedSimulatedQueryCount romImpl
                      (IsRelevantHashQuery relevant) (next output)
                        (cache.cacheQuery hashInput output)) / digestCard := by
                gcongr
                rw [← probEvent_eq_tsum_ite]
                exact (uniform_truncate_probability (target hashInput)).le
              _ = (1 + ∑' output, Pr[= output | ($ᵗ HashOutput)] *
                    expectedSimulatedQueryCount romImpl
                      (IsRelevantHashQuery relevant) (next output)
                        (cache.cacheQuery hashInput output)) / digestCard := by
                simp [div_eq_mul_inv, add_mul]
              _ = expectedSimulatedQueryCount romImpl
                    (IsRelevantHashQuery relevant)
                    (liftM (OracleWorld.query (.inr hashInput)) >>= next) cache /
                  ((2 ^ digestBits : Nat) : ENNReal) := by
                rw [hcount, if_pos hrelevant]
          · have hcontinue : ∀ output : HashOutput,
                Pr[fun result => ∃ input candidateOutput,
                      result.2 input = some candidateOutput ∧ cache input = none ∧
                        relevant input ∧ truncateHash candidateOutput = target input |
                  (simulateQ romImpl (next output)).run
                    (cache.cacheQuery hashInput output)] ≤
                  expectedSimulatedQueryCount romImpl
                      (IsRelevantHashQuery relevant) (next output)
                        (cache.cacheQuery hashInput output) / digestCard := by
              intro output
              calc
                Pr[fun result => ∃ input candidateOutput,
                      result.2 input = some candidateOutput ∧ cache input = none ∧
                        relevant input ∧ truncateHash candidateOutput = target input |
                    (simulateQ romImpl (next output)).run
                      (cache.cacheQuery hashInput output)] ≤
                  Pr[fun result => ∃ input candidateOutput,
                      result.2 input = some candidateOutput ∧
                        (cache.cacheQuery hashInput output) input = none ∧
                        relevant input ∧ truncateHash candidateOutput = target input |
                    (simulateQ romImpl (next output)).run
                      (cache.cacheQuery hashInput output)] := by
                    apply probEvent_mono
                    intro result _hresult
                    rintro ⟨input, candidateOutput, hfinal, hinitial,
                      hinputRelevant, htarget⟩
                    have hne : input ≠ hashInput := by
                      intro heq
                      subst input
                      exact hrelevant hinputRelevant
                    exact ⟨input, candidateOutput, hfinal, by
                      rw [QueryCache.cacheQuery_of_ne _ _ hne]
                      exact hinitial, hinputRelevant, htarget⟩
                _ ≤ _ := ih output (cache.cacheQuery hashInput output)
            calc
              ∑' output, Pr[= output | ($ᵗ HashOutput)] *
                  Pr[fun result => ∃ input candidateOutput,
                      result.2 input = some candidateOutput ∧ cache input = none ∧
                        relevant input ∧ truncateHash candidateOutput = target input |
                    (simulateQ romImpl (next output)).run
                      (cache.cacheQuery hashInput output)] ≤
                ∑' output, Pr[= output | ($ᵗ HashOutput)] *
                  (expectedSimulatedQueryCount romImpl
                    (IsRelevantHashQuery relevant) (next output)
                      (cache.cacheQuery hashInput output) / digestCard) := by
                    apply ENNReal.tsum_le_tsum
                    intro output
                    exact mul_le_mul' le_rfl (hcontinue output)
              _ = (∑' output, Pr[= output | ($ᵗ HashOutput)] *
                    expectedSimulatedQueryCount romImpl
                      (IsRelevantHashQuery relevant) (next output)
                        (cache.cacheQuery hashInput output)) / digestCard := by
                rw [div_eq_mul_inv, ← ENNReal.tsum_mul_right]
                apply tsum_congr
                intro output
                rw [div_eq_mul_inv, mul_assoc]
              _ = expectedSimulatedQueryCount romImpl
                    (IsRelevantHashQuery relevant)
                    (liftM (OracleWorld.query (.inr hashInput)) >>= next) cache /
                  ((2 ^ digestBits : Nat) : ENNReal) := by
                rw [hcount, if_neg hrelevant, zero_add]

/-- An adaptive fresh-target collision is charged only to source queries at inputs moved by the
target map. -/
theorem mixed_adaptiveFreshDigestCollisionWith_le_expected_moved
    {α : Type} (computation : OracleComp OracleWorld α)
    (cache : QueryCache HashSpec) (targetInput : HashInput → HashInput)
    (win : α × QueryCache HashSpec → Prop)
    (hwin : ∀ result ∈ support ((simulateQ romImpl computation).run cache),
      win result → AdaptiveFreshDigestCollisionWith cache result.2 targetInput) :
    Pr[win | (simulateQ romImpl computation).run cache] ≤
      expectedSimulatedQueryCount romImpl
          (IsRelevantHashQuery fun input => targetInput input ≠ input)
        computation cache / ((2 ^ digestBits : Nat) : ENNReal) := by
  let experiment := (simulateQ romImpl computation).run cache
  let target : HashInput → Digest := fun input =>
    Concrete.CacheView.digestAt cache (targetInput input)
  calc
    Pr[win | experiment] ≤
        Pr[fun result => ∃ input output,
          result.2 input = some output ∧ cache input = none ∧
            targetInput input ≠ input ∧ truncateHash output = target input |
          experiment] := by
      apply probEvent_mono
      intro result hresult hresultWin
      obtain ⟨input, output, targetOutput, houtput, hfresh, htarget, hcollision⟩ :=
        hwin result hresult hresultWin
      have hcacheLe := xmssRom_cache_le computation cache result hresult
      have htargetFinal := hcacheLe htarget
      have hmoved : targetInput input ≠ input := by
        intro heq
        have htargetSelf := htarget
        rw [heq] at htargetSelf
        rw [hfresh] at htargetSelf
        cases htargetSelf
      refine ⟨input, output, houtput, hfresh, hmoved, ?_⟩
      calc
        truncateHash output = Concrete.CacheView.digestAt result.2 input :=
          (Concrete.CacheView.digestAt_eq_of_cache_eq_some houtput).symm
        _ = Concrete.CacheView.digestAt result.2 (targetInput input) := hcollision
        _ = truncateHash targetOutput :=
          Concrete.CacheView.digestAt_eq_of_cache_eq_some htargetFinal
        _ = Concrete.CacheView.digestAt cache (targetInput input) :=
          (Concrete.CacheView.digestAt_eq_of_cache_eq_some htarget).symm
    _ ≤ _ := mixed_adaptive_truncated_output_fresh_relevant_hit_from_cache_le_expected
      computation (fun input => targetInput input ≠ input) target cache

/-- A randomized prefix may choose the initial cache and target map. The collision is charged
only to continuation queries at inputs moved by the chosen map. -/
theorem mixed_adaptiveFreshDigestCollision_after_prefix_le_expectedMovedContinuation
    {α β : Type}
    (head : OracleComp OracleWorld β)
    (continuation : β → OracleComp OracleWorld α)
    (initialCache : QueryCache HashSpec)
    (targetInput : β → QueryCache HashSpec → HashInput → HashInput)
    (win : α × QueryCache HashSpec → Prop)
    (hwin : ∀ prefixResult ∈ support ((simulateQ romImpl head).run initialCache),
      ∀ result ∈ support
        ((simulateQ romImpl (continuation prefixResult.1)).run prefixResult.2),
        win result → AdaptiveFreshDigestCollisionWith prefixResult.2 result.2
          (targetInput prefixResult.1 prefixResult.2)) :
    Pr[win | (simulateQ romImpl (head >>= continuation)).run initialCache] ≤
      (∑' prefixResult,
        Pr[= prefixResult | (simulateQ romImpl head).run initialCache] *
          expectedSimulatedQueryCount romImpl
            (IsRelevantHashQuery fun input =>
              targetInput prefixResult.1 prefixResult.2 input ≠ input)
            (continuation prefixResult.1) prefixResult.2) /
        ((2 ^ digestBits : Nat) : ENNReal) := by
  rw [simulateQ_bind, StateT.run_bind, probEvent_bind_eq_tsum]
  calc
    ∑' prefixResult,
        Pr[= prefixResult | (simulateQ romImpl head).run initialCache] *
          Pr[win | (simulateQ romImpl
            (continuation prefixResult.1)).run prefixResult.2] ≤
      ∑' prefixResult,
        Pr[= prefixResult | (simulateQ romImpl head).run initialCache] *
          (expectedSimulatedQueryCount romImpl
            (IsRelevantHashQuery fun input =>
              targetInput prefixResult.1 prefixResult.2 input ≠ input)
            (continuation prefixResult.1) prefixResult.2 /
              ((2 ^ digestBits : Nat) : ENNReal)) := by
      apply ENNReal.tsum_le_tsum
      intro prefixResult
      by_cases hprefix : prefixResult ∈
          support ((simulateQ romImpl head).run initialCache)
      · gcongr
        exact mixed_adaptiveFreshDigestCollisionWith_le_expected_moved
          (continuation prefixResult.1) prefixResult.2
          (targetInput prefixResult.1 prefixResult.2) win
          (hwin prefixResult hprefix)
      · rw [probOutput_eq_zero_of_not_mem_support hprefix, zero_mul, zero_mul]
    _ = _ := by
      rw [div_eq_mul_inv, ← ENNReal.tsum_mul_right]
      apply tsum_congr
      intro prefixResult
      rw [div_eq_mul_inv, mul_assoc]

end XmssSecurity.Rom
