import XmssSecurity.Proof.CappedConcreteExecution
import XmssSecurity.Proof.PrecomputedBoundedSign
import XmssSecurity.Proof.SigningLogConsistency
import XmssSecurity.Proof.WinningEventReduction

open OracleComp OracleSpec ENNReal
open scoped BigOperators

namespace XmssSecurity

noncomputable def cappedMappedAdversaryImpl
    (_publicKey : PublicKey) (secretKey : SecretKey) :
    QueryImpl (OracleWorld + SigningSpec)
      (WriterT (QueryLog SigningSpec) (StateT (QueryCache HashSpec) ProbComp)) :=
  romImpl.writerTMapBase
    (forwardOracles + signingOracle Concrete.scheme secretKey)

theorem cappedMappedAdversary_cache_le
    (publicKey : PublicKey) (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialCache : QueryCache HashSpec)
    (result : (α × QueryLog SigningSpec) × QueryCache HashSpec)
    (hmem : result ∈ support
      (((simulateQ (cappedMappedAdversaryImpl publicKey secretKey) computation).run).run
        initialCache)) :
    initialCache ≤ result.2 := by
  apply xmssRom_cache_le
    ((simulateQ (forwardOracles + signingOracle Concrete.scheme secretKey)
      computation).run) initialCache result
  rw [QueryImpl.simulateQ_writerTMapBase_run]
  exact hmem

theorem cappedMappedAdversary_signingLog_consistent
    (publicKey : PublicKey) (secretKey : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) α)
    (initialCache : QueryCache HashSpec)
    (result : (α × QueryLog SigningSpec) × QueryCache HashSpec)
    (hmem : result ∈ support
      (((simulateQ (cappedMappedAdversaryImpl publicKey secretKey) computation).run).run
        initialCache))
    (keygenCache largerCache : QueryCache HashSpec)
    (hconsistent : PrecomputedKeyConsistent keygenCache secretKey)
    (hkeygenLe : keygenCache ≤ largerCache) (hle : result.2 ≤ largerCache) :
    SigningLogConsistent largerCache secretKey result.1.2 := by
  induction computation using OracleComp.inductionOn generalizing initialCache result with
  | pure value =>
      simp only [simulateQ_pure, WriterT.run_pure', StateT.run_pure,
        support_pure, Set.mem_singleton_iff] at hmem
      subst result
      intro request signature hreturned
      obtain ⟨entry, hentry, _⟩ := hreturned
      simp at hentry
  | query_bind input next ih =>
      rw [simulateQ_bind] at hmem
      rw [WriterT.run_bind', StateT.run_bind, mem_support_bind_iff] at hmem
      obtain ⟨⟨⟨output, queryLog⟩, middleCache⟩, hquery, hrestMapped⟩ := hmem
      rw [StateT.run_map, support_map] at hrestMapped
      obtain ⟨⟨⟨value, restLog⟩, finalCache⟩, hrest, heq⟩ := hrestMapped
      cases heq
      intro request signature hreturned
      obtain ⟨entry, hentry, hrequest, hsignature⟩ := hreturned
      change entry ∈ queryLog ++ restLog at hentry
      change finalCache ≤ largerCache at hle
      rw [List.mem_append] at hentry
      rcases hentry with hcurrent | hlater
      · cases input with
        | inl worldInput =>
            simp only [simulateQ_spec_query, cappedMappedAdversaryImpl,
              QueryImpl.writerTMapBase, QueryImpl.add_apply_inl, forwardOracles,
              WriterT.run_mk] at hquery
            erw [WriterT.run_liftM] at hquery
            rw [simulateQ_map, StateT.run_map, support_map] at hquery
            obtain ⟨⟨worldOutput, worldCache⟩, _hworld, heq⟩ := hquery
            cases heq
            simp at hcurrent
        | inr signingRequest =>
            simp only [simulateQ_spec_query, cappedMappedAdversaryImpl,
              QueryImpl.writerTMapBase, QueryImpl.add_apply_inr,
              signingOracle] at hquery
            rw [WriterT.run_mk] at hquery
            erw [QueryImpl.run_withLogging_apply] at hquery
            erw [simulateQ_bind] at hquery
            rw [StateT.run_bind, mem_support_bind_iff] at hquery
            obtain ⟨⟨signOutput, signCache⟩, hsign, hpure⟩ := hquery
            cases hpure
            simp only [List.mem_singleton] at hcurrent
            cases hcurrent
            simp only at hrequest hsignature
            have hmiddleFinal : signCache ≤ finalCache :=
              cappedMappedAdversary_cache_le publicKey secretKey (next signOutput)
                signCache ((value, restLog), finalCache) hrest
            rw [hrequest] at hsign
            rw [hsignature] at hsign
            change (some signature, signCache) ∈ support
              ((simulateQ romImpl
                (Concrete.precomputedCappedSign secretKey request.leafIndex
                  request.message)).run initialCache) at hsign
            apply Concrete.precomputedCappedSign_success_replay secretKey request
              keygenCache initialCache signCache largerCache signature hconsistent hkeygenLe
            · exact hsign
            · exact hmiddleFinal.trans hle
      · apply ih output middleCache ((value, restLog), finalCache) hrest hle
        exact ⟨entry, hlater, hrequest, hsignature⟩

theorem capped_detailed_execution_signingLog_consistent
    (adversary : Adversary)
    (execution : GameOutcome × QueryCache HashSpec)
    (hmem : execution ∈ support
      (detailedGameWithCache Concrete.scheme adversary)) :
    SigningLogConsistent execution.2 execution.1.secretKey execution.1.signingLog := by
  have hgame := hmem
  unfold detailedGameWithCache detailedGameCore at hgame
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hgame
  obtain ⟨⟨⟨publicKey, secretKey⟩, keyCache⟩, hkeygen, hrest⟩ := hgame
  unfold detailedGameAfterKeygen at hrest
  simp only at hrest
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hrest
  obtain ⟨⟨⟨forgery, signingLog⟩, adversaryCache⟩, hadversary, hverifyRest⟩ := hrest
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hverifyRest
  obtain ⟨⟨verified, finalCache⟩, hverify, hfinal⟩ := hverifyRest
  simp only [simulateQ_pure, StateT.run_pure, support_pure,
    Set.mem_singleton_iff] at hfinal
  subst execution
  simp only
  have hadversary' : ((forgery, signingLog), adversaryCache) ∈ support
      (((simulateQ (cappedMappedAdversaryImpl publicKey secretKey)
        (adversary.main publicKey)).run).run keyCache) := by
    rw [cappedMappedAdversaryImpl]
    rw [← QueryImpl.simulateQ_writerTMapBase_run]
    exact hadversary
  have hcacheLe : adversaryCache ≤ finalCache :=
    xmssRom_cache_le _ adversaryCache (verified, finalCache) hverify
  have hkeygen' : ((publicKey, secretKey), keyCache) ∈ support
      ((simulateQ romImpl Concrete.precomputedKeygen).run ∅) := by
    simpa only [Concrete.scheme] using hkeygen
  have hconsistent :=
    Concrete.precomputedKeygen_support_consistent
      ((publicKey, secretKey), keyCache) hkeygen'
  have hkeygenLeAdversary : keyCache ≤ adversaryCache :=
    cappedMappedAdversary_cache_le publicKey secretKey (adversary.main publicKey)
      keyCache ((forgery, signingLog), adversaryCache) hadversary'
  exact cappedMappedAdversary_signingLog_consistent publicKey secretKey
    (adversary.main publicKey) keyCache ((forgery, signingLog), adversaryCache)
    hadversary' keyCache finalCache hconsistent
      (hkeygenLeAdversary.trans hcacheLe) hcacheLe

theorem capped_detailed_execution_consistent
    (adversary : Adversary)
    (execution : GameOutcome × QueryCache HashSpec)
    (hmem : execution ∈ support
      (detailedGameWithCache Concrete.scheme adversary)) :
    ConcreteOutcomeConsistent execution.2 execution.1 :=
  capped_detailed_execution_consistent_of_signing adversary execution hmem
    (capped_detailed_execution_signingLog_consistent adversary execution hmem)

end XmssSecurity
