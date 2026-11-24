module

public import XmssSecurity.Proof.CappedChain.ChainOriginProbability

@[expose] public section

open OracleSpec

namespace XmssSecurity.CappedChain

theorem outcomeChainValueHasKeygenOrigin_eq_table
    (keygenCache finalCache : QueryCache HashSpec) (secretKey : SecretKey)
    (outcome : GameOutcome) (chain : ChainIndex)
    (horigin : OutcomeChainValueHasKeygenOrigin keygenCache finalCache secretKey
      outcome chain) :
    ∃ encoding,
      TargetSum.decodeDigest
        (Concrete.CacheView.encodingHash finalCache secretKey.parameter
          outcome.forgery.leafIndex
          (outcome.forgery.message, outcome.forgery.signature.randomness)) =
        some encoding ∧
      outcome.forgery.signature.chainValue chain =
        keygenChainValueTable keygenCache secretKey chain
          (.inl outcome.forgery.leafIndex, encoding chain) := by
  obtain ⟨_verified, encoding, hdecode, hzero | hpositive⟩ := horigin
  · obtain ⟨hdigit, hvalue⟩ := hzero
    refine ⟨encoding, hdecode, ?_⟩
    rw [hvalue, keygenChainValueTable]
    simp [hdigit]
  · obtain ⟨previous, output, hprevious, hcached, houtput⟩ := hpositive
    refine ⟨encoding, hdecode, ?_⟩
    rw [keygenChainValueTable, ← hprevious]
    simp only [Wots.walk, zero_add, Concrete.CacheView.keyChainStep_inl,
      SecretKey.keyChainStart_inl]
    rw [Concrete.CacheView.chainStep_eq]
    · rw [Concrete.CacheView.digestAt_eq_of_cache_eq_some hcached]
      exact houtput.symm
    · exact previous.isLt

theorem winningOutcomeChainValueHasKeygenOrigin_eq_table
    (keygenCache finalCache : QueryCache HashSpec) (secretKey : SecretKey)
    (outcome : GameOutcome) (chain : ChainIndex)
    (horigin : WinningOutcomeChainValueHasKeygenOrigin keygenCache finalCache
      secretKey outcome chain) :
    ∃ encoding,
      TargetSum.decodeDigest
        (Concrete.CacheView.encodingHash finalCache secretKey.parameter
          outcome.forgery.leafIndex
          (outcome.forgery.message, outcome.forgery.signature.randomness)) =
        some encoding ∧
      outcome.forgery.signature.chainValue chain =
        keygenChainValueTable keygenCache secretKey chain
          (.inl outcome.forgery.leafIndex, encoding chain) :=
  outcomeChainValueHasKeygenOrigin_eq_table keygenCache finalCache secretKey
    outcome chain horigin.2

end XmssSecurity.CappedChain
