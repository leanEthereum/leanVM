import XmssSecurity.Proof.CappedGlobalChainHighCoverage
import XmssSecurity.Proof.CappedChain.ChainEventDecomposition
import XmssSecurity.Proof.TopStructural

/-!
# The origin of a top guess

A winning top guess forges the hidden honest top value at a coordinate no returned signature
revealed.
-/

open OracleComp OracleSpec

namespace XmssSecurity.CappedChain

set_option maxRecDepth 100000 in
set_option linter.constructorNameAsVariable false in
theorem topGuess_afterKeygen_has_origin
    (adversary : Adversary)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeygen : keyResult ∈ support
      ((simulateQ romImpl Concrete.scheme.keygen).run ∅))
    (execution : GameOutcome × QueryCache HashSpec)
    (hafter : execution ∈ support
      ((simulateQ romImpl
        (detailedGameAfterKeygen Concrete.scheme adversary keyResult.1.1 keyResult.1.2)).run
          keyResult.2))
    (hguess : WinningTopGuessOccurs execution.2 execution.1) :
    GlobalWinningOutcomeTopChainValueHasKeygenOrigin keyResult.2 execution.2 keyResult.1.2
      execution.1 := by
  obtain ⟨_hwon, chain, hbad, hrevealed⟩ := hguess
  obtain ⟨_hverified, encoding, forgedTopEncoding, hdecode, htopDecode, hbadTop⟩ := hbad
  obtain ⟨encoding', forgedTopEncoding', hdecode', htopDecode', hvalue⟩ := hrevealed
  have hencoding : encoding' = encoding := by
    rw [hdecode] at hdecode'
    exact (Option.some.inj hdecode').symm
  subst encoding'
  have htopEncoding : forgedTopEncoding' = forgedTopEncoding := by
    rw [htopDecode] at htopDecode'
    exact (Option.some.inj htopDecode').symm
  subst forgedTopEncoding'
  have hkeys := CappedLeaf.detailedGameAfterKeygen_keys_eq adversary keyResult.1.1 keyResult.1.2
    keyResult.2 execution hafter
  have hcacheLe := xmssRom_cache_le
    (detailedGameAfterKeygen Concrete.scheme adversary keyResult.1.1 keyResult.1.2)
    keyResult.2 execution hafter
  have hkeygen' : keyResult ∈ support
      ((simulateQ romImpl Concrete.precomputedKeygen).run ∅) := by
    simpa only [Concrete.scheme] using hkeygen
  have hold := Concrete.precomputedKeygen_support_oldKeygen keyResult hkeygen'
  let key := topKeyOf execution.1.forgery.leafIndex
  refine ⟨chain, forgedTopEncoding chain, ?_, ?_⟩
  · have hwalk := Concrete.keygen_chainWalk_eq_of_cache_le _ hold execution.2 hcacheLe
      (.inr key) chain (forgedTopEncoding chain).val
      (Nat.le_pred_of_lt (forgedTopEncoding chain).isLt)
    rw [hvalue, hkeys.2]
    unfold globalKeygenChainValueTable keygenChainValueTable
    simp only [Concrete.CacheView.keyChainStep_inr, SecretKey.keyChainStart_inr] at hwalk ⊢
    exact hwalk.symm
  · intro hmem
    rw [mem_returnedChainValueIndices_iff] at hmem
    rcases hmem with ⟨_, _, _, _, _, hkey, _⟩ |
      ⟨request, signature, randomness, topEncoding, _hreturned, htop, hkey, hdigit⟩
    · cases hkey
    · have hkey' : key = topKeyOf request.leafIndex := Sum.inr_injective hkey
      rw [← hkey'] at htop
      rw [hkeys.2] at hbadTop
      unfold Concrete.TopBadEventOccurs at hbadTop
      rw [htop] at hbadTop
      obtain ⟨_hvalid, hbackward⟩ := hbadTop
      exact (not_lt_of_ge hdigit) hbackward.1
