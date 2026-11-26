module

public import XmssSecurity.Proof.CappedEncodingSourceImpl
public import XmssSecurity.Proof.CappedUnifiedStructuralCollision

@[expose] public section

/-!
# The structural collisions' bound on the source game

`keygenStructuralTargetInput` fixes every encoding input, so an encoding hash query is never a moved
query (`encodingHashQuery_structuralQuery_disjoint`). The structural collisions' probability is at
most `expectedPostKeygenStructuralQueries` over `2^digestBits`
(`winningStructuralCollision_probability_le_expectedPostKeygenStructuralQueries`), the expected
number of moved queries after key generation counted on the unlogged source game
(`cappedSourceUnloggedDetailedGameAfterKeygen`), a map of the detailed game and so with the same
count (`expectedStructuralQueries_detailed_eq_source`).
-/

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

theorem keygenChainTargetInput_encodingInput_eq_self
    (secretKey : SecretKey) (cache : QueryCache HashSpec)
    (leafIndex : LeafIndex) (payload : Message × Randomness) :
    keygenChainTargetInput secretKey cache
      (Concrete.CacheView.encodingInput secretKey.parameter leafIndex payload) =
    Concrete.CacheView.encodingInput secretKey.parameter leafIndex payload := by
  unfold keygenChainTargetInput
  split
  · rename_i h
    obtain ⟨value, hinput⟩ := h.choose_spec
    have hdomain := domain_eq_of_tweakableHashInput_eq secretKey.parameter hinput
    cases hdomain
  · rfl

theorem CappedLeaf.keygenLeafTargetInput_encodingInput_eq_self
    (secretKey : SecretKey) (cache : QueryCache HashSpec)
    (leafIndex : LeafIndex) (payload : Message × Randomness) :
    CappedLeaf.keygenLeafTargetInput secretKey cache
      (Concrete.CacheView.encodingInput secretKey.parameter leafIndex payload) =
    Concrete.CacheView.encodingInput secretKey.parameter leafIndex payload := by
  unfold CappedLeaf.keygenLeafTargetInput
  split
  · rename_i h
    obtain ⟨endpoints, hinput⟩ := h.choose_spec
    have hdomain := domain_eq_of_tweakableHashInput_eq secretKey.parameter hinput
    cases hdomain
  · rfl

theorem CappedMerkle.keygenMerkleTargetInput_encodingInput_eq_self
    (secretKey : SecretKey) (cache : QueryCache HashSpec)
    (leafIndex : LeafIndex) (payload : Message × Randomness) :
    CappedMerkle.keygenMerkleTargetInput secretKey cache
      (Concrete.CacheView.encodingInput secretKey.parameter leafIndex payload) =
    Concrete.CacheView.encodingInput secretKey.parameter leafIndex payload := by
  unfold CappedMerkle.keygenMerkleTargetInput
  split
  · rename_i h
    obtain ⟨left, right, hinput⟩ := h.choose_spec
    have hdomain := domain_eq_of_tweakableHashInput_eq secretKey.parameter hinput
    cases hdomain
  · rfl

@[simp]
theorem keygenStructuralTargetInput_encodingInput
    (secretKey : SecretKey) (cache : QueryCache HashSpec)
    (leafIndex : LeafIndex) (payload : Message × Randomness) :
    keygenStructuralTargetInput secretKey cache
      (Concrete.CacheView.encodingInput secretKey.parameter leafIndex payload) =
    Concrete.CacheView.encodingInput secretKey.parameter leafIndex payload := by
  unfold keygenStructuralTargetInput
  rw [keygenChainTargetInput_encodingInput_eq_self,
    CappedLeaf.keygenLeafTargetInput_encodingInput_eq_self,
    CappedMerkle.keygenMerkleTargetInput_encodingInput_eq_self,
    CappedTop.keygenTopTargetInput_encodingInput]

theorem encodingHashQuery_structuralQuery_disjoint
    (secretKey : SecretKey) (cache : QueryCache HashSpec)
    (input : OracleWorld.Domain) :
    ¬(CappedEncodingMonitor.IsEncodingHashQuery secretKey.parameter input ∧
      Rom.IsRelevantHashQuery (fun hashInput =>
        keygenStructuralTargetInput secretKey cache hashInput ≠ hashInput) input) := by
  cases input with
  | inl index => simp [CappedEncodingMonitor.IsEncodingHashQuery]
  | inr hashInput =>
      intro hboth
      rcases hboth with ⟨hencoding, hstructural⟩
      change (encodingInputLeafIndex? secretKey.parameter hashInput).isSome at hencoding
      change keygenStructuralTargetInput secretKey cache hashInput ≠ hashInput at hstructural
      cases hleafIndex : encodingInputLeafIndex? secretKey.parameter hashInput with
      | none => simp [hleafIndex] at hencoding
      | some leafIndex =>
          obtain ⟨payload, hpayload⟩ :=
            exists_encodingInput_of_encodingInputLeafIndex?_eq_some
              secretKey.parameter hashInput leafIndex hleafIndex
          rw [← hpayload] at hstructural
          exact hstructural
            (keygenStructuralTargetInput_encodingInput secretKey cache leafIndex payload)

noncomputable def expectedPostKeygenStructuralQueries
    (adversary : Adversary) : ENNReal :=
  ∑' keyResult,
    Pr{let x ← (simulateQ romImpl Concrete.scheme.keygen).run ∅}[x = keyResult] *
      expectedSimulatedQueryCount romImpl
        (Rom.IsRelevantHashQuery fun input =>
          keygenStructuralTargetInput keyResult.1.2 keyResult.2 input ≠ input)
        (cappedSourceUnloggedDetailedGameAfterKeygen adversary
          keyResult.1.1 keyResult.1.2) keyResult.2

theorem expectedStructuralQueries_detailed_eq_source
    (adversary : Adversary)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec) :
    expectedSimulatedQueryCount romImpl
        (Rom.IsRelevantHashQuery fun input =>
          keygenStructuralTargetInput keyResult.1.2 keyResult.2 input ≠ input)
        (detailedGameAfterKeygen Concrete.scheme adversary
          keyResult.1.1 keyResult.1.2) keyResult.2 =
      expectedSimulatedQueryCount romImpl
        (Rom.IsRelevantHashQuery fun input =>
          keygenStructuralTargetInput keyResult.1.2 keyResult.2 input ≠ input)
        (cappedSourceUnloggedDetailedGameAfterKeygen adversary
          keyResult.1.1 keyResult.1.2) keyResult.2 := by
  have hprojection := congrArg
    (fun computation => expectedSimulatedQueryCount romImpl
      (Rom.IsRelevantHashQuery fun input =>
        keygenStructuralTargetInput keyResult.1.2 keyResult.2 input ≠ input)
      computation keyResult.2)
    (cappedDetailedGameAfterKeygen_unloggedProjection adversary
      keyResult.1.1 keyResult.1.2)
  rw [expectedSimulatedQueryCount_map] at hprojection
  exact hprojection

theorem winningStructuralCollision_probability_le_expectedPostKeygenStructuralQueries
    (adversary : Adversary) :
    Pr{let execution ← detailedGameWithCache Concrete.scheme adversary}[WinningStructuralCollisionOccurs execution.2 execution.1] ≤
      expectedPostKeygenStructuralQueries adversary /
        ((2 ^ digestBits : Nat) : ENNReal) := by
  apply (winningStructuralCollision_probability_le_expectedMovedQueries
    adversary).trans_eq
  unfold expectedPostKeygenStructuralQueries
  congr 1
  apply tsum_congr
  intro keyResult
  congr 1
  exact expectedStructuralQueries_detailed_eq_source adversary keyResult

end XmssSecurity
