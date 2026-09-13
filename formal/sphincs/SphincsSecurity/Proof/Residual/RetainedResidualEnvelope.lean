import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Ots.ReferencePrefixGame
import SphincsSecurity.Proof.Residual.RetainedResidualSource
namespace SphincsSecurity.Concrete.RetainedResidual

open _root_.OracleComp OracleSpec
attribute [local instance] Classical.propDecidable
attribute [local irreducible] hashInputs sourceInputs canonicalEncodingInputs canonicalGraphInputs instFintypePosition canonicalGraphGameInputs
set_option backward.isDefEq.respectTransparency false

noncomputable local instance keyFintype : Fintype SecretKey := by
  classical
  exact Fintype.ofEquiv
    (PublicParameter × Digest × (Layer → TreeIndex → LeafIndex → ChainIndex → Digest) × (Index → FtsTree → FtsLeaf → Digest))
    { toFun := fun key => ⟨key.1, key.2.1, key.2.2.1, key.2.2.2⟩
      invFun := fun key => (key.parameter, key.root, key.otsSecret, key.ftsSecret)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

attribute [local irreducible] keyFintype signatureFintype

noncomputable def verificationInputs (key : SecretKey) : Finset HashInput :=
  Finset.univ.biUnion fun message : Message => Finset.univ.biUnion fun signature : Signature =>
    hashInputs (scheme.verify ⟨key.root, key.parameter⟩ message signature)

noncomputable def gameInputs (adversary : Adversary) : Finset HashInput :=
  canonicalGraphGameInputs adversary ∪ Finset.univ.biUnion fun key : SecretKey =>
    sourceInputs key (adversary.main ⟨key.root, key.parameter⟩) ∪ verificationInputs key

theorem sourceInputs_subset_gameInputs (adversary : Adversary) (key : SecretKey) :
    sourceInputs key (adversary.main ⟨key.root, key.parameter⟩) ⊆ gameInputs adversary := by
  intro input hinput
  rw [gameInputs, Finset.mem_union]
  exact Or.inr (Finset.mem_biUnion.mpr ⟨key, Finset.mem_univ _, Finset.mem_union_left _ hinput⟩)

theorem verifyInputs_subset_gameInputs (adversary : Adversary) (key : SecretKey) (forgery : Forgery) :
    hashInputs (scheme.verify ⟨key.root, key.parameter⟩ forgery.message forgery.signature) ⊆ gameInputs adversary := by
  intro input hinput
  rw [gameInputs, Finset.mem_union]
  apply Or.inr
  apply Finset.mem_biUnion.mpr
  refine ⟨key, Finset.mem_univ _, Finset.mem_union_right _ ?_⟩
  rw [verificationInputs, Finset.mem_biUnion]
  exact ⟨forgery.message, Finset.mem_univ _, Finset.mem_biUnion.mpr ⟨forgery.signature, Finset.mem_univ _, hinput⟩⟩

theorem canonicalEncodingInputs_subset_retainedGameInputs (adversary : Adversary) (parameter : PublicParameter) :
    canonicalEncodingInputs parameter ⊆ gameInputs adversary :=
  (canonicalEncodingInputs_subset_gameInputs adversary parameter).trans Finset.subset_union_left

theorem canonicalGraphInputs_subset_retainedGameInputs (adversary : Adversary) (parameter : PublicParameter) :
    canonicalGraphInputs parameter ⊆ gameInputs adversary :=
  (canonicalGraphInputs_subset_gameInputs adversary parameter).trans Finset.subset_union_left

theorem boundaryInputs_subset_retainedGameInputs (adversary : Adversary) :
    hashInputs (boundaryGameCore adversary) ⊆ gameInputs adversary :=
  (hashInputs_subset_canonicalGraphGameInputs adversary).trans Finset.subset_union_left

theorem boundaryGameCore_eq_retainedPrefixPrior (dummy : OtsReferenceWords) (adversary : Adversary) :
    𝒟[(simulateQ romImpl (boundaryGameCore adversary)).run' ∅] =
      Prod.snd <$> referencePrefixJointPriorGame (gameInputs adversary)
        (canonicalEncodingInputs_subset_retainedGameInputs adversary) dummy adversary := by
  rw [← referencePrefixCoordinateGame_eq_jointPrior, ← referenceResidualGame_eq_prefixCoordinates]
  exact evalDist_boundaryGameCore_referenceResidual (gameInputs adversary)
    (canonicalEncodingInputs_subset_retainedGameInputs adversary) (canonicalGraphInputs_subset_retainedGameInputs adversary)
    dummy adversary (boundaryInputs_subset_retainedGameInputs adversary)

end SphincsSecurity.Concrete.RetainedResidual
