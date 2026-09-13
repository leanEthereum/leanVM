import SphincsSecurity.Proof.Reference.VerifierWitnessClassification
import SphincsSecurity.Proof.Hypertree.PublicGraphSigner
namespace SphincsSecurity.Concrete.OtsVerifierWitness

open _root_.OracleComp OracleSpec CanonicalProbeRouting
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs instFintypePosition signAfterDigest sequenceFin chainWalk
set_option backward.isDefEq.respectTransparency false

theorem known_honest_public_plan (key : SecretKey) (f : QueryImpl HashSpec Id) (words : OtsReferenceWords) (selections : ReferenceFamily)
    (disclosed : Index → FtsTree → FtsLeaf → Prop) (known : Labels)
    (hagrees : PublicAgreement words disclosed known
      (CanonicalCoordinate.value key.otsSecret key.ftsSecret (canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret f)))
    (cache : QueryCache HashSpec) (index : Index) (leaves : IndexGroup → FtsLeaf) (signature : Signature)
    (hfull : FullyHonestOpening f cache key index leaves signature)
    (hreference : ∀ lay, ReferenceLayerOpening f key words selections index signature lay) :
    (publicSignPlan known words selections signature.randomness index leaves).1.map
      (fun plan => plan.finish (fun tree => key.ftsSecret index tree (leaves (ftsIndexOf tree)))) = some signature := by
  have hfrontier := knownFrontier_eq key.otsSecret key.ftsSecret _ words disclosed known hagrees
  rw [canonicalGraphLabels_frontier key.parameter key.otsSecret key.ftsSecret f words key.root] at hfrontier
  let parts : Layer → LayerPart := fun lay => (signature.counter lay, signature.chainValue lay,
    knownTreePath known lay (treeIndexAt index lay) (leafIndexAt index lay))
  have hlayers : ∀ lay, (publicSignLayer known words selections index lay).1 = some (parts lay) := by
    intro lay
    obtain ⟨selected, hselected, hcounter, _, hvalues, _⟩ := hreference lay
    have hchain : knownFrontier known words lay (treeIndexAt index lay) (leafIndexAt index lay) = signature.chainValue lay := by
      rw [hfrontier]
      funext chain
      exact (hvalues chain).symm
    simp only [publicSignLayer, referenceSelectionResult, hselected, Option.map_some, hchain, ← hcounter, parts]
  have hftsPath : knownFtsPath known index leaves = signature.ftsPath := by
    rw [knownFtsPath_eq key.parameter key.otsSecret key.ftsSecret f words disclosed known hagrees]
    funext tree level
    simp only [ftsOpen, evalWithAnswerFn_sequenceFin]
    exact ((hfull.2.1 tree).2 level.val level.isLt).symm
  have hauthPath : flattenPaths (fun lay => (parts lay).2.2) = signature.authPath := by
    funext position
    obtain ⟨lay, level, hlevel, hposition⟩ := authPath_exhausted position
    rw [flattenPaths_apply _ lay level hlevel position hposition.symm]
    change knownTreePath known lay (treeIndexAt index lay) (leafIndexAt index lay) level = signature.authPath position
    rw [knownTreePath_eq key.parameter key.otsSecret key.ftsSecret f words disclosed known hagrees]
    simp only [treePath, evalWithAnswerFn_sequenceFin, if_pos hlevel]
    obtain ⟨_, _, _, hpath⟩ := (hfull.1 lay).1
    have hp := hpath level.val hlevel
    have hsum : heightAbove lay + level.val < totalHeight := by rw [hposition]; exact position.isLt
    simp only [signaturePath, dif_pos hsum] at hp
    have hfin : (⟨heightAbove lay + level.val, hsum⟩ : PathIndex) = position := Fin.ext hposition
    simpa only [hfin, honestNode] using hp.symm
  simp only [publicSignPlan, hlayers, sequenceFin_some, Option.map_some, hftsPath, PublicSigningPlan.finish, parts]
  congr 1
  change Signature.mk signature.randomness (fun tree => key.ftsSecret index tree (leaves (ftsIndexOf tree)))
    signature.ftsPath signature.counter signature.chainValue
      (flattenPaths fun lay => knownTreePath known lay (treeIndexAt index lay) (leafIndexAt index lay)) = signature
  have hsecrets : (fun tree => key.ftsSecret index tree (leaves (ftsIndexOf tree))) = signature.ftsSecret :=
    funext fun tree => ((hfull.2.1 tree).1).symm
  rw [hsecrets, hauthPath]

theorem honest_signAfterDigest (key : SecretKey) (f : QueryImpl HashSpec Id) (dummy : OtsReferenceWords)
    (cache : QueryCache HashSpec) (index : Index) (leaves : IndexGroup → FtsLeaf) (signature : Signature)
    (hfull : FullyHonestOpening f cache key index leaves signature)
    (hreference : ∀ lay, ReferenceLayerOpening f key (canonicalReferenceWords key f dummy) (referenceTableSelection key f) index signature lay) :
    evalWithAnswerFn f (signAfterDigest key signature.randomness index leaves) = some signature := by
  let known := CanonicalCoordinate.value key.otsSecret key.ftsSecret (canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret f)
  have hagrees : PublicAgreement (canonicalReferenceWords key f dummy) (fun _ _ _ => False) known known := fun _ _ => rfl
  have hp := known_honest_public_plan key f (canonicalReferenceWords key f dummy) (referenceTableSelection key f)
    (fun _ _ _ => False) known hagrees cache index leaves signature hfull hreference
  have he := congrArg Prod.fst (boundaryEval_signAfterDigest_public key f (fun _ _ _ => False) known dummy hagrees signature.randomness index leaves)
  rw [boundaryEval_fst] at he
  exact he.trans hp

theorem honest_signature_eq (key : SecretKey) (f : QueryImpl HashSpec Id) (dummy : OtsReferenceWords)
    (cache : QueryCache HashSpec) (index : Index) (leaves : IndexGroup → FtsLeaf) (signature signed : Signature)
    (hfull : FullyHonestOpening f cache key index leaves signature)
    (hreference : ∀ lay, ReferenceLayerOpening f key (canonicalReferenceWords key f dummy) (referenceTableSelection key f) index signature lay)
    (hsigned : evalWithAnswerFn f (signAfterDigest key signed.randomness index leaves) = some signed)
    (hrandomness : signed.randomness = signature.randomness) : signed = signature := by
  rw [hrandomness, honest_signAfterDigest key f dummy cache index leaves signature hfull hreference] at hsigned
  exact (Option.some.inj hsigned).symm

theorem strong_signing_payload_ne (key : SecretKey) (f : QueryImpl HashSpec Id) (dummy : OtsReferenceWords)
    (cache : QueryCache HashSpec) (log : QueryLog SigningSpec) (forgery : Forgery)
    (hnew : ¬ SigningTranscript.Contains log forgery)
    (hfull : let digest := truncateMessageDigest (f (tweakableHashInput key.parameter .message
      (messageDigestPayload key.root forgery.message forgery.signature.randomness)))
      FullyHonestOpening f cache key (digestIndex digest) (digestLeaves digest) forgery.signature)
    (hreference : let digest := truncateMessageDigest (f (tweakableHashInput key.parameter .message
      (messageDigestPayload key.root forgery.message forgery.signature.randomness)))
      ∀ lay, ReferenceLayerOpening f key (canonicalReferenceWords key f dummy) (referenceTableSelection key f)
        (digestIndex digest) forgery.signature lay)
    (message : Message) (signature : Signature) (hentry : (⟨message, some signature⟩ : SigningEntry) ∈ log)
    (hsigned : let digest := truncateMessageDigest (f (tweakableHashInput key.parameter .message
      (messageDigestPayload key.root message signature.randomness)))
      evalWithAnswerFn f (signAfterDigest key signature.randomness (digestIndex digest) (digestLeaves digest)) = some signature) :
    messageDigestPayload key.root message signature.randomness ≠
      messageDigestPayload key.root forgery.message forgery.signature.randomness := by
  intro heq
  obtain ⟨hmessage, hrandomness⟩ := messageDigestPayload_injective key.root heq
  dsimp only at hsigned
  rw [heq] at hsigned
  have hsignature := honest_signature_eq key f dummy cache _ _ forgery.signature signature hfull hreference hsigned hrandomness
  exact hnew ⟨⟨message, some signature⟩, hentry, hmessage, congrArg some hsignature⟩

end SphincsSecurity.Concrete.OtsVerifierWitness
