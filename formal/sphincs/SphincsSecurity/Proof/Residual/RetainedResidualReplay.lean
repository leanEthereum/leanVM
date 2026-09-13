import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Residual.RetainedResidualRecovery
namespace SphincsSecurity.Concrete.RetainedResidual

open _root_.OracleComp OracleSpec CanonicalProbeRouting
attribute [local instance] Classical.propDecidable
attribute [local irreducible] hashInputs canonicalEncodingInputs canonicalGraphInputs instFintypePosition
  signDigestLoop signAfterDigest sequenceFin chainWalk
set_option backward.isDefEq.respectTransparency false

theorem Compatible.honest_public_plan {inputs : Finset HashInput} {context : Context inputs} {memory : Memory}
    (hcompatible : Compatible context memory) (hdummy : ∀ lay tree leaf, TargetSum.Valid (context.dummy lay tree leaf))
    (index : Index) (leaves : IndexGroup → FtsLeaf) (signature : Signature)
    (hfull : FullyHonestOpening context.oracle memory.external.cache context.key index leaves signature) :
    (publicSignPlan memory.routing.known context.words context.auxiliary.selections signature.randomness index leaves).1.map
      (fun plan => plan.finish (fun tree => context.key.ftsSecret index tree (leaves (ftsIndexOf tree)))) = some signature := by
  have hagrees : PublicAgreement context.words memory.routing.disclosed memory.routing.known
      (CanonicalCoordinate.value context.key.otsSecret context.key.ftsSecret
        (canonicalGraphLabels context.key.parameter context.key.otsSecret context.key.ftsSecret context.oracle)) := by
    rw [context.graph_eq]
    exact hcompatible.agrees
  have hfrontier := knownFrontier_eq context.key.otsSecret context.key.ftsSecret context.graph context.words
    memory.routing.disclosed memory.routing.known hcompatible.agrees
  rw [← context.graph_eq, canonicalGraphLabels_frontier context.key.parameter context.key.otsSecret context.key.ftsSecret
    context.oracle context.words context.key.root] at hfrontier
  let parts : Layer → LayerPart := fun lay =>
    (signature.counter lay, signature.chainValue lay,
      knownTreePath memory.routing.known lay (treeIndexAt index lay) (leafIndexAt index lay))
  have hlayers : ∀ lay, (publicSignLayer memory.routing.known context.words context.auxiliary.selections index lay).1 = some (parts lay) := by
    intro lay
    obtain ⟨selected, hselected, _, hcounter, hvalues, _⟩ := hcompatible.layer_reference lay (treeIndexAt index lay) (leafIndexAt index lay)
      (evalWithAnswerFn context.oracle (layerMessage context.key index lay)) (signature.counter lay) (signature.chainValue lay)
      (signaturePath signature lay) (context.words_valid hdummy _ _ _) (hfull.1 lay).1 (hfull.1 lay).2
    have hchain : knownFrontier memory.routing.known context.words lay (treeIndexAt index lay) (leafIndexAt index lay) =
        signature.chainValue lay := by
      rw [hfrontier]
      funext chain
      exact (hvalues chain).symm
    simp only [publicSignLayer, referenceSelectionResult, hselected, Option.map_some, hchain, ← hcounter, parts]
  have hftsPath : knownFtsPath memory.routing.known index leaves = signature.ftsPath := by
    rw [knownFtsPath_eq context.key.parameter context.key.otsSecret context.key.ftsSecret context.oracle context.words
      memory.routing.disclosed memory.routing.known hagrees]
    funext tree level
    simp only [ftsOpen, evalWithAnswerFn_sequenceFin]
    exact ((hfull.2.1 tree).2 level.val level.isLt).symm
  have hauthPath : flattenPaths (fun lay => (parts lay).2.2) = signature.authPath := by
    funext position
    obtain ⟨lay, level, hlevel, hposition⟩ := authPath_exhausted position
    rw [flattenPaths_apply _ lay level hlevel position hposition.symm]
    change knownTreePath memory.routing.known lay (treeIndexAt index lay) (leafIndexAt index lay) level = signature.authPath position
    rw [knownTreePath_eq context.key.parameter context.key.otsSecret context.key.ftsSecret context.oracle context.words
      memory.routing.disclosed memory.routing.known hagrees]
    simp only [treePath, evalWithAnswerFn_sequenceFin, if_pos hlevel]
    obtain ⟨_, _, _, hpath⟩ := (hfull.1 lay).1
    have hpath := hpath level.val hlevel
    have hsum : heightAbove lay + level.val < totalHeight := by rw [hposition]; exact position.isLt
    simp only [signaturePath, dif_pos hsum] at hpath
    have hfin : (⟨heightAbove lay + level.val, hsum⟩ : PathIndex) = position := Fin.ext hposition
    simpa only [hfin, honestNode] using hpath.symm
  simp only [publicSignPlan, hlayers, sequenceFin_some, Option.map_some, hftsPath, PublicSigningPlan.finish, parts]
  congr 1
  change Signature.mk signature.randomness (fun tree => context.key.ftsSecret index tree (leaves (ftsIndexOf tree)))
    signature.ftsPath signature.counter signature.chainValue
      (flattenPaths fun lay => knownTreePath memory.routing.known lay (treeIndexAt index lay) (leafIndexAt index lay)) = signature
  have hsecrets : (fun tree => context.key.ftsSecret index tree (leaves (ftsIndexOf tree))) = signature.ftsSecret :=
    funext fun tree => ((hfull.2.1 tree).1).symm
  rw [hsecrets, hauthPath]

theorem Compatible.honest_signAfterDigest {inputs : Finset HashInput} {context : Context inputs} {memory : Memory}
    (hcompatible : Compatible context memory) (hdummy : ∀ lay tree leaf, TargetSum.Valid (context.dummy lay tree leaf))
    (index : Index) (leaves : IndexGroup → FtsLeaf) (signature : Signature)
    (hfull : FullyHonestOpening context.oracle memory.external.cache context.key index leaves signature) :
    evalWithAnswerFn context.oracle (signAfterDigest context.key signature.randomness index leaves) = some signature := by
  have hwords : context.words = canonicalReferenceWords context.key context.oracle context.dummy :=
    referencePrefix_words context.key inputs context.encoding context.graph context.auxiliary context.auxiliary_valid context.dummy
  have hagrees : PublicAgreement (canonicalReferenceWords context.key context.oracle context.dummy)
      memory.routing.disclosed memory.routing.known
      (CanonicalCoordinate.value context.key.otsSecret context.key.ftsSecret
        (canonicalGraphLabels context.key.parameter context.key.otsSecret context.key.ftsSecret context.oracle)) := by
    rw [← hwords, context.graph_eq]
    exact hcompatible.agrees
  have hselection : referenceTableSelection context.key context.oracle = context.auxiliary.selections :=
    referenceTableSelection_prefix context.key inputs context.encoding context.graph context.auxiliary context.auxiliary_valid
  rw [← boundaryEval_fst context.key.parameter context.oracle,
    boundaryEval_signAfterDigest_public context.key context.oracle memory.routing.disclosed memory.routing.known context.dummy hagrees,
    ← hwords, hselection]
  exact hcompatible.honest_public_plan hdummy index leaves signature hfull

theorem Compatible.honest_signature_eq {inputs : Finset HashInput} {context : Context inputs} {memory : Memory}
    (hcompatible : Compatible context memory) (hdummy : ∀ lay tree leaf, TargetSum.Valid (context.dummy lay tree leaf))
    (index : Index) (leaves : IndexGroup → FtsLeaf) (signature signed : Signature)
    (hfull : FullyHonestOpening context.oracle memory.external.cache context.key index leaves signature)
    (hsigned : evalWithAnswerFn context.oracle (signAfterDigest context.key signed.randomness index leaves) = some signed)
    (hrandomness : signed.randomness = signature.randomness) : signed = signature := by
  rw [hrandomness, hcompatible.honest_signAfterDigest hdummy index leaves signature hfull] at hsigned
  exact (Option.some.inj hsigned).symm

end SphincsSecurity.Concrete.RetainedResidual
