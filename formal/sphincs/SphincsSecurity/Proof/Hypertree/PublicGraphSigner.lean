import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Ots.EncodingFamilyOracleSplit
import SphincsSecurity.Proof.Hypertree.PublicGraphOpenings
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec CanonicalProbeRouting
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] instFintypePosition boundaryEval referenceEncodingSearch

def publicSignLayer (known : Labels) (words : OtsReferenceWords) (selections : ReferenceFamily)
    (index : Index) (lay : Layer) : Option LayerPart × Nat :=
  let search := referenceSelectionResult (selections ⟨lay, treeIndexAt index lay, leafIndexAt index lay⟩)
  let cost := layerMessageHashCost lay + search.2
  match search.1 with
  | none => (none, cost)
  | some (counter, _) =>
      (some (counter, knownFrontier known words lay (treeIndexAt index lay) (leafIndexAt index lay),
        knownTreePath known lay (treeIndexAt index lay) (leafIndexAt index lay)),
        cost + 191 + authenticationHashCost lay)

structure PublicSigningPlan where
  randomness : Randomness
  ftsPath : FtsTree → Fin ftsTreeHeight → Digest
  parts : Layer → LayerPart

def PublicSigningPlan.finish (plan : PublicSigningPlan) (secrets : FtsTree → Digest) : Signature where
  randomness := plan.randomness
  ftsSecret := secrets
  ftsPath := plan.ftsPath
  counter := fun lay => (plan.parts lay).1
  chainValue := fun lay => (plan.parts lay).2.1
  authPath := flattenPaths fun lay => (plan.parts lay).2.2

def publicSignPlan (known : Labels) (words : OtsReferenceWords) (selections : ReferenceFamily)
    (randomness : Randomness) (index : Index) (leaves : IndexGroup → FtsLeaf) : Option PublicSigningPlan × Nat :=
  let layers := fun lay => publicSignLayer known words selections index lay
  ((sequenceFin (m := Option) (fun lay => (layers lay).1)).map (fun parts =>
      ⟨randomness, knownFtsPath known index leaves, parts⟩),
    28504 + ∑ lay, (layers lay).2)

variable (key : SecretKey) (f : QueryImpl HashSpec Id) (words : OtsReferenceWords)
  (disclosed : Index → FtsTree → FtsLeaf → Prop) (known : Labels)
  (hagrees : PublicAgreement words disclosed known
    (CanonicalCoordinate.value key.otsSecret key.ftsSecret (canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret f)))

include hagrees in
theorem frontierSignLayer_eq_public (index : Index) (lay : Layer) :
    frontierSignLayer key.parameter f key.ftsSecret words
        (canonicalGraphFrontier key.otsSecret (canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret f) words) index lay =
      publicSignLayer known words (referenceTableSelection key f) index lay := by
  have hfrontier : IsSigningFrontier key f words
      (canonicalGraphFrontier key.otsSecret (canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret f) words) := by
    rw [canonicalGraphLabels_frontier key.parameter key.otsSecret key.ftsSecret f words key.root]
    exact isSigningFrontier_canonical key f words
  have hsearch : frontierLayerSearch key.parameter f key.ftsSecret words
      (canonicalGraphFrontier key.otsSecret (canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret f) words) index lay =
        referenceSelectionResult (referenceTableSelection key f ⟨lay, treeIndexAt index lay, leafIndexAt index lay⟩) := by
    rw [referenceSelectionResult_eq_search, canonicalEncodingSearch_at, frontierLayerSearch,
      eval_frontierLayerMessage key f words _ hfrontier index lay]
  have hpath := eval_frontierTreePath key.parameter f lay (treeIndexAt index lay)
    (key.otsSecret lay (treeIndexAt index lay)) (words lay (treeIndexAt index lay))
    (canonicalGraphFrontier key.otsSecret (canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret f) words lay
      (treeIndexAt index lay)) (hfrontier lay (treeIndexAt index lay)) (leafIndexAt index lay)
  rw [← knownTreePath_eq key.parameter key.otsSecret key.ftsSecret f words disclosed known hagrees] at hpath
  simp only [frontierSignLayer, publicSignLayer, hsearch, hpath,
    knownFrontier_eq key.otsSecret key.ftsSecret _ words disclosed known hagrees]
  rfl

include hagrees in
theorem frontierSignAfterDigest_eq_publicPlan (randomness : Randomness) (index : Index) (leaves : IndexGroup → FtsLeaf) :
    frontierSignAfterDigest key.parameter f key.ftsSecret words
        (canonicalGraphFrontier key.otsSecret (canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret f) words)
        randomness index leaves =
      ((publicSignPlan known words (referenceTableSelection key f) randomness index leaves).1.map
        (fun plan => plan.finish (fun tree => key.ftsSecret index tree (leaves (ftsIndexOf tree)))),
        (publicSignPlan known words (referenceTableSelection key f) randomness index leaves).2) := by
  simp only [frontierSignAfterDigest, publicSignPlan,
    frontierSignLayer_eq_public key f words disclosed known hagrees,
    ← knownFtsPath_eq key.parameter key.otsSecret key.ftsSecret f words disclosed known hagrees,
    Option.map_map, Function.comp_def, PublicSigningPlan.finish]

theorem boundaryEval_signAfterDigest_public (dummy : OtsReferenceWords)
    (hagrees : PublicAgreement (canonicalReferenceWords key f dummy) disclosed known
      (CanonicalCoordinate.value key.otsSecret key.ftsSecret (canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret f)))
    (randomness : Randomness) (index : Index) (leaves : IndexGroup → FtsLeaf) :
    boundaryEval key.parameter f (signAfterDigest key randomness index leaves) =
      ((publicSignPlan known (canonicalReferenceWords key f dummy) (referenceTableSelection key f) randomness index leaves).1.map
        (fun plan => plan.finish (fun tree => key.ftsSecret index tree (leaves (ftsIndexOf tree)))),
        (FreeMonoid.of none) ^
          (publicSignPlan known (canonicalReferenceWords key f dummy) (referenceTableSelection key f) randomness index leaves).2) := by
  have h := frontierSignAfterDigest_eq_publicPlan key f (canonicalReferenceWords key f dummy) disclosed known hagrees randomness index leaves
  rw [canonicalGraphLabels_frontier key.parameter key.otsSecret key.ftsSecret f _ key.root] at h
  rw [boundaryEval_signAfterDigest_canonical key f dummy, h]

end SphincsSecurity.Concrete
