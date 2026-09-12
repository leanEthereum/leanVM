import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Hypertree.CanonicalGraphHonest
import SphincsSecurity.Proof.Hypertree.CanonicalGraphSampling
import SphincsSecurity.Proof.Ots.EncodingInputs
import SphincsSecurity.Proof.Hypertree.FrontierRandomOracle
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec OracleComp.DeferredSampling
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] canonicalGraphInputs canonicalPayloadInputs canonicalEncodingInputs

noncomputable def graphFrontierGameRest (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (labels : CanonicalGraphLabels)
    (f : QueryImpl HashSpec Id) (dummy : OtsReferenceWords) (adversary : Adversary) :
    ProbComp (Bool × SigningBoundaryTrace) := do
  let key : SecretKey := ⟨parameter, canonicalGraphRoot labels, otsSecret, ftsSecret⟩
  let words := canonicalReferenceWords key f dummy
  frontierGame parameter f ftsSecret words (canonicalGraphFrontier otsSecret labels words) adversary

theorem graphFrontierGameRest_canonical (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (f : QueryImpl HashSpec Id) (dummy : OtsReferenceWords) (adversary : Adversary) :
    graphFrontierGameRest parameter otsSecret ftsSecret
      (canonicalGraphLabels parameter otsSecret ftsSecret f) f dummy adversary =
        fixedBoundaryRun parameter f (gameAfterSecrets adversary parameter otsSecret ftsSecret) := by
  rw [graphFrontierGameRest, canonicalGraphLabels_root,
    canonicalGraphLabels_frontier parameter otsSecret ftsSecret f _
      (evalWithAnswerFn f (treeRoot parameter topLayer rootTree (otsSecret topLayer rootTree))),
    fixedBoundaryRun_gameAfterSecrets_canonical adversary parameter otsSecret ftsSecret f dummy]

noncomputable def fixedGraphGame (f : QueryImpl HashSpec Id) (dummy : OtsReferenceWords)
    (adversary : Adversary) : ProbComp (Bool × SigningBoundaryTrace) := do
  let parameter ← sampleParameter
  let otsSecret ← sampleOtsSecrets
  let ftsSecret ← sampleFtsSecrets
  graphFrontierGameRest parameter otsSecret ftsSecret
    (canonicalGraphLabels parameter otsSecret ftsSecret f) f dummy adversary

theorem fixedGraphGame_eq_frontier (f : QueryImpl HashSpec Id) (dummy : OtsReferenceWords)
    (adversary : Adversary) : fixedGraphGame f dummy adversary = fixedFrontierGame f dummy adversary := by
  rw [← simulateQ_boundaryGameCore_frontier f dummy adversary, boundaryGameCore, fixedGraphGame]
  simp only [simulateQ_bind, simulateQ_fixedHashWorld_lift_prob]
  apply bind_congr
  intro parameter
  apply bind_congr
  intro otsSecret
  apply bind_congr
  intro ftsSecret
  rw [graphFrontierGameRest_canonical, fixedBoundaryRun_eq_boundaryComputation]

noncomputable def canonicalGraphOracleGame (inputs : Finset HashInput)
    (hgraph : ∀ parameter, canonicalGraphInputs parameter ⊆ inputs)
    (dummy : OtsReferenceWords) (adversary : Adversary) : ProbComp (Bool × SigningBoundaryTrace) := do
  let parameter ← sampleParameter
  let otsSecret ← sampleOtsSecrets
  let ftsSecret ← sampleFtsSecrets
  let graph ← plantCanonicalGraph parameter otsSecret ftsSecret inputs (hgraph parameter)
  graphFrontierGameRest parameter otsSecret ftsSecret graph.1
    (finiteHashAnswer ∅ inputs graph.2) dummy adversary

theorem evalDist_frontier_eq_canonicalGraph (inputs : Finset HashInput)
    (hgraph : ∀ parameter, canonicalGraphInputs parameter ⊆ inputs)
    (dummy : OtsReferenceWords) (adversary : Adversary) :
    𝒟[frontierOracleGame inputs dummy adversary] =
      𝒟[canonicalGraphOracleGame inputs hgraph dummy adversary] := by
  rw [frontierOracleGame, canonicalGraphOracleGame]
  simp_rw [← fixedGraphGame_eq_frontier]
  simp only [fixedGraphGame]
  rw [evalDist_bind_comm]
  apply evalDist_bind_congr_left
  intro parameter
  rw [evalDist_bind_comm]
  apply evalDist_bind_congr_left
  intro otsSecret
  rw [evalDist_bind_comm]
  apply evalDist_bind_congr_left
  intro ftsSecret
  exact evalDist_canonicalGraph_bind_eq_plant parameter otsSecret ftsSecret inputs (hgraph parameter)
    (fun labels table => graphFrontierGameRest parameter otsSecret ftsSecret labels
      (finiteHashAnswer ∅ inputs table) dummy adversary)

theorem evalDist_boundaryGameCore_canonicalGraph (inputs : Finset HashInput)
    (hgraph : ∀ parameter, canonicalGraphInputs parameter ⊆ inputs)
    (dummy : OtsReferenceWords) (adversary : Adversary)
    (hinputs : hashInputs (boundaryGameCore adversary) ⊆ inputs) :
    𝒟[(simulateQ romImpl (boundaryGameCore adversary)).run' ∅] =
      𝒟[canonicalGraphOracleGame inputs hgraph dummy adversary] := by
  exact (evalDist_boundaryGameCore_frontier inputs dummy adversary hinputs).trans
    (evalDist_frontier_eq_canonicalGraph inputs hgraph dummy adversary)

noncomputable def canonicalGraphGameInputs (adversary : Adversary) : Finset HashInput :=
  (hashInputs (boundaryGameCore adversary) ∪ Finset.univ.biUnion canonicalGraphInputs) ∪
    Finset.univ.biUnion canonicalEncodingInputs

attribute [local irreducible] canonicalGraphGameInputs

theorem canonicalGraphInputs_subset_gameInputs (adversary : Adversary) (parameter : PublicParameter) :
    canonicalGraphInputs parameter ⊆ canonicalGraphGameInputs adversary := by
  intro input hinput
  rw [canonicalGraphGameInputs, Finset.mem_union]
  apply Or.inl
  rw [Finset.mem_union]
  apply Or.inr
  rw [Finset.mem_biUnion]
  simp only [Finset.mem_univ, true_and]
  exact ⟨parameter, hinput⟩

theorem hashInputs_subset_canonicalGraphGameInputs (adversary : Adversary) :
    hashInputs (boundaryGameCore adversary) ⊆ canonicalGraphGameInputs adversary := by
  rw [canonicalGraphGameInputs]
  exact Finset.Subset.trans Finset.subset_union_left Finset.subset_union_left

theorem canonicalEncodingInputs_subset_gameInputs (adversary : Adversary) (parameter : PublicParameter) :
    canonicalEncodingInputs parameter ⊆ canonicalGraphGameInputs adversary := by
  intro input hinput
  rw [canonicalGraphGameInputs, Finset.mem_union]
  apply Or.inr
  rw [Finset.mem_biUnion]
  simp only [Finset.mem_univ, true_and]
  exact ⟨parameter, hinput⟩

end SphincsSecurity.Concrete
