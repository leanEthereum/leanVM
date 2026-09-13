import SphincsSecurity.Proof.Chains.AdaptiveChainErasure
import SphincsSecurity.Proof.Ots.OtsPrefixSeedGame
namespace SphincsSecurity.Concrete.OtsPrefix

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false

noncomputable def uniformImpl : QueryImpl unifSpec PMF :=
  fun input => PMF.uniformOfFintype (Fin (input + 1))

theorem fixedImpl_evalDist (segment : OtsPrefix) (tables : Fin segment.digit.val → Digest → Digest)
    {Result : Type} (computation : OracleComp segment.World Result) :
    𝒟[simulateQ (PartialChainEndpoint.fixedImpl uniformImpl tables) computation] =
      𝒟[simulateQ (segment.fixedImpl tables) computation] := by
  induction computation using OracleComp.inductionOn with
  | pure result => simp only [simulateQ_pure, evalDist_pure]
  | query_bind input next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, evalDist_bind, ih]
      cases input with
      | inl input =>
          simp only [PartialChainEndpoint.fixedImpl, fixedImpl, QueryImpl.add_apply_inl,
            uniformImpl]
          change (𝒟[PMF.uniformOfFintype (Fin (input + 1))] >>= fun answer =>
            𝒟[simulateQ (segment.fixedImpl tables) (next answer)]) =
            (𝒟[(liftM (unifSpec.query input) : ProbComp (Fin (input + 1)))] >>= fun answer =>
              𝒟[simulateQ (segment.fixedImpl tables) (next answer)])
          rw [evalDist_query]
      | inr query =>
          simp only [PartialChainEndpoint.fixedImpl, fixedImpl, QueryImpl.add_apply_inr,
            ← PMF.monad_pure_eq_pure, evalDist_pure]

theorem realRun_empty_forget (segment : OtsPrefix) {Result : Type}
    (computation : Digest → OracleComp segment.World Result) :
    𝒟[(PartialChainEndpoint.realRun (fun _ => uniformImpl) computation (fun _ _ => none)).map
      (fun result => result.2.1)] = (do
        let tables ← 𝒟[PMF.uniformOfFintype (Fin segment.digit.val → Digest → Digest)]
        let secret ← 𝒟[PMF.uniformOfFintype Digest]
        𝒟[simulateQ (segment.fixedImpl tables) (computation (PartialChainEndpoint.evaluate tables secret))] : SPMF Result) := by
  rw [PartialChainEndpoint.realRun_empty_forget]
  simp only [← PMF.monad_bind_eq_bind, evalDist_bind, segment.fixedImpl_evalDist]

noncomputable def seedObservedRun (segment : OtsPrefix) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs segment.parameter ⊆ inputs)
    (hgraph : canonicalGraphInputs segment.parameter ⊆ inputs)
    (auxiliary : segment.ReferenceAuxSeed inputs hencoding hgraph) (secrets : OtsFrontierValues)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (words : OtsReferenceWords) (adversary : Adversary) :
    PMF (Digest × ((Bool × SigningBoundaryTrace) × (Fin segment.digit.val → Digest → Option Digest))) :=
  PartialChainEndpoint.realRun (fun _ => uniformImpl)
    (fun endpoint => segment.seedGame inputs hencoding hgraph auxiliary secrets ftsSecret words endpoint adversary)
    (fun _ _ => none)

end SphincsSecurity.Concrete.OtsPrefix
