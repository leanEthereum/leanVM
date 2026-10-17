import XmssSecurity.Proof.EncodingActionTrace
import VCVio.OracleComp.Constructions.SampleableType

open OracleComp OracleSpec

namespace XmssSecurity

inductive EncodingSampleKind where
  | side
  | query
  | sign
deriving DecidableEq

noncomputable def uniformHashOutput : ProbComp HashOutput :=
  $ᵗ HashOutput

theorem uniformSampleImpl_hash_eq (input : HashInput) :
    (uniformSampleImpl (spec := HashSpec)) input = uniformHashOutput := by
  rfl

theorem randomOracle_run_none_eq_uniformHashOutput
    (input : HashInput) (cache : QueryCache HashSpec)
    (hcache : cache input = none) :
    (randomOracle input).run cache =
      (fun output => (output, cache.cacheQuery input output)) <$>
        uniformHashOutput := by
  rw [randomOracle, QueryImpl.withCaching_run_none _ hcache]
  rw [uniformSampleImpl_hash_eq]

end XmssSecurity
