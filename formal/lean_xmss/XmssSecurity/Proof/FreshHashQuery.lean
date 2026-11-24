module

public import VCVio.OracleComp.Constructions.SampleableType
public import XmssSecurity.Scheme

@[expose] public section

/-!
# Uniform answers to fresh hash queries

A fresh query to the lazy random oracle samples `uniformHashOutput` and caches it
(`randomOracle_run_none_eq_uniformHashOutput`). `EncodingSampleKind` tags such a sample as an
adversary's query, a signing attempt or a side sample, which the first-lane experiment answers with
an encoding query, an encoding signing attempt or a plain uniform sample
(`globalFirstLaneFreshEncodingQuery`).
-/

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
