import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Scheme.SignSupport
/-!
# Cached encoding queries

Successful verifier and signer executions retain the encoding query that selected their counter.
-/

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec

theorem CachedRun.encode_cached {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {parameter : PublicParameter} {lay : Layer}
    {tree : TreeIndex} {leafIdx : LeafIndex} {message : Digest} {counter : Counter}
    (hrun : CachedRun cache f (encode parameter lay tree leafIdx message counter)) :
    cache (tweakableHashInput parameter (.encoding lay tree leafIdx)
      (digestBytes message ++ counterBytes counter)) ≠ none := by
  apply hrun
  rw [encode]
  apply queriedInputs_mono_bind_left
  simp only [queriedInputs_tweakableHash, List.mem_singleton]

theorem CachedRun.otsLeaf_encode_cached {f : QueryImpl HashSpec Id}
    {cache : QueryCache HashSpec} {parameter : PublicParameter} {lay : Layer}
    {tree : TreeIndex} {leafIdx : LeafIndex} {message : Digest} {counter : Counter}
    {values : ChainIndex → Digest}
    (hrun : CachedRun cache f (otsLeaf parameter lay tree leafIdx message counter values)) :
    cache (tweakableHashInput parameter (.encoding lay tree leafIdx)
      (digestBytes message ++ counterBytes counter)) ≠ none :=
  CachedRun.encode_cached hrun.bind_left

end SphincsSecurity.Concrete
