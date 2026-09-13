import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Scheme.SignSupport
/-!
# Comparing honest layer openings

Two honest openings at the same one-time position either agree on the signed layer component, use
distinct encoding inputs with the same digest, or the forged codeword starts earlier on some chain.
-/

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec

theorem decode_of_eval_encode_eq_some (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (message : Digest)
    (counter : Counter) (codeword : Encoding)
    (hencode : evalWithAnswerFn f (encode parameter lay tree leafIdx message counter)
      = some codeword) :
    TargetSum.decodeDigest (truncateHash (f (tweakableHashInput parameter
      (.encoding lay tree leafIdx) (digestBytes message ++ counterBytes counter))))
        = some codeword := by
  simpa only [encode, evalWithAnswerFn_bind, evalWithAnswerFn_pure, eval_tweakableHash] using hencode

theorem valid_of_eval_encode_eq_some (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (message : Digest)
    (counter : Counter) (codeword : Encoding)
    (hencode : evalWithAnswerFn f (encode parameter lay tree leafIdx message counter)
      = some codeword) : TargetSum.Valid codeword :=
  TargetSum.valid_of_decodeDigest_eq_some
    (decode_of_eval_encode_eq_some f parameter lay tree leafIdx message counter codeword hencode)

end SphincsSecurity.Concrete
