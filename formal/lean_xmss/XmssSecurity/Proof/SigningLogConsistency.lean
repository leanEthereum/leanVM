import XmssSecurity.Proof.OutcomeClassification

open OracleSpec

namespace XmssSecurity

def SigningLogConsistent (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (log : QueryLog SigningSpec) : Prop :=
  ∀ request signature, SigningTranscript.Returned log request signature →
    ∃ encoding,
      TargetSum.decodeDigest
        (Concrete.CacheView.encodingHash cache secretKey.parameter request.leafIndex
          (request.message, signature.randomness)) = some encoding ∧
      signature = Concrete.CacheReplay.signWithEncoding cache secretKey
        request.leafIndex signature.randomness encoding

end XmssSecurity
