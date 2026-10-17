import XmssSecurity.Proof.CappedChain.ChainInputTrace

open OracleComp OracleSpec

namespace XmssSecurity.CappedChain

def actionTraceOutcome
    (publicKey : PublicKey) (secretKey : SecretKey)
    (result : (Forgery × Bool) × AttackerActionTrace) : GameOutcome :=
  ⟨publicKey, secretKey, result.1.1, result.2.toSigningLog, result.1.2⟩

noncomputable def actionTracedForgeryEncoding
    (result : ((((PublicKey × SecretKey) × QueryCache HashSpec) ×
      (GameOutcome × QueryCache HashSpec)) × AttackerActionTrace)) : Encoding :=
  (TargetSum.decodeDigest
    (Concrete.CacheView.encodingHash result.1.2.2 result.1.1.1.2.parameter
      result.1.2.1.forgery.leafIndex
      (result.1.2.1.forgery.message,
        result.1.2.1.forgery.signature.randomness))).getD
          (fun _ => ⟨0, by simp [chainLength]⟩)

end XmssSecurity.CappedChain
