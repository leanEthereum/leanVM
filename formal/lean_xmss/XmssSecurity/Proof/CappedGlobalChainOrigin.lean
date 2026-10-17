import XmssSecurity.Proof.CappedChain.ChainOriginProbability

open OracleComp OracleSpec

namespace XmssSecurity.CappedChain

noncomputable def GlobalWinningOutcomeChainValueHasKeygenOrigin
    (keygenCache finalCache : QueryCache HashSpec) (secretKey : SecretKey)
    (outcome : GameOutcome) : Prop :=
  ∃ chain, WinningOutcomeChainValueHasKeygenOrigin keygenCache finalCache
    secretKey outcome chain

end XmssSecurity.CappedChain
