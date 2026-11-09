module

public import XmssSecurity.Proof.CappedChain.ChainOriginProbability

@[expose] public section

open OracleComp OracleSpec

namespace XmssSecurity.CappedChain

noncomputable def GlobalWinningOutcomeChainValueHasKeygenOrigin
    (keygenCache finalCache : QueryCache HashSpec) (secretKey : SecretKey)
    (outcome : GameOutcome) : Prop :=
  ∃ chain, WinningOutcomeChainValueHasKeygenOrigin keygenCache finalCache
    secretKey outcome chain

end XmssSecurity.CappedChain
