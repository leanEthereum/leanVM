module

public import XmssSecurity.Proof.CappedChain.ChainEventDecomposition
public import XmssSecurity.Proof.WinningEventReduction

@[expose] public section

open OracleComp OracleSpec

namespace XmssSecurity.CappedChain

noncomputable def WinningOutcomeChainValueHasKeygenOrigin
    (keygenCache finalCache : QueryCache HashSpec) (secretKey : SecretKey)
    (outcome : GameOutcome) (chain : ChainIndex) : Prop :=
  WinningOutcomeBadEventOccurs finalCache outcome (.chain chain) ∧
    OutcomeChainValueHasKeygenOrigin keygenCache finalCache secretKey outcome chain

end XmssSecurity.CappedChain
