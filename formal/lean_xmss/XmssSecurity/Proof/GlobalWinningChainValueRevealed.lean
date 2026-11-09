module

public import XmssSecurity.Proof.GlobalBadEvent
public import XmssSecurity.Proof.CappedChain.ChainEventDecomposition

@[expose] public section

open OracleComp OracleSpec

namespace XmssSecurity

def GlobalWinningChainValueRevealed
    (cache : QueryCache HashSpec) (outcome : GameOutcome) : Prop :=
  ∃ chain, WinningOutcomeBadEventOccurs cache outcome (.chain chain) ∧
    CappedChain.OutcomeChainValueRevealed cache outcome chain

end XmssSecurity

