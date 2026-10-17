import XmssSecurity.Proof.GlobalBadEvent
import XmssSecurity.Proof.CappedChain.ChainEventDecomposition

open OracleComp OracleSpec

namespace XmssSecurity

def GlobalWinningChainValueRevealed
    (cache : QueryCache HashSpec) (outcome : GameOutcome) : Prop :=
  ∃ chain, WinningOutcomeBadEventOccurs cache outcome (.chain chain) ∧
    CappedChain.OutcomeChainValueRevealed cache outcome chain

end XmssSecurity

