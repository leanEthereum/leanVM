module

public import XmssSecurity.Proof.LossDecomposition

@[expose] public section

/-!
# The second lane

`WinningSecondLaneBadEventOccurs` is a cached selection or a structural collision in the capped game
with the encoding trace, and `HasSecondLaneBound q adversary` says its probability is at most
`q / 2^digestBits`. `CappedExactFirstLane` splits a win into it and the exact first lane, and
`OwnSecondLane` proves the bound (`hasSecondLaneBound`).
-/

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

def WinningSecondLaneBadEventOccurs
    (execution : CappedEncodingTraceExecution) : Prop :=
  WinningCachedSelectionOccurs execution ∨
    WinningStructuralCollisionOccurs execution.2.1.1 execution.1

def HasSecondLaneBound
    (q : Nat) (adversary : Adversary) : Prop :=
  Pr{let x ← cappedDetailedGameWithEncodingTrace adversary}[WinningSecondLaneBadEventOccurs x] ≤
    q /
      ((2 ^ digestBits : Nat) : ENNReal)

end XmssSecurity
