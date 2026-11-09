module

public import XmssSecurity.Proof.CachedSelectionBound
public import XmssSecurity.Proof.CappedUnifiedExpectedDigest
public import XmssSecurity.Proof.LossDecomposition

@[expose] public section

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
