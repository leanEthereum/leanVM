import XmssSecurity.Proof.Deterministic.TrialSampling

open OracleComp OracleSpec

namespace XmssSecurity.Seeded

set_option backward.isDefEq.respectTransparency false

theorem evalDist_tableSign {State : Type} (hash : QueryImpl HashSpec (StateT State ProbComp))
    (secretKey : XmssSecurity.SecretKey) (epoch : Epoch) (message : Message) (state : State) :
    𝒟[do
      let tape ← sampleTrialTape
      (simulateQ (worldHandler hash) (liftM (tableSign (fun position => tape position.2)
        secretKey epoch message : OracleComp HashSpec (Option Signature)) : OracleComp OracleWorld _)).run state] =
      𝒟[(simulateQ (worldHandler hash) (Concrete.precomputedCappedSign secretKey epoch message)).run state] := by
  unfold tableSign Concrete.precomputedCappedSign
  exact evalDist_tableSignFrom hash secretKey epoch message signingAttemptLimit 0 (by decide) state

end XmssSecurity.Seeded
