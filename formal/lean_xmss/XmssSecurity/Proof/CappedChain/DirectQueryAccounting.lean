module

public import XmssSecurity.Proof.CappedChain.ChainInputTrace

@[expose] public section

/-!
# Hash costs of the adversary's and the verifier's queries

`directHashActionCost` charges one per adversary hash query and nothing for a uniform or signing
query: the number of hash inputs the query adds to the action trace
(`attackerActionFragment_hashInputs_length`). `verifierHashQueryCost` charges one per verifier hash
query. The first lane's hazard counts use both (`CappedExactFirstLaneTransportReduction`,
`CappedExactFirstLaneBound`).
-/

open OracleComp OracleSpec

namespace XmssSecurity.CappedChain

def directHashActionCost :
    (OracleWorld + SigningSpec).Domain → Nat
  | .inl (.inr _) => 1
  | _ => 0

@[simp]
theorem attackerActionFragment_hashInputs_length
    (input : (OracleWorld + SigningSpec).Domain)
    (output : (OracleWorld + SigningSpec).Range input) :
    (attackerActionFragment input output).hashInputs.length =
      directHashActionCost input := by
  rcases input with (uniformOrHash | request)
  · rcases uniformOrHash with n | hashInput <;> rfl
  · rfl

def verifierHashQueryCost : OracleWorld.Domain → Nat
  | .inl _ => 0
  | .inr _ => 1

end XmssSecurity.CappedChain
