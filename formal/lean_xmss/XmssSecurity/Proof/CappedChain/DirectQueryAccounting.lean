module

public import XmssSecurity.Proof.CappedChain.SourceDirectTrace

@[expose] public section

open OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false

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
