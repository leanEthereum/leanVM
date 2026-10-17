import XmssSecurity.Proof.CappedChain.SourceDirectTrace

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

theorem sourceUnloggedMappedAdversaryImpl_consistent_query_bound
    (publicKey : PublicKey) (secretKey : SecretKey) (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp OracleWorld α)
    (cache : QueryCache HashSpec) (q : Nat)
    (hbound : HashQueryBound (sourceUnloggedMappedAdversaryImpl publicKey secretKey input >>= next) cache q)
    (result : (OracleWorld + SigningSpec).Range input × QueryCache HashSpec)
    (hr : result ∈ support ((simulateQ romImpl (sourceUnloggedMappedAdversaryImpl publicKey secretKey input)).run cache)) :
    directHashActionCost input ≤ q ∧ HashQueryBound (next result.1) result.2 (q - directHashActionCost input) := by
  cases input with
  | inl input =>
      simp only [sourceUnloggedMappedAdversaryImpl, simulateQ_spec_query] at hr
      have h := hashQueryBound_query_bind input next cache q hbound result hr
      cases input <;> exact h
  | inr request =>
      exact ⟨Nat.zero_le q, hashQueryBound_bind_right _ next cache q hbound result hr⟩

end XmssSecurity.CappedChain
