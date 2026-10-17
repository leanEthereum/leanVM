import XmssSecurity.Proof.CappedExactFirstLaneBound

namespace XmssSecurity.Proof

/-- What the lanes prove about the model with precomputed keys. -/
theorem concreteScheme_afterKeygenSecurity : HasAfterKeygenSecurity Concrete.scheme :=
  concreteScheme_afterKeygenSecurity_of_exactFirstLaneBounds CappedChain.hasExactFirstLaneBounds

end XmssSecurity.Proof
