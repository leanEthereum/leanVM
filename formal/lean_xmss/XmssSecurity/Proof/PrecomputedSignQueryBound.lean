import XmssSecurity.Proof.ConcreteQueryBound

open OracleComp OracleSpec

namespace XmssSecurity

theorem Concrete.precomputedSignAttempt_queryBound_zero_at_other_encodingInput
    (secretKey : SecretKey) (leafIndex targetLeafIndex : LeafIndex)
    (message : Message) (randomness : Randomness) (targetInput : Message × Randomness)
    (hne : Concrete.CacheView.encodingInput secretKey.parameter leafIndex
        (message, randomness) ≠
      Concrete.CacheView.encodingInput secretKey.parameter targetLeafIndex targetInput) :
    (Concrete.precomputedSignAttempt secretKey leafIndex message randomness :
      OracleComp HashSpec (Option Signature)).IsQueryBoundP
        (· = Concrete.CacheView.encodingInput secretKey.parameter targetLeafIndex targetInput) 0 := by
  rw [Concrete.precomputedSignAttempt]
  refine OracleComp.isQueryBoundP_bind (m := 0)
    (Concrete.encodingHash_queryBound_zero_at_other_input secretKey.parameter leafIndex
      message randomness
      (Concrete.CacheView.encodingInput secretKey.parameter targetLeafIndex targetInput) hne) ?_
  intro digest _
  split <;> simp

end XmssSecurity
