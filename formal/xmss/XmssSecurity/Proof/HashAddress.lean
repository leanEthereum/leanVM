import XmssSecurity.Proof.CacheQuerySupport
import XmssSecurity.Proof.IdealStatement
import XmssSecurity.Proof.HashInputLemmas

open OracleComp OracleSpec

namespace XmssSecurity

/-- Inputs with the 32-byte tweak and public-parameter prefix for one concrete hash address. -/
def AtHashAddress (parameter : PublicParameter) (domain : HashDomain)
    (input : HashInput) : Prop :=
  input.take 32 = tweakBytes domain ++ bytesLE 16 parameter

noncomputable instance (parameter : PublicParameter) (domain : HashDomain) :
    DecidablePred (AtHashAddress parameter domain) :=
  Classical.decPred _

theorem atHashAddress_unique
    (parameter : PublicParameter) (left right : HashDomain)
    (input : HashInput)
    (hleft : AtHashAddress parameter left input)
    (hright : AtHashAddress parameter right input) :
    left = right := by
  unfold AtHashAddress at hleft hright
  have htweaks : tweakBytes left = tweakBytes right := by
    exact List.append_left_injective (bytesLE 16 parameter)
      (hleft.symm.trans hright)
  exact tweakBytes_injective htweaks

@[simp]
theorem atHashAddress_tweakableHashInput_iff (parameter : PublicParameter)
    (targetDomain calledDomain : HashDomain) (payload : HashInput) :
    AtHashAddress parameter targetDomain
      (tweakableHashInput parameter calledDomain payload) ↔
      calledDomain = targetDomain := by
  have hprefix : (tweakBytes calledDomain ++ bytesLE 16 parameter).length = 32 := by
    simp [tweakBytes]
  rw [AtHashAddress, tweakableHashInput,
    List.take_append_of_le_length (by omega : 32 ≤
      (tweakBytes calledDomain ++ bytesLE 16 parameter).length)]
  rw [List.take_of_length_le (by omega :
    (tweakBytes calledDomain ++ bytesLE 16 parameter).length ≤ 32)]
  exact (List.append_left_injective (bytesLE 16 parameter)).eq_iff.trans
    tweakBytes_injective.eq_iff

/-- One tweakable-hash call makes exactly one query in its own address class. -/
theorem Concrete.tweakableHash_queryBound_atAddress
    (parameter : PublicParameter) (domain : HashDomain) (payload : HashInput) :
    (Concrete.tweakableHash parameter domain payload : OracleComp HashSpec Digest).IsQueryBoundP
      (AtHashAddress parameter domain) 1 := by
  simp [Concrete.tweakableHash, Concrete.oracleHash, AtHashAddress,
    tweakableHashInput, tweakBytes]

/-- One tweakable-hash call makes no query in a distinct address class. -/
theorem Concrete.tweakableHash_queryBound_atOtherAddress
    (parameter : PublicParameter) (targetDomain calledDomain : HashDomain)
    (payload : HashInput) (hne : calledDomain ≠ targetDomain) :
    (Concrete.tweakableHash parameter calledDomain payload :
      OracleComp HashSpec Digest).IsQueryBoundP
        (AtHashAddress parameter targetDomain) 0 := by
  simp [Concrete.tweakableHash, Concrete.oracleHash, hne]

end XmssSecurity
