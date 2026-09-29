import XmssSecurity.Proof.CacheQuerySupport
import XmssSecurity.Proof.IdealStatement
import XmssSecurity.Proof.HashInputLemmas

open OracleComp OracleSpec

namespace XmssSecurity

/-- Inputs of one concrete hash address: its 32-byte tweak and public-parameter prefix, ending with
its domain suffix. -/
def AtHashAddress (parameter : PublicParameter) (domain : HashDomain)
    (input : HashInput) : Prop :=
  input.take 32 = tweakBytes domain ++ bytesLE 16 parameter ∧ domainSuffix domain <:+ input

noncomputable instance (parameter : PublicParameter) (domain : HashDomain) :
    DecidablePred (AtHashAddress parameter domain) :=
  Classical.decPred _

private theorem suffix_eq_of_length_eq {left right input : HashInput}
    (hleft : left <:+ input) (hright : right <:+ input) (hlength : left.length = right.length) :
    left = right :=
  (List.suffix_of_suffix_length_le hleft hright hlength.le).eq_of_length hlength

theorem atHashAddress_unique
    (parameter : PublicParameter) (left right : HashDomain)
    (input : HashInput)
    (hleft : AtHashAddress parameter left input)
    (hright : AtHashAddress parameter right input) :
    left = right := by
  have htweaks : tweakBytes left = tweakBytes right := by
    exact List.append_left_injective (bytesLE 16 parameter)
      (hleft.1.symm.trans hright.1)
  obtain ⟨hlength, hdomain⟩ := domain_eq_of_hashDomainFields_eq (fieldBytes_injective htweaks)
  exact hdomain (suffix_eq_of_length_eq hleft.2 hright.2 hlength)

@[simp]
theorem atHashAddress_tweakableHashInput_iff (parameter : PublicParameter)
    (targetDomain calledDomain : HashDomain) (payload : HashInput) :
    AtHashAddress parameter targetDomain
      (tweakableHashInput parameter calledDomain payload) ↔
      calledDomain = targetDomain := by
  have hcalled : AtHashAddress parameter calledDomain
      (tweakableHashInput parameter calledDomain payload) := by
    have hprefix : (tweakBytes calledDomain ++ bytesLE 16 parameter).length = 32 := by
      simp [tweakBytes]
    refine ⟨?_, List.suffix_append _ _⟩
    rw [tweakableHashInput, List.append_assoc,
      List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
  exact ⟨fun htarget => atHashAddress_unique parameter _ _ _ hcalled htarget,
    fun h => h ▸ hcalled⟩

/-- One tweakable-hash call makes exactly one query in its own address class. -/
theorem Concrete.tweakableHash_queryBound_atAddress
    (parameter : PublicParameter) (domain : HashDomain) (payload : HashInput) :
    (Concrete.tweakableHash parameter domain payload : OracleComp HashSpec Digest).IsQueryBoundP
      (AtHashAddress parameter domain) 1 := by
  simp [Concrete.tweakableHash, Concrete.oracleHash]

/-- One tweakable-hash call makes no query in a distinct address class. -/
theorem Concrete.tweakableHash_queryBound_atOtherAddress
    (parameter : PublicParameter) (targetDomain calledDomain : HashDomain)
    (payload : HashInput) (hne : calledDomain ≠ targetDomain) :
    (Concrete.tweakableHash parameter calledDomain payload :
      OracleComp HashSpec Digest).IsQueryBoundP
        (AtHashAddress parameter targetDomain) 0 := by
  simp [Concrete.tweakableHash, Concrete.oracleHash, hne]

end XmssSecurity
