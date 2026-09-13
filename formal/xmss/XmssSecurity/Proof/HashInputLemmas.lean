import XmssSecurity.Proof.IdealStatement
import XmssSecurity.Proof.StatementLemmas
import XmssSecurity.Proof.EncodingLemmas
import Mathlib.Tactic.NormNum

open OracleSpec

namespace XmssSecurity

def hashDomainTag : HashDomain → Nat
  | .chain .. => 1
  | .leaf .. => 2
  | .merkle .. => 3
  | .encoding .. => 4

@[simp]
theorem length_bytesLE (byteCount : Nat) (value : BitVec (8 * byteCount)) :
    (bytesLE byteCount value).length = byteCount := by
  simp [bytesLE]

theorem bytesLE_injective (byteCount : Nat) : Function.Injective (bytesLE byteCount) := by
  intro left right heq
  have hbytes :
      (fun index : Fin byteCount => UInt8.ofBitVec (left.extractLsb' (8 * index.val) 8)) =
        (fun index : Fin byteCount => UInt8.ofBitVec (right.extractLsb' (8 * index.val) 8)) :=
    List.ofFn_injective heq
  apply BitVec.eq_of_getLsbD_eq
  intro bit hbit
  let byte : Fin byteCount := ⟨bit / 8, by omega⟩
  have hbyte := congrFun hbytes byte
  have hbyteBits := congrArg UInt8.toBitVec hbyte
  have hlocal := congrArg (fun value => value.getLsbD (bit % 8)) hbyteBits
  have hmod : bit % 8 < 8 := Nat.mod_lt bit (by omega)
  have hposition : 8 * (bit / 8) + bit % 8 = bit := by
    omega
  simpa [byte, BitVec.getLsbD_extractLsb', hmod, hposition] using hlocal

@[simp]
theorem length_fieldBytes (fields : TweakFields) : (fieldBytes fields).length = 16 := by
  simp [fieldBytes]

theorem fieldBytes_injective : Function.Injective fieldBytes := by
  intro left right heq
  simp only [fieldBytes] at heq
  obtain ⟨hfront, hepochBytes⟩ := List.append_inj heq (by simp)
  have hfields := List.append_left_injective (List.replicate 4 0) hfront
  obtain ⟨hheader, hpositionBytes⟩ := List.append_inj hfields (by simp)
  have htagPrefix := List.append_left_injective [0, 0] hheader
  have htagBytes := List.append_right_injective [protocolDomainSep] htagPrefix
  have htag : left.tag = right.tag := bytesLE_injective 1 htagBytes
  have hposition : left.position = right.position := bytesLE_injective 4 hpositionBytes
  have hepoch : left.epoch = right.epoch := bytesLE_injective 4 hepochBytes
  cases left
  cases right
  simp_all

@[simp]
theorem hashDomainFields_tag (domain : HashDomain) :
    (hashDomainFields domain).tag = BitVec.ofNat 8 (hashDomainTag domain) := by
  cases domain <;> rfl

private theorem ofNat32_eq_of_lt {left right : Nat}
    (hleft : left < 2 ^ 32) (hright : right < 2 ^ 32)
    (heq : BitVec.ofNat 32 left = BitVec.ofNat 32 right) : left = right := by
  have := congrArg BitVec.toNat heq
  norm_num at hleft hright this ⊢
  omega

private theorem ofNat8_eq_of_lt {left right : Nat}
    (hleft : left < 2 ^ 8) (hright : right < 2 ^ 8)
    (heq : BitVec.ofNat 8 left = BitVec.ofNat 8 right) : left = right := by
  have := congrArg BitVec.toNat heq
  norm_num at hleft hright this ⊢
  omega

private theorem hashDomainTag_lt_8 (domain : HashDomain) : hashDomainTag domain < 2 ^ 8 := by
  cases domain <;> norm_num [hashDomainTag]

private theorem epoch_lt_32 (epoch : Epoch) : epoch.val < 2 ^ 32 := by
  change epoch.val < lifetime
  exact epoch.isLt

private theorem chainPosition_lt_32 (chain : ChainIndex) (step : ChainStep) :
    chainLength * chain.val + step.val < 2 ^ 32 := by
  have hchain := chain.isLt
  have hstep := step.isLt
  norm_num [chainLength, winternitzBits, numChains] at hchain hstep ⊢
  omega

private theorem merkleLevel_lt_32 (level : MerkleLevel) : level.val + 1 < 2 ^ 32 := by
  have hlevel := level.isLt
  norm_num [treeHeight] at hlevel ⊢
  omega

private theorem merkleNode_lt_32 (node : MerkleNode) : node.val < 2 ^ 32 := by
  change node.val < lifetime
  exact node.isLt

theorem hashDomainFields_injective : Function.Injective hashDomainFields := by
  intro left right heq
  have htagBits := congrArg TweakFields.tag heq
  rw [hashDomainFields_tag, hashDomainFields_tag] at htagBits
  have htag := ofNat8_eq_of_lt (hashDomainTag_lt_8 left) (hashDomainTag_lt_8 right) htagBits
  cases left <;> cases right <;> simp [hashDomainTag] at htag
  all_goals simp only [hashDomainFields] at heq
  · rename_i leftEpoch leftChain leftStep rightEpoch rightChain rightStep
    have hposition := congrArg TweakFields.position heq
    have hepoch := congrArg TweakFields.epoch heq
    have hpositionNat := ofNat32_eq_of_lt
      (chainPosition_lt_32 leftChain leftStep) (chainPosition_lt_32 rightChain rightStep) hposition
    have hepochNat := ofNat32_eq_of_lt (epoch_lt_32 leftEpoch) (epoch_lt_32 rightEpoch) hepoch
    have hleftChain := leftChain.isLt
    have hrightChain := rightChain.isLt
    have hleftStep := leftStep.isLt
    have hrightStep := rightStep.isLt
    norm_num [chainLength, winternitzBits, numChains] at hpositionNat hleftChain hrightChain hleftStep hrightStep
    congr
    · exact Fin.ext hepochNat
    · apply Fin.ext
      omega
    · apply Fin.ext
      omega
  · rename_i leftEpoch rightEpoch
    have hepoch := congrArg TweakFields.epoch heq
    exact congrArg HashDomain.leaf
      (Fin.ext (ofNat32_eq_of_lt (epoch_lt_32 leftEpoch) (epoch_lt_32 rightEpoch) hepoch))
  · rename_i leftLevel leftNode rightLevel rightNode
    have hposition := congrArg TweakFields.position heq
    have hnode := congrArg TweakFields.epoch heq
    have hlevelNat := ofNat32_eq_of_lt
      (merkleLevel_lt_32 leftLevel) (merkleLevel_lt_32 rightLevel) hposition
    have hnodeNat := ofNat32_eq_of_lt (merkleNode_lt_32 leftNode) (merkleNode_lt_32 rightNode) hnode
    congr
    · exact Fin.ext (by omega)
    · exact Fin.ext hnodeNat
  · rename_i leftEpoch rightEpoch
    have hepoch := congrArg TweakFields.epoch heq
    exact congrArg HashDomain.encoding
      (Fin.ext (ofNat32_eq_of_lt (epoch_lt_32 leftEpoch) (epoch_lt_32 rightEpoch) hepoch))

theorem tweakBytes_injective : Function.Injective tweakBytes :=
  fieldBytes_injective.comp hashDomainFields_injective

theorem domain_eq_of_tweakableHashInput_eq (parameter : PublicParameter)
    {leftDomain rightDomain : HashDomain} {leftMessage rightMessage : HashInput}
    (heq : tweakableHashInput parameter leftDomain leftMessage =
      tweakableHashInput parameter rightDomain rightMessage) :
    leftDomain = rightDomain := by
  apply tweakBytes_injective
  have heq' :
      tweakBytes leftDomain ++ (bytesLE 16 parameter ++ leftMessage) =
        tweakBytes rightDomain ++ (bytesLE 16 parameter ++ rightMessage) := by
    simpa [tweakableHashInput, List.append_assoc] using heq
  exact (List.append_inj heq' (by simp [tweakBytes])).1

theorem payload_eq_of_tweakableHashInput_eq (parameter : PublicParameter)
    (domain : HashDomain) {left right : HashInput}
    (heq : tweakableHashInput parameter domain left =
      tweakableHashInput parameter domain right) :
    left = right := by
  exact List.append_right_injective
    (tweakBytes domain ++ bytesLE 16 parameter) heq

namespace Concrete

theorem digestBytes_injective : Function.Injective digestBytes :=
  bytesLE_injective 16

theorem messageBytes_injective : Function.Injective messageBytes :=
  bytesLE_injective 32

theorem randomnessBytes_injective : Function.Injective randomnessBytes :=
  bytesLE_injective 24

private theorem flatMap_injective_of_eq_length {α β : Type}
    (encode : α → List β) (hinjective : Function.Injective encode)
    (encodedLength : Nat) (hlength : ∀ value, (encode value).length = encodedLength)
    {left right : List α} (hsameLength : left.length = right.length)
    (heq : left.flatMap encode = right.flatMap encode) : left = right := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => rfl
      | cons => simp at hsameLength
  | cons head tail ih =>
      cases right with
      | nil => simp at hsameLength
      | cons rightHead rightTail =>
          simp only [List.flatMap_cons] at heq
          obtain ⟨hhead, htail⟩ := List.append_inj heq (by simp [hlength])
          congr
          · exact hinjective hhead
          · apply ih
            · simpa using Nat.succ.inj hsameLength
            · exact htail

theorem encodingPayload_injective :
    Function.Injective fun input : Message × Randomness => encodingPayload input.1 input.2 := by
  rintro ⟨leftMessage, leftRandomness⟩ ⟨rightMessage, rightRandomness⟩ heq
  have hpairs :
      messageBytes leftMessage ++ randomnessBytes leftRandomness =
        messageBytes rightMessage ++ randomnessBytes rightRandomness :=
    List.append_left_injective (List.replicate 8 0) heq
  obtain ⟨hmessage, hrandomness⟩ := List.append_inj hpairs (by simp [messageBytes])
  exact Prod.ext (messageBytes_injective hmessage) (randomnessBytes_injective hrandomness)

theorem leafPayload_injective : Function.Injective leafPayload := by
  intro left right heq
  apply List.ofFn_injective
  exact flatMap_injective_of_eq_length digestBytes digestBytes_injective 16
    (fun value => by simp [digestBytes]) (by simp) heq

theorem nodePayload_injective :
    Function.Injective fun input : Digest × Digest => nodePayload input.1 input.2 := by
  rintro ⟨leftFirst, leftSecond⟩ ⟨rightFirst, rightSecond⟩ heq
  obtain ⟨hfirst, hsecond⟩ := List.append_inj heq (by simp [digestBytes])
  exact Prod.ext (digestBytes_injective hfirst) (digestBytes_injective hsecond)

namespace CacheView

theorem digestAt_eq_of_cache_eq_some {cache : QueryCache HashSpec} {input : HashInput}
    {output : HashOutput} (hcache : cache input = some output) :
    digestAt cache input = truncateHash output := by
  simp [digestAt, hcache]

theorem encodingInput_cached_of_decode_some
    (cache : QueryCache HashSpec) (parameter : PublicParameter) (epoch : Epoch)
    (message : Message) (randomness : Randomness) (encoding : Encoding)
    (hdecode : TargetSum.decodeDigest
      (encodingHash cache parameter epoch (message, randomness)) = some encoding) :
    ∃ output, cache (encodingInput parameter epoch (message, randomness)) = some output := by
  cases hcache : cache (encodingInput parameter epoch (message, randomness)) with
  | some output => exact ⟨output, rfl⟩
  | none =>
      rw [encodingHash, digestAt, hcache, TargetSum.decodeDigest_zero_eq_none] at hdecode
      contradiction

@[simp]
theorem chainStep_eq (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (epoch : Epoch) (chain : ChainIndex) (position : Nat) (value : Digest)
    (hposition : position < chainLength - 1) :
    chainStep cache parameter epoch chain position value =
      digestAt cache (chainInput parameter epoch chain ⟨position, hposition⟩ value) := by
  simp [chainStep, hposition]

@[simp]
theorem nodeHash_eq (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (epoch : Epoch) (level : Nat) (left right : Digest)
    (hlevel : level < treeHeight) :
    nodeHash cache parameter epoch level left right =
      digestAt cache (nodeInput parameter epoch ⟨level, hlevel⟩ left right) := by
  simp [nodeHash, hlevel]

theorem encodingInput_injective (parameter : PublicParameter) (epoch : Epoch) :
    Function.Injective (encodingInput parameter epoch) := by
  intro left right heq
  apply Concrete.encodingPayload_injective
  exact payload_eq_of_tweakableHashInput_eq parameter (.encoding epoch) heq

/-- Serialized encoding inputs are separated by epoch as well as by message and randomness. -/
theorem encodingInput_eq_iff (parameter : PublicParameter)
    (leftEpoch rightEpoch : Epoch) (left right : Message × Randomness) :
    encodingInput parameter leftEpoch left =
        encodingInput parameter rightEpoch right ↔
      leftEpoch = rightEpoch ∧ left = right := by
  constructor
  · intro heq
    have hdomain : HashDomain.encoding leftEpoch = .encoding rightEpoch :=
      domain_eq_of_tweakableHashInput_eq parameter heq
    have hepoch : leftEpoch = rightEpoch := HashDomain.encoding.inj hdomain
    subst rightEpoch
    exact ⟨rfl, encodingInput_injective parameter leftEpoch heq⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem epoch_eq_of_encodingInput_eq (parameter : PublicParameter)
    {leftEpoch rightEpoch : Epoch} {left right : Message × Randomness}
    (heq : encodingInput parameter leftEpoch left =
      encodingInput parameter rightEpoch right) :
    leftEpoch = rightEpoch :=
  (encodingInput_eq_iff parameter leftEpoch rightEpoch left right).mp heq |>.1

theorem chainInput_injective (parameter : PublicParameter) (epoch : Epoch)
    (chain : ChainIndex) (position : ChainStep) :
    Function.Injective (chainInput parameter epoch chain position) := by
  intro left right heq
  apply Concrete.digestBytes_injective
  exact payload_eq_of_tweakableHashInput_eq parameter (.chain epoch chain position) heq

theorem leafInput_injective (parameter : PublicParameter) (epoch : Epoch) :
    Function.Injective (leafInput parameter epoch) := by
  intro left right heq
  apply Concrete.leafPayload_injective
  exact payload_eq_of_tweakableHashInput_eq parameter (.leaf epoch) heq

end CacheView

end Concrete

end XmssSecurity
