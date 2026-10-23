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
  | .encoding .. => 12
  | .topChain .. => 1
  | .topLeaf .. => 2
  | .topMerkle .. => 3
  | .topEncoding .. => 12

/-- The step, `hi` and `lo` fields of a domain, as naturals. -/
def hashDomainNats : HashDomain → Nat × Nat × Nat
  | .chain leafIndex _ step => (step, 0, leafIndex)
  | .leaf leafIndex => (0, 0, leafIndex)
  | .merkle level node => (0, level.val + 1, node)
  | .encoding leafIndex => (0, 0, leafIndex)
  | .topChain key _ step => (step, topFlag, key)
  | .topLeaf key => (0, topFlag, key)
  | .topMerkle level node => (0, topFlag + level.val + 1, node)
  | .topEncoding key => (0, topFlag, key)

@[simp]
theorem length_bytesLE (byteCount : Nat) (value : BitVec (8 * byteCount)) :
    (bytesLE byteCount value).length = byteCount := by
  simp [bytesLE]

@[simp]
theorem length_bytesLE_digest (value : Digest) : (bytesLE 16 value).length = 16 :=
  length_bytesLE 16 value

@[simp]
theorem length_bytesLE_publicParameter (value : PublicParameter) :
    (bytesLE 16 value).length = 16 :=
  length_bytesLE 16 value

@[simp]
theorem length_bytesLE_message (value : Message) : (bytesLE 32 value).length = 32 :=
  length_bytesLE 32 value


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

/-- A concatenation determines its two halves. -/
theorem bitVec_append_inj {n m : Nat} {a a' : BitVec n} {b b' : BitVec m}
    (h : a ++ b = a' ++ b') : a = a' ∧ b = b' := by
  constructor
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have := congrArg (fun v : BitVec (n + m) => v.getLsbD (m + i)) h
    simpa [BitVec.getLsbD_append] using this
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have := congrArg (fun v : BitVec (n + m) => v.getLsbD i) h
    simpa [BitVec.getLsbD_append, hi] using this

theorem fieldBytes_injective' {t1 t2 : TweakFields} (h : fieldBytes t1 = fieldBytes t2) :
    t1 = t2 := by
  obtain ⟨tag1, step1, hi1, lo1⟩ := t1
  obtain ⟨tag2, step2, hi2, lo2⟩ := t2
  simp only [fieldBytes] at h
  obtain ⟨h, _⟩ := List.append_inj' h (by simp [length_bytesLE])
  obtain ⟨h, htag⟩ := List.append_inj' h (by simp [length_bytesLE])
  obtain ⟨hlo, hhi⟩ := List.append_inj' h (by simp [length_bytesLE])
  have hb : (step1 ++ tag1 : BitVec 8) = step2 ++ tag2 := bytesLE_injective 1 htag
  obtain ⟨hstep, htag⟩ := bitVec_append_inj hb
  simp only [bytesLE_injective 4 hlo, bytesLE_injective 3 hhi, hstep, htag]

theorem fieldBytes_injective : Function.Injective fieldBytes :=
  fun _ _ h => fieldBytes_injective' h

@[simp]
theorem hashDomainFields_tag (domain : HashDomain) :
    (hashDomainFields domain).tag = BitVec.ofNat 5 (hashDomainTag domain) := by
  cases domain <;> rfl

private theorem ofNat_eq_of_lt {w left right : Nat}
    (hleft : left < 2 ^ w) (hright : right < 2 ^ w)
    (heq : BitVec.ofNat w left = BitVec.ofNat w right) : left = right := by
  have := congrArg BitVec.toNat heq
  rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hleft,
    Nat.mod_eq_of_lt hright] at this

private theorem hashDomainTag_lt (domain : HashDomain) : hashDomainTag domain < 2 ^ 5 := by
  cases domain <;> norm_num [hashDomainTag]

private theorem leafIndex_lt_32 (leafIndex : LeafIndex) : leafIndex.val < 2 ^ 32 := by
  change leafIndex.val < lifetime
  exact leafIndex.isLt

private theorem merkleNode_lt_32 (node : MerkleNode) : node.val < 2 ^ 32 := by
  change node.val < lifetime
  exact node.isLt

theorem hashDomainFields_eq (domain : HashDomain) :
    hashDomainFields domain = tweakFields (hashDomainTag domain) (hashDomainNats domain).1
      (hashDomainNats domain).2.1 (hashDomainNats domain).2.2 := by
  cases domain <;> rfl

private theorem hashDomainNats_lt (domain : HashDomain) :
    (hashDomainNats domain).1 < 2 ^ 3 ∧ (hashDomainNats domain).2.1 < 2 ^ 24 ∧
      (hashDomainNats domain).2.2 < 2 ^ 32 := by
  cases domain with
  | chain leafIndex _ step =>
      have := leafIndex.isLt; have := step.isLt
      simp only [lifetime, treeHeight, chainLength, winternitzBits] at *
      simp [hashDomainNats]; omega
  | leaf leafIndex => have := leafIndex.isLt; simp only [lifetime, treeHeight] at *; simp [hashDomainNats]; omega
  | merkle level node =>
      have := level.isLt; have := node.isLt
      simp only [lifetime, treeHeight] at *; simp [hashDomainNats]; omega
  | encoding leafIndex => have := leafIndex.isLt; simp only [lifetime, treeHeight] at *; simp [hashDomainNats]; omega
  | topChain key _ step =>
      have := key.isLt; have := step.isLt
      simp only [topLifetime, treeHeight, chainLength, winternitzBits] at *
      simp [hashDomainNats, topFlag]; omega
  | topLeaf key => have := key.isLt; simp only [topLifetime, treeHeight] at *; simp [hashDomainNats, topFlag]; omega
  | topMerkle level node =>
      have := level.isLt; have := node.isLt
      simp only [topLifetime, treeHeight] at *; simp [hashDomainNats, topFlag]; omega
  | topEncoding key => have := key.isLt; simp only [topLifetime, treeHeight] at *; simp [hashDomainNats, topFlag]; omega

/-- The top layer's domains. -/
def HashDomain.isTop : HashDomain → Bool
  | .topChain .. | .topLeaf .. | .topMerkle .. | .topEncoding .. => true
  | _ => false

private theorem hashDomainNats_hi_lt_iff (domain : HashDomain) :
    (hashDomainNats domain).2.1 < topFlag ↔ domain.isTop = false := by
  cases domain with
  | merkle level _ => have := level.isLt; simp only [treeHeight] at this; simp [hashDomainNats, HashDomain.isTop, topFlag]; omega
  | topMerkle level _ => simp [hashDomainNats, HashDomain.isTop, topFlag]; omega
  | _ => simp [hashDomainNats, HashDomain.isTop, topFlag]

/-- The address fixes a domain up to its chain index: domains with equal address fields have suffixes
of equal length, and are equal once their suffixes are. -/
theorem domain_eq_of_hashDomainFields_eq {left right : HashDomain}
    (heq : hashDomainFields left = hashDomainFields right) :
    (domainSuffix left).length = (domainSuffix right).length ∧
      (domainSuffix left = domainSuffix right → left = right) := by
  have htagBits := congrArg TweakFields.tag heq
  rw [hashDomainFields_tag, hashDomainFields_tag] at htagBits
  have htag := ofNat_eq_of_lt (hashDomainTag_lt left) (hashDomainTag_lt right) htagBits
  rw [hashDomainFields_eq, hashDomainFields_eq] at heq
  obtain ⟨hls, hlh, hll⟩ := hashDomainNats_lt left
  obtain ⟨hrs, hrh, hrl⟩ := hashDomainNats_lt right
  have hstep := ofNat_eq_of_lt hls hrs (congrArg TweakFields.step heq)
  have hhi := ofNat_eq_of_lt hlh hrh (congrArg TweakFields.hi heq)
  have hlo := ofNat_eq_of_lt hll hrl (congrArg TweakFields.lo heq)
  have chain_eq : ∀ left right : ChainIndex,
      bytesLE 16 (BitVec.ofNat 128 left.val) = bytesLE 16 (BitVec.ofNat 128 right.val) →
        left = right := by
    intro left right h
    have := congrArg BitVec.toNat (bytesLE_injective 16 h)
    have hl := left.isLt; have hr := right.isLt
    norm_num [numChains] at this hl hr
    exact Fin.ext (by omega)
  have hlayer := (hashDomainNats_hi_lt_iff left).symm.trans (hhi ▸ hashDomainNats_hi_lt_iff right)
  cases left <;> cases right <;> simp only [HashDomain.isTop] at hlayer <;> (try simp at hlayer) <;>
    simp only [hashDomainTag, hashDomainNats, topFlag] at htag hstep hhi hlo hll hrl hlh hrh <;>
    (try omega) <;>
    refine ⟨by simp [domainSuffix], fun hsuffix => ?_⟩ <;>
    simp only [domainSuffix] at hsuffix
  all_goals (try obtain rfl := chain_eq _ _ hsuffix)
  all_goals (congr 1 <;> apply Fin.ext <;> omega)

theorem domain_eq_of_tweakableHashInput_eq (parameter : PublicParameter)
    {leftDomain rightDomain : HashDomain} {leftMessage rightMessage : HashInput}
    (heq : tweakableHashInput parameter leftDomain leftMessage =
      tweakableHashInput parameter rightDomain rightMessage) :
    leftDomain = rightDomain := by
  have hfront :
      (bytesLE 16 parameter ++ tweakBytes leftDomain) ++ (leftMessage ++ domainSuffix leftDomain) =
        (bytesLE 16 parameter ++ tweakBytes rightDomain) ++
          (rightMessage ++ domainSuffix rightDomain) := by
    simpa [tweakableHashInput, List.append_assoc] using heq
  have hprefix := (List.append_inj hfront (by simp [tweakBytes])).1
  obtain ⟨hlength, hdomain⟩ := domain_eq_of_hashDomainFields_eq
    (fieldBytes_injective (List.append_right_injective (bytesLE 16 parameter) hprefix))
  unfold tweakableHashInput at heq
  exact hdomain (List.append_inj' heq hlength).2

theorem payload_eq_of_tweakableHashInput_eq (parameter : PublicParameter)
    (domain : HashDomain) {left right : HashInput}
    (heq : tweakableHashInput parameter domain left =
      tweakableHashInput parameter domain right) :
    left = right := by
  unfold tweakableHashInput at heq
  exact List.append_right_injective (bytesLE 16 parameter ++ tweakBytes domain)
    (List.append_left_injective (domainSuffix domain) heq)

namespace Concrete

theorem digestBytes_injective : Function.Injective digestBytes :=
  bytesLE_injective 16

theorem messageBytes_injective : Function.Injective messageBytes :=
  bytesLE_injective 32

theorem randomnessBytes_injective : Function.Injective randomnessBytes :=
  bytesLE_injective 16

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
        messageBytes rightMessage ++ randomnessBytes rightRandomness := heq
  obtain ⟨hmessage, hrandomness⟩ := List.append_inj hpairs
    ((length_bytesLE 32 leftMessage).trans (length_bytesLE 32 rightMessage).symm)
  exact Prod.ext (messageBytes_injective hmessage) (randomnessBytes_injective hrandomness)

theorem leafPayload_injective : Function.Injective leafPayload := by
  intro left right heq
  apply List.ofFn_injective
  exact flatMap_injective_of_eq_length digestBytes digestBytes_injective 16
    (fun value => length_bytesLE 16 value) (by simp) heq

theorem nodePayload_injective :
    Function.Injective fun input : Digest × Digest => nodePayload input.1 input.2 := by
  rintro ⟨leftFirst, leftSecond⟩ ⟨rightFirst, rightSecond⟩ heq
  obtain ⟨hfirst, hsecond⟩ := List.append_inj heq
    ((length_bytesLE 16 leftFirst).trans (length_bytesLE 16 rightFirst).symm)
  exact Prod.ext (digestBytes_injective hfirst) (digestBytes_injective hsecond)

namespace CacheView

theorem digestAt_eq_of_cache_eq_some {cache : QueryCache HashSpec} {input : HashInput}
    {output : HashOutput} (hcache : cache input = some output) :
    digestAt cache input = truncateHash output := by
  simp [digestAt, hcache]

theorem encodingInput_cached_of_decode_some
    (cache : QueryCache HashSpec) (parameter : PublicParameter) (leafIndex : LeafIndex)
    (message : Message) (randomness : Randomness) (encoding : Encoding)
    (hdecode : TargetSum.decodeDigest
      (encodingHash cache parameter leafIndex (message, randomness)) = some encoding) :
    ∃ output, cache (encodingInput parameter leafIndex (message, randomness)) = some output := by
  cases hcache : cache (encodingInput parameter leafIndex (message, randomness)) with
  | some output => exact ⟨output, rfl⟩
  | none =>
      rw [encodingHash, digestAt, hcache, TargetSum.decodeDigest_zero_eq_none] at hdecode
      contradiction

@[simp]
theorem chainStep_eq (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (leafIndex : LeafIndex) (chain : ChainIndex) (position : Nat) (value : Digest)
    (hposition : position < chainLength - 1) :
    chainStep cache parameter leafIndex chain position value =
      digestAt cache (chainInput parameter leafIndex chain ⟨position, hposition⟩ value) := by
  simp [chainStep, hposition]

@[simp]
theorem nodeHash_eq (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (leafIndex : LeafIndex) (level : Nat) (left right : Digest)
    (hlevel : level < treeHeight) :
    nodeHash cache parameter leafIndex level left right =
      digestAt cache (nodeInput parameter leafIndex ⟨level, hlevel⟩ left right) := by
  simp [nodeHash, hlevel]

theorem encodingInput_injective (parameter : PublicParameter) (leafIndex : LeafIndex) :
    Function.Injective (encodingInput parameter leafIndex) := by
  intro left right heq
  apply Concrete.encodingPayload_injective
  exact payload_eq_of_tweakableHashInput_eq parameter (.encoding leafIndex) heq

/-- Serialized encoding inputs are separated by leaf index as well as by message and randomness. -/
theorem encodingInput_eq_iff (parameter : PublicParameter)
    (leftLeafIndex rightLeafIndex : LeafIndex) (left right : Message × Randomness) :
    encodingInput parameter leftLeafIndex left =
        encodingInput parameter rightLeafIndex right ↔
      leftLeafIndex = rightLeafIndex ∧ left = right := by
  constructor
  · intro heq
    have hdomain : HashDomain.encoding leftLeafIndex = .encoding rightLeafIndex :=
      domain_eq_of_tweakableHashInput_eq parameter heq
    have hleafIndex : leftLeafIndex = rightLeafIndex := HashDomain.encoding.inj hdomain
    subst rightLeafIndex
    exact ⟨rfl, encodingInput_injective parameter leftLeafIndex heq⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem leafIndex_eq_of_encodingInput_eq (parameter : PublicParameter)
    {leftLeafIndex rightLeafIndex : LeafIndex} {left right : Message × Randomness}
    (heq : encodingInput parameter leftLeafIndex left =
      encodingInput parameter rightLeafIndex right) :
    leftLeafIndex = rightLeafIndex :=
  (encodingInput_eq_iff parameter leftLeafIndex rightLeafIndex left right).mp heq |>.1

theorem chainInput_injective (parameter : PublicParameter) (leafIndex : LeafIndex)
    (chain : ChainIndex) (position : ChainStep) :
    Function.Injective (chainInput parameter leafIndex chain position) := by
  intro left right heq
  apply Concrete.digestBytes_injective
  exact payload_eq_of_tweakableHashInput_eq parameter (.chain leafIndex chain position) heq

theorem leafInput_injective (parameter : PublicParameter) (leafIndex : LeafIndex) :
    Function.Injective (leafInput parameter leafIndex) := by
  intro left right heq
  apply Concrete.leafPayload_injective
  exact payload_eq_of_tweakableHashInput_eq parameter (.leaf leafIndex) heq

end CacheView

end Concrete

end XmssSecurity
