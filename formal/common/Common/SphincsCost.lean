module

public import Common.CostCombinators
public import Statement.LeanSphincs

@[expose] public section

/-!
# leanSPHINCS's worst-case permutation calls

Bounds on every path (`QueryCostAtMost`, in calls of `π`) of the statement's leanSPHINCS over `π`:
key generation (`keygenFromSeed_cost`), the signer of one message, its WOTS+C counter search at the
cap of `2^32` trials per layer included (`sign_cost`), and the verifier (`verify_cost`). Every
addressed hash hashes at most `16 + 32 + 1024` bytes, so makes at most `8` calls
(`addressedHash_cost`); the bounds are crude, and only serve to keep the whole game's calls below
`2^128` (`Common.SufCma.stronglyUnforgeable_of_romBoundAdv`).
-/

open OracleComp OracleSpec
open HashSig HashSig.OverPermutation

namespace Common.SphincsCost

open Sphincs

-- Elaborating a combinator's bound at a literal size otherwise unfolds the combinator.
attribute [local irreducible] sequenceFin walkChain foldPath List.mapM List.range
  KeyGenerationAndSigning.merkleLevelsFrom KeyGenerationAndSigning.treeLevels
  KeyGenerationAndSigning.forsTreeOpen KeyGenerationAndSigning.keygenInternal
  KeyGenerationAndSigning.expandKey KeyGenerationAndSigning.signLayer
  KeyGenerationAndSigning.otsSignFrom KeyGenerationAndSigning.forsOpen

/-- The permutation calls of an addressed hash. -/
def thCost : ℕ := 8

theorem flatMap_length_const {α β : Type} (f : α → List β) (k : ℕ) (hf : ∀ x, (f x).length = k) :
    ∀ l : List α, (l.flatMap f).length = k * l.length
  | [] => by simp
  | x :: l => by
    rw [List.flatMap_cons, List.length_append, hf, flatMap_length_const f k hf l, List.length_cons]
    ring

theorem digestsPayload_length {n : ℕ} (d : Fin n → Digest) : (digestsPayload d).length = 16 * n := by
  have h := flatMap_length_const (fun x : Digest ↦ littleEndianBytes 16 x) 16
    (fun x ↦ by simp [littleEndianBytes]) (List.ofFn d)
  rw [List.length_ofFn] at h
  exact h

theorem addressedHashInput_length (publicSeed : PublicParameter) (address : Address)
    (payload : HashInput) :
    (addressedHashInput publicSeed address payload).length = 48 + payload.length := by
  simp [addressedHashInput, hasherInput, Address.toBytes, bigEndianBytes, littleEndianBytes]
  omega

namespace Verification

open Sphincs.Verification

theorem addressedHash_cost (publicSeed : PublicParameter) (address : Address) (payload : HashInput)
    (h : payload.length ≤ 1024) :
    QueryCostAtMost (addressedHash (HashSig.OverPermutation.keccakHash queryPermutation) publicSeed address payload) permutationCallCost
      thCost := by
  unfold addressedHash
  exact ((keccakHash_cost_le _ (k := 7) (by rw [addressedHashInput_length]; omega)).bind fun _ ↦
    isWeightBound_pure _ _ 0).mono (by simp [thCost])

theorem chainWalk_cost (publicSeed : PublicParameter) (layer : Layer) (tree : TreeIndex)
    (leaf : TreeLeafIndex) (chainIndex : ChainIndex) (start steps : ℕ) (v : Digest) :
    QueryCostAtMost (chainWalk (HashSig.OverPermutation.keccakHash queryPermutation) publicSeed layer tree leaf chainIndex start steps v)
      permutationCallCost (steps * thCost) :=
  walkChain_cost _ thCost (fun _ _ ↦ addressedHash_cost _ _ _ (by simp [littleEndianBytes]))
    start steps v

theorem recoverChain_cost (publicSeed : PublicParameter) (layer : Layer) (tree : TreeIndex)
    (leaf : TreeLeafIndex) (chainIndex : ChainIndex) (digit : WinternitzDigit) (v : Digest) :
    QueryCostAtMost (recoverChain (HashSig.OverPermutation.keccakHash queryPermutation) publicSeed layer tree leaf chainIndex digit v)
      permutationCallCost (3 * thCost) :=
  (chainWalk_cost _ _ _ _ _ _ _ _).mono
    (Nat.mul_le_mul_right _ (by simp [chainLength, winternitzBits]))

theorem leafHash_cost (publicSeed : PublicParameter) (layer : Layer) (tree : TreeIndex)
    (leaf : TreeLeafIndex) (endpoints : ChainIndex → Digest) :
    QueryCostAtMost (leafHash (HashSig.OverPermutation.keccakHash queryPermutation) publicSeed layer tree leaf endpoints)
      permutationCallCost thCost :=
  addressedHash_cost _ _ _ (by rw [digestsPayload_length]; simp [chainCount])

theorem encode_cost (publicSeed : PublicParameter) (layer : Layer) (tree : TreeIndex)
    (leaf : TreeLeafIndex) (message : Digest) (counter : EncodingCounter) :
    QueryCostAtMost (encode (HashSig.OverPermutation.keccakHash queryPermutation) publicSeed layer tree leaf message counter)
      permutationCallCost thCost := by
  unfold encode
  exact ((addressedHash_cost _ _ _ (by simp [littleEndianBytes, bigEndianBytes])).bind fun _ ↦
    isWeightBound_pure _ _ 0).mono (by simp)

/-- The calls of a one-time leaf's recovery. -/
def otsLeafCost : ℕ := thCost + (chainCount * (3 * thCost) + thCost)

theorem otsLeaf_cost (publicSeed : PublicParameter) (layer : Layer) (tree : TreeIndex)
    (leaf : TreeLeafIndex) (message : Digest) (counter : EncodingCounter)
    (values : ChainIndex → Digest) :
    QueryCostAtMost (otsLeaf (HashSig.OverPermutation.keccakHash queryPermutation) publicSeed layer tree leaf message counter values)
      permutationCallCost otsLeafCost := by
  unfold otsLeaf
  refine ((encode_cost _ _ _ _ _ _).bind fun e ↦ ?_).mono le_rfl
  cases e with
  | none => exact (isWeightBound_pure _ _ _).mono (Nat.zero_le _)
  | some _ =>
    exact (QueryCostAtMost.bind (sequenceFin_cost _ _ fun _ ↦ recoverChain_cost _ _ _ _ _ _ _)
      fun _ ↦ QueryCostAtMost.bind (leafHash_cost _ _ _ _ _) fun _ ↦ isWeightBound_pure _ _ 0).mono
        (by simp)

theorem treeFold_cost (publicSeed : PublicParameter) (layer : Layer) (tree : TreeIndex)
    (leaf : TreeLeafIndex) (path : ℕ → Digest) (levels : ℕ) (v : Digest) :
    QueryCostAtMost (treeFold (HashSig.OverPermutation.keccakHash queryPermutation) publicSeed layer tree leaf path levels v)
      permutationCallCost (levels * thCost) :=
  foldPath_cost _ thCost (fun _ _ _ _ ↦ addressedHash_cost _ _ _ (by
    simp [nodePayload, littleEndianBytes])) _ _ levels v

theorem layerHeight_le (layer : Layer) : layerHeight layer ≤ 10 := by
  unfold layerHeight
  split <;> omega

/-- The calls of one FORS tree's recovery. -/
def forsTreeRecoverCost : ℕ := thCost + forsTreeHeight * thCost

theorem forsTreeRecover_cost (publicSeed : PublicParameter) (index : Index)
    (forsTree : ForsTreeIndex) (leaf : ForsLeafIndex) (opening : ForsTreeOpening) :
    QueryCostAtMost (forsTreeRecover (HashSig.OverPermutation.keccakHash queryPermutation) publicSeed index forsTree leaf opening)
      permutationCallCost forsTreeRecoverCost := by
  unfold forsTreeRecover forsLeafHash
  exact (addressedHash_cost _ _ _ (by simp [littleEndianBytes])).bind fun _ ↦
    foldPath_cost _ thCost (fun _ _ _ _ ↦ addressedHash_cost _ _ _ (by
      simp [nodePayload, littleEndianBytes])) _ _ _ _

/-- The calls of the FORS key's recovery. -/
def forsRecoverCost : ℕ := forsTreeCount * forsTreeRecoverCost + thCost

theorem forsRecover_cost (publicSeed : PublicParameter) (index : Index)
    (leaves : ForsTreeIndex → ForsLeafIndex) (opening : ForsTreeIndex → ForsTreeOpening) :
    QueryCostAtMost (forsRecover (HashSig.OverPermutation.keccakHash queryPermutation) publicSeed index leaves opening)
      permutationCallCost forsRecoverCost := by
  unfold forsRecover forsPublicKey
  exact (sequenceFin_cost _ _ fun _ ↦ forsTreeRecover_cost _ _ _ _ _).bind fun _ ↦
    addressedHash_cost _ _ _ (by rw [digestsPayload_length]; simp [forsTreeCount])

theorem messageDigest_cost (publicKey : Sphincs.PublicKey) (randomizer : Randomizer) (message : Message) :
    QueryCostAtMost (messageDigest (HashSig.OverPermutation.keccakHash queryPermutation) publicKey randomizer message)
      permutationCallCost 2 := by
  unfold messageDigest messageDigestCall
  exact (QueryCostAtMost.bind (sequenceFin_cost 1 _ fun _ ↦ keccakHash_cost_le _ (k := 0)
    (by simp [littleEndianBytes, bigEndianBytes])) fun _ ↦ isWeightBound_pure _ _ 0).mono
      (by simp [digestCallCount])

/-- The calls of one layer of the walk up the hypertree. -/
def layerCost : ℕ := otsLeafCost + 10 * thCost

theorem verifyLayers_cost (publicSeed : PublicParameter) (index : Index) (signature : Signature) :
    ∀ n message, QueryCostAtMost (verifyLayers (HashSig.OverPermutation.keccakHash queryPermutation) publicSeed index signature n message)
      permutationCallCost (n * layerCost)
  | 0, _ => by
    simp only [verifyLayers]
    exact isWeightBound_pure _ _ _
  | n + 1, message => by
    simp only [verifyLayers]
    split
    · refine ((otsLeaf_cost _ _ _ _ _ _ _).bind fun v ↦ ?_).mono
        (Q := otsLeafCost + (10 * thCost + n * layerCost)) (by
          have := Nat.add_one_mul n layerCost; unfold layerCost at *; omega)
      cases v with
      | none => exact (isWeightBound_pure _ _ _).mono (Nat.zero_le _)
      | some _ =>
        refine ((treeFold_cost _ _ _ _ _ _ _).bind fun _ ↦ ?_).mono
          (Nat.add_le_add_right (Nat.mul_le_mul_right _ (layerHeight_le _)) _)
        split
        · exact (isWeightBound_pure _ _ _).mono (Nat.zero_le _)
        · exact verifyLayers_cost publicSeed index signature n _
    · exact (isWeightBound_pure _ _ _).mono (Nat.zero_le _)

/-- The verifier's calls. -/
def verifyCost : ℕ := 2 + (forsRecoverCost + layerCount * layerCost)

theorem verify_cost (publicKey : Sphincs.PublicKey) (message : Message) (signature : Signature) :
    QueryCostAtMost (verify (HashSig.OverPermutation.keccakHash queryPermutation) publicKey message signature) permutationCallCost
      verifyCost := by
  unfold verify
  refine (messageDigest_cost _ _ _).bind fun _ ↦ (forsRecover_cost _ _ _ _).bind fun _ ↦ ?_
  refine ((verifyLayers_cost _ _ _ _ _).bind fun r ↦ ?_).mono (Q := layerCount * layerCost + 0)
    (by simp)
  cases r <;> exact isWeightBound_pure _ _ _

end Verification

namespace KeyGenerationAndSigning

open Sphincs.Verification Sphincs.KeyGenerationAndSigning Verification

theorem expandKey_cost (secretSeed : SecretKey) :
    QueryCostAtMost (expandKey (HashSig.OverPermutation.keccakHash queryPermutation) secretSeed) permutationCallCost 2 := by
  unfold expandKey
  exact (QueryCostAtMost.bind (keccakHash_cost_le _ (k := 0) (by
    simp [keyDerivationInput, seedTag, littleEndianBytes])) fun _ ↦
    QueryCostAtMost.bind (keccakHash_cost_le _ (k := 0) (by
      simp [keyDerivationInput, seedTag, littleEndianBytes])) fun _ ↦ isWeightBound_pure _ _ 0).mono
    (by simp)

theorem prf_cost (key : ExpandedKey) (domain : KeygenDomain) :
    QueryCostAtMost (prf (HashSig.OverPermutation.keccakHash queryPermutation) key domain) permutationCallCost thCost :=
  addressedHash_cost _ _ _ (by simp [littleEndianBytes])

theorem prfMessage_cost (secretPrfKey : HashOutput) (optionalRandomness : Digest) (message : Message) :
    QueryCostAtMost (prfMessage (HashSig.OverPermutation.keccakHash queryPermutation) secretPrfKey optionalRandomness message)
      permutationCallCost 1 := by
  unfold prfMessage
  exact ((keccakHash_cost_le _ (k := 0) (by
    simp [framedMessage, contextString, seedTag, littleEndianBytes])).bind fun _ ↦
    isWeightBound_pure _ _ 0).mono le_rfl

/-- Merkle levels over at most `L` nodes make at most `L` node hashes per level. -/
theorem merkleLevelsFrom_cost (node : ℕ → ℕ → HashInput → OracleComp RandomPermutationOracles Digest)
    (b : ℕ) (hn : ∀ h j left right, QueryCostAtMost (node h j (nodePayload left right)) permutationCallCost b)
    (L : ℕ) : ∀ remaining height (below : List Digest), below.length ≤ L →
      QueryCostAtMost (merkleLevelsFrom node height below remaining) permutationCallCost
        (remaining * (L * b))
  | 0, _, _, _ => by
    simp only [merkleLevelsFrom]
    exact isWeightBound_pure _ _ _
  | remaining + 1, height, below, hb => by
    simp only [merkleLevelsFrom]
    have hlen : (List.range (below.length / 2)).length ≤ L := by
      rw [List.length_range]
      omega
    refine (QueryCostAtMost.bind_of_support ((mapM_cost _ b (fun _ ↦ hn _ _ _ _) _).mono
      (Nat.mul_le_mul_right b hlen)) fun above habove ↦ ?_).mono
      (Q := L * b + remaining * (L * b)) (by rw [Nat.add_one_mul]; omega)
    have hab : above.length ≤ L :=
      (length_of_mem_support_mapM _ _ above habove).trans_le hlen
    exact ((merkleLevelsFrom_cost node b hn L remaining _ above hab).bind fun _ ↦
      isWeightBound_pure _ _ 0).mono (by simp)

/-- The calls of a one-time key's secrets. -/
def otsSecretsCost : ℕ := chainCount * thCost

theorem otsSecrets_cost (key : ExpandedKey) (layer : Layer) (tree : TreeIndex)
    (leaf : TreeLeafIndex) :
    QueryCostAtMost (otsSecrets (HashSig.OverPermutation.keccakHash queryPermutation) key layer tree leaf) permutationCallCost
      otsSecretsCost :=
  sequenceFin_cost _ _ fun _ ↦ prf_cost _ _

/-- The calls of a one-time key's leaf. -/
def otsPublicLeafCost : ℕ := otsSecretsCost + (chainCount * (3 * thCost) + thCost)

theorem otsPublicLeaf_cost (key : ExpandedKey) (layer : Layer) (tree : TreeIndex)
    (leaf : TreeLeafIndex) :
    QueryCostAtMost (otsPublicLeaf (HashSig.OverPermutation.keccakHash queryPermutation) key layer tree leaf) permutationCallCost
      otsPublicLeafCost := by
  unfold otsPublicLeaf
  exact (otsSecrets_cost _ _ _ _).bind fun _ ↦
    (sequenceFin_cost (3 * thCost) _ fun _ ↦ (chainWalk_cost _ _ _ _ _ _ _ _).mono
      (Nat.mul_le_mul_right _ (by simp [chainLength, winternitzBits]))).bind fun _ ↦
    leafHash_cost _ _ _ _ _

/-- The calls of opening a one-time key once its counter is found. -/
def openCost : ℕ := otsSecretsCost + chainCount * (3 * thCost)

theorem otsSignFrom_cost (key : ExpandedKey) (layer : Layer) (tree : TreeIndex)
    (leaf : TreeLeafIndex) (message : Digest) :
    ∀ attempts counter, QueryCostAtMost
      (otsSignFrom (HashSig.OverPermutation.keccakHash queryPermutation) key layer tree leaf message attempts counter)
      permutationCallCost (attempts * thCost + openCost)
  | 0, _ => by
    simp only [otsSignFrom]
    exact isWeightBound_pure _ _ _
  | attempts + 1, counter => by
    simp only [otsSignFrom]
    refine ((encode_cost _ _ _ _ _ _).bind fun e ↦ ?_).mono
      (Q := thCost + (attempts * thCost + openCost)) (by rw [Nat.succ_mul]; omega)
    cases e with
    | some encoding =>
      refine (QueryCostAtMost.bind (otsSecrets_cost _ _ _ _) fun _ ↦
        QueryCostAtMost.bind (sequenceFin_cost (3 * thCost) _ fun i ↦ ?_) fun _ ↦
          isWeightBound_pure _ _ 0).mono (by simp [openCost])
      refine (chainWalk_cost _ _ _ _ _ _ _ _).mono (Nat.mul_le_mul_right _ ?_)
      have := (encoding i).isLt
      simp only [chainLength, winternitzBits] at this
      omega
    | none => exact otsSignFrom_cost key layer tree leaf message attempts (counter + 1)

/-- The calls of a one-time signature: the counter search at its cap, then the opening. -/
def otsSignCost : ℕ := encodingAttemptLimit * thCost + openCost

theorem otsSign_cost (key : ExpandedKey) (layer : Layer) (tree : TreeIndex) (leaf : TreeLeafIndex)
    (message : Digest) :
    QueryCostAtMost (otsSign (HashSig.OverPermutation.keccakHash queryPermutation) key layer tree leaf message) permutationCallCost
      otsSignCost :=
  otsSignFrom_cost _ _ _ _ _ _ _

/-- The calls of a hypertree tree's levels, crudely at height `10`. -/
def treeLevelsCost : ℕ := 2 ^ 10 * otsPublicLeafCost + 10 * (2 ^ 10 * thCost)

theorem treeLevels_cost (key : ExpandedKey) (layer : Layer) (tree : TreeIndex) :
    QueryCostAtMost (treeLevels (HashSig.OverPermutation.keccakHash queryPermutation) key layer tree) permutationCallCost
      treeLevelsCost := by
  unfold treeLevels merkleLevels
  have hh := layerHeight_le layer
  have hp : 2 ^ layerHeight layer ≤ 2 ^ 10 := Nat.pow_le_pow_right (by norm_num) hh
  refine (QueryCostAtMost.bind_of_support ((mapM_cost _ _ (fun _ ↦ otsPublicLeaf_cost _ _ _ _)
    _).mono (Nat.mul_le_mul_right _ (by rw [List.length_range]; exact hp))) fun leaves hl ↦ ?_).mono
    le_rfl
  have hl' : leaves.length ≤ 2 ^ 10 :=
    (length_of_mem_support_mapM _ _ leaves hl).trans_le (by rw [List.length_range]; exact hp)
  exact (merkleLevelsFrom_cost _ thCost (fun _ _ _ _ ↦ addressedHash_cost _ _ _ (by
    simp [nodePayload, littleEndianBytes])) _ _ 0 leaves hl').mono
    (Nat.mul_le_mul_right _ hh)

/-- The calls of one FORS tree, built once. -/
def forsTreeOpenCost : ℕ := 2 ^ forsTreeHeight * thCost +
  (2 ^ forsTreeHeight * thCost + forsTreeHeight * (2 ^ forsTreeHeight * thCost))

theorem forsTreeOpen_cost (key : ExpandedKey) (index : Index) (forsTree : ForsTreeIndex)
    (leaf : ForsLeafIndex) :
    QueryCostAtMost (forsTreeOpen (HashSig.OverPermutation.keccakHash queryPermutation) key index forsTree leaf) permutationCallCost
      forsTreeOpenCost := by
  unfold forsTreeOpen merkleLevels
  refine ((mapM_cost _ _ (fun _ ↦ prf_cost _ _) _).bind fun secrets ↦ ?_).mono
    (by simp only [List.length_range, forsTreeOpenCost]; exact le_rfl)
  refine (QueryCostAtMost.bind_of_support (mapM_cost _ thCost (fun _ ↦ addressedHash_cost _ _ _
    (by simp [littleEndianBytes])) _) fun leaves hl ↦ ?_).mono (by rw [List.length_range])
  have hl' : leaves.length ≤ 2 ^ forsTreeHeight :=
    (length_of_mem_support_mapM _ _ leaves hl).trans_le (by rw [List.length_range])
  exact ((merkleLevelsFrom_cost _ thCost (fun _ _ _ _ ↦ addressedHash_cost _ _ _ (by
    simp [nodePayload, littleEndianBytes])) _ _ 0 leaves hl').bind fun _ ↦
    isWeightBound_pure _ _ 0).mono (by simp)

/-- The calls of the FORS instance. -/
def forsOpenCost : ℕ := forsTreeCount * forsTreeOpenCost + thCost

theorem forsOpen_cost (key : ExpandedKey) (index : Index) (leaves : ForsTreeIndex → ForsLeafIndex) :
    QueryCostAtMost (forsOpen (HashSig.OverPermutation.keccakHash queryPermutation) key index leaves) permutationCallCost
      forsOpenCost := by
  unfold forsOpen forsPublicKey
  exact (QueryCostAtMost.bind (sequenceFin_cost _ _ fun _ ↦ forsTreeOpen_cost _ _ _ _) fun _ ↦
    QueryCostAtMost.bind (addressedHash_cost _ _ _ (by
      rw [digestsPayload_length]; simp [forsTreeCount])) fun _ ↦ isWeightBound_pure _ _ 0).mono
    (by simp [forsOpenCost])

/-- Key generation's calls. -/
def keygenCost : ℕ := 2 + treeLevelsCost

theorem keygenInternal_cost (key : ExpandedKey) :
    QueryCostAtMost (keygenInternal (HashSig.OverPermutation.keccakHash queryPermutation) key) permutationCallCost treeLevelsCost := by
  unfold keygenInternal
  exact ((treeLevels_cost _ _ _).bind fun _ ↦ isWeightBound_pure _ _ 0).mono (by simp)

theorem keygenFromSeed_cost (secretSeed : SecretKey) :
    QueryCostAtMost (keygenFromSeed (HashSig.OverPermutation.keccakHash queryPermutation) secretSeed) permutationCallCost keygenCost := by
  unfold keygenFromSeed
  refine (expandKey_cost _).bind fun _ ↦ ((keygenInternal_cost _).bind fun p ↦ ?_).mono
    (Q := treeLevelsCost + 0) (by simp)
  obtain ⟨_, _⟩ := p
  exact isWeightBound_pure _ _ _

/-- A layer's signature's calls. -/
def signLayerCost : ℕ := otsSignCost + treeLevelsCost

theorem signLayer_cost (key : ExpandedKey) (top : List (List Digest)) (index : Index)
    (layer : Layer) (message : Digest) :
    QueryCostAtMost (signLayer (HashSig.OverPermutation.keccakHash queryPermutation) key top index layer message) permutationCallCost
      signLayerCost := by
  unfold signLayer
  refine ((otsSign_cost _ _ _ _ _).bind fun o ↦ ?_).mono
    (Q := otsSignCost + (treeLevelsCost + 0)) (by simp [signLayerCost])
  rcases o with _ | ⟨_, _⟩
  · exact (isWeightBound_pure _ _ _).mono (Nat.zero_le _)
  · dsimp only
    split
    · exact (QueryCostAtMost.bind (isWeightBound_pure _ _ 0) fun _ ↦ isWeightBound_pure _ _ 0).mono
        (Nat.zero_le _)
    · exact QueryCostAtMost.bind (treeLevels_cost _ _ _) fun _ ↦ isWeightBound_pure _ _ 0

/-- A signing request's calls. -/
def signCost : ℕ := 2 + (treeLevelsCost + (1 + (2 + (forsOpenCost + 3 * signLayerCost))))

theorem sign_cost (secretKey : SecretKey) (message : Message) :
    QueryCostAtMost (sign (HashSig.OverPermutation.keccakHash queryPermutation) secretKey message) permutationCallCost signCost := by
  unfold sign signWithExpandedKey
  refine (expandKey_cost _).bind fun _ ↦ (keygenInternal_cost _).bind fun p ↦ ?_
  obtain ⟨_, _⟩ := p
  refine (prfMessage_cost _ _ _).bind fun _ ↦ (messageDigest_cost _ _ _).bind fun _ ↦
    (forsOpen_cost _ _ _).bind fun f ↦ ?_
  obtain ⟨_, _⟩ := f
  refine ((signLayer_cost _ _ _ _ _).bind fun o ↦ ?_).mono
    (Q := signLayerCost + (signLayerCost + (signLayerCost + 0))) (by omega)
  rcases o with _ | ⟨_, _⟩
  · exact (isWeightBound_pure _ _ _).mono (Nat.zero_le _)
  refine (signLayer_cost _ _ _ _ _).bind fun o ↦ ?_
  rcases o with _ | ⟨_, _⟩
  · exact (isWeightBound_pure _ _ _).mono (Nat.zero_le _)
  refine (signLayer_cost _ _ _ _ _).bind fun o ↦ ?_
  rcases o with _ | ⟨_, _⟩ <;> exact isWeightBound_pure _ _ _

end KeyGenerationAndSigning

open KeyGenerationAndSigning Verification

/-- **leanSPHINCS's total**: key generation, `signatureLimit` signing requests and the verification
stay below `2^128` permutation calls. -/
theorem total_le : keygenCost + signatureLimit * signCost + verifyCost ≤ 2 ^ 128 := by
  simp only [keygenCost, signCost, signLayerCost, otsSignCost, treeLevelsCost, otsPublicLeafCost,
    otsSecretsCost, openCost, forsOpenCost, forsTreeOpenCost, verifyCost, forsRecoverCost,
    forsTreeRecoverCost, layerCost, otsLeafCost, thCost, signatureLimit, chainCount,
    encodingAttemptLimit, forsTreeCount, forsTreeHeight, layerCount]
  norm_num

/-- The statement's key generation (`Sphincs.RandomPermutationModel.sufCmaScheme`). -/
theorem sufCmaScheme_generateKeys_cost (seed : MasterSeed) :
    QueryCostAtMost (RandomPermutationModel.sufCmaScheme.generateKeys seed) permutationCallCost
      keygenCost :=
  keygenFromSeed_cost seed

/-- The statement's signer, on one message. -/
theorem sufCmaScheme_sign_cost (secretKey : SecretKey) (message : Message) :
    QueryCostAtMost (RandomPermutationModel.sufCmaScheme.sign secretKey message)
      permutationCallCost signCost :=
  sign_cost _ _

/-- The statement's verifier. -/
theorem sufCmaScheme_verify_cost (publicKey : Sphincs.PublicKey) (forgery : Forgery) :
    QueryCostAtMost (RandomPermutationModel.sufCmaScheme.verify publicKey forgery)
      permutationCallCost verifyCost :=
  verify_cost _ _ _

end Common.SphincsCost
