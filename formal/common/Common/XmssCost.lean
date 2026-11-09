module

public import Common.CostCombinators
public import Statement.LeanXmss

@[expose] public section

/-!
# leanXMSS's worst-case permutation calls

Bounds on every path (`QueryCostAtMost`, in calls of `π`) of the statement's leanXMSS over `π`:
key generation (`keygen_cost`), the signer of one request, its randomizer grinding at the cap of
`2^32` trials per layer included (`sign_cost`), and the verifier (`verify_cost`). Every tweakable
hash hashes at most `32 + 952` bytes, so makes at most `8` calls (`th_cost`); the bounds are crude,
and only serve to keep the whole game's calls below `2^128` (`Common.SufCma.stronglyUnforgeable_of_romBoundAdv`).
-/

open OracleComp OracleSpec
open HashSig HashSig.OverPermutation

namespace Common.XmssCost

-- Elaborating a combinator's bound at a literal size otherwise unfolds the combinator.
attribute [local irreducible] sequenceFin walkChain foldPath buildTree

open LeanXmss

/-- The permutation calls of a tweakable hash. -/
def thCost : ℕ := 8

theorem littleEndianBytes_length (n : ℕ) (v : BitVec (8 * n)) :
    (littleEndianBytes n v).length = n := by
  simp [littleEndianBytes]

theorem thInput_length (parameter : PublicParameter) (fields : TweakFields) (payload : HashInput) :
    (thInput parameter fields payload).length = 32 + payload.length := by
  simp [thInput, hasherInput, addressBytes, littleEndianBytes]
  omega

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

theorem th_cost (parameter : PublicParameter) (fields : TweakFields) (payload : HashInput)
    (h : payload.length ≤ 952) :
    QueryCostAtMost (th queryPermutation parameter fields payload) permutationCallCost thCost := by
  unfold th
  exact ((keccakHash_cost_le _ (k := 7) (by rw [thInput_length]; omega)).bind fun _ ↦
    isWeightBound_pure _ _ 0).mono (by simp [thCost])

theorem thPair_cost (parameter : PublicParameter) (fields : TweakFields) (payload : HashInput)
    (h : payload.length ≤ 952) :
    QueryCostAtMost (thPair queryPermutation parameter fields payload) permutationCallCost
      thCost :=
  (keccakHash_cost_le _ (k := 7) (by rw [thInput_length]; omega)).mono (by simp [thCost])

theorem schemeSeedOf_cost (s : MasterSeed) :
    QueryCostAtMost (schemeSeedOf queryPermutation s) permutationCallCost 1 :=
  keccakHash_cost_le _ (k := 0) (by simp [seedTag, littleEndianBytes])

/-! ## The verifier -/

namespace Verification

open LeanXmss.Verification

theorem chainWalk_cost (parameter : PublicParameter) (layer : Layer) (key : KeyIndex)
    (chainIndex : ChainIndex) (start steps : ℕ) (v : Digest) :
    QueryCostAtMost (chainWalk queryPermutation parameter layer key chainIndex start steps v)
      permutationCallCost (steps * thCost) :=
  walkChain_cost _ thCost (fun _ _ ↦ th_cost _ _ _ (by
    simp [chainPayload, littleEndianBytes])) start steps v

theorem recoverChain_cost (parameter : PublicParameter) (layer : Layer) (key : KeyIndex)
    (chainIndex : ChainIndex) (digit : WinternitzDigit) (v : Digest) :
    QueryCostAtMost (recoverChain queryPermutation parameter layer key chainIndex digit v)
      permutationCallCost (3 * thCost) :=
  (chainWalk_cost _ _ _ _ _ _ _).mono (Nat.mul_le_mul_right _ (by simp [chainLength, winternitzBits]))

theorem leafHash_cost (parameter : PublicParameter) (layer : Layer) (key : KeyIndex)
    (endpoints : ChainIndex → Digest) :
    QueryCostAtMost (leafHash queryPermutation parameter layer key endpoints) permutationCallCost
      thCost :=
  th_cost _ _ _ (by rw [digestsPayload_length]; simp [chainCount])

theorem messageDigest_cost (parameter : PublicParameter) (layer : Layer) (key : KeyIndex)
    (message : HashInput) (randomizer : Randomizer) (hm : message.length ≤ 32) :
    QueryCostAtMost (messageDigest queryPermutation parameter layer key message randomizer)
      permutationCallCost thCost :=
  th_cost _ _ _ (by simp [littleEndianBytes]; omega)

/-- The calls of a one-time leaf's recovery. -/
def otsLeafCost : ℕ := thCost + chainCount * (3 * thCost) + thCost

theorem otsLeaf_cost (parameter : PublicParameter) (layer : Layer) (key : KeyIndex)
    (message : HashInput) (randomizer : Randomizer) (values : ChainIndex → Digest)
    (hm : message.length ≤ 32) :
    QueryCostAtMost (otsLeaf queryPermutation parameter layer key message randomizer values)
      permutationCallCost otsLeafCost := by
  unfold otsLeaf
  refine ((messageDigest_cost parameter layer key message randomizer hm).bind fun digest ↦ ?_).mono
    (Q := thCost + (chainCount * (3 * thCost) + thCost)) (by simp [otsLeafCost]; omega)
  split
  · exact ((sequenceFin_cost _ _ fun i ↦ recoverChain_cost _ _ _ _ _ _).bind fun endpoints ↦
      (leafHash_cost _ _ _ _).bind fun _ ↦ isWeightBound_pure _ _ 0).mono (by simp)
  · exact (isWeightBound_pure _ _ _).mono (Nat.zero_le _)

theorem treeFold_cost (parameter : PublicParameter) (layer : Layer) (key : KeyIndex)
    (path : Fin layerHeight → Digest) (levels : ℕ) (v : Digest) :
    QueryCostAtMost (treeFold queryPermutation parameter layer key path levels v)
      permutationCallCost (levels * thCost) :=
  foldPath_cost _ thCost (fun _ _ _ _ ↦ th_cost _ _ _ (by simp [nodePayload, littleEndianBytes]))
    _ _ levels v

/-- The calls of a layer's root. -/
def layerRootCost : ℕ := otsLeafCost + layerHeight * thCost

theorem layerRoot_cost (parameter : PublicParameter) (layer : Layer) (key : KeyIndex)
    (message : HashInput) (layerSignature : LayerSignature) (hm : message.length ≤ 32) :
    QueryCostAtMost (layerRoot queryPermutation parameter layer key message layerSignature)
      permutationCallCost layerRootCost := by
  unfold layerRoot
  refine ((otsLeaf_cost _ _ _ _ _ _ hm).bind fun leaf ↦ ?_).mono
    (Q := otsLeafCost + layerHeight * thCost) le_rfl
  cases leaf with
  | none => exact (isWeightBound_pure _ _ _).mono (Nat.zero_le _)
  | some _ =>
    exact (QueryCostAtMost.bind (treeFold_cost _ _ _ _ _ _) fun _ ↦ isWeightBound_pure _ _ 0).mono
      (by simp)

/-- The verifier's calls. -/
def verifyCost : ℕ := 2 * layerRootCost

theorem verify_cost (publicKey : PublicKey) (message : Message) (signature : Signature) :
    QueryCostAtMost (verify queryPermutation publicKey message signature) permutationCallCost
      verifyCost := by
  unfold verify
  refine ((layerRoot_cost _ _ _ _ _ (by simp [littleEndianBytes])).bind fun r ↦ ?_).mono
    (Q := layerRootCost + layerRootCost) (by simp [verifyCost]; omega)
  cases r with
  | none => exact (isWeightBound_pure _ _ _).mono (Nat.zero_le _)
  | some _ =>
    refine ((layerRoot_cost _ _ _ _ _ (by simp [littleEndianBytes])).bind fun r' ↦ ?_).mono
      (Q := layerRootCost + 0) (by simp)
    cases r' <;> exact isWeightBound_pure _ _ _

end Verification

/-! ## Key generation and the signer -/

namespace KeyGenerationAndSigning

open LeanXmss.Verification LeanXmss.KeyGenerationAndSigning

/-- The calls of a one-time key's secrets. -/
def otsSecretsCost : ℕ := (chainCount / 2) * thCost

theorem otsSecrets_cost (parameter : PublicParameter) (layer : Layer) (key : KeyIndex)
    (seed : MasterSeed) :
    QueryCostAtMost (otsSecrets queryPermutation parameter layer key seed) permutationCallCost
      otsSecretsCost := by
  unfold otsSecrets
  exact ((sequenceFin_cost _ _ fun _ ↦ thPair_cost _ _ _ (by simp [littleEndianBytes])).bind
    fun _ ↦ isWeightBound_pure _ _ 0).mono (by simp [otsSecretsCost])

/-- The calls of a one-time public key. -/
def oneTimePublicKeyCost : ℕ := otsSecretsCost + chainCount * (3 * thCost)

theorem oneTimePublicKey_cost (parameter : PublicParameter) (layer : Layer) (key : KeyIndex)
    (seed : MasterSeed) :
    QueryCostAtMost (oneTimePublicKey queryPermutation parameter layer key seed)
      permutationCallCost oneTimePublicKeyCost := by
  unfold oneTimePublicKey
  exact (otsSecrets_cost _ _ _ _).bind fun _ ↦ sequenceFin_cost _ _ fun _ ↦
    (Verification.chainWalk_cost _ _ _ _ _ _ _).mono
      (Nat.mul_le_mul_right _ (by simp [chainLength, winternitzBits]))

/-- The calls of opening a one-time key once its digest is found. -/
def openCost : ℕ := otsSecretsCost + chainCount * (3 * thCost)

theorem otsSignFrom_cost (parameter : PublicParameter) (layer : Layer) (key : KeyIndex)
    (seed : MasterSeed) (message : HashInput) (randomizerBase : Randomizer)
    (hm : message.length ≤ 32) :
    ∀ attempts trial, QueryCostAtMost
      (otsSignFrom queryPermutation parameter layer key seed message randomizerBase attempts trial)
      permutationCallCost (attempts * thCost + openCost)
  | 0, _ => by
    simp only [otsSignFrom]
    exact isWeightBound_pure _ _ _
  | attempts + 1, trial => by
    simp only [otsSignFrom]
    refine ((Verification.messageDigest_cost parameter layer key message _ hm).bind
      fun digest ↦ ?_).mono (Q := thCost + (attempts * thCost + openCost)) (by
        rw [Nat.succ_mul]; omega)
    split
    next encoding _ =>
      refine (QueryCostAtMost.bind (otsSecrets_cost _ _ _ _) fun _ ↦
        QueryCostAtMost.bind (sequenceFin_cost (3 * thCost) _ fun i ↦ ?_) fun _ ↦
          isWeightBound_pure _ _ 0).mono (by simp [openCost])
      · refine (Verification.chainWalk_cost _ _ _ _ _ _ _).mono (Nat.mul_le_mul_right _ ?_)
        have := (encoding i).isLt
        simp only [chainLength, winternitzBits] at this
        omega
    · exact otsSignFrom_cost parameter layer key seed message randomizerBase hm attempts (trial + 1)

/-- The calls of a one-time signature: the randomizer base, the grinding at its cap, the opening. -/
def otsSignCost : ℕ := thCost + (randomizerAttemptLimit * thCost + openCost)

theorem otsSign_cost (parameter : PublicParameter) (layer : Layer) (key : KeyIndex)
    (seed : MasterSeed) (message : HashInput) (hm : message.length ≤ 32) :
    QueryCostAtMost (otsSign queryPermutation parameter layer key seed message)
      permutationCallCost otsSignCost := by
  unfold otsSign
  exact (th_cost _ _ _ (by simp [littleEndianBytes]; omega)).bind fun _ ↦
    otsSignFrom_cost _ _ _ _ _ _ hm _ _

/-- The calls of a tree node at level `16` or below, crudely. -/
def treeNodeCost : ℕ := 2 ^ layerHeight * (oneTimePublicKeyCost + thCost) +
  (2 ^ layerHeight - 1) * thCost

theorem treeNode_cost (parameter : PublicParameter) (layer : Layer) (seed : MasterSeed)
    (level index : ℕ) (hl : level ≤ layerHeight) :
    QueryCostAtMost (treeNode queryPermutation parameter layer seed level index)
      permutationCallCost treeNodeCost := by
  unfold treeNode
  refine (buildTree_cost _ _ (oneTimePublicKeyCost + thCost) thCost
    (fun _ ↦ (oneTimePublicKey_cost _ _ _ _).bind fun _ ↦ Verification.leafHash_cost _ _ _ _)
    (fun _ _ _ _ ↦ th_cost _ _ _ (by simp [nodePayload, littleEndianBytes])) level index).mono ?_
  have hp : 2 ^ level ≤ 2 ^ layerHeight := Nat.pow_le_pow_right (by norm_num) hl
  unfold treeNodeCost
  gcongr

/-- The calls of an authentication path. -/
def treePathCost : ℕ := layerHeight * treeNodeCost

theorem treePath_cost (parameter : PublicParameter) (layer : Layer) (seed : MasterSeed)
    (key : KeyIndex) :
    QueryCostAtMost (treePath queryPermutation parameter layer seed key) permutationCallCost
      treePathCost :=
  sequenceFin_cost _ _ fun level ↦ treeNode_cost _ _ _ _ _ level.isLt.le

/-- Key generation's calls. -/
def keygenCost : ℕ := 1 + (thCost + treeNodeCost)

theorem keygenFromSeed_cost (s : MasterSeed) :
    QueryCostAtMost (keygenFromSeed queryPermutation s) permutationCallCost keygenCost := by
  unfold keygenFromSeed publicParameterOf
  exact (QueryCostAtMost.bind (schemeSeedOf_cost s) fun _ ↦
    QueryCostAtMost.bind (th_cost _ _ _ (by simp [littleEndianBytes])) fun _ ↦
    QueryCostAtMost.bind (treeNode_cost _ _ _ _ _ le_rfl) fun _ ↦ isWeightBound_pure _ _ 0).mono
      (by simp [keygenCost])

/-- A layer's signature's calls. -/
def signLayerCost : ℕ := otsSignCost + treePathCost

theorem signLayer_cost (seed : MasterSeed) (parameter : PublicParameter) (layer : Layer)
    (key : KeyIndex) (message : HashInput) (hm : message.length ≤ 32) :
    QueryCostAtMost (signLayer queryPermutation seed parameter layer key message)
      permutationCallCost signLayerCost := by
  unfold signLayer
  refine ((otsSign_cost _ _ _ _ _ hm).bind fun o ↦ ?_).mono (Q := otsSignCost + treePathCost) le_rfl
  rcases o with _ | ⟨_, _⟩
  · exact (isWeightBound_pure _ _ _).mono (Nat.zero_le _)
  · exact (QueryCostAtMost.bind (treePath_cost _ _ _ _) fun _ ↦ isWeightBound_pure _ _ 0).mono
      (by simp)

/-- A signing request's calls. -/
def signCost : ℕ := 1 + (signLayerCost + (treeNodeCost + signLayerCost))

theorem sign_cost (secretKey : SecretKey) (leafIndex : LeafIndex) (message : Message) :
    QueryCostAtMost (sign queryPermutation secretKey leafIndex message) permutationCallCost
      signCost := by
  unfold sign signWithSchemeSeed
  refine (schemeSeedOf_cost _).bind fun seed ↦ ?_
  refine ((signLayer_cost _ _ _ _ _ (by simp [littleEndianBytes])).bind fun o ↦ ?_).mono
    (Q := signLayerCost + (treeNodeCost + signLayerCost)) le_rfl
  cases o with
  | none => exact (isWeightBound_pure _ _ _).mono (Nat.zero_le _)
  | some _ =>
    refine QueryCostAtMost.bind (treeNode_cost _ _ _ _ _ le_rfl) fun root ↦ ?_
    refine (QueryCostAtMost.bind (signLayer_cost _ _ _ _ _ (by simp [littleEndianBytes]))
      fun o' ↦ ?_).mono (Q := signLayerCost + 0) (by simp)
    cases o' <;> exact isWeightBound_pure _ _ _

end KeyGenerationAndSigning

open KeyGenerationAndSigning Verification

/-- **leanXMSS's total**: key generation, `2^32` signing requests and the verification stay below
`2^128` permutation calls. -/
theorem total_le : keygenCost + lifetime * signCost + verifyCost ≤ 2 ^ 128 := by
  simp only [keygenCost, signCost, signLayerCost, otsSignCost, treePathCost, treeNodeCost,
    oneTimePublicKeyCost, otsSecretsCost, openCost, verifyCost, layerRootCost, otsLeafCost, thCost,
    lifetime, layerCount, layerHeight, chainCount, randomizerAttemptLimit]
  norm_num

/-- The statement's key generation (`LeanXmss.RandomPermutationModel.sufCmaScheme`). -/
theorem sufCmaScheme_generateKeys_cost (seed : MasterSeed) :
    QueryCostAtMost (RandomPermutationModel.sufCmaScheme.generateKeys seed) permutationCallCost
      keygenCost :=
  keygenFromSeed_cost seed

/-- The statement's signer, on one request. -/
theorem sufCmaScheme_sign_cost (secretKey : SecretKey) (request : SigningRequest) :
    QueryCostAtMost (RandomPermutationModel.sufCmaScheme.sign secretKey request)
      permutationCallCost signCost :=
  sign_cost _ _ _

/-- The statement's verifier. -/
theorem sufCmaScheme_verify_cost (publicKey : PublicKey) (forgery : Forgery) :
    QueryCostAtMost (RandomPermutationModel.sufCmaScheme.verify publicKey forgery)
      permutationCallCost verifyCost :=
  verify_cost _ _ _

end Common.XmssCost
