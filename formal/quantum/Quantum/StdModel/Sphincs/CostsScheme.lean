module

public import Quantum.Qrom.Sphincs.Slots
public import Common.CostCombinators

@[expose] public section

/-!
# leanSPHINCS's hash calls over any hash, by kind of input

Worst-case bounds (`QueryCostAtMost`) on the key generation, the signer and the verifier of
`LeanSphincsOver hash`, for any hash whose call on an input of each kind costs at most a given
bound. Every input the scheme hashes is the input `slotInput key root s p` of a slot `s`
(`Quantum.StdModel.sphincs_*_eq`), so a bound per kind of slot (`Kinds`, `HashKinds`) bounds
every call.

* `Kinds`: one bound per kind of slot; `Kinds.const κ` the same bound everywhere.
* `verify_cost`, `keygenFromSeed_cost`, `sign_cost`: the bounds `verifyW c`, `keygenW c`,
  `signW c`, linear in the kinds' bounds. The signer's counter search is charged at its cap,
  `encodingAttemptLimit = 2^32` trials per layer (`otsSignFrom_cost`, by induction on the trials);
  the trees' levels crudely at height `10` and `10` hashes per level and leaf.
* At the same bound `κ` for every kind (`verifyW_const`, `keygenW_const`, `signW_const`):
  `879 κ`, `273410 κ` and `12886291206 κ`.
-/

open OracleComp OracleSpec
open HashSig hiding PublicKey
open HashSig.OverPermutation (sequenceFin walkChain foldPath nodePayload)
open Sphincs hiding HashDomain
open Sphincs.KeyGenerationAndSigning (ExpandedKey keyDerivationInput merkleLevels merkleLevelsFrom)
open Quantum.Sphincs (Slot)
open Quantum.Qrom.Sphincs (SlotPayload slotInput length_slotInput_le)
open Common

namespace Quantum.StdModel.Sphincs

/-! ## Bounds by kind of input -/

/-- **A bound on a hash call per kind of input**, the kinds of `Quantum.Sphincs.Slot`. -/
structure Kinds where
  /-- The key expansion. -/
  expand : ℕ
  /-- A secret's `PRF`. -/
  prf : ℕ
  /-- `PRF_msg`. -/
  prfMsg : ℕ
  /-- A call of `H_msg`. -/
  hmsg : ℕ
  /-- A WOTS chain step. -/
  chain : ℕ
  /-- A WOTS leaf. -/
  leaf : ℕ
  /-- A hypertree node. -/
  node : ℕ
  /-- An encoding trial. -/
  enc : ℕ
  /-- A FORS leaf. -/
  forsLeaf : ℕ
  /-- A FORS node. -/
  forsNode : ℕ
  /-- A FORS key. -/
  forsRoots : ℕ

/-- The bound of a slot's kind. -/
def Kinds.of (c : Kinds) : Slot → ℕ
  | .chain .. => c.chain
  | .leaf .. => c.leaf
  | .node .. => c.node
  | .enc .. => c.enc
  | .forsLeaf .. => c.forsLeaf
  | .forsNode .. => c.forsNode
  | .forsRoots _ => c.forsRoots
  | .prf _ => c.prf
  | .hmsg .. => c.hmsg
  | .prfMsg _ => c.prfMsg
  | .expand _ => c.expand

/-- The same bound `κ` for every kind. -/
def Kinds.const (κ : ℕ) : Kinds :=
  ⟨κ, κ, κ, κ, κ, κ, κ, κ, κ, κ, κ⟩

theorem Kinds.of_const (κ : ℕ) (s : Slot) : (Kinds.const κ).of s = κ := by
  cases s <;> rfl

variable {ι : Type} {O : OracleSpec.{0, 0} ι}

/-- **`hash` costs at most `c.of s` on every input of a slot `s`**. -/
def HashKinds (hash : HashInput → OracleComp O HashOutput) (cost : ι → ℕ) (c : Kinds) : Prop :=
  ∀ (key : ExpandedKey) (root : Digest) (s : Slot) (p : SlotPayload s),
    QueryCostAtMost (hash (slotInput key root s p)) cost (c.of s)

/-- A hash costing at most `κ` on every input of at most `maxLen` bytes costs at most `κ` on
every kind. -/
theorem hashKinds_const {hash : HashInput → OracleComp O HashOutput} {cost : ι → ℕ} {κ : ℕ}
    (h : ∀ l : HashInput, l.length ≤ Quantum.Qrom.maxLen → QueryCostAtMost (hash l) cost κ) :
    HashKinds hash cost (Kinds.const κ) := fun key root s p ↦ by
  rw [Kinds.of_const]
  exact h _ (length_slotInput_le key root s p)

/-! ## The bounds -/

/-- A one-time leaf's recovery. -/
def otsLeafW (c : Kinds) : ℕ := c.enc + (chainCount * (3 * c.chain) + c.leaf)

/-- A FORS tree's recovery. -/
def forsTreeRecoverW (c : Kinds) : ℕ := c.forsLeaf + forsTreeHeight * c.forsNode

/-- The FORS key's recovery. -/
def forsRecoverW (c : Kinds) : ℕ := forsTreeCount * forsTreeRecoverW c + c.forsRoots

/-- One layer of the walk up the hypertree. -/
def layerW (c : Kinds) : ℕ := otsLeafW c + 10 * c.node

/-- **The verifier.** -/
def verifyW (c : Kinds) : ℕ := 2 * c.hmsg + (forsRecoverW c + layerCount * layerW c)

/-- A one-time key's leaf. -/
def otsPublicLeafW (c : Kinds) : ℕ := chainCount * c.prf + (chainCount * (3 * c.chain) + c.leaf)

/-- Opening a one-time key once its counter is found. -/
def openW (c : Kinds) : ℕ := chainCount * c.prf + chainCount * (3 * c.chain)

/-- A one-time signature: the counter search at its cap, then the opening. -/
def otsSignW (c : Kinds) : ℕ := encodingAttemptLimit * c.enc + openW c

/-- A hypertree tree's levels, crudely at height `10`. -/
def treeLevelsW (c : Kinds) : ℕ := 2 ^ 10 * otsPublicLeafW c + 10 * (2 ^ 10 * c.node)

/-- One FORS tree, built once. -/
def forsTreeOpenW (c : Kinds) : ℕ := 2 ^ forsTreeHeight * c.prf +
  (2 ^ forsTreeHeight * c.forsLeaf + forsTreeHeight * (2 ^ forsTreeHeight * c.forsNode))

/-- The FORS instance. -/
def forsOpenW (c : Kinds) : ℕ := forsTreeCount * forsTreeOpenW c + c.forsRoots

/-- **Key generation.** -/
def keygenW (c : Kinds) : ℕ := 2 * c.expand + treeLevelsW c

/-- A layer's signature. -/
def signLayerW (c : Kinds) : ℕ := otsSignW c + treeLevelsW c

/-- **The signer of one message.** -/
def signW (c : Kinds) : ℕ :=
  2 * c.expand + (treeLevelsW c + (c.prfMsg + (2 * c.hmsg + (forsOpenW c + 3 * signLayerW c))))

theorem verifyW_const (κ : ℕ) : verifyW (Kinds.const κ) = 879 * κ := by
  simp only [verifyW, forsRecoverW, forsTreeRecoverW, layerW, otsLeafW, Kinds.const, chainCount,
    forsTreeCount, forsTreeHeight, layerCount]
  ring

theorem keygenW_const (κ : ℕ) : keygenW (Kinds.const κ) = 273410 * κ := by
  simp only [keygenW, treeLevelsW, otsPublicLeafW, Kinds.const, chainCount]
  ring

theorem signW_const (κ : ℕ) : signW (Kinds.const κ) = 12886291206 * κ := by
  simp only [signW, treeLevelsW, otsPublicLeafW, forsOpenW, forsTreeOpenW, signLayerW, otsSignW,
    openW, Kinds.const, chainCount, forsTreeCount, forsTreeHeight, encodingAttemptLimit]
  ring

/-! ## The scheme's calls -/

section Over

open Quantum.Qrom.Sphincs.LeanSphincsOver

-- Elaborating a combinator's bound at a literal size otherwise unfolds the combinator.
attribute [local irreducible] sequenceFin walkChain foldPath List.mapM List.range merkleLevelsFrom

variable {hash : HashInput → OracleComp O HashOutput} {cost : ι → ℕ} {c : Kinds}

/-- A truncated hash costs the hash. -/
theorem truncate_cost {input : HashInput} {n : ℕ} (h : QueryCostAtMost (hash input) cost n) :
    QueryCostAtMost (do return truncateHash (← hash input) : OracleComp O Digest) cost n :=
  (h.bind fun _ ↦ isWeightBound_pure _ _ 0).mono (Nat.le_of_eq (Nat.add_zero _))

theorem layerHeight_le' (l : Layer) : layerHeight l ≤ 10 := by
  unfold layerHeight
  split <;> omega

variable (hh : HashKinds hash cost c)
include hh

theorem chainWalk_cost (seed : PublicParameter) (l : Layer) (τ : TreeIndex) (e : TreeLeafIndex)
    (i : ChainIndex) (start steps : ℕ) (v : Digest) :
    QueryCostAtMost (chainWalk hash seed l τ e i start steps v) cost (steps * c.chain) :=
  walkChain_cost _ c.chain (fun step v ↦ truncate_cost (hh ⟨0, 0, seed⟩ 0 (.chain l τ e i step) v))
    start steps v

theorem recoverChain_cost (seed : PublicParameter) (l : Layer) (τ : TreeIndex) (e : TreeLeafIndex)
    (i : ChainIndex) (digit : WinternitzDigit) (v : Digest) :
    QueryCostAtMost (recoverChain hash seed l τ e i digit v) cost (3 * c.chain) :=
  (chainWalk_cost hh _ _ _ _ _ _ _ _).mono
    (Nat.mul_le_mul_right _ (by simp [chainLength, winternitzBits]))

theorem leafHash_cost (seed : PublicParameter) (l : Layer) (τ : TreeIndex) (e : TreeLeafIndex)
    (endpoints : ChainIndex → Digest) :
    QueryCostAtMost (leafHash hash seed l τ e endpoints) cost c.leaf :=
  truncate_cost (hh ⟨0, 0, seed⟩ 0 (.leaf l τ e) endpoints)

theorem encode_cost (seed : PublicParameter) (l : Layer) (τ : TreeIndex) (e : TreeLeafIndex)
    (m : Digest) (counter : EncodingCounter) :
    QueryCostAtMost (encode hash seed l τ e m counter) cost c.enc := by
  unfold encode
  exact ((truncate_cost (hh ⟨0, 0, seed⟩ 0 (.enc l τ e) (m, counter))).bind fun _ ↦
    isWeightBound_pure _ _ 0).mono (Nat.le_of_eq (Nat.add_zero _))

theorem otsLeaf_cost (seed : PublicParameter) (l : Layer) (τ : TreeIndex) (e : TreeLeafIndex)
    (m : Digest) (counter : EncodingCounter) (values : ChainIndex → Digest) :
    QueryCostAtMost (otsLeaf hash seed l τ e m counter values) cost (otsLeafW c) := by
  unfold otsLeaf
  refine ((encode_cost hh _ _ _ _ _ _).bind fun x ↦ ?_).mono le_rfl
  cases x with
  | none => exact (isWeightBound_pure _ _ _).mono (Nat.zero_le _)
  | some _ =>
    exact (QueryCostAtMost.bind (sequenceFin_cost _ _ fun _ ↦ recoverChain_cost hh _ _ _ _ _ _ _)
      fun _ ↦ QueryCostAtMost.bind (leafHash_cost hh _ _ _ _ _) fun _ ↦
        isWeightBound_pure _ _ 0).mono (by simp)

theorem treeFold_cost (seed : PublicParameter) (l : Layer) (τ : TreeIndex) (e : TreeLeafIndex)
    (path : ℕ → Digest) (levels : ℕ) (v : Digest) :
    QueryCostAtMost (treeFold hash seed l τ e path levels v) cost (levels * c.node) :=
  foldPath_cost _ c.node (fun h j left right ↦
    truncate_cost (hh ⟨0, 0, seed⟩ 0 (.node l τ (h + 1) j) (left, right))) _ _ levels v

theorem forsTreeRecover_cost (seed : PublicParameter) (idx : Index) (κ : ForsTreeIndex)
    (leaf : ForsLeafIndex) (opening : ForsTreeOpening) :
    QueryCostAtMost (forsTreeRecover hash seed idx κ leaf opening) cost (forsTreeRecoverW c) := by
  unfold forsTreeRecover forsLeafHash
  exact (truncate_cost (hh ⟨0, 0, seed⟩ 0 (.forsLeaf idx κ leaf) opening.secret)).bind fun _ ↦
    foldPath_cost _ c.forsNode (fun h j left right ↦
      truncate_cost (hh ⟨0, 0, seed⟩ 0 (.forsNode idx κ (h + 1) j) (left, right))) _ _ _ _

theorem forsRecover_cost (seed : PublicParameter) (idx : Index)
    (leaves : ForsTreeIndex → ForsLeafIndex) (opening : ForsTreeIndex → ForsTreeOpening) :
    QueryCostAtMost (forsRecover hash seed idx leaves opening) cost (forsRecoverW c) := by
  unfold forsRecover forsPublicKey
  exact (sequenceFin_cost _ _ fun _ ↦ forsTreeRecover_cost hh _ _ _ _ _).bind fun roots ↦
    truncate_cost (hh ⟨0, 0, seed⟩ 0 (.forsRoots idx) roots)

theorem messageDigest_cost (pk : PublicKey) (R : Randomizer) (msg : Message) :
    QueryCostAtMost (messageDigest hash pk R msg) cost (2 * c.hmsg) := by
  unfold messageDigest messageDigestCall
  exact (QueryCostAtMost.bind (sequenceFin_cost c.hmsg _ fun call ↦
    hh ⟨0, 0, pk.publicSeed⟩ pk.root (.hmsg R msg call) ()) fun _ ↦
      isWeightBound_pure _ _ 0).mono (by simp [digestCallCount])

theorem verifyLayers_cost (seed : PublicParameter) (idx : Index) (sig : Signature) :
    ∀ n msg, QueryCostAtMost (verifyLayers hash seed idx sig n msg) cost (n * layerW c)
  | 0, _ => by
    simp only [verifyLayers]
    exact isWeightBound_pure _ _ _
  | n + 1, msg => by
    simp only [verifyLayers]
    split
    · refine ((otsLeaf_cost hh _ _ _ _ _ _ _).bind fun x ↦ ?_).mono
        (Q := otsLeafW c + (10 * c.node + n * layerW c)) (by
          have := Nat.add_one_mul n (layerW c); unfold layerW at *; omega)
      cases x with
      | none => exact (isWeightBound_pure _ _ _).mono (Nat.zero_le _)
      | some _ =>
        refine ((treeFold_cost hh _ _ _ _ _ _ _).bind fun _ ↦ ?_).mono
          (Nat.add_le_add_right (Nat.mul_le_mul_right _ (layerHeight_le' _)) _)
        split
        · exact (isWeightBound_pure _ _ _).mono (Nat.zero_le _)
        · exact verifyLayers_cost seed idx sig n _
    · exact (isWeightBound_pure _ _ _).mono (Nat.zero_le _)

/-- **The verifier's calls.** -/
theorem verify_cost (pk : PublicKey) (msg : Message) (sig : Signature) :
    QueryCostAtMost (verify hash pk msg sig) cost (verifyW c) := by
  unfold verify
  refine (messageDigest_cost hh _ _ _).bind fun _ ↦ (forsRecover_cost hh _ _ _ _).bind fun _ ↦ ?_
  refine ((verifyLayers_cost hh _ _ _ _ _).bind fun r ↦ ?_).mono
    (Q := layerCount * layerW c + 0) (by simp)
  cases r <;> exact isWeightBound_pure _ _ _

theorem expandKey_cost (S : SecretKey) :
    QueryCostAtMost (expandKey hash S) cost (2 * c.expand) := by
  unfold expandKey
  exact (QueryCostAtMost.bind (hh ⟨S, 0, 0⟩ 0 (.expand 1) ()) fun _ ↦
    QueryCostAtMost.bind (hh ⟨S, 0, 0⟩ 0 (.expand 0) ()) fun _ ↦ isWeightBound_pure _ _ 0).mono
      (by show c.expand + (c.expand + 0) ≤ 2 * c.expand; omega)

theorem prf_cost (key : ExpandedKey) (d : KeygenDomain) :
    QueryCostAtMost (prf hash key d) cost c.prf :=
  truncate_cost (hh key 0 (.prf d) ())

theorem prfMessage_cost (key : ExpandedKey) (msg : Message) :
    QueryCostAtMost (prfMessage hash key.secretPrfKey key.publicSeed msg) cost c.prfMsg :=
  truncate_cost (hh key 0 (.prfMsg msg) ())

omit hh in
/-- Merkle levels over at most `L` nodes make at most `L` node hashes per level. -/
theorem merkleLevelsFrom_cost (node : ℕ → ℕ → HashInput → OracleComp O Digest) (b : ℕ)
    (hn : ∀ h j left right, QueryCostAtMost (node h j (nodePayload left right)) cost b)
    (L : ℕ) : ∀ remaining height (below : List Digest), below.length ≤ L →
      QueryCostAtMost (merkleLevelsFrom node height below remaining) cost (remaining * (L * b))
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

theorem otsSecrets_cost (key : ExpandedKey) (l : Layer) (τ : TreeIndex) (e : TreeLeafIndex) :
    QueryCostAtMost (otsSecrets hash key l τ e) cost (chainCount * c.prf) :=
  sequenceFin_cost _ _ fun _ ↦ prf_cost hh _ _

theorem otsPublicLeaf_cost (key : ExpandedKey) (l : Layer) (τ : TreeIndex) (e : TreeLeafIndex) :
    QueryCostAtMost (otsPublicLeaf hash key l τ e) cost (otsPublicLeafW c) := by
  unfold otsPublicLeaf
  exact (otsSecrets_cost hh _ _ _ _).bind fun _ ↦
    (sequenceFin_cost (3 * c.chain) _ fun _ ↦ (chainWalk_cost hh _ _ _ _ _ _ _ _).mono
      (Nat.mul_le_mul_right _ (by simp [chainLength, winternitzBits]))).bind fun _ ↦
    leafHash_cost hh _ _ _ _ _

/-- **The counter search**: `attempts` trials, then the opening. -/
theorem otsSignFrom_cost (key : ExpandedKey) (l : Layer) (τ : TreeIndex) (e : TreeLeafIndex)
    (m : Digest) : ∀ attempts counter, QueryCostAtMost
      (otsSignFrom hash key l τ e m attempts counter) cost (attempts * c.enc + openW c)
  | 0, _ => by
    simp only [otsSignFrom]
    exact isWeightBound_pure _ _ _
  | attempts + 1, counter => by
    simp only [otsSignFrom]
    refine ((encode_cost hh _ _ _ _ _ _).bind fun x ↦ ?_).mono
      (Q := c.enc + (attempts * c.enc + openW c)) (by rw [Nat.succ_mul]; omega)
    cases x with
    | some encoding =>
      refine (QueryCostAtMost.bind (otsSecrets_cost hh _ _ _ _) fun _ ↦
        QueryCostAtMost.bind (sequenceFin_cost (3 * c.chain) _ fun i ↦ ?_) fun _ ↦
          isWeightBound_pure _ _ 0).mono (by simp [openW])
      refine (chainWalk_cost hh _ _ _ _ _ _ _ _).mono (Nat.mul_le_mul_right _ ?_)
      have := (encoding i).isLt
      simp only [chainLength, winternitzBits] at this
      omega
    | none => exact otsSignFrom_cost key l τ e m attempts (counter + 1)

theorem otsSign_cost (key : ExpandedKey) (l : Layer) (τ : TreeIndex) (e : TreeLeafIndex)
    (m : Digest) : QueryCostAtMost (otsSign hash key l τ e m) cost (otsSignW c) :=
  otsSignFrom_cost hh _ _ _ _ _ _ _

theorem treeLevels_cost (key : ExpandedKey) (l : Layer) (τ : TreeIndex) :
    QueryCostAtMost (treeLevels hash key l τ) cost (treeLevelsW c) := by
  unfold treeLevels merkleLevels
  have hh' := layerHeight_le' l
  have hp : 2 ^ layerHeight l ≤ 2 ^ 10 := Nat.pow_le_pow_right (by norm_num) hh'
  refine (QueryCostAtMost.bind_of_support ((mapM_cost _ _ (fun _ ↦ otsPublicLeaf_cost hh _ _ _ _)
    _).mono (Nat.mul_le_mul_right _ (by rw [List.length_range]; exact hp))) fun leaves hl ↦ ?_).mono
    le_rfl
  have hl' : leaves.length ≤ 2 ^ 10 :=
    (length_of_mem_support_mapM _ _ leaves hl).trans_le (by rw [List.length_range]; exact hp)
  exact (merkleLevelsFrom_cost _ c.node (fun h j left right ↦
    truncate_cost (hh ⟨0, 0, key.publicSeed⟩ 0 (.node l τ h j) (left, right))) _ _ 0 leaves
    hl').mono (Nat.mul_le_mul_right _ hh')

theorem forsTreeOpen_cost (key : ExpandedKey) (idx : Index) (κ : ForsTreeIndex)
    (leaf : ForsLeafIndex) :
    QueryCostAtMost (forsTreeOpen hash key idx κ leaf) cost (forsTreeOpenW c) := by
  unfold forsTreeOpen merkleLevels
  refine ((mapM_cost _ _ (fun _ ↦ prf_cost hh _ _) _).bind fun secrets ↦ ?_).mono
    (by simp only [List.length_range, forsTreeOpenW]; exact le_rfl)
  refine (QueryCostAtMost.bind_of_support (mapM_cost _ c.forsLeaf (fun s ↦
    truncate_cost (hh ⟨0, 0, key.publicSeed⟩ 0 (.forsLeaf idx κ (forsLeafOfNat s))
      (secrets.getD s 0))) _) fun leaves hl ↦ ?_).mono (by rw [List.length_range])
  have hl' : leaves.length ≤ 2 ^ forsTreeHeight :=
    (length_of_mem_support_mapM _ _ leaves hl).trans_le (by rw [List.length_range])
  exact ((merkleLevelsFrom_cost _ c.forsNode (fun h j left right ↦
    truncate_cost (hh ⟨0, 0, key.publicSeed⟩ 0 (.forsNode idx κ h j) (left, right))) _ _ 0
    leaves hl').bind fun _ ↦ isWeightBound_pure _ _ 0).mono (by simp)

theorem forsOpen_cost (key : ExpandedKey) (idx : Index) (leaves : ForsTreeIndex → ForsLeafIndex) :
    QueryCostAtMost (forsOpen hash key idx leaves) cost (forsOpenW c) := by
  unfold forsOpen forsPublicKey
  exact (QueryCostAtMost.bind (sequenceFin_cost _ _ fun _ ↦ forsTreeOpen_cost hh _ _ _ _)
    fun trees ↦ QueryCostAtMost.bind (truncate_cost (hh ⟨0, 0, key.publicSeed⟩ 0 (.forsRoots idx)
      fun κ ↦ (trees κ).1)) fun _ ↦ isWeightBound_pure _ _ 0).mono
        (by simp [forsOpenW, Kinds.of])

theorem keygenInternal_cost (key : ExpandedKey) :
    QueryCostAtMost (keygenInternal hash key) cost (treeLevelsW c) := by
  unfold keygenInternal
  exact ((treeLevels_cost hh _ _ _).bind fun _ ↦ isWeightBound_pure _ _ 0).mono (by simp)

/-- **Key generation's calls.** -/
theorem keygenFromSeed_cost (S : SecretKey) :
    QueryCostAtMost (keygenFromSeed hash S) cost (keygenW c) := by
  unfold keygenFromSeed
  refine (expandKey_cost hh _).bind fun _ ↦ ((keygenInternal_cost hh _).bind fun p ↦ ?_).mono
    (Q := treeLevelsW c + 0) (by simp)
  obtain ⟨_, _⟩ := p
  exact isWeightBound_pure _ _ _

theorem signLayer_cost (key : ExpandedKey) (top : List (List Digest)) (idx : Index) (l : Layer)
    (m : Digest) : QueryCostAtMost (signLayer hash key top idx l m) cost (signLayerW c) := by
  unfold signLayer
  refine ((otsSign_cost hh _ _ _ _ _).bind fun o ↦ ?_).mono
    (Q := otsSignW c + (treeLevelsW c + 0)) (by simp [signLayerW])
  rcases o with _ | ⟨_, _⟩
  · exact (isWeightBound_pure _ _ _).mono (Nat.zero_le _)
  · dsimp only
    split
    · exact (QueryCostAtMost.bind (isWeightBound_pure _ _ 0) fun _ ↦ isWeightBound_pure _ _ 0).mono
        (Nat.zero_le _)
    · exact QueryCostAtMost.bind (treeLevels_cost hh _ _ _) fun _ ↦ isWeightBound_pure _ _ 0

/-- **The signer's calls on one message**, the counter search at its cap. -/
theorem sign_cost (S : SecretKey) (msg : Message) :
    QueryCostAtMost (sign hash S msg) cost (signW c) := by
  unfold sign signWithExpandedKey
  refine (expandKey_cost hh _).bind fun key ↦ (keygenInternal_cost hh _).bind fun p ↦ ?_
  obtain ⟨_, _⟩ := p
  refine (prfMessage_cost hh _ _).bind fun _ ↦ (messageDigest_cost hh _ _ _).bind fun _ ↦
    (forsOpen_cost hh _ _ _).bind fun f ↦ ?_
  obtain ⟨_, _⟩ := f
  refine ((signLayer_cost hh _ _ _ _ _).bind fun o ↦ ?_).mono
    (Q := signLayerW c + (signLayerW c + (signLayerW c + 0))) (by omega)
  rcases o with _ | ⟨_, _⟩
  · exact (isWeightBound_pure _ _ _).mono (Nat.zero_le _)
  refine (signLayer_cost hh _ _ _ _ _).bind fun o ↦ ?_
  rcases o with _ | ⟨_, _⟩
  · exact (isWeightBound_pure _ _ _).mono (Nat.zero_le _)
  refine (signLayer_cost hh _ _ _ _ _).bind fun o ↦ ?_
  rcases o with _ | ⟨_, _⟩ <;> exact isWeightBound_pure _ _ _

end Over

end Quantum.StdModel.Sphincs

end
