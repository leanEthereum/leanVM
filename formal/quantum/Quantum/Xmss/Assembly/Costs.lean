module

public import Quantum.Xmss.Game
public import Quantum.Xmss.Events
public import Quantum.Xmss.Hybrid.Seed
public import Common.XmssCost
public import Common.Rerun

@[expose] public section

/-!
# leanXMSS's honest costs and the cap on the hardwired cells

**Honest costs.** Every hash of the scheme is counted in Keccak-f blocks (`hashBlocks`,
`⌊n / 136⌋ + 1` for `n` bytes): one for every tweakable hash except the leaf hash (`8`). The
hash-query scheme `schemeWithHashFromSeed` makes, on every path,

* key generation: `keygenBlocks = 13893633` blocks (the top tree: `2^16` one-time keys of `29 + 174`
  blocks and their `8`-block leaves, `2^16 - 1` nodes, the seed and the parameter);
* a signature: `signBlocks = 9048424824` blocks (the randomizer search at its cap `2^32` per
  layer, the openings, crude `16`-node authentication paths and the bottom root);
* verification: `verifyBlocks = 398` blocks.

Over `π` each block is one permutation call (`keccak256With_cost`), so these are the costs `kc`,
`sc`, `vc` of `Quantum.Xmss.isTotalQueryBound_game` (`sufCmaScheme_generateKeys_cost`, ...,
`isTotalQueryBound_game_concrete`), sharper than the crude `Common.XmssCost` bounds. Against keys
`t`, the honest evaluation reads three cells per block (`length_snd_honestEval`), so it makes at
most `3 * keygenBlocks`, `3 * signBlocks`, `3 * verifyBlocks` reads
(`length_snd_honestEval_keygen_le`, `..._sign_le`, `..._verify_le`).

**The cap.** In the hardwired runtime only the program ports change the hardwired cells, each by
one cell, so after `K` program calls every reachable state has `dbGrade W ≤ dbGrade W₀ + K`
(`dbGrade_le_of_programs`). Runtime 2 programs the three cells (`k`, `k'`, `h`) of every block of
the honest input of each slot a signature makes public (`slotCells`: `3` for a chain step or a
node, `24` for a leaf), repeats included. These slots lie in the slots of the request's two keys
(`keySlots`: all chain steps, the leaf and the `16` nodes on the path; `public_disclosures_subset`),
so a request makes at most `1188` program calls (`sum_slotCells_le_of_subset_keySlots`,
`sum_slotCells_le_of_subset_public`). With at most `2^32` requests from `W₀ = ∅`, every reachable
state has `dbGrade W ≤ progCap = 1188 · 2^32` (`dbGrade_le_progCap`; with further ports that keep
the hardwired cells, such as record ports, `dbGrade_le_progCap_extend`).
-/

open OracleComp OracleSpec Matrix IPFunctor
open scoped Kronecker

universe w u₁ v₁ uL vL

/-! ## The honest costs -/

namespace Quantum.Xmss

open Common Common.SufCma HashSig HashSig.OverPermutation LeanXmss
  LeanXmss.RandomPermutationModel

-- Elaborating a combinator's bound at a literal size otherwise unfolds the combinator.
attribute [local irreducible] sequenceFin walkChain foldPath buildTree

/-- The Keccak-f blocks of hashing an input: `⌊n / 136⌋ + 1` for `n` bytes. -/
def hashBlocks (input : HashInput) : ℕ :=
  input.length / 136 + 1

theorem hashBlocks_eq_length_blocks (input : HashInput) :
    hashBlocks input = (blocks input).length :=
  (length_blocks input).symm

/-- One hash query costs its blocks. -/
theorem oracleHash_cost (input : HashInput) :
    QueryCostAtMost (Verification.oracleHashWithHash (m := OracleComp HashSpec) input) hashBlocks
      (hashBlocks input) := by
  rw [Verification.oracleHashWithHash, HasQuery.instOfMonadLift_query]
  exact isWeightBound_query _ _

theorem hashBlocks_le {input : HashInput} {k : ℕ} (h : input.length < 136 * (k + 1)) :
    hashBlocks input ≤ k + 1 := by
  have : input.length / 136 < k + 1 := Nat.div_lt_of_lt_mul (by omega)
  unfold hashBlocks
  omega

theorem th_cost (parameter : PublicParameter) (fields : TweakFields) (payload : HashInput) {k : ℕ}
    (h : 32 + payload.length < 136 * (k + 1)) :
    QueryCostAtMost (Verification.thWithHash (m := OracleComp HashSpec) parameter fields payload)
      hashBlocks (k + 1) := by
  unfold Verification.thWithHash
  refine ((oracleHash_cost _).bind fun _ ↦ isWeightBound_pure _ _ 0).mono ?_
  rw [Nat.add_zero]
  exact hashBlocks_le (by rw [XmssCost.thInput_length]; exact h)

theorem thPair_cost (parameter : PublicParameter) (fields : TweakFields) (payload : HashInput)
    {k : ℕ} (h : 32 + payload.length < 136 * (k + 1)) :
    QueryCostAtMost (Verification.thPairWithHash (m := OracleComp HashSpec) parameter fields payload)
      hashBlocks (k + 1) :=
  (oracleHash_cost _).mono (hashBlocks_le (by rw [XmssCost.thInput_length]; exact h))

theorem taggedSeed_cost (seed : MasterSeed) :
    QueryCostAtMost (Verification.taggedSeedWithHash (m := OracleComp HashSpec) seedTag seed)
      hashBlocks 1 :=
  (oracleHash_cost _).mono (hashBlocks_le (k := 0) (by simp [seedTag, littleEndianBytes]))

/-! ### The verifier -/

section Verification

open LeanXmss.Verification

theorem chainWalk_cost (parameter : PublicParameter) (layer : Layer) (key : KeyIndex)
    (chainIndex : ChainIndex) (start steps : ℕ) (v : Digest) :
    QueryCostAtMost (chainWalkWithHash (m := OracleComp HashSpec) parameter layer key chainIndex
      start steps v) hashBlocks (steps * 1) :=
  walkChain_cost _ 1 (fun _ _ ↦ th_cost _ _ _ (k := 0) (by
    simp [chainPayload, littleEndianBytes])) start steps v

theorem recoverChain_cost (parameter : PublicParameter) (layer : Layer) (key : KeyIndex)
    (chainIndex : ChainIndex) (digit : WinternitzDigit) (v : Digest) :
    QueryCostAtMost (recoverChainWithHash (m := OracleComp HashSpec) parameter layer key chainIndex
      digit v) hashBlocks (3 * 1) :=
  (chainWalk_cost _ _ _ _ _ _ _).mono
    (Nat.mul_le_mul_right _ (by simp [chainLength, winternitzBits]))

theorem leafHash_cost (parameter : PublicParameter) (layer : Layer) (key : KeyIndex)
    (endpoints : ChainIndex → Digest) :
    QueryCostAtMost (leafHashWithHash (m := OracleComp HashSpec) parameter layer key endpoints)
      hashBlocks 8 :=
  th_cost _ _ _ (k := 7) (by rw [XmssCost.digestsPayload_length]; simp [chainCount])

theorem messageDigest_cost (parameter : PublicParameter) (layer : Layer) (key : KeyIndex)
    (message : HashInput) (randomizer : Randomizer) (hm : message.length ≤ 32) :
    QueryCostAtMost (messageDigestWithHash (m := OracleComp HashSpec) parameter layer key message
      randomizer) hashBlocks 1 :=
  th_cost _ _ _ (k := 0) (by simp [littleEndianBytes]; omega)

/-- The blocks of a one-time leaf's recovery. -/
def otsLeafBlocks : ℕ := 1 + chainCount * (3 * 1) + 8

theorem otsLeaf_cost (parameter : PublicParameter) (layer : Layer) (key : KeyIndex)
    (message : HashInput) (randomizer : Randomizer) (values : ChainIndex → Digest)
    (hm : message.length ≤ 32) :
    QueryCostAtMost (otsLeafWithHash (m := OracleComp HashSpec) parameter layer key message
      randomizer values) hashBlocks otsLeafBlocks := by
  unfold otsLeafWithHash
  refine ((messageDigest_cost parameter layer key message randomizer hm).bind fun digest ↦
    ?_).mono (Q := 1 + (chainCount * (3 * 1) + 8)) (by simp [otsLeafBlocks]; omega)
  split
  · exact ((sequenceFin_cost _ _ fun i ↦ recoverChain_cost _ _ _ _ _ _).bind fun endpoints ↦
      (leafHash_cost _ _ _ _).bind fun _ ↦ isWeightBound_pure _ _ 0).mono (by simp)
  · exact (isWeightBound_pure _ _ _).mono (Nat.zero_le _)

theorem treeFold_cost (parameter : PublicParameter) (layer : Layer) (key : KeyIndex)
    (path : Fin layerHeight → Digest) (levels : ℕ) (v : Digest) :
    QueryCostAtMost (treeFoldWithHash (m := OracleComp HashSpec) parameter layer key path levels v)
      hashBlocks (levels * 1) :=
  foldPath_cost _ 1 (fun _ _ _ _ ↦ th_cost _ _ _ (k := 0) (by
    simp [nodePayload, littleEndianBytes])) _ _ levels v

/-- The blocks of a layer's root. -/
def layerRootBlocks : ℕ := otsLeafBlocks + layerHeight * 1

theorem layerRoot_cost (parameter : PublicParameter) (layer : Layer) (key : KeyIndex)
    (message : HashInput) (layerSignature : LayerSignature) (hm : message.length ≤ 32) :
    QueryCostAtMost (layerRootWithHash (m := OracleComp HashSpec) parameter layer key message
      layerSignature) hashBlocks layerRootBlocks := by
  unfold layerRootWithHash
  refine ((otsLeaf_cost _ _ _ _ _ _ hm).bind fun leaf ↦ ?_).mono
    (Q := otsLeafBlocks + layerHeight * 1) le_rfl
  cases leaf with
  | none => exact (isWeightBound_pure _ _ _).mono (Nat.zero_le _)
  | some _ =>
    exact (QueryCostAtMost.bind (treeFold_cost _ _ _ _ _ _) fun _ ↦ isWeightBound_pure _ _ 0).mono
      (by simp)

/-- **The verifier's blocks.** -/
def verifyBlocks : ℕ := 2 * layerRootBlocks

theorem verifyBlocks_eq : verifyBlocks = 398 := by
  simp [verifyBlocks, layerRootBlocks, otsLeafBlocks, chainCount, layerHeight]

theorem verify_cost (publicKey : PublicKey) (message : Message) (signature : Signature) :
    QueryCostAtMost (verifyWithHash (m := OracleComp HashSpec) publicKey message signature)
      hashBlocks verifyBlocks := by
  unfold verifyWithHash
  refine ((layerRoot_cost _ _ _ _ _ (by simp [littleEndianBytes])).bind fun r ↦ ?_).mono
    (Q := layerRootBlocks + layerRootBlocks) (by simp [verifyBlocks]; omega)
  cases r with
  | none => exact (isWeightBound_pure _ _ _).mono (Nat.zero_le _)
  | some _ =>
    refine ((layerRoot_cost _ _ _ _ _ (by simp [littleEndianBytes])).bind fun r' ↦ ?_).mono
      (Q := layerRootBlocks + 0) (by simp)
    cases r' <;> exact isWeightBound_pure _ _ _

end Verification

/-! ### Key generation and the signer -/

section KeyGenerationAndSigning

open LeanXmss.Verification LeanXmss.KeyGenerationAndSigning

/-- The blocks of a one-time key's secrets. -/
def otsSecretsBlocks : ℕ := (chainCount / 2) * 1

theorem otsSecrets_cost (parameter : PublicParameter) (layer : Layer) (key : KeyIndex)
    (seed : MasterSeed) :
    QueryCostAtMost (otsSecretsWithHash (m := OracleComp HashSpec) parameter layer key seed)
      hashBlocks otsSecretsBlocks := by
  unfold otsSecretsWithHash
  exact ((sequenceFin_cost _ _ fun _ ↦ thPair_cost _ _ _ (k := 0)
    (by simp [littleEndianBytes])).bind fun _ ↦ isWeightBound_pure _ _ 0).mono
      (by simp [otsSecretsBlocks])

/-- The blocks of a one-time public key, and of opening a one-time key. -/
def oneTimePublicKeyBlocks : ℕ := otsSecretsBlocks + chainCount * (3 * 1)

theorem oneTimePublicKey_cost (parameter : PublicParameter) (layer : Layer) (key : KeyIndex)
    (seed : MasterSeed) :
    QueryCostAtMost (oneTimePublicKeyWithHash (m := OracleComp HashSpec) parameter layer key seed)
      hashBlocks oneTimePublicKeyBlocks := by
  unfold oneTimePublicKeyWithHash
  exact (otsSecrets_cost _ _ _ _).bind fun _ ↦ sequenceFin_cost _ _ fun _ ↦
    (chainWalk_cost _ _ _ _ _ _ _).mono
      (Nat.mul_le_mul_right _ (by simp [chainLength, winternitzBits]))

theorem otsSignFrom_cost (parameter : PublicParameter) (layer : Layer) (key : KeyIndex)
    (seed : MasterSeed) (message : HashInput) (randomizerBase : Randomizer)
    (hm : message.length ≤ 32) :
    ∀ attempts trial, QueryCostAtMost
      (otsSignFromWithHash (m := OracleComp HashSpec) parameter layer key seed message
        randomizerBase attempts trial)
      hashBlocks (attempts * 1 + oneTimePublicKeyBlocks)
  | 0, _ => by
    simp only [otsSignFromWithHash]
    exact isWeightBound_pure _ _ _
  | attempts + 1, trial => by
    simp only [otsSignFromWithHash]
    refine ((messageDigest_cost parameter layer key message _ hm).bind
      fun digest ↦ ?_).mono (Q := 1 + (attempts * 1 + oneTimePublicKeyBlocks)) (by
        rw [Nat.succ_mul]; omega)
    split
    next encoding _ =>
      refine (QueryCostAtMost.bind (otsSecrets_cost _ _ _ _) fun _ ↦
        QueryCostAtMost.bind (sequenceFin_cost (3 * 1) _ fun i ↦ ?_) fun _ ↦
          isWeightBound_pure _ _ 0).mono (by simp [oneTimePublicKeyBlocks])
      · refine (chainWalk_cost _ _ _ _ _ _ _).mono (Nat.mul_le_mul_right _ ?_)
        have := (encoding i).isLt
        simp only [chainLength, winternitzBits] at this
        omega
    · exact otsSignFrom_cost parameter layer key seed message randomizerBase hm attempts
        (trial + 1)

/-- The blocks of a one-time signature: the randomizer base, the search at its cap, the
opening. -/
def otsSignBlocks : ℕ := 1 + (randomizerAttemptLimit * 1 + oneTimePublicKeyBlocks)

theorem otsSign_cost (parameter : PublicParameter) (layer : Layer) (key : KeyIndex)
    (seed : MasterSeed) (message : HashInput) (hm : message.length ≤ 32) :
    QueryCostAtMost (otsSignWithHash (m := OracleComp HashSpec) parameter layer key seed message)
      hashBlocks otsSignBlocks := by
  unfold otsSignWithHash
  exact (th_cost _ _ _ (k := 0) (by simp [littleEndianBytes]; omega)).bind fun _ ↦
    otsSignFrom_cost _ _ _ _ _ _ hm _ _

/-- The blocks of a tree node at level `16` or below, crudely. -/
def treeNodeBlocks : ℕ := 2 ^ layerHeight * (oneTimePublicKeyBlocks + 8) +
  (2 ^ layerHeight - 1) * 1

theorem treeNode_cost (parameter : PublicParameter) (layer : Layer) (seed : MasterSeed)
    (level index : ℕ) (hl : level ≤ layerHeight) :
    QueryCostAtMost (treeNodeWithHash (m := OracleComp HashSpec) parameter layer seed level index)
      hashBlocks treeNodeBlocks := by
  unfold treeNodeWithHash
  refine (buildTree_cost _ _ (oneTimePublicKeyBlocks + 8) 1
    (fun _ ↦ (oneTimePublicKey_cost _ _ _ _).bind fun _ ↦ leafHash_cost _ _ _ _)
    (fun _ _ _ _ ↦ th_cost _ _ _ (k := 0) (by simp [nodePayload, littleEndianBytes]))
    level index).mono ?_
  have hp : 2 ^ level ≤ 2 ^ layerHeight := Nat.pow_le_pow_right (by norm_num) hl
  unfold treeNodeBlocks
  gcongr

/-- The blocks of an authentication path. -/
def treePathBlocks : ℕ := layerHeight * treeNodeBlocks

theorem treePath_cost (parameter : PublicParameter) (layer : Layer) (seed : MasterSeed)
    (key : KeyIndex) :
    QueryCostAtMost (treePathWithHash (m := OracleComp HashSpec) parameter layer seed key)
      hashBlocks treePathBlocks :=
  sequenceFin_cost _ _ fun level ↦ treeNode_cost _ _ _ _ _ level.isLt.le

/-- **Key generation's blocks.** -/
def keygenBlocks : ℕ := 1 + (1 + treeNodeBlocks)

theorem keygenBlocks_eq : keygenBlocks = 13893633 := by
  simp [keygenBlocks, treeNodeBlocks, oneTimePublicKeyBlocks, otsSecretsBlocks, chainCount,
    layerHeight]

theorem keygen_cost (S0 : MasterSeed) :
    QueryCostAtMost (schemeWithHashFromSeed.keygen S0) hashBlocks keygenBlocks := by
  simp only [schemeWithHashFromSeed, SufCma.KeptKey.scheme, keptKey, deriveSchemeSeedKey,
    keygenRest, bind_assoc, pure_bind]
  exact QueryCostAtMost.bind (taggedSeed_cost S0) fun _ ↦
    QueryCostAtMost.bind (th_cost _ _ _ (k := 0) (by simp [littleEndianBytes])) fun _ ↦
      isWeightBound_map _ (QueryCostAtMost.bind (treeNode_cost _ _ _ _ _ le_rfl) fun _ ↦
        isWeightBound_pure _ _ 0) |>.mono (by simp)

/-- A layer's signature's blocks. -/
def signLayerBlocks : ℕ := otsSignBlocks + treePathBlocks

theorem signLayer_cost (secretKey : SchemeSeedKey) (layer : Layer) (key : KeyIndex)
    (message : HashInput) (hm : message.length ≤ 32) :
    QueryCostAtMost (signLayerWithHash (m := OracleComp HashSpec) secretKey layer key message)
      hashBlocks signLayerBlocks := by
  unfold signLayerWithHash
  refine ((otsSign_cost _ _ _ _ _ hm).bind fun o ↦ ?_).mono
    (Q := otsSignBlocks + treePathBlocks) le_rfl
  rcases o with _ | ⟨_, _⟩
  · exact (isWeightBound_pure _ _ _).mono (Nat.zero_le _)
  · exact (QueryCostAtMost.bind (treePath_cost _ _ _ _) fun _ ↦ isWeightBound_pure _ _ 0).mono
      (by simp)

/-- **A signature's blocks**: the scheme seed, the two layers' signatures and the bottom root. -/
def signBlocks : ℕ := 1 + (signLayerBlocks + (treeNodeBlocks + signLayerBlocks))

theorem signBlocks_eq : signBlocks = 9048424824 := by
  simp [signBlocks, signLayerBlocks, otsSignBlocks, treePathBlocks, treeNodeBlocks,
    oneTimePublicKeyBlocks, otsSecretsBlocks, chainCount, layerHeight, randomizerAttemptLimit]

theorem sign_cost (secretKey : SecretKey) (request : SigningRequest) :
    QueryCostAtMost (schemeWithHashFromSeed.sign secretKey request) hashBlocks signBlocks := by
  simp only [schemeWithHashFromSeed, SufCma.KeptKey.scheme, keptKey, rederiveSchemeSeedKey,
    schemeWithHash, bind_assoc, pure_bind]
  refine (taggedSeed_cost _).bind fun _ ↦ ?_
  unfold signWithHash
  refine ((signLayer_cost _ _ _ _ (by simp [littleEndianBytes])).bind fun o ↦ ?_).mono
    (Q := signLayerBlocks + (treeNodeBlocks + signLayerBlocks)) le_rfl
  cases o with
  | none => exact (isWeightBound_pure _ _ _).mono (Nat.zero_le _)
  | some _ =>
    refine QueryCostAtMost.bind (treeNode_cost _ _ _ _ _ le_rfl) fun root ↦ ?_
    refine (QueryCostAtMost.bind (signLayer_cost _ _ _ _ (by simp [littleEndianBytes]))
      fun o' ↦ ?_).mono (Q := signLayerBlocks + 0) (by simp)
    cases o' <;> exact isWeightBound_pure _ _ _

theorem verify_cost' (publicKey : PublicKey) (forgery : Forgery) :
    QueryCostAtMost (schemeWithHashFromSeed.verify publicKey forgery) hashBlocks verifyBlocks :=
  verify_cost _ _ _

end KeyGenerationAndSigning

/-! ### Permutation calls -/

/-- A hash over `π` makes one call per block. -/
theorem schemeHashOverPermutation_cost (input : HashInput) :
    QueryCostAtMost (schemeHashOverPermutation input) permutationCallCost (hashBlocks input) :=
  isWeightBound_map _ (isWeightBound_map _ (keccak256With_cost input))

/-- **`kc`**: the statement's key generation makes at most `13893633` permutation calls. -/
theorem sufCmaScheme_generateKeys_cost (S0 : MasterSeed) :
    QueryCostAtMost (sufCmaScheme.generateKeys S0) permutationCallCost 13893633 := by
  rw [scheme_eq, ← keygenBlocks_eq]
  exact isWeightBound_simulateQ _ _ _ schemeHashOverPermutation_cost (keygen_cost S0)

/-- **`sc`**: the statement's signer makes at most `9048424824` permutation calls per request. -/
theorem sufCmaScheme_sign_cost (sk : SecretKey) (r : SigningRequest) :
    QueryCostAtMost (sufCmaScheme.sign sk r) permutationCallCost 9048424824 := by
  rw [scheme_eq, ← signBlocks_eq]
  exact isWeightBound_simulateQ _ _ _ schemeHashOverPermutation_cost (sign_cost sk r)

/-- **`vc`**: the statement's verifier makes at most `398` permutation calls. -/
theorem sufCmaScheme_verify_cost (pk : PublicKey) (f : Forgery) :
    QueryCostAtMost (sufCmaScheme.verify pk f) permutationCallCost 398 := by
  rw [scheme_eq, ← verifyBlocks_eq]
  exact isWeightBound_simulateQ _ _ _ schemeHashOverPermutation_cost (verify_cost' pk f)

/-- **The game's calls, concretely**: key generation's `13893633`, the adversary's `q`, at most
`9048424824` per signing request, and verification's `398`. -/
theorem isTotalQueryBound_game_concrete {S : Type} [Fintype S] [DecidableEq S] [AddCommGroup S]
    (e : LeanVM.Semantics.KeccakState ≃ S) (S0 : MasterSeed) {A : Adversary S} {q n : ℕ}
    (hperm : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge permCharge) q)
    (hsignq : ∀ pk, IFreeM.IsChargeBound (A pk) (cmdCharge signCharge) n) :
    (game e S0 A).IsTotalQueryBound (13893633 + (q + 9048424824 * n) + 398) :=
  isTotalQueryBound_game e S0 (sufCmaScheme_generateKeys_cost S0) sufCmaScheme_sign_cost
    sufCmaScheme_verify_cost hperm hsignq

/-! ### Honest reads -/

/-- The queries along the path answered by `f` cost at most a bound on every path. -/
theorem sum_map_queries_le {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type}
    (f : QueryImpl spec Id) (w : ι → ℕ) {x : OracleComp spec α} {n : ℕ}
    (h : QueryCostAtMost x w n) : ((queries f x).map w).sum ≤ n := by
  induction x using OracleComp.inductionOn generalizing n with
  | pure a => simp [queries, trace_pure]
  | query_bind t k ih =>
    rw [isWeightBound_query_bind_iff] at h
    rw [queries, trace_query_bind, ← queries]
    have := ih (f t) (h.2 (f t))
    simp only [List.singleton_append, List.map_cons, List.sum_cons]
    omega

/-- **The reads of an honest evaluation**: at most three per block of a path bound. -/
theorem length_snd_honestEval_le (t : SpongeKeys X Z) (π : Equiv.Perm (X × Z)) {α : Type}
    {x : OracleComp HashSpec α} {n : ℕ} (h : QueryCostAtMost x hashBlocks n) :
    (honestEval t π x).2.length ≤ 3 * n := by
  rw [Hybrid.length_snd_honestEval]
  have hs := sum_map_queries_le (spongeOut (spongePerm t π)) hashBlocks h
  have hf : (fun inp : HashInput ↦ 3 * (blocks inp).length) = fun inp ↦ 3 * hashBlocks inp :=
    funext fun inp ↦ by rw [hashBlocks_eq_length_blocks]
  rw [hf, List.sum_map_mul_left]
  exact Nat.mul_le_mul_left 3 hs

theorem length_snd_honestEval_keygen_le (t : SpongeKeys X Z) (π : Equiv.Perm (X × Z))
    (S0 : MasterSeed) :
    (honestEval t π (schemeWithHashFromSeed.keygen S0)).2.length ≤ 3 * 13893633 :=
  keygenBlocks_eq ▸ length_snd_honestEval_le t π (keygen_cost S0)

theorem length_snd_honestEval_sign_le (t : SpongeKeys X Z) (π : Equiv.Perm (X × Z))
    (sk : SecretKey) (r : SigningRequest) :
    (honestEval t π (schemeWithHashFromSeed.sign sk r)).2.length ≤ 3 * 9048424824 :=
  signBlocks_eq ▸ length_snd_honestEval_le t π (sign_cost sk r)

theorem length_snd_honestEval_verify_le (t : SpongeKeys X Z) (π : Equiv.Perm (X × Z))
    (pk : PublicKey) (f : Forgery) :
    (honestEval t π (schemeWithHashFromSeed.verify pk f)).2.length ≤ 3 * 398 :=
  verifyBlocks_eq ▸ length_snd_honestEval_le t π (verify_cost' pk f)

end Quantum.Xmss

/-! ## The hardwired cells grow only through program calls -/

namespace Quantum

namespace QuerySupportedOn

variable {spec : QuantumOracleSpec.{u₁, v₁}} (R : QuantumRuntime spec) (g : R.D → ℕ)
  (κ : spec.Port → ℕ)

/-- **One call of a runtime whose port `i` raises the grade by at most `κ i`.** -/
theorem queryStep_of_charge_step
    (hR : ∀ i r t (σ : Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ),
      QuerySupportedOn (fun m : spec.In i × R.D ↦ g m.2) (Set.Iic t) σ →
        QuerySupportedOn (fun m : spec.Out i × R.D ↦ g m.2) (Set.Iic (t + κ i))
          ((R.step i).branch r σ))
    {A : QReg} {t : ℕ} (i : spec.Port) (E : QReg) (ℓ : A ≃ spec.In i × E) (r : spec.Result i)
    {ρ : Matrix (A × R.D) (A × R.D) ℂ}
    (h : QuerySupportedOn (fun m : A × R.D ↦ g m.2) (Set.Iic t) ρ) :
    QuerySupportedOn (fun m : (spec.Out i × E) × R.D ↦ g m.2) (Set.Iic (t + κ i))
      ((R.queryStep i E ℓ).branch r ρ) := by
  rw [QuantumRuntime.queryStep_branch_apply, DSubInstrument.branch_frame_apply]
  have h₁ := (h.branch_relabel (QuantumRuntime.queryEquivIn ℓ R.D)).imp
    (q' := fun m : (spec.In i × R.D) × E ↦ g m.1.2) (S' := Set.Iic t) fun m hm ↦ by
      obtain ⟨y, rfl⟩ := (QuantumRuntime.queryEquivIn ℓ R.D).surjective m
      rwa [Function.comp_apply, Equiv.symm_apply_apply] at hm
  have h₂ := QuerySupportedOn.amplify_fst (q := fun m : spec.In i × R.D ↦ g m.2)
    (q' := fun m : spec.Out i × R.D ↦ g m.2) (fun σ hσ ↦ hR i r t σ hσ) h₁
  refine (h₂.branch_relabel (QuantumRuntime.queryEquivOut _ R.D E)).imp fun m hm ↦ ?_
  obtain ⟨y, rfl⟩ := (QuantumRuntime.queryEquivOut _ R.D E).surjective m
  rwa [Function.comp_apply, Equiv.symm_apply_apply] at hm

variable {L : LocalSig.{uL, vL}} {W : QReg → Type w} {A : QReg}

/-- **The grade after a program with a charge budget.** If port `i` raises the grade of the
support by at most `κ i`, a program of charge at most `n` takes support on grades at most `t` to
support on grades at most `t + n` on every branch. -/
theorem run_of_charge_step
    (hR : ∀ i r t (σ : Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ),
      QuerySupportedOn (fun m : spec.In i × R.D ↦ g m.2) (Set.Iic t) σ →
        QuerySupportedOn (fun m : spec.Out i × R.D ↦ g m.2) (Set.Iic (t + κ i))
          ((R.step i).branch r σ))
    (I : L.Interp) {x : QuantumComp L spec W A} {n : ℕ}
    (hx : IFreeM.IsChargeBound x (Sponge.portCharge κ) n)
    {t : ℕ} {ρ : Matrix (A × R.D) (A × R.D) ℂ}
    (hρ : QuerySupportedOn (fun m : A × R.D ↦ g m.2) (Set.Iic t) ρ) (p : Σ u, W u) :
    QuerySupportedOn (fun m : p.1 × R.D ↦ g m.2) (Set.Iic (t + n))
      ((R.run I x).branch p ρ) := by
  classical
  induction x using QuantumComp.inductionOn generalizing n t with
  | pure _ y =>
    rw [QuantumRuntime.run_pure]
    by_cases hp : p = ⟨_, y⟩
    · subst hp
      rw [DSubInstrument.branch_ret_self]
      exact hρ.mono (Set.Iic_subset_Iic.mpr (Nat.le_add_right t _))
    · rw [DSubInstrument.branch_ret_of_ne _ hp]
      exact querySupportedOn_zero _ _
  | primBind _ o k ih =>
    rw [Sponge.isChargeBound_portCharge_primBind_iff] at hx
    rw [QuantumRuntime.run_primBind, DSubInstrument.branch_bind_apply]
    exact QuerySupportedOn.tsum fun c ↦ ih c (hx c) (QuerySupportedOn.amplify_snd (q := g) hρ _)
  | queryBind _ i E ℓ k ih =>
    obtain ⟨hq, hk⟩ := (Sponge.isChargeBound_portCharge_queryBind_iff κ i E ℓ k n).mp hx
    rw [QuantumRuntime.run_queryBind, DSubInstrument.branch_bind_apply]
    refine QuerySupportedOn.tsum fun r ↦ ?_
    have h := ih r (hk r) (queryStep_of_charge_step R g κ hR i E ℓ r hρ)
    rwa [Nat.add_assoc, Nat.add_sub_cancel' hq] at h

end QuerySupportedOn

namespace Sponge

variable {X Z : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
  {M : Type} [Fintype M] [DecidableEq M]

variable (X Z M) in
/-- The charge of the program ports: one per call, the other ports free. -/
def progCharge : (hwSpec X Z M).Port → ℕ
  | .inl _ => 0
  | .inr _ => 1

omit [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] [Fintype M] in
/-- A nonzero entry of a classical Kraus operator moves the classical part by `φ`. -/
theorem snd_eq_of_clsKraus_ne_zero {T B : Type} [DecidableEq B] {p : B → Prop} [DecidablePred p]
    {φ : B → B} {R : B → Matrix T T ℂ} {s s' : T × B} (h : clsKraus p φ R s' s ≠ 0) :
    s'.2 = φ s.2 := by
  rw [clsKraus_apply] at h
  split_ifs at h with hs
  · exact hs.2
  · exact absurd rfl h

omit [Fintype M] in
/-- A read port keeps the hardwired cells. -/
theorem hw_eq_of_hwReadKraus_ne_zero (c : HwRead X Z M) (r : c.Result) (u u' : Unit)
    (s s' : HwReg X Z M) (h : hwReadKraus c r (u', s') (u, s) ≠ 0) : s'.2.1 = s.2.1 := by
  cases c with
  | readH z upd =>
    simp only [hwReadKraus, readKrausH] at h
    rw [snd_eq_of_clsKraus_ne_zero (one_kronecker_ne_zero h).2]
  | readK x upd =>
    simp only [hwReadKraus, readKrausK] at h
    rw [snd_eq_of_clsKraus_ne_zero (one_kronecker_ne_zero h).2]
  | readK' x upd =>
    simp only [hwReadKraus, readKrausK'] at h
    rw [snd_eq_of_clsKraus_ne_zero (one_kronecker_ne_zero h).2]

omit [Fintype M] in
/-- A program port hardwires at most one more cell. -/
theorem dbGrade_hw_le_of_hwProgKraus_ne_zero (c : HwProg X Z) (r : c.Result) (u u' : Unit)
    (s s' : HwReg X Z M) (h : hwProgKraus c r (u', s') (u, s) ≠ 0) :
    dbGrade s'.2.1 ≤ dbGrade s.2.1 + 1 := by
  cases c with
  | programH z v =>
    simp only [hwProgKraus, programKrausH] at h
    rw [snd_eq_of_clsKraus_ne_zero (one_kronecker_ne_zero h).2]
    exact dbGrade_le_of_sizes (size_le_of_eq_off fun _ hx ↦ Function.update_of_ne hx _ _)
      (by simp) (by simp)
  | programK x v =>
    simp only [hwProgKraus, programKrausK] at h
    rw [snd_eq_of_clsKraus_ne_zero (one_kronecker_ne_zero h).2]
    exact dbGrade_le_of_sizes (by simp)
      (size_le_of_eq_off fun _ hx ↦ Function.update_of_ne hx _ _) (by simp)
  | programK' x v =>
    simp only [hwProgKraus, programKrausK'] at h
    rw [snd_eq_of_clsKraus_ne_zero (one_kronecker_ne_zero h).2]
    exact dbGrade_le_of_sizes (by simp) (by simp)
      (size_le_of_eq_off fun _ hx ↦ Function.update_of_ne hx _ _)

variable [AddCommGroup X] [AddCommGroup Z]

/-- A sponge port keeps the hardwired cells and the memory. -/
theorem snd_eq_of_spongeHardwired_U_ne_zero (W₀ : Hw X Z) (m₀ : M) (i : SpongePort)
    (a a' : spongeIn X Z i) (s s' : HwReg X Z M)
    (h : (spongeHardwired X Z W₀ m₀).U i (a', s') (a, s) ≠ 0) : s'.2 = s.2 := by
  rw [spongeHardwired_U] at h
  generalize (spongeCompressed X Z).U i = O at h
  obtain ⟨D', b'⟩ := s'
  obtain ⟨D, b⟩ := s
  simp only [liftBlocks, submatrix_apply, hwSplit, Equiv.prodAssoc_symm_apply,
    blockDiagonal_apply] at h
  split_ifs at h with hb
  · exact hb
  · exact absurd rfl h

/-- Every step of the hardwired runtime raises the grade of the hardwired cells by at most its
program charge. -/
theorem querySupportedOn_hw_step (W₀ : Hw X Z) (m₀ : M) (i : (hwSpec X Z M).Port)
    (r : (hwSpec X Z M).Result i) (t : ℕ)
    (σ : Matrix ((hwSpec X Z M).In i × (spongeHardwiredRuntime X Z W₀ m₀).D)
      ((hwSpec X Z M).In i × (spongeHardwiredRuntime X Z W₀ m₀).D) ℂ)
    (hσ : QuerySupportedOn (fun q : (hwSpec X Z M).In i × (spongeHardwiredRuntime X Z W₀ m₀).D ↦
      dbGrade q.2.2.1) (Set.Iic t) σ) :
    QuerySupportedOn (fun q : (hwSpec X Z M).Out i × (spongeHardwiredRuntime X Z W₀ m₀).D ↦
      dbGrade q.2.2.1) (Set.Iic (t + progCharge X Z M i))
        (((spongeHardwiredRuntime X Z W₀ m₀).step i).branch r σ) := by
  rcases i with (p | c) | c
  · have hb : ((spongeHardwiredRuntime X Z W₀ m₀).step (.inl (.inl p))).branch r σ =
        MatrixMap.conj ((spongeHardwired X Z W₀ m₀).U p) σ :=
      LinearMap.congr_fun (spongeHardwiredRuntime_step_sponge W₀ m₀ p r) σ
    refine (congrArg (QuerySupportedOn _ _) hb).mpr ?_
    exact QuerySupportedOn.conj hσ fun q' q hK hq ↦ by
      have he := snd_eq_of_spongeHardwired_U_ne_zero W₀ m₀ p q.1 q'.1 q.2 q'.2 hK
      rw [Set.mem_Iic] at hq ⊢
      rw [he]
      exact hq.trans (Nat.le_add_right _ _)
  · have hb : ((spongeHardwiredRuntime X Z W₀ m₀).step (.inl (.inr c))).branch r σ =
        MatrixMap.conj (hwReadKraus c r) σ :=
      LinearMap.congr_fun (spongeHardwiredRuntime_step_read W₀ m₀ c r) σ
    refine (congrArg (QuerySupportedOn _ _) hb).mpr ?_
    exact QuerySupportedOn.conj hσ fun q' q hK hq ↦ by
      have he := hw_eq_of_hwReadKraus_ne_zero c r q.1 q'.1 q.2 q'.2 hK
      rw [Set.mem_Iic] at hq ⊢
      rw [he]
      exact hq.trans (Nat.le_add_right _ _)
  · have hb : ((spongeHardwiredRuntime X Z W₀ m₀).step (.inr c)).branch r σ =
        MatrixMap.conj (hwProgKraus c r) σ :=
      LinearMap.congr_fun (spongeHardwiredRuntime_step_prog W₀ m₀ c r) σ
    refine (congrArg (QuerySupportedOn _ _) hb).mpr ?_
    exact QuerySupportedOn.conj hσ fun q' q hK hq ↦
      (dbGrade_hw_le_of_hwProgKraus_ne_zero c r q.1 q'.1 q.2 q'.2 hK).trans
        (Nat.add_le_add_right hq 1)

variable {L : LocalSig.{uL, vL}} {W : QReg → Type w} {A : QReg}

/-- **`dbGrade_le_of_programs`**: a program making at most `K` program calls on every path ends,
on every branch, supported on hardwired cells of grade at most `dbGrade W₀ + K`. -/
theorem dbGrade_le_of_programs (W₀ : Hw X Z) (m₀ : M) (I : L.Interp)
    {x : QuantumComp L (hwSpec X Z M) W A} {K : ℕ}
    (hx : IFreeM.IsChargeBound x (portCharge (progCharge X Z M)) K) (ρ : SubState A)
    (p : Σ u, W u) :
    QuerySupportedOn (fun s : p.1 × HwReg X Z M ↦ dbGrade s.2.2.1) (Set.Iic (dbGrade W₀ + K))
      (((spongeHardwiredRuntime X Z W₀ m₀).run I x).branch p
        (ρ.matrix ⊗ₖ (spongeHardwiredRuntime X Z W₀ m₀).init.matrix)) := by
  have hgrade : QuerySupportedOn (fun m : A × HwReg X Z M ↦ dbGrade m.2.2.1) (Set.Iic (dbGrade W₀))
      (ρ.matrix ⊗ₖ (SubState.basis (((Database.empty, Database.empty, Database.empty),
        W₀, m₀) : HwReg X Z M)).matrix) := by
    intro m m' hm
    rw [SubState.matrix_basis, kroneckerMap_apply] at hm
    have h := right_ne_zero_of_mul hm
    rw [Matrix.single_apply] at h
    split_ifs at h with he
    · constructor <;> simp [← he.1, ← he.2]
    · exact False.elim (h rfl)
  exact QuerySupportedOn.run_of_charge_step (spongeHardwiredRuntime X Z W₀ m₀)
    (fun s : HwReg X Z M ↦ dbGrade s.2.1) (progCharge X Z M)
    (fun i r t σ hσ ↦ querySupportedOn_hw_step W₀ m₀ i r t σ hσ) I hx hgrade p

end Sponge

end Quantum

/-! ## The public slots and their cells -/

namespace Quantum.Xmss

open HashSig LeanXmss

/-- The root position the public key discloses. -/
def rootPos : Pos := .tree topLayer layerHeight 0

/-- The positions of key `e` of layer `l` that its signatures disclose or make computable: every
position of its chains, and the path of `e` and its siblings at every level. -/
def keyPos (l : Layer) (e : KeyIndex) : Set Pos :=
  {p | (∃ i j, p = .chain l e i j) ∨ (∃ lv, p = .tree l lv (e.val / 2 ^ lv)) ∨
    ∃ lv, p = .tree l lv (Nat.xor (e.val / 2 ^ lv) 1)}

/-- The positions of the two keys of a request. -/
def reqPos (req : SigningRequest) : Set Pos :=
  keyPos bottomLayer (keyIndexOnLayer req.leafIndex bottomLayer) ∪
    keyPos topLayer (keyIndexOnLayer req.leafIndex topLayer)

/-- The positions reachable from the disclosures of `reqs`: the root and the requests' keys'
positions. -/
def reachPos (reqs : List SigningRequest) : Set Pos :=
  {rootPos} ∪ ⋃ req ∈ reqs, reqPos req

theorem layerDisclosed_subset_keyPos (l : Layer) (e : KeyIndex) (x : Encoding) :
    layerDisclosed l e x ⊆ keyPos l e := by
  rintro p (⟨i, rfl⟩ | ⟨lv, rfl⟩)
  · exact Or.inl ⟨i, _, rfl⟩
  · exact Or.inr (Or.inr ⟨lv.val, rfl⟩)

theorem disclosures_subset_reachPos (L : HonestTable) (reqs : List SigningRequest) :
    L.disclosures reqs ⊆ reachPos reqs := by
  refine Set.union_subset_union_right _ (Set.biUnion_mono subset_rfl fun req _ ↦ ?_)
  unfold HonestTable.disclosedBy
  split
  · exact Set.union_subset_union (layerDisclosed_subset_keyPos _ _ _)
      (layerDisclosed_subset_keyPos _ _ _)
  · exact Set.empty_subset _

/-- The payload position of a structural slot that names its key: a chain position for chain
steps and leaves, the right child for nodes. -/
def anchor : Slot → Option Pos
  | .chain l e step i => some (.chain l e i step.val)
  | .leaf l e => some (.chain l e ⟨0, by decide⟩ (chainLength - 1))
  | .node l level index => some (.tree l (level - 1) (2 * index + 1))
  | _ => none

theorem exists_anchor_of_payloadIn {K : Pos → Prop} {s : Slot} (h : PayloadIn K s) :
    ∃ a, anchor s = some a ∧ K a := by
  cases s with
  | chain => exact ⟨_, rfl, h⟩
  | leaf => exact ⟨_, rfl, h ⟨0, by decide⟩⟩
  | node => exact ⟨_, rfl, h.2.2⟩
  | msg => exact h.elim
  | prf => exact h.elim
  | rnd => exact h.elim
  | param => exact h.elim
  | seed => exact h.elim

theorem anchor_ne_rootPos {s : Slot} {a : Pos} (h : anchor s = some a) : a ≠ rootPos := by
  cases s <;> simp only [anchor, Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
    simp [rootPos]

theorem xor_one_div_two (n : ℕ) : Nat.xor n 1 / 2 = n / 2 := by
  rcases Nat.even_or_odd n with h | h
  · change (n ^^^ 1) / 2 = _
    rw [Nat.xor_one_of_even h]
    have := Nat.even_iff.1 h
    omega
  · change (n ^^^ 1) / 2 = _
    rw [Nat.xor_one_of_odd h]
    have := Nat.odd_iff.1 h
    omega

/-- The parent of the right child at level `level - 1` of a key's path or sibling is the key's
path node at `level`. -/
theorem index_eq_of_child {e level index : ℕ} (hl : level ≠ 0)
    (h : 2 * index + 1 = e / 2 ^ (level - 1) ∨ 2 * index + 1 = Nat.xor (e / 2 ^ (level - 1)) 1) :
    index = e / 2 ^ level := by
  have hp : e / 2 ^ level = e / 2 ^ (level - 1) / 2 := by
    rw [Nat.div_div_eq_div_mul, ← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hl)]
  rw [hp]
  rcases h with h | h
  · omega
  · rw [← xor_one_div_two, ← h]
    omega

theorem mem_keyPos_chain {l l' : Layer} {e e' : KeyIndex} {i : ChainIndex} {j : ℕ}
    (h : Pos.chain l e i j ∈ keyPos l' e') : l = l' ∧ e = e' := by
  simp only [keyPos, Set.mem_ofPred_eq, Pos.chain.injEq, reduceCtorEq, exists_false,
    or_false] at h
  obtain ⟨_, _, h⟩ := h
  exact ⟨h.1, h.2.1⟩

theorem mem_keyPos_tree {l l' : Layer} {e' : KeyIndex} {level index : ℕ}
    (h : Pos.tree l level index ∈ keyPos l' e') :
    l = l' ∧ (index = e'.val / 2 ^ level ∨ index = Nat.xor (e'.val / 2 ^ level) 1) := by
  simp only [keyPos, Set.mem_ofPred_eq, Pos.tree.injEq, reduceCtorEq, exists_false,
    false_or] at h
  rcases h with ⟨lv, hl, rfl, rfl⟩ | ⟨lv, hl, rfl, rfl⟩
  · exact ⟨hl, Or.inl rfl⟩
  · exact ⟨hl, Or.inr rfl⟩

/-- **A slot whose anchor is a key's position outputs a key's position.** -/
theorem output_mem_keyPos {s : Slot} {a p : Pos} {l : Layer} {e : KeyIndex}
    (ha : anchor s = some a) (hk : a ∈ keyPos l e) (hs : slotOutput s = some p) :
    p ∈ keyPos l e := by
  cases s with
  | chain l' e' step i =>
    obtain rfl := Option.some.inj ha
    obtain rfl := Option.some.inj hs
    obtain ⟨rfl, rfl⟩ := mem_keyPos_chain hk
    exact Or.inl ⟨i, _, rfl⟩
  | leaf l' e' =>
    obtain rfl := Option.some.inj ha
    obtain rfl := Option.some.inj hs
    obtain ⟨rfl, rfl⟩ := mem_keyPos_chain hk
    exact Or.inr (Or.inl ⟨0, by simp⟩)
  | node l' level index =>
    obtain rfl := Option.some.inj ha
    simp only [slotOutput] at hs
    split_ifs at hs with hl
    obtain rfl := Option.some.inj hs
    obtain ⟨rfl, hi⟩ := mem_keyPos_tree hk
    exact Or.inr (Or.inl ⟨level, by rw [index_eq_of_child hl hi]⟩)
  | msg => simp [anchor] at ha
  | prf => simp [anchor] at ha
  | rnd => simp [anchor] at ha
  | param => simp [anchor] at ha
  | seed => simp [anchor] at ha

/-- A reachable position other than the root is a position of a request's key. -/
theorem exists_req_of_mem_reachPos {reqs : List SigningRequest} {a : Pos}
    (h : a ∈ reachPos reqs) (ha : a ≠ rootPos) : ∃ req ∈ reqs, a ∈ reqPos req := by
  rcases h with h | h
  · exact absurd h ha
  · simpa only [Set.mem_iUnion, exists_prop] using h

/-- **The reachable positions are closed**: they contain the output of every slot whose payload
they contain. -/
theorem reachPos_closed (reqs : List SigningRequest) (s : Slot) (p : Pos)
    (hs : slotOutput s = some p) (hk : PayloadIn (· ∈ reachPos reqs) s) : p ∈ reachPos reqs := by
  obtain ⟨a, ha, hm⟩ := exists_anchor_of_payloadIn hk
  obtain ⟨req, hr, hreq⟩ := exists_req_of_mem_reachPos hm (anchor_ne_rootPos ha)
  refine Or.inr (Set.mem_biUnion hr ?_)
  rcases hreq with h | h
  · exact Or.inl (output_mem_keyPos ha h hs)
  · exact Or.inr (output_mem_keyPos ha h hs)

theorem known_subset_reachPos (L : HonestTable) (reqs : List SigningRequest) {p : Pos}
    (h : Known (L.disclosures reqs) p) : p ∈ reachPos reqs :=
  known_subset (disclosures_subset_reachPos L reqs) (reachPos_closed reqs) h

/-- The structural slots of key `e` of layer `l` that can become public: all chain steps, the leaf
and the `16` nodes on the key's path. -/
def keySlots (l : Layer) (e : KeyIndex) : Finset Slot :=
  (Finset.univ : Finset (ChainStep × ChainIndex)).image (fun q ↦ Slot.chain l e q.1 q.2) ∪
    ({Slot.leaf l e} ∪
      (Finset.range layerHeight).image fun k ↦ Slot.node l (k + 1) (e.val / 2 ^ (k + 1)))

/-- The slots of the two keys of a request. -/
def reqSlots (req : SigningRequest) : Finset Slot :=
  keySlots bottomLayer (keyIndexOnLayer req.leafIndex bottomLayer) ∪
    keySlots topLayer (keyIndexOnLayer req.leafIndex topLayer)

theorem mem_keySlots {s : Slot} {a : Pos} {l : Layer} {e : KeyIndex} (hs : InTable s)
    (ha : anchor s = some a) (hk : a ∈ keyPos l e) : s ∈ keySlots l e := by
  simp only [keySlots, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and,
    Finset.mem_singleton, Finset.mem_range]
  cases s with
  | chain l' e' step i =>
    obtain rfl := Option.some.inj ha
    obtain ⟨rfl, rfl⟩ := mem_keyPos_chain hk
    exact Or.inl ⟨(step, i), rfl⟩
  | leaf l' e' =>
    obtain rfl := Option.some.inj ha
    obtain ⟨rfl, rfl⟩ := mem_keyPos_chain hk
    exact Or.inr (Or.inl rfl)
  | node l' level index =>
    obtain rfl := Option.some.inj ha
    obtain ⟨rfl, hi⟩ := mem_keyPos_tree hk
    have h1 := hs.1
    have h2 := hs.2.1
    have hl : level ≠ 0 := by omega
    refine Or.inr (Or.inr ⟨level - 1, by simp only [layerHeight] at h2 ⊢; omega, ?_⟩)
    rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hl), index_eq_of_child hl hi]
  | msg => exact hs.elim
  | prf => exact hs.elim
  | rnd => exact hs.elim
  | param => exact hs.elim
  | seed => exact hs.elim

/-- **The public slots of the disclosures lie in the requests' keys' slots.** -/
theorem public_disclosures_subset (L : HonestTable) (reqs : List SigningRequest) :
    Public (L.disclosures reqs) ⊆ ↑(reqs.toFinset.biUnion reqSlots) := by
  rintro s ⟨hs, hp⟩
  obtain ⟨a, ha, hm⟩ := exists_anchor_of_payloadIn
    (hp.mono fun _ hk ↦ known_subset_reachPos L reqs hk)
  obtain ⟨req, hr, hreq⟩ := exists_req_of_mem_reachPos hm (anchor_ne_rootPos ha)
  rw [Finset.coe_biUnion]
  refine Set.mem_biUnion (List.mem_toFinset.2 hr) ?_
  rw [Finset.mem_coe, reqSlots, Finset.mem_union]
  rcases hreq with h | h
  · exact Or.inl (mem_keySlots hs ha h)
  · exact Or.inr (mem_keySlots hs ha h)

/-- **The cells runtime 2 programs for a public slot**: the `k`, `k'` and `h` cells of every
block of its honest input: one block for a chain step or a node, eight for a leaf. -/
def slotCells : Slot → ℕ
  | .chain .. => 3
  | .leaf .. => 24
  | .node .. => 3
  | _ => 0

/-- The cells of a slot are three per block of its honest input. -/
theorem HonestTable.slotCells_eq (L : HonestTable) {s : Slot} {input : HashInput}
    (h : L.honestInput s = some input) : 3 * (blocks input).length = slotCells s := by
  simp only [HonestTable.honestInput] at h
  split_ifs at h with hs
  obtain rfl := Option.some.inj h
  rw [length_blocks, Common.XmssCost.thInput_length]
  cases s with
  | chain => simp [HonestTable.payload, Verification.chainPayload, littleEndianBytes, slotCells]
  | leaf =>
    simp only [HonestTable.payload, slotCells]
    rw [Common.XmssCost.digestsPayload_length]
    simp [chainCount]
  | node => simp [HonestTable.payload, OverPermutation.nodePayload, littleEndianBytes, slotCells]
  | msg => exact hs.elim
  | prf => exact hs.elim
  | rnd => exact hs.elim
  | param => exact hs.elim
  | seed => exact hs.elim

theorem sum_union_le_nat {β : Type*} [DecidableEq β] (A B : Finset β) (f : β → ℕ) :
    ∑ s ∈ A ∪ B, f s ≤ ∑ s ∈ A, f s + ∑ s ∈ B, f s := by
  rw [← Finset.sum_union_inter]
  exact Nat.le_add_right _ _

theorem sum_biUnion_le_nat {α β : Type*} [DecidableEq α] [DecidableEq β] (T : Finset α)
    (F : α → Finset β) (f : β → ℕ) : ∑ s ∈ T.biUnion F, f s ≤ ∑ t ∈ T, ∑ s ∈ F t, f s := by
  refine Finset.induction_on T (by simp) fun a T ha ih ↦ ?_
  rw [Finset.biUnion_insert, Finset.sum_insert ha]
  exact (sum_union_le_nat _ _ f).trans (Nat.add_le_add_left ih _)

theorem sum_slotCells_keySlots_le (l : Layer) (e : KeyIndex) :
    ∑ s ∈ keySlots l e, slotCells s ≤ 594 := by
  unfold keySlots
  refine (sum_union_le_nat _ _ _).trans ?_
  refine (Nat.add_le_add (Finset.sum_image_le_of_nonneg fun _ _ ↦ Nat.zero_le _)
    ((sum_union_le_nat _ _ _).trans (Nat.add_le_add_left
      (Finset.sum_image_le_of_nonneg fun _ _ ↦ Nat.zero_le _) _))).trans ?_
  simp [slotCells, Finset.card_univ, chainCount, chainLength, winternitzBits, layerHeight]

/-- **Program calls of one layer's signature**: programming the cells of any slots of the key
(repeats included) takes at most `594` calls, so a request takes at most `reqCells`. -/
theorem sum_slotCells_le_of_subset_keySlots {l : Layer} {e : KeyIndex} {F : Finset Slot}
    (hF : F ⊆ keySlots l e) : ∑ s ∈ F, slotCells s ≤ 594 :=
  (Finset.sum_le_sum_of_subset hF).trans (sum_slotCells_keySlots_le l e)

/-- The cells of one request: `1188`, `594` per layer. -/
def reqCells : ℕ := 1188

/-- **The cells programmed for the public slots of `reqs`**: at most `1188` per request. -/
theorem sum_slotCells_le_of_subset_public (L : HonestTable) (reqs : List SigningRequest)
    (F : Finset Slot) (hF : ↑F ⊆ Public (L.disclosures reqs)) :
    ∑ s ∈ F, slotCells s ≤ reqCells * reqs.length := by
  have hsub : F ⊆ reqs.toFinset.biUnion reqSlots := by
    intro s hs
    exact Finset.mem_coe.1 (public_disclosures_subset L reqs (hF hs))
  refine (Finset.sum_le_sum_of_subset hsub).trans ((sum_biUnion_le_nat _ _ _).trans ?_)
  refine (Finset.sum_le_sum fun req _ ↦ ((sum_union_le_nat _ _ _).trans
    (Nat.add_le_add (sum_slotCells_keySlots_le _ _) (sum_slotCells_keySlots_le _ _)))).trans ?_
  rw [Finset.sum_const, smul_eq_mul, reqCells, mul_comm]
  exact Nat.mul_le_mul_left _ (List.toFinset_card_le reqs)

/-- **The cap `N` of `Bad L N`**: `1188` cells for each of at most `2^32` requests. -/
def progCap : ℕ := reqCells * lifetime

theorem progCap_eq : progCap = 5102421147648 := by
  simp [progCap, reqCells, lifetime, layerCount, layerHeight]

/-- **The cap on reachable states.** From `W₀ = ∅`, a program of runtime 2 making at most
`K ≤ progCap` program calls ends, on every branch, supported on `dbGrade W ≤ progCap`. -/
theorem dbGrade_le_progCap {X₁ Z₁ : Type} [Fintype X₁] [DecidableEq X₁] [Fintype Z₁]
    [DecidableEq Z₁] [AddCommGroup X₁] [AddCommGroup Z₁] {M : Type} [Fintype M] [DecidableEq M]
    (m₀ : M) {L : LocalSig.{uL, vL}} {W : QReg → Type w} {A : QReg} (I : L.Interp)
    {x : QuantumComp L (Sponge.hwSpec X₁ Z₁ M) W A} {K : ℕ}
    (hx : IFreeM.IsChargeBound x (Sponge.portCharge (Sponge.progCharge X₁ Z₁ M)) K)
    (hK : K ≤ progCap) (ρ : SubState A) (p : Σ u, W u) :
    QuerySupportedOn (fun s : p.1 × Sponge.HwReg X₁ Z₁ M ↦ Sponge.dbGrade s.2.2.1)
      (Set.Iic progCap)
      (((Sponge.spongeHardwiredRuntime X₁ Z₁ (Database.empty, Database.empty, Database.empty)
        m₀).run I x).branch p (ρ.matrix ⊗ₖ (Sponge.spongeHardwiredRuntime X₁ Z₁
          (Database.empty, Database.empty, Database.empty) m₀).init.matrix)) :=
  (Sponge.dbGrade_le_of_programs _ m₀ I hx ρ p).mono (Set.Iic_subset_Iic.2 (by
    simp [Sponge.dbGrade, Database.size_empty, hK]))

section extend

variable {X₁ Z₁ : Type} [Fintype X₁] [DecidableEq X₁] [Fintype Z₁] [DecidableEq Z₁]
  {M : Type} [Fintype M] [DecidableEq M] {P P' : Type} [Fintype P] [DecidableEq P] [Fintype P']
  [DecidableEq P']

omit [DecidableEq M] [DecidableEq P] [Fintype P'] [DecidableEq P'] in
/-- An operator whose nonzero entries keep the hardwired cells keeps the grade of the hardwired
cells (for example a classical port that only updates the memory). -/
theorem querySupportedOn_conj_of_hw_eq {K : Matrix (P' × Sponge.HwReg X₁ Z₁ M)
      (P × Sponge.HwReg X₁ Z₁ M) ℂ}
    (hK : ∀ a a' s s', K (a', s') (a, s) ≠ 0 → s'.2.1 = s.2.1) {n : ℕ}
    {σ : Matrix (P × Sponge.HwReg X₁ Z₁ M) (P × Sponge.HwReg X₁ Z₁ M) ℂ}
    (hσ : QuerySupportedOn (fun q : P × Sponge.HwReg X₁ Z₁ M ↦ Sponge.dbGrade q.2.2.1)
      (Set.Iic n) σ) :
    QuerySupportedOn (fun q : P' × Sponge.HwReg X₁ Z₁ M ↦ Sponge.dbGrade q.2.2.1) (Set.Iic n)
      (MatrixMap.conj K σ) :=
  QuerySupportedOn.conj hσ fun q' q hk hq ↦ by
    rw [Set.mem_Iic] at hq ⊢
    rw [hK q.1 q'.1 q.2 q'.2 hk]
    exact hq

variable [AddCommGroup X₁] [AddCommGroup Z₁] [Nonempty X₁] [Nonempty Z₁]

variable (X₁ Z₁ M) in
/-- The program charge on runtime 2 extended by further ports `t`: one per program call, the
other ports (sponge, read, and the extension's) free. -/
def extProgCharge (t : QuantumOracleSpec.{0, 0}) : ((Sponge.hwSpec X₁ Z₁ M).sum t).Port → ℕ
  | .inl i => Sponge.progCharge X₁ Z₁ M i
  | .inr _ => 0

variable {L : LocalSig.{uL, vL}} {W : QReg → Type w} {A : QReg}

/-- **The cap for runtime 2 extended by ports keeping the hardwired cells** (such as record
ports): a program making at most `K ≤ progCap` program calls on every path ends, on every branch,
supported on `dbGrade W ≤ progCap`. -/
theorem dbGrade_le_progCap_extend {t : QuantumOracleSpec.{0, 0}} (m₀ : M)
    (step' : ∀ j : t.Port, SubInstrument (t.In j × (Hybrid.runtime2 X₁ Z₁ m₀).D)
      (t.Out j × (Hybrid.runtime2 X₁ Z₁ m₀).D) (t.Result j))
    (hstep' : ∀ j r n (σ : Matrix (t.In j × (Hybrid.runtime2 X₁ Z₁ m₀).D)
        (t.In j × (Hybrid.runtime2 X₁ Z₁ m₀).D) ℂ),
      QuerySupportedOn (fun q : t.In j × (Hybrid.runtime2 X₁ Z₁ m₀).D ↦ Sponge.dbGrade q.2.2.1)
        (Set.Iic n) σ →
      QuerySupportedOn (fun q : t.Out j × (Hybrid.runtime2 X₁ Z₁ m₀).D ↦ Sponge.dbGrade q.2.2.1)
        (Set.Iic n) ((step' j).branch r σ))
    (I : L.Interp) {x : QuantumComp L ((Sponge.hwSpec X₁ Z₁ M).sum t) W A} {K : ℕ}
    (hx : IFreeM.IsChargeBound x (Sponge.portCharge (extProgCharge X₁ Z₁ M t)) K)
    (hK : K ≤ progCap) (ρ : SubState A) (p : Σ u, W u) :
    QuerySupportedOn (fun s : p.1 × Sponge.HwReg X₁ Z₁ M ↦ Sponge.dbGrade s.2.2.1)
      (Set.Iic progCap)
      ((((Hybrid.runtime2 X₁ Z₁ m₀).extend step').run I x).branch p
        (ρ.matrix ⊗ₖ (Hybrid.runtime2 X₁ Z₁ m₀).init.matrix)) := by
  have hgrade : QuerySupportedOn (fun m : A × Sponge.HwReg X₁ Z₁ M ↦ Sponge.dbGrade m.2.2.1)
      (Set.Iic 0) (ρ.matrix ⊗ₖ (Hybrid.runtime2 X₁ Z₁ m₀).init.matrix) := by
    intro m m' hm
    change (ρ.matrix ⊗ₖ (SubState.basis (((Database.empty, Database.empty, Database.empty),
      Sponge.hwEmpty X₁ Z₁, m₀) : Sponge.HwReg X₁ Z₁ M)).matrix) m m' ≠ 0 at hm
    rw [SubState.matrix_basis, kroneckerMap_apply] at hm
    have h := right_ne_zero_of_mul hm
    rw [Matrix.single_apply] at h
    split_ifs at h with he
    · constructor <;> simp [← he.1, ← he.2, Sponge.hwEmpty, Sponge.dbGrade, Database.size_empty]
    · exact False.elim (h rfl)
  refine (QuerySupportedOn.run_of_charge_step ((Hybrid.runtime2 X₁ Z₁ m₀).extend step')
    (fun s : Sponge.HwReg X₁ Z₁ M ↦ Sponge.dbGrade s.2.1) (extProgCharge X₁ Z₁ M t)
    (fun i r n σ hσ ↦ ?_) I hx hgrade p).mono (Set.Iic_subset_Iic.2 (by omega))
  rcases i with i | j
  · exact Sponge.querySupportedOn_hw_step (Sponge.hwEmpty X₁ Z₁) m₀ i r n σ hσ
  · exact hstep' j r n σ hσ

end extend

end Quantum.Xmss

end
