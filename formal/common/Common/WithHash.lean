module

public import Statement.LeanXmss
public import Common.Defs

/-!
# The SUF-CMA game and leanXMSS with a hash oracle

The statement's SUF-CMA game and leanXMSS are over the permutation `π` alone
(`Statement/RandomPermutation.lean`, `Statement/LeanXmss.lean`): every hash is Keccak-256 over `π`.
The proofs reason with the hash a query of its own (`LeanXmss.HashSpec`, the game's
`SufCma.SchemeHashSpec`), which a random oracle answers in the random-oracle steps and Keccak-256
over `π` in the random-permutation model (`SufCma.schemeHashOverPermutation`). These are those
forms, each the statement's definition with the hash a query: the game (`SufCma.SchemeWithHash`,
`forgeryGameWithHash`) and leanXMSS's algorithms
(`LeanXmss.Verification`, `LeanXmss.KeyGenerationAndSigning`, the scheme
`LeanXmss.RandomPermutationModel.schemeWithHash`).
`Common.WithHashBridge` proves the statement's the hash-query forms with the hash Keccak-256 over
`π`.
-/

@[expose] public section

open OracleComp OracleSpec
open scoped ENNReal

namespace Common

open LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash

/-- **Keccak-256 in the model**: the sponge over `π` (`keccak256With`), one call of `π` per block
of the padded message (`⌊n / 136⌋ + 1` for `n` bytes), its digest's 32 bytes. -/
def keccak256OverPermutation (m : List UInt8) : OracleComp RandomPermutationOracles DigestBytes :=
  Digest.toBytes <$> keccak256With queryPermutation m

namespace SufCma


/-- The hash of a signature scheme, `H : List UInt8 → BitVec 256`: in the model Keccak-256, its
digest read as a little-endian number (`digestBytesEquivBitVec`). -/
abbrev SchemeHashSpec := List UInt8 →ₒ BitVec 256

/-- **A signature scheme** with the hash `H` (`SchemeHashSpec`): a seed sampler, key generation from
a seed, the signer answering a request `Req` with `Resp`, the verifier of a claimed forgery `F`, and
the winning condition on the signing transcript and the forgery. -/
structure SchemeWithHash (Seed PK SK Req Resp F : Type) where
  /-- Sample the secret seed. -/
  sample : ProbComp Seed
  /-- Generate the keys from the seed. -/
  keygen : Seed → OracleComp SchemeHashSpec (PK × SK)
  /-- Answer a signing request. -/
  sign : SK → Req → OracleComp SchemeHashSpec Resp
  /-- Verify a claimed forgery. -/
  verify : PK → F → OracleComp SchemeHashSpec Bool
  /-- The transcript and the forgery make a win (when the forgery verifies). -/
  win : QueryLog (Req →ₒ Resp) → F → Bool

variable {Seed PK SK Req Resp F : Type}

/-- **A kept-key form of a scheme**: key generation derives `D` from the seed (`derive`, hash
queries only) and continues (`rest`), but the secret key keeps `keep seed d` (the seed and part of what it derived, as the
leanXMSS crate's key keeps the seed and the public parameter), from which the signer derives the
rest again (`rederive`) and signs as `signWith` of the derived value. (`Common.SeedKey` shows the
two have the same success when `rederive` reruns queries of `derive`.) -/
structure KeptKey (S : SchemeWithHash Seed PK SK Req Resp F) (D SK' : Type) where
  /-- What the signer needs, derived from the seed. -/
  derive : Seed → OracleComp SchemeHashSpec D
  /-- The rest of key generation. -/
  rest : Seed → D → OracleComp SchemeHashSpec (PK × SK)
  /-- The signer, from the derived value. -/
  signWith : D → Req → OracleComp SchemeHashSpec Resp
  /-- The secret key kept, from the seed and the derived value. -/
  keep : Seed → D → SK'
  /-- What the signer derives again from the kept key. -/
  rederive : SK' → OracleComp SchemeHashSpec D
  keygen_eq : ∀ seed, S.keygen seed = derive seed >>= rest seed
  sign_eq : ∀ seed d, ∀ keys ∈ support (rest seed d), S.sign keys.2 = signWith d

/-- The scheme with the kept key: key generation as `S`'s, keeping `keep seed d` as the key, the
signer deriving its value from the kept key first. -/
def KeptKey.scheme {S : SchemeWithHash Seed PK SK Req Resp F} {D SK' : Type}
    (K : KeptKey S D SK') : SchemeWithHash Seed PK SK' Req Resp F where
  sample := S.sample
  keygen seed := K.derive seed >>= fun d ↦ (fun keys ↦ (keys.1, K.keep seed d)) <$> K.rest seed d
  sign key request := K.rederive key >>= fun d ↦ K.signWith d request
  verify := S.verify
  win := S.win

/-- The hash in the random-permutation model: Keccak-256 over `π` (`keccak256OverPermutation`), its
digest read as a bit vector (`digestBytesEquivBitVec`). -/
def schemeHashOverPermutation : QueryImpl SchemeHashSpec (OracleComp RandomPermutationOracles) :=
  fun m ↦ digestBytesEquivBitVec <$> keccak256OverPermutation m

/-- The signing oracle in the random-permutation model. -/
def loggedSigningOracleWithHash (S : SchemeWithHash Seed PK SK Req Resp F) (sk : SK) :
    QueryImpl (Req →ₒ Resp)
      (WriterT (QueryLog (Req →ₒ Resp)) (OracleComp RandomPermutationOracles)) :=
  QueryImpl.withLogging fun r ↦ simulateQ schemeHashOverPermutation (S.sign sk r)

/-- **The RPM game**: the game with `H` Keccak-256 over the permutation, and an adversary that
also queries `π` and `π⁻¹`. -/
noncomputable def forgeryGameWithHash (S : SchemeWithHash Seed PK SK Req Resp F)
    (main : PK → OracleComp (RandomPermutationOracles + (Req →ₒ Resp)) F) :
      OracleComp RandomPermutationOracles Bool := do
  let seed ← liftM S.sample
  let (pk, sk) ← simulateQ schemeHashOverPermutation (S.keygen seed)
  let ((forgery, log) : F × QueryLog (Req →ₒ Resp)) ←
    (simulateQ
      (QueryImpl.ofLift RandomPermutationOracles
        (WriterT (QueryLog (Req →ₒ Resp)) (OracleComp RandomPermutationOracles)) +
      loggedSigningOracleWithHash S sk) (main pk)).run
  let verified ← simulateQ schemeHashOverPermutation (S.verify pk forgery)
  return S.win log forgery && verified


end SufCma

end Common

namespace LeanXmss

open HashSig

/-- What leanXMSS's signer derives from the key's seed `S_0` and signs with: the scheme seed
`S = H(leanXMSS ‖ S_0)` and the public parameter of `S`; the secret key of the proofs' game. -/
structure SchemeSeedKey where
  /-- `S`, the scheme seed. -/
  schemeSeed : MasterSeed
  /-- The public parameter `P`. -/
  parameter : PublicParameter

/-- A hash query takes an arbitrary byte string and returns 32 bytes (the SUF-CMA game's
`Common.SufCma.SchemeHashSpec`). -/
abbrev HashSpec := HashInput →ₒ HashOutput

namespace Verification

open HashSig.OverPermutation

variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]


/-- One query to the hash `H` (`HashSpec`), which the model answers. -/
def oracleHashWithHash (input : HashInput) : m HashOutput :=
  HasQuery.query (spec := HashSpec) (m := m) input

/-- `Th(P, A, M) = Truncate_n(H(P || A || M))` (`th`, `lean_xmss/hash.rs`). -/
def thWithHash (parameter : PublicParameter) (fields : TweakFields) (payload : HashInput) :
    m Digest := do
  return truncateHash (← oracleHashWithHash (thInput parameter fields payload))

/-- `H(P || A || M)`, untruncated: two secrets for one hash (`th_pair`,
`lean_xmss/hash.rs`). -/
def thPairWithHash (parameter : PublicParameter) (fields : TweakFields) (payload : HashInput) :
    m HashOutput :=
  oracleHashWithHash (thInput parameter fields payload)

/-- `H(tag || S_0)`, all 32 bytes: at `seedTag` the scheme seed `S` (`scheme_seed`). -/
def taggedSeedWithHash (tag : HashInput) (seed : MasterSeed) : m MasterSeed :=
  oracleHashWithHash (tag ++ littleEndianBytes 32 seed)

/-- The tweakable hash at a hash domain's address. -/
abbrev tweakableHashWithHash (parameter : PublicParameter) (domain : HashDomain)
    (payload : HashInput) :
    m Digest :=
  thWithHash parameter (hashDomainFields domain) payload

/-- Chain `i` of a one-time key; the step leaving position `s` carries step `s`. -/
def chainWalkWithHash (parameter : PublicParameter) (lay : Layer) (key : KeyIndex)
    (chainIdx : ChainIndex) : Nat → Nat → Digest → m Digest :=
  walkChain fun step value ↦
    tweakableHashWithHash parameter (.chain lay key step) (chainPayload chainIdx value)

/-- The verifier's half of a chain: walk the remaining `3 - x_i` steps. -/
def recoverChainWithHash (parameter : PublicParameter) (lay : Layer) (key : KeyIndex)
    (chainIdx : ChainIndex) (digit : WinternitzDigit) (value : Digest) : m Digest :=
  chainWalkWithHash parameter lay key chainIdx digit.val (chainLength - 1 - digit.val) value

/-- The one-time leaf: the hash of the `v` chain ends (`wots_leaf_hash`). -/
def leafHashWithHash (parameter : PublicParameter) (lay : Layer) (key : KeyIndex)
    (endpoints : ChainIndex → Digest) : m Digest :=
  tweakableHashWithHash parameter (.leaf lay key) (digestsPayload endpoints)

/-- `D = Th(P, A_msg(l, e), M || rho)` (`message_digest`). -/
def messageDigestWithHash (parameter : PublicParameter) (lay : Layer) (key : KeyIndex)
    (message : HashInput) (randomness : Randomizer) : m Digest :=
  tweakableHashWithHash parameter (.message lay key) (message ++ littleEndianBytes 16 randomness)

/-- `Ots.leaf` (`wots_leaf`): the leaf a claimed one-time signature recovers, or nothing if its
digest is not a codeword. -/
def otsLeafWithHash (parameter : PublicParameter) (lay : Layer) (key : KeyIndex)
    (message : HashInput)
    (randomness : Randomizer) (values : ChainIndex → Digest) : m (Option Digest) := do
  let digest ← messageDigestWithHash parameter lay key message randomness
  let some encoding := Codeword.decode digest | return none
  let endpoints ← sequenceFin fun chainIdx =>
    recoverChainWithHash parameter lay key chainIdx (encoding chainIdx) (values chainIdx)
  let value ← leafHashWithHash parameter lay key endpoints
  return some value

/-- `Tree.fold`: fold a key's leaf and path into its tree's root. -/
def treeFoldWithHash (parameter : PublicParameter) (lay : Layer) (key : KeyIndex)
    (path : Fin layerHeight → Digest) : Nat → Digest → m Digest :=
  foldPath (fun level nodeIdx ↦ tweakableHashWithHash parameter (.node lay (level + 1) nodeIdx))
    key.val
    fun level ↦ if h : level < layerHeight then path ⟨level, h⟩ else 0

/-- The root a layer's signature by key `e` reaches from `message`, or nothing (`layer_root`). -/
def layerRootWithHash (parameter : PublicParameter) (lay : Layer) (key : KeyIndex)
    (message : HashInput)
    (part : LayerSignature) : m (Option Digest) := do
  let some leaf ← otsLeafWithHash parameter lay key message part.randomizer part.chainValues |
    return none
  let root ← treeFoldWithHash parameter lay key part.authenticationPath layerHeight leaf
  return some root

/-- `Ver(pk, m, sigma)`: recover the bottom root from the message, then the top root from the bottom
root, and compare it with the public key. -/
def verifyWithHash (publicKey : PublicKey) (message : Message) (signature : Signature) : m Bool :=
  do
  let index := signature.leafIndex
  let some bottomRoot ← layerRootWithHash publicKey.parameter bottomLayer (keyIndexOnLayer index
      bottomLayer)
      (littleEndianBytes 32 message) (signature.layers bottomLayer) | return false
  let some root ← layerRootWithHash publicKey.parameter topLayer (keyIndexOnLayer index topLayer)
      (littleEndianBytes 16 bottomRoot) (signature.layers topLayer) | return false
  return decide (root = publicKey.root)

end Verification

namespace KeyGenerationAndSigning

open Verification HashSig.OverPermutation

variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]


/-- `wots_secrets`: the starts of the `v` chains of a one-time key, from 29 seed derivations.
Chains `2t` and `2t + 1` start at the two halves of derivation `t`. -/
def otsSecretsWithHash (parameter : PublicParameter) (lay : Layer) (key : KeyIndex)
    (seed : MasterSeed) :
    m (ChainIndex → Digest) := do
  let outputs ← sequenceFin fun pair : ChainPairIndex =>
    thPairWithHash parameter (keygenDomainFields (.oneTimeChainPair lay key pair))
        (littleEndianBytes 32 seed)
  return fun chainIdx => hashHalfForChain chainIdx.val (outputs (chainPair chainIdx))

/-- The chain ends of a one-time key. -/
def oneTimePublicKeyWithHash (parameter : PublicParameter) (lay : Layer) (key : KeyIndex)
    (seed : MasterSeed) : m (ChainIndex → Digest) := do
  let secrets ← otsSecretsWithHash parameter lay key seed
  sequenceFin fun chainIdx =>
    chainWalkWithHash parameter lay key chainIdx 0 (chainLength - 1) (secrets chainIdx)

/-- The randomizer trials `R0 + c, R0 + c + 1, ...`, stopping at the first codeword. -/
def otsSignFromWithHash (parameter : PublicParameter) (lay : Layer) (key : KeyIndex)
    (seed : MasterSeed)
    (message : HashInput) (base : Randomizer) :
    Nat → Nat → m (Option (Randomizer × (ChainIndex → Digest)))
  | 0, _ => pure none
  | attempts + 1, trial => do
      let randomness := base + BitVec.ofNat digestBits trial
      let digest ← messageDigestWithHash parameter lay key message randomness
      match Codeword.decode digest with
      | some encoding => do
          let secrets ← otsSecretsWithHash parameter lay key seed
          let values ← sequenceFin fun chainIdx =>
            chainWalkWithHash parameter lay key chainIdx 0 (encoding chainIdx).val
              (secrets chainIdx)
          return some (randomness, values)
      | none => otsSignFromWithHash parameter lay key seed message base attempts (trial + 1)

/-- `wots_sign`: derive `R0`, take the least admissible trial, then open the chains. -/
def otsSignWithHash (parameter : PublicParameter) (lay : Layer) (key : KeyIndex) (seed : MasterSeed)
    (message : HashInput) : m (Option (Randomizer × (ChainIndex → Digest))) := do
  -- `R0`, the randomizer base (`TWEAK_RANDOMIZER = 7`)
  let base ← thWithHash parameter (tweakFields 7 0 (layerHi lay 0) key) (littleEndianBytes 32 seed
      ++ message)
  otsSignFromWithHash parameter lay key seed message base randomizerAttemptLimit 0

/-- Node `nodeIdx` at tree level `level` of layer `l`, from the one-time keys below it. On the
bottom layer node indices are global: node `j` at level `level` is in bottom tree
`j / 2^(16 - level)`. -/
def treeNodeWithHash (parameter : PublicParameter) (lay : Layer) (seed : MasterSeed) :
    Nat → Nat → m Digest :=
  buildTree (fun nodeIdx ↦ do
      let key : KeyIndex := ⟨nodeIdx % lifetime, Nat.mod_lt _ (by decide)⟩
      leafHashWithHash parameter lay key (← oneTimePublicKeyWithHash parameter lay key seed))
    fun level nodeIdx ↦ tweakableHashWithHash parameter (.node lay (level + 1) nodeIdx)

/-- The authentication path of key `e`: at level `level`, the sibling of `e / 2^level`. -/
def treePathWithHash (parameter : PublicParameter) (lay : Layer) (seed : MasterSeed)
    (key : KeyIndex) :
    m (Fin layerHeight → Digest) :=
  sequenceFin fun level =>
    treeNodeWithHash parameter lay seed level.val (Nat.xor (key.val / 2 ^ level.val) 1)

/-- `Gen` (`key_gen`): hash the key's seed `S_0` into `S`, derive the public parameter and build the
top tree. -/
def keygenFromSeedWithHash (keySeed : MasterSeed) :
    OracleComp HashSpec (PublicKey × SchemeSeedKey) :=
  do
  let seed ← taggedSeedWithHash seedTag keySeed
  let parameter ← thWithHash 0 (keygenDomainFields .parameter) (littleEndianBytes 32 seed)
  let root ← treeNodeWithHash parameter topLayer seed layerHeight 0
  return (⟨root, parameter⟩, ⟨seed, parameter⟩)

/-- One layer's signature by key `e` of `message`: the one-time signature and the path. -/
def signLayerWithHash (secretKey : SchemeSeedKey) (lay : Layer) (key : KeyIndex) (message : HashInput) :
    m (Option LayerSignature) := do
  let some (randomness, values) ← otsSignWithHash secretKey.parameter lay key secretKey.schemeSeed
      message
    | return none
  let path ← treePathWithHash secretKey.parameter lay secretKey.schemeSeed key
  return some ⟨randomness, values, path⟩

/-- `Sign` at leaf index `idx`: the bottom key `idx` signs `m`, and the top key `idx / 2^16` signs
the root of bottom tree `idx / 2^16`. -/
def signWithHash (secretKey : SchemeSeedKey) (index : LeafIndex) (message : Message) :
    m (Option Signature) := do
  let bottomKey := keyIndexOnLayer index bottomLayer
  let topKey := keyIndexOnLayer index topLayer
  let some bottom ← signLayerWithHash secretKey bottomLayer bottomKey
    (littleEndianBytes 32 message) | return none
  let bottomRoot ← treeNodeWithHash secretKey.parameter bottomLayer secretKey.schemeSeed layerHeight
    topKey.val
  let some top ← signLayerWithHash secretKey topLayer topKey (littleEndianBytes 16
      bottomRoot) | return none
  return some ⟨index, fun lay => if lay = bottomLayer then bottom else top⟩

/-- `S` and `P` from the key's seed `S_0`, as key generation derives them. -/
def deriveSchemeSeedKey (keySeed : MasterSeed) : OracleComp HashSpec SchemeSeedKey := do
  let seed ← taggedSeedWithHash seedTag keySeed
  let parameter ← thWithHash 0 (keygenDomainFields .parameter) (littleEndianBytes 32 seed)
  return ⟨seed, parameter⟩

/-- `S` again from the secret key's seed `S_0`, beside its public parameter, as the crate's signer
derives it. -/
def rederiveSchemeSeedKey (secretKey : SecretKey) : OracleComp HashSpec SchemeSeedKey := do
  let seed ← taggedSeedWithHash seedTag secretKey.keySeed
  return ⟨seed, secretKey.parameter⟩

end KeyGenerationAndSigning

namespace RandomPermutationModel

open Common Common.SufCma


/-- leanXMSS in the generic SUF-CMA game: the seed, key generation, the signer of a request, the
verifier, and the winning condition: a valid transcript without the forgery
(`SignerReturnedForgery`). -/
noncomputable def schemeWithHash :
    SchemeWithHash MasterSeed PublicKey SchemeSeedKey SigningRequest
      (Option Signature) Forgery where
  sample := sampleMasterSeed
  keygen := KeyGenerationAndSigning.keygenFromSeedWithHash
  sign sk request :=
    KeyGenerationAndSigning.signWithHash (m := OracleComp HashSpec) sk request.leafIndex
        request.message
  verify pk forgery :=
    Verification.verifyWithHash (m := OracleComp HashSpec) pk forgery.message forgery.signature
  win log forgery :=
    decide (SigningTranscript.NoLeafIndexReused log ∧
      ¬SignerReturnedForgery SigningRequest.message log forgery.message forgery.signature)

attribute [local irreducible] KeyGenerationAndSigning.treeNodeWithHash
  KeyGenerationAndSigning.signWithHash

/-- The rest of leanXMSS's key generation once `S` and `P` are derived: the top tree's root. -/
def keygenRest (key : SchemeSeedKey) : OracleComp HashSpec (PublicKey × SchemeSeedKey) := do
  let root ← KeyGenerationAndSigning.treeNodeWithHash key.parameter topLayer key.schemeSeed
    layerHeight 0
  return (⟨root, key.parameter⟩, key)

theorem keygen_eq_derive (seed : MasterSeed) :
    schemeWithHash.keygen seed =
      KeyGenerationAndSigning.deriveSchemeSeedKey seed >>= keygenRest := by
  simp only [schemeWithHash, KeyGenerationAndSigning.keygenFromSeedWithHash,
    KeyGenerationAndSigning.deriveSchemeSeedKey, keygenRest, bind_assoc, pure_bind]

theorem keygenRest_key (key : SchemeSeedKey) :
    ∀ keys ∈ support (keygenRest key), keys.2 = key := by
  intro keys hkeys
  simp only [keygenRest, support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hkeys
  obtain ⟨_, _, rfl⟩ := hkeys
  rfl

/-- leanXMSS's key generation derives `S` and `P` first and keeps `S_0` and `P` as the key; its
signer derives `S` again and signs with `S` and `P`. -/
noncomputable def keptKey : KeptKey schemeWithHash SchemeSeedKey SecretKey where
  derive := KeyGenerationAndSigning.deriveSchemeSeedKey
  rest _ := keygenRest
  signWith key request := schemeWithHash.sign key request
  keep seed key := ⟨seed, key.parameter⟩
  rederive := KeyGenerationAndSigning.rederiveSchemeSeedKey
  keygen_eq := keygen_eq_derive
  sign_eq _ key keys hkeys := by rw [keygenRest_key key keys hkeys]

/-- leanXMSS with the crate's secret key, the seed `S_0` and the public parameter: the signer
derives `S` first. -/
noncomputable abbrev schemeWithHashFromSeed :
    SchemeWithHash MasterSeed PublicKey SecretKey SigningRequest (Option Signature) Forgery :=
  keptKey.scheme

end RandomPermutationModel

end LeanXmss

end
