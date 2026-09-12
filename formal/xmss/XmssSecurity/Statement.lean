import VCVio.OracleComp.QueryTracking.LoggingOracle
import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation
import VCVio.OracleComp.QueryTracking.QueryBound

/-!
# Classical random-oracle security of the concrete XMSS instance

This single module is the reviewer-facing statement of the formalization. It contains everything the statement depends on: the concrete parameters and types, the byte layout of every hash input, the three algorithms exactly as run in the security experiment, the strong-unforgeability experiment, and the security claim `XmssSecurityStatement`. Nothing here imports proof machinery, and nothing below describes a reduction or an intermediate game. The theorem itself is stated and proved in the root module `XmssSecurity`.

The concrete instance has 32-byte messages, 32-bit epochs, 128-bit digests, a 256-bit random-oracle output truncated to 128 bits, 42 Winternitz chains of length 8, and a Merkle tree of height 32.
-/

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

/-! ## The instance: parameters, types, and hash-input layout -/

def digestBits : Nat := 128
def hashOutputBits : Nat := 256
def messageBits : Nat := 256
def publicParameterBits : Nat := 128
def randomnessBits : Nat := 192
/-- Encoding attempts per signature, `A_max`. -/
def signingAttemptLimit : Nat := 2 ^ 23
/-- The Merkle tree height `h`; the lifetime is `L = 2^h` epochs. -/
def treeHeight : Nat := 32
def lifetime : Nat := 2 ^ treeHeight
def winternitzBits : Nat := 3
def chainLength : Nat := 2 ^ winternitzBits
def numChains : Nat := 42
def targetSum : Nat := 195

abbrev Digest := BitVec digestBits
abbrev HashOutput := BitVec hashOutputBits
abbrev Message := BitVec messageBits
abbrev PublicParameter := BitVec publicParameterBits
abbrev Randomness := BitVec randomnessBits
/-- `ep < L`. -/
abbrev Epoch := Fin lifetime
abbrev ChainIndex := Fin numChains
abbrev Digit := Fin chainLength
/-- A chain step; the tweak carries `2^w * i + step`. -/
abbrev ChainStep := Fin (chainLength - 1)
/-- A level of the stored tree, `0` the leaves and `h` the root. -/
abbrev MerkleHeight := Fin (treeHeight + 1)
/-- A level of the authentication path, below the root; the tweak carries `level + 1`. -/
abbrev MerkleLevel := Fin treeHeight
/-- A node within a level. Level `ℓ` only uses the values below `2^(h - ℓ)`. -/
abbrev MerkleNode := Fin lifetime
abbrev Encoding := ChainIndex → Digit
abbrev HashInput := List UInt8

/-- Keep the first 128 output bits, the low bits of the little-endian bit vector. -/
def truncateHash (output : HashOutput) : Digest :=
  output.extractLsb' 0 digestBits

/-- `pk = (root, P)`. -/
structure PublicKey where
  root : Digest
  parameter : PublicParameter
deriving DecidableEq

/-- The ideal precomputed key of the specification: `P`, the sampled `sk_{ep,i}`, every chain value `C_{ep,i,k}` and every Merkle node `X_{ℓ,j}`. -/
structure SecretKey where
  parameter : PublicParameter
  chainStart : Epoch → ChainIndex → Digest
  chainValue : Epoch → ChainIndex → Digit → Digest
  treeValue : MerkleHeight → MerkleNode → Digest

/-- `sigma = (rho, sigma_OTS, path_ep)`: the encoding randomness, the `v` chain values and the `h` authentication nodes. -/
structure Signature where
  randomness : Randomness
  chainValue : ChainIndex → Digest
  authPath : Fin treeHeight → Digest
deriving DecidableEq

/-- Serialize a bit vector into a fixed number of bytes, least significant byte first. -/
def bytesLE (byteCount : Nat) (value : BitVec (8 * byteCount)) : List UInt8 :=
  List.ofFn fun index : Fin byteCount =>
    UInt8.ofBitVec (value.extractLsb' (8 * index.val) 8)

/-- The three fields of the specification's `enc(t, p, j)`. -/
structure TweakFields where
  tag : BitVec 8
  position : BitVec 32
  epoch : BitVec 32
deriving DecidableEq

/-- The specification's 16 tweak bytes `tag || position || epoch || 0^7`, each field serialized least significant byte first. -/
def fieldBytes (fields : TweakFields) : List UInt8 :=
  bytesLE 1 fields.tag ++ bytesLE 4 fields.position ++ bytesLE 4 fields.epoch ++
    List.replicate 7 0

/-- Every domain-separated hash call the instance makes, tweak types `0` to `3`. -/
inductive HashDomain where
  | chain (epoch : Epoch) (chain : ChainIndex) (step : ChainStep)
  | leaf (epoch : Epoch)
  | merkle (level : MerkleLevel) (node : MerkleNode)
  | encoding (epoch : Epoch)
deriving DecidableEq

/-- Serialize a typed hash domain into the fields of a tweak. -/
def hashDomainFields : HashDomain → TweakFields
  | .chain epoch chain step =>
      ⟨0#8, BitVec.ofNat 32 (chainLength * chain.val + step.val), BitVec.ofNat 32 epoch.val⟩
  | .leaf epoch => ⟨1#8, 0#32, BitVec.ofNat 32 epoch.val⟩
  | .merkle level node =>
      ⟨2#8, BitVec.ofNat 32 (level.val + 1), BitVec.ofNat 32 node.val⟩
  | .encoding epoch => ⟨3#8, 0#32, BitVec.ofNat 32 epoch.val⟩

/-- The exact 16 bytes supplied by the specification as a hash tweak. -/
def tweakBytes (domain : HashDomain) : List UInt8 :=
  fieldBytes (hashDomainFields domain)

/-- The random-oracle input `tweak || parameter || message` used by every tweakable hash call. -/
def tweakableHashInput (parameter : PublicParameter) (domain : HashDomain)
    (message : HashInput) : HashInput :=
  tweakBytes domain ++ bytesLE 16 parameter ++ message

/-! ### The target-sum code

`v = 42` chunks of `w = 3` bits, 21 in each half of the digest, one pinned bit per half, and the code is the words of digit sum `T = 195`. -/

namespace TargetSum

/-- The digit sum of a word. -/
def sum (x : Encoding) : Nat := ∑ i, (x i).val

/-- Membership in the code `C`: digit sum `T`. -/
def Valid (x : Encoding) : Prop := sum x = targetSum

instance : DecidablePred Valid :=
  fun x => inferInstanceAs (Decidable (sum x = targetSum))

/-- `v / 2 = 21` digits in each half of the digest. -/
def digitsPerHalf : Nat := numChains / 2

/-- Offset of a three-bit digit, skipping padding bits 63 and 127. -/
def digitOffset (i : ChainIndex) : Nat :=
  winternitzBits * i.val + if i.val < digitsPerHalf then 0 else 1

/-- `x_i`, the three bits of the digest at the digit's offset. -/
def digestEncoding (digest : Digest) : Encoding :=
  fun i => (digest.extractLsb' (digitOffset i) winternitzBits).toFin

/-- Decode the concrete little-endian layout used by `IncEnc`: 21 three-bit digits, padding bit 63, 21 digits, and padding bit 127. A digest decodes exactly when both padding bits are clear and the digits reach the target sum. -/
def decodeDigest (digest : Digest) : Option Encoding :=
  if digest.getLsbD 63 = false ∧ digest.getLsbD 127 = false ∧ Valid (digestEncoding digest)
  then some (digestEncoding digest) else none

end TargetSum

/-! ## The algorithms

Key generation, signing and verification as run in the experiment, with every oracle hash call they make. Everything under `Concrete` is the instance; the experiment after it is generic over `Scheme`. The hashing algorithms are written for any monad `m` that can query the hash, and key generation and signing run them with `liftM` inside the world that also samples. Key generation computes the Merkle root through the oracle and stores every chain value and node as the replay of that computation against its own query log, so reading them while signing is not an oracle query; signing makes at most `signingAttemptLimit` encoding attempts, each sampling fresh randomness and hashing once; verification is the ordinary verifier. Branches that return `0` out of range exist only to make the definitions total; the honest algorithms never take them and verification never reads them. The `irreducible` attributes at the end of the namespace only seal definitions against accidental unfolding in proofs, and Lean restricts global reducibility attributes to the defining module. -/

/-- A hash query takes an arbitrary byte string and returns 32 bytes. -/
abbrev HashSpec := HashInput →ₒ HashOutput

/-- `unifSpec` for uniform sampling, `HashSpec` for the random oracle (hash). A query is `.inl` to sample or `.inr` to hash, so `HasHashQueryBound` counts only the hash side. -/
abbrev OracleWorld := unifSpec + HashSpec

/-- Enter a query log into a cache, in order. -/
def extendHashCacheWithLog (initialCache : QueryCache HashSpec) :
    QueryLog HashSpec → QueryCache HashSpec
  | [] => initialCache
  | ⟨input, output⟩ :: tail =>
      extendHashCacheWithLog (initialCache.cacheQuery input output) tail

/-- The cache a query log records. -/
def hashCacheOfLog (log : QueryLog HashSpec) : QueryCache HashSpec :=
  extendHashCacheWithLog ∅ log

namespace Concrete

def digestBytes (value : Digest) : HashInput := bytesLE 16 value

def messageBytes (message : Message) : HashInput := bytesLE 32 message

def randomnessBytes (randomness : Randomness) : HashInput := bytesLE 24 randomness

/-- `m || rho || 0^64`. -/
def encodingPayload (message : Message) (randomness : Randomness) : HashInput :=
  messageBytes message ++ randomnessBytes randomness ++ List.replicate 8 0

/-- `pk_0 || ... || pk_{v-1}`. -/
def leafPayload (endpoints : ChainIndex → Digest) : HashInput :=
  (List.ofFn endpoints).flatMap digestBytes

/-- The two children of a Merkle node. -/
def nodePayload (left right : Digest) : HashInput :=
  digestBytes left ++ digestBytes right

/-- Run the `n` computations in index order and collect their results. -/
def sequenceFin {m : Type → Type} [Monad m] {n : Nat}
    (computation : Fin n → m α) : m (Fin n → α) :=
  match n with
  | 0 => pure Fin.elim0
  | n + 1 => do
      let head ← computation 0
      let tail ← sequenceFin fun index : Fin n => computation index.succ
      return Fin.cases head tail

variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]

/-- One query to the random oracle `H`. -/
def oracleHash (input : HashInput) : m HashOutput :=
  HasQuery.query (spec := HashSpec) (m := m) input

/-- `Th(P, tw, M) = Truncate_n(H(tw || P || M))`. -/
def tweakableHash
    (parameter : PublicParameter) (domain : HashDomain) (payload : HashInput) : m Digest := do
  let output ← oracleHash (tweakableHashInput parameter domain payload)
  return truncateHash output

/-- The digest `D` of `IncEnc(P, m, rho, ep)`. -/
def encodingHash (parameter : PublicParameter) (epoch : Epoch)
    (message : Message) (randomness : Randomness) : m Digest :=
  tweakableHash parameter (.encoding epoch) (encodingPayload message randomness)

/-- One chain step, under `tweak_chain(ep, i, step + 1)`. -/
def chainHash (parameter : PublicParameter) (epoch : Epoch) (chain : ChainIndex)
    (step : ChainStep) (value : Digest) : m Digest :=
  tweakableHash parameter (.chain epoch chain step) (digestBytes value)

/-- `X_{0,ep}`, the hash of the `v` public values. -/
def leafHash (parameter : PublicParameter) (epoch : Epoch)
    (endpoints : ChainIndex → Digest) : m Digest :=
  tweakableHash parameter (.leaf epoch) (leafPayload endpoints)

/-- `X_{level+1,node}` from its two children. -/
def nodeHash (parameter : PublicParameter) (level : MerkleLevel) (node : MerkleNode)
    (left right : Digest) : m Digest :=
  tweakableHash parameter (.merkle level node) (nodePayload left right)

/-! ### Verification -/

/-- `A_level`, or `0` above the tree. -/
def signaturePath (signature : Signature) (level : Nat) : Digest :=
  if hlevel : level < treeHeight then
    signature.authPath ⟨level, hlevel⟩
  else
    0

/-- `Chain_{i,ep}(P, start, steps, value)`: the step onto position `start + steps + 1` carries tweak position `2^w * i + start + steps`. -/
def chainWalk (parameter : PublicParameter) (epoch : Epoch) (chain : ChainIndex) :
    Nat → Nat → Digest → m Digest
  | _, 0, value => pure value
  | position, steps + 1, value => do
      let previous ← chainWalk parameter epoch chain position steps value
      if hposition : position + steps < chainLength - 1 then
        chainHash parameter epoch chain ⟨position + steps, hposition⟩ previous
      else
        pure 0

/-- The verifier's half of a chain: walk the remaining `2^w - 1 - x_i` steps. -/
def recoverChain (parameter : PublicParameter) (epoch : Epoch) (chain : ChainIndex)
    (digit : Digit) (value : Digest) : m Digest :=
  chainWalk parameter epoch chain digit.val (chainLength - 1 - digit.val) value

/-- `pk'_{ep,i}` for every chain. -/
def recoverEndpoints (parameter : PublicParameter) (epoch : Epoch)
    (encoding : Encoding) (signature : Signature) :
    m (ChainIndex → Digest) :=
  sequenceFin fun chain =>
    recoverChain parameter epoch chain (encoding chain) (signature.chainValue chain)

/-- The index of the Merkle node on the path of `epoch` one level above `level`. -/
def nodeIndex (epoch : Epoch) (level : Nat) : MerkleNode :=
  ⟨epoch.val / 2 ^ (level + 1), by
    have hle := Nat.div_le_self epoch.val (2 ^ (level + 1))
    exact hle.trans_lt epoch.isLt⟩

/-- `Z_{level+1}` from `Z_level` and `A_level`, in the order bit `level` of the epoch dictates. -/
def authenticationNodeHash (parameter : PublicParameter) (epoch : Epoch)
    (level : Nat) (current sibling : Digest) : m Digest :=
  if hlevel : level < treeHeight then
    if epoch.val.testBit level then
      nodeHash parameter ⟨level, hlevel⟩ (nodeIndex epoch level) sibling current
    else
      nodeHash parameter ⟨level, hlevel⟩ (nodeIndex epoch level) current sibling
  else
    pure 0

/-- `Z_levels`, folded up from the leaf `Z_0`. -/
def authenticationRoot (parameter : PublicParameter) (epoch : Epoch)
    (signature : Signature) : Nat → Digest → m Digest
  | 0, leaf => pure leaf
  | levels + 1, leaf => do
      let current ← authenticationRoot parameter epoch signature levels leaf
      authenticationNodeHash parameter epoch levels current (signaturePath signature levels)

/-- Accept exactly when `Z_h = root`. -/
def verifyAfterLeaf
    (publicKey : PublicKey) (epoch : Epoch) (signature : Signature) (leaf : Digest) : m Bool := do
  let root ← authenticationRoot publicKey.parameter epoch signature treeHeight leaf
  return decide (root = publicKey.root)

/-- `Ver(pk, ep, m, sigma)`. -/
def verify (publicKey : PublicKey) (epoch : Epoch)
    (message : Message) (signature : Signature) : m Bool := do
  let digest ← encodingHash publicKey.parameter epoch message signature.randomness
  match TargetSum.decodeDigest digest with
  | none => pure false
  | some encoding => do
      let endpoints ← recoverEndpoints publicKey.parameter epoch encoding signature
      let leaf ← leafHash publicKey.parameter epoch endpoints
      verifyAfterLeaf publicKey epoch signature leaf

/-! ### Key generation

Uniform sampling of the parameter and of every one-time secret; `$ᵗ X` draws a uniform element of `X`. -/

noncomputable local instance : SampleableType PublicParameter :=
  SampleableType.ofFintype PublicParameter

noncomputable local instance : SampleableType (Epoch → ChainIndex → Digest) :=
  SampleableType.ofFintype (Epoch → ChainIndex → Digest)

/-- `pk_{ep,i} = Chain(P, 0, 2^w - 1, sk_{ep,i})` for every chain. -/
def oneTimePublicKey (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (epoch : Epoch) : m (ChainIndex → Digest) :=
  sequenceFin fun chain =>
    chainWalk parameter epoch chain 0 (chainLength - 1) (secret epoch chain)

/-- `X_{0,ep}` from the secrets. -/
def leafAt (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (epoch : Epoch) : m Digest := do
  let endpoints ← oneTimePublicKey parameter secret epoch
  leafHash parameter epoch endpoints

/-- A natural read as a node index. -/
def merkleNodeOfNat (value : Nat) : MerkleNode :=
  ⟨value % lifetime,
    Nat.mod_lt _ (by simp [lifetime])⟩

/-- `2j` or `2j + 1`. -/
def childNode (node : MerkleNode) (right : Bool) : MerkleNode :=
  merkleNodeOfNat (2 * node.val + if right then 1 else 0)

/-- `X_{levels,node}`, the Merkle tree over the one-time leaves. -/
def treeNode (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest) :
    Nat → MerkleNode → m Digest
  | 0, node => leafAt parameter secret node
  | levels + 1, node => do
      let left ← treeNode parameter secret levels (childNode node false)
      let right ← treeNode parameter secret levels (childNode node true)
      if hlevel : levels < treeHeight then
        nodeHash parameter ⟨levels, hlevel⟩ node left right
      else
        pure 0

/-- The root is node `0` of level `h`. -/
def rootNode : MerkleNode :=
  ⟨0, by simp [lifetime]⟩

noncomputable def samplePublicParameter : ProbComp PublicParameter :=
  $ᵗ PublicParameter

noncomputable def sampleSecret : ProbComp (Epoch → ChainIndex → Digest) :=
  $ᵗ (Epoch → ChainIndex → Digest)

/-- Answer a hash query from a recorded query cache, and by 0 for an unrecorded input. -/
def replayHash (cache : QueryCache HashSpec) : QueryImpl HashSpec Id :=
  fun input => (cache input).getD 0

/-- The ideal precomputed secret key. Every stored table entry is the corresponding oracle computation from this module, replayed against the recorded key-generation cache. -/
def precomputedSecretKey (parameter : PublicParameter)
    (secret : Epoch → ChainIndex → Digest) (cache : QueryCache HashSpec) :
    SecretKey where
  parameter := parameter
  chainStart := secret
  chainValue := fun epoch chain digit =>
    evalWithAnswerFn (replayHash cache)
      (chainWalk parameter epoch chain 0 digit.val (secret epoch chain) :
        OracleComp HashSpec Digest)
  treeValue := fun height node =>
    evalWithAnswerFn (replayHash cache)
      (treeNode parameter secret height.val node : OracleComp HashSpec Digest)

/-- `Gen`: sample the parameter and the secrets, compute the root through the oracle, and store every chain value and node as the replay of that computation. -/
noncomputable def precomputedKeygen :
    OracleComp OracleWorld (PublicKey × SecretKey) := do
  let parameter ← liftM samplePublicParameter
  let secret ← liftM sampleSecret
  let result ← liftM
    (treeNode parameter secret treeHeight rootNode :
      OracleComp HashSpec Digest).withQueryLog
  let cache := hashCacheOfLog result.2
  return (⟨result.1, parameter⟩, precomputedSecretKey parameter secret cache)

/-! ### Signing -/

noncomputable local instance : SampleableType Randomness :=
  SampleableType.ofFintype Randomness

/-- `rho`, fresh per attempt. -/
noncomputable def signingRandomness : ProbComp Randomness :=
  $ᵗ Randomness

/-- `floor(ep / 2^level) xor 1`, the sibling on the path. -/
def authenticationPathNode (epoch : Epoch) (level : MerkleLevel) : MerkleNode :=
  merkleNodeOfNat (Nat.xor (epoch.val / 2 ^ level.val) 1)

/-- `sigma_OTS,i = C_{ep,i,x_i}`. -/
def precomputedSignedChainValues (secretKey : SecretKey) (epoch : Epoch)
    (encoding : Encoding) : ChainIndex → Digest :=
  fun chain => secretKey.chainValue epoch chain (encoding chain)

/-- `path_ep = (A_0, ..., A_{h-1})`, read from the stored tree. -/
def precomputedAuthenticationPath (secretKey : SecretKey) (epoch : Epoch) :
    Fin treeHeight → Digest :=
  fun level => secretKey.treeValue level.castSucc (authenticationPathNode epoch level)

/-- The signature once the encoding is found. -/
def precomputedSignWithEncoding (secretKey : SecretKey) (epoch : Epoch)
    (randomness : Randomness) (encoding : Encoding) : Signature :=
  ⟨randomness, precomputedSignedChainValues secretKey epoch encoding,
    precomputedAuthenticationPath secretKey epoch⟩

/-- One attempt: hash once, and sign if the digest encodes. -/
def precomputedSignAttempt (secretKey : SecretKey) (epoch : Epoch)
    (message : Message) (randomness : Randomness) : m (Option Signature) := do
  let digest ← encodingHash secretKey.parameter epoch message randomness
  match TargetSum.decodeDigest digest with
  | none => pure none
  | some encoding =>
      pure (some (precomputedSignWithEncoding secretKey epoch randomness encoding))

/-- At most `attempts` attempts, each with fresh randomness, stopping at the first that encodes. -/
noncomputable def precomputedSignBoundedAttempts :
    Nat → SecretKey → Epoch → Message →
      OracleComp OracleWorld (Option Signature)
  | 0, _secretKey, _epoch, _message => pure none
  | attempts + 1, secretKey, epoch, message => do
      let randomness ← liftM signingRandomness
      let result ← liftM
        (precomputedSignAttempt secretKey epoch message randomness :
          OracleComp HashSpec (Option Signature))
      match result with
      | some signature => pure (some signature)
      | none => precomputedSignBoundedAttempts attempts secretKey epoch message

/-- `Sig(sk, ep, m)`, at most `A_max` attempts. The once-per-epoch discipline is the game's, in `SigningTranscript.Valid`. -/
noncomputable def precomputedCappedSign (secretKey : SecretKey)
    (epoch : Epoch) (message : Message) :
    OracleComp OracleWorld (Option Signature) :=
  precomputedSignBoundedAttempts signingAttemptLimit secretKey epoch message

attribute [irreducible] verifyAfterLeaf treeNode samplePublicParameter sampleSecret
  precomputedKeygen signingRandomness precomputedCappedSign

end Concrete

/-! ## The security experiment -/

/-- The random-oracle semantics: hash queries are answered lazily and consistently by uniform sampling and cached; uniform-sampling queries are forwarded unchanged. -/
noncomputable def romImpl : QueryImpl OracleWorld (StateT (QueryCache HashSpec) ProbComp) :=
  unifFwdImpl HashSpec +
    (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))

/-- A signing request contains a 32-bit epoch and a 32-byte message. -/
structure SignRequest where
  epoch : Epoch
  message : Message
deriving DecidableEq

/-- A claimed forgery: an epoch, a message, and a signature. -/
structure Forgery where
  epoch : Epoch
  message : Message
  signature : Signature
deriving DecidableEq

/-- The request a forgery claims to answer. -/
def Forgery.request (forgery : Forgery) : SignRequest :=
  ⟨forgery.epoch, forgery.message⟩

/-- The interface of a synchronized signature scheme in the random-oracle experiment. -/
structure Scheme where
  keygen : OracleComp OracleWorld (PublicKey × SecretKey)
  sign : SecretKey → Epoch → Message → OracleComp OracleWorld (Option Signature)
  verify : PublicKey → Epoch → Message → Signature → OracleComp OracleWorld Bool

/-- The signing oracle answers a request with either a signature or `none` if the signer fails. -/
abbrev SigningSpec := SignRequest →ₒ Option Signature

/-- A classical adaptive adversary. After receiving the public key, it may query the shared random oracle, request signatures, and finally return a claimed forgery. -/
structure Adversary where
  main : PublicKey → OracleComp (OracleWorld + SigningSpec) Forgery

namespace SigningTranscript

/-- A signing transcript is valid exactly when no epoch occurs twice. Thus the adversary may make adaptive signing requests, but may not request two signatures at the same epoch. -/
def Valid (log : QueryLog SigningSpec) : Prop :=
  (log.map fun entry => entry.1.epoch).Nodup

instance (log : QueryLog SigningSpec) : Decidable (Valid log) :=
  inferInstanceAs (Decidable ((log.map fun entry => entry.1.epoch).Nodup))

/-- The signer returned the claimed forgery exactly when the transcript contains the same epoch, message, and signature. A different signature for a signed message is therefore a valid strong forgery. -/
def Contains (log : QueryLog SigningSpec) (forgery : Forgery) : Prop :=
  ∃ entry ∈ log, entry.1 = forgery.request ∧ entry.2 = some forgery.signature

instance (log : QueryLog SigningSpec) (forgery : Forgery) : Decidable (Contains log forgery) :=
  inferInstanceAs
    (Decidable (∃ entry ∈ log, entry.1 = forgery.request ∧ entry.2 = some forgery.signature))

end SigningTranscript

/-- The signing oracle used in the game. It records every request and response while forwarding the request to the scheme's signer. -/
def signingOracle (scheme : Scheme) (sk : SecretKey) :
    QueryImpl SigningSpec (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) :=
  QueryImpl.withLogging fun request => scheme.sign sk request.epoch request.message

/-- Forward the shared random oracle and uniform sampling to the adversary unchanged, alongside the logged signing oracle. -/
def forwardOracles :
    QueryImpl OracleWorld (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)) :=
  fun input => liftM (OracleWorld.query input)

/-- The complete strong-unforgeability experiment.

The random oracle is sampled lazily by the semantics of `OracleWorld`. Key generation, the adversary, the signing oracle, and final verification all share the same oracle. The game returns `true` precisely when the signing transcript uses every epoch at most once, the claimed forgery is not an exact replay, and the signature verifies. -/
noncomputable def gameCore (scheme : Scheme) (adversary : Adversary) :
    OracleComp OracleWorld Bool := do
  let (pk, sk) ← scheme.keygen
  let ((forgery, log) : Forgery × QueryLog SigningSpec) ←
    (simulateQ (forwardOracles + signingOracle scheme sk) (adversary.main pk)).run
  let verified ← scheme.verify pk forgery.epoch forgery.message forgery.signature
  return decide (SigningTranscript.Valid log ∧ ¬SigningTranscript.Contains log forgery) && verified

/-- The probability that the adversary wins, over key generation, signer randomness, and the random oracle, which starts from the empty cache. The final cache is discarded. -/
noncomputable def forgeAdvantage (scheme : Scheme) (adversary : Adversary) : ℝ≥0∞ :=
  Pr[= true | (simulateQ romImpl (gameCore scheme adversary)).run' ∅]

/-- The whole experiment makes at most `q` random-oracle queries on every execution path. The count includes queries during key generation, adversarial hashing, signing, and final verification. Uniform sampling operations are not hash queries. -/
def HasHashQueryBound (scheme : Scheme) (adversary : Adversary) (q : Nat) : Prop :=
  (gameCore scheme adversary).IsQueryBoundP (· matches .inr _) q

/-- Having `bits` bits of classical security means that every classical adaptive adversary whose complete experiment stays within a nonzero hash-query budget `q` forges with probability at most `q / 2^bits`. -/
def HasClassicalSecurityBits (scheme : Scheme) (bits : Nat) : Prop :=
  ∀ q, 1 ≤ q → ∀ adversary, HasHashQueryBound scheme adversary q →
    forgeAdvantage scheme adversary ≤ q / ((2 ^ bits : Nat) : ℝ≥0∞)

/-- The concrete XMSS scheme: the precomputed key generation, the capped retry signer, and the ordinary verifier defined above. -/
noncomputable def Concrete.scheme : Scheme where
  keygen := Concrete.precomputedKeygen
  sign := Concrete.precomputedCappedSign
  verify := fun publicKey epoch message signature =>
    liftM (Concrete.verify publicKey epoch message signature : OracleComp HashSpec Bool)

/-- The security claim: `127` bits of classical strong unforgeability in the random-oracle model. -/
abbrev XmssSecurityStatement : Prop :=
  HasClassicalSecurityBits Concrete.scheme 127

end XmssSecurity
