import VCVio.OracleComp.QueryTracking.LoggingOracle
import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation
import VCVio.OracleComp.QueryTracking.QueryBound
import VCVio.OracleComp.QueryTracking.WriterCost

/-!
# XMSS with a 256-bit master seed

This module contains the complete seeded scheme: parameters, types, serialized hash inputs, key generation, signing, verification, the consistent random-oracle experiment, and the target `XmssSecurityStatement`. The experiment samples one 32-byte secret seed; key generation derives the public parameter and every signing secret through the same random oracle. Derivation and verification use disjoint domains.

The theorem `xmss_has_127_bits_of_classical_security` proves the `127`-bit bound, counting every hash call in the experiment.
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

abbrev MasterSeed := BitVec 256

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

/-- Cached chain starts, chain values and Merkle nodes, together with the public parameter. -/
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

/-- The protocol domain separator. -/
def protocolDomainSep : UInt8 := 0

/-- The specification's 16 tweak bytes `protocol_domain_sep || tag || 0 || 0 || position || 0^4 || epoch`, each field serialized least significant byte first. -/
def fieldBytes (fields : TweakFields) : List UInt8 :=
  [protocolDomainSep] ++ bytesLE 1 fields.tag ++ [0, 0] ++ bytesLE 4 fields.position ++
    List.replicate 4 0 ++ bytesLE 4 fields.epoch

/-- The verification hash domains, tweak types `1` to `4`. -/
inductive HashDomain where
  | chain (epoch : Epoch) (chain : ChainIndex) (step : ChainStep)
  | leaf (epoch : Epoch)
  | merkle (level : MerkleLevel) (node : MerkleNode)
  | encoding (epoch : Epoch)
deriving DecidableEq

/-- Serialize a typed hash domain into the fields of a tweak. -/
def hashDomainFields : HashDomain → TweakFields
  | .chain epoch chain step =>
      ⟨1#8, BitVec.ofNat 32 (chainLength * chain.val + step.val), BitVec.ofNat 32 epoch.val⟩
  | .leaf epoch => ⟨2#8, 0#32, BitVec.ofNat 32 epoch.val⟩
  | .merkle level node =>
      ⟨3#8, BitVec.ofNat 32 (level.val + 1), BitVec.ofNat 32 node.val⟩
  | .encoding epoch => ⟨4#8, 0#32, BitVec.ofNat 32 epoch.val⟩

/-- The exact 16 bytes supplied by the specification as a hash tweak. -/
def tweakBytes (domain : HashDomain) : List UInt8 :=
  fieldBytes (hashDomainFields domain)

/-- The random-oracle input `tweak || parameter || message` used by every tweakable hash call. -/
def tweakableHashInput (parameter : PublicParameter) (domain : HashDomain)
    (message : HashInput) : HashInput :=
  tweakBytes domain ++ bytesLE 16 parameter ++ message

/-- `tweak(12, trial, epoch) || P || S || m`. -/
def randomizerHashInput (parameter : PublicParameter) (seed : MasterSeed)
    (epoch : Epoch) (message : Message) (trial : BitVec 32) : HashInput :=
  fieldBytes ⟨12#8, trial, BitVec.ofNat 32 epoch.val⟩ ++
    bytesLE 16 parameter ++ bytesLE 32 seed ++ bytesLE 32 message

inductive KeygenDomain where
  | parameter
  | chain (epoch : Epoch) (chain : ChainIndex)
deriving DecidableEq

def keygenDomainFields : KeygenDomain → TweakFields
  | .parameter => ⟨10#8, 0#32, 0#32⟩
  | .chain epoch chain => ⟨0#8, BitVec.ofNat 32 chain.val, BitVec.ofNat 32 epoch.val⟩

/-- `tweak || P || S`; parameter derivation uses `P = 0`. -/
def keygenHashInput (parameter : PublicParameter) (domain : KeygenDomain)
    (seed : MasterSeed) : HashInput :=
  fieldBytes (keygenDomainFields domain) ++ bytesLE 16 parameter ++ bytesLE 32 seed

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

`Concrete` contains the hash and verification routines; `Seeded` contains key generation and signing. Hashing routines work in any monad with access to `HashSpec`. The experiment samples the master seed and charges every hash call, including repeated calls. Out-of-range branches only make the definitions total; honest algorithms never reach them. -/

/-- A hash query takes an arbitrary byte string and returns 32 bytes. -/
abbrev HashSpec := HashInput →ₒ HashOutput

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

/-- `m || rho || 0^64`. -/
def encodingPayload (message : Message) (randomness : Randomness) : HashInput :=
  bytesLE 32 message ++ bytesLE 24 randomness ++ List.replicate 8 0

/-- `pk_0 || ... || pk_{v-1}`. -/
def leafPayload (endpoints : ChainIndex → Digest) : HashInput :=
  (List.ofFn endpoints).flatMap (bytesLE 16)

/-- The two children of a Merkle node. -/
def nodePayload (left right : Digest) : HashInput :=
  bytesLE 16 left ++ bytesLE 16 right

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
  tweakableHash parameter (.chain epoch chain step) (bytesLE 16 value)

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

/-! ### Precomputed chains and tree -/

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

/-- Answer a hash query from a recorded query cache, and by 0 for an unrecorded input. -/
def replayHash (cache : QueryCache HashSpec) : QueryImpl HashSpec Id :=
  fun input => (cache input).getD 0

/-- Compute the stored chain values and Merkle nodes by replaying the key-generation query log. -/
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

/-! ### Signing -/

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

attribute [irreducible] verifyAfterLeaf treeNode

end Concrete

def deriveKey {m : Type → Type} [Monad m] [HasQuery HashSpec m]
    (parameter : PublicParameter) (domain : KeygenDomain) (seed : MasterSeed) : m Digest := do
  return truncateHash (← Concrete.oracleHash (keygenHashInput parameter domain seed))

def deriveRandomizer {m : Type → Type} [Monad m] [HasQuery HashSpec m]
    (parameter : PublicParameter) (seed : MasterSeed) (epoch : Epoch)
    (message : Message) (trial : BitVec 32) : m Randomness := do
  return (← Concrete.oracleHash (randomizerHashInput parameter seed epoch message trial)).extractLsb' 0 randomnessBits

noncomputable def sampleMasterSeed : ProbComp MasterSeed :=
  letI := SampleableType.ofFintype MasterSeed
  $ᵗ MasterSeed

namespace Seeded

/-- The seed and the chain and tree values computed during key generation. -/
structure SecretKey where
  seed : MasterSeed
  precomputed : XmssSecurity.SecretKey

def keygenFromSeed (seed : MasterSeed) : OracleComp HashSpec (PublicKey × SecretKey) := do
  let parameter ← deriveKey 0 .parameter seed
  let secret ← Concrete.sequenceFin fun epoch => Concrete.sequenceFin fun chain =>
    deriveKey parameter (.chain epoch chain) seed
  let result ← (Concrete.treeNode parameter secret treeHeight Concrete.rootNode :
    OracleComp HashSpec Digest).withQueryLog
  let precomputed := Concrete.precomputedSecretKey parameter secret (hashCacheOfLog result.2)
  return (⟨result.1, parameter⟩, ⟨seed, precomputed⟩)

/-- Derive trials in increasing order, stopping at the first admissible encoding. -/
def signFrom {m : Type → Type} [Monad m] [HasQuery HashSpec m]
    (secretKey : SecretKey) (epoch : Epoch) (message : Message) : Nat → Nat → m (Option Signature)
  | 0, _ => pure none
  | attempts + 1, trial => do
      let randomness ← deriveRandomizer secretKey.precomputed.parameter secretKey.seed epoch message (BitVec.ofNat 32 trial)
      match ← Concrete.precomputedSignAttempt secretKey.precomputed epoch message randomness with
      | some signature => return some signature
      | none => signFrom secretKey epoch message attempts (trial + 1)

def sign {m : Type → Type} [Monad m] [HasQuery HashSpec m]
    (secretKey : SecretKey) (epoch : Epoch) (message : Message) : m (Option Signature) :=
  signFrom secretKey epoch message signingAttemptLimit 0

end Seeded

/-! ## The security experiment -/

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

/-- The signing oracle answers a request with either a signature or `none` if the signer fails. -/
abbrev SigningSpec := SignRequest →ₒ Option Signature

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

namespace Security

/-- A deterministic adaptive adversary with access to hashing and signing. -/
structure Adversary where
  main : PublicKey → OracleComp (HashSpec + SigningSpec) Forgery

/-- Record each signing request and its answer. -/
def signingOracle (sk : Seeded.SecretKey) :
    QueryImpl SigningSpec (WriterT (QueryLog SigningSpec) (OracleComp HashSpec)) :=
  QueryImpl.withLogging fun request => Seeded.sign sk request.epoch request.message

/-- For a fixed seed, all parties share the same hash oracle. -/
def gameCore (seed : MasterSeed) (adversary : Adversary) : OracleComp HashSpec Bool := do
  let (pk, sk) ← Seeded.keygenFromSeed seed
  let ((forgery, log) : Forgery × QueryLog SigningSpec) ←
    (simulateQ (QueryImpl.ofLift HashSpec (WriterT (QueryLog SigningSpec) (OracleComp HashSpec)) + signingOracle sk) (adversary.main pk)).run
  let verified ← Concrete.verify pk forgery.epoch forgery.message forgery.signature
  return decide (SigningTranscript.Valid log ∧ ¬SigningTranscript.Contains log forgery) && verified

/-- Answer hash queries consistently and count every call, including cache hits. -/
noncomputable def countedOracle :=
  (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp)).withAddCost (fun _ => (1 : Nat))

/-- Sample the master seed and run the game with an initially empty random-oracle cache.
The result records whether the adversary won and the total number of hash calls. -/
noncomputable def experiment (adversary : Adversary) : ProbComp (Bool × Nat) := do
  let seed ← sampleMasterSeed
  (simulateQ countedOracle (gameCore seed adversary)).run.run' ∅

/-- The probability of a successful forgery. -/
noncomputable def forgeAdvantage (adversary : Adversary) : ℝ≥0∞ :=
  Pr[fun result => result.1 = true | experiment adversary]

/-- Every execution uses at most `q` hash calls, including key generation, signing, and verification. -/
def HasHashQueryBound (adversary : Adversary) (q : Nat) : Prop :=
  ∀ result ∈ support (experiment adversary), result.2 ≤ q

/-- Every adversary with nonzero query budget `q` wins with probability at most `q / 2^bits`. -/
def HasClassicalSecurityBits (bits : Nat) : Prop :=
  ∀ q, 1 ≤ q → ∀ adversary, HasHashQueryBound adversary q →
    forgeAdvantage adversary ≤ q / ((2 ^ bits : Nat) : ℝ≥0∞)

end Security

/-- The security claim for the scheme with a 256-bit master seed. -/
abbrev XmssSecurityStatement : Prop := Security.HasClassicalSecurityBits 127

end XmssSecurity
