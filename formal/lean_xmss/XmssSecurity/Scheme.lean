module

public import VCVio.OracleComp.QueryTracking.LoggingOracle.Core
public import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation

@[expose] public section

/-!
# The leanXMSS model

The scheme of `LeanXmss/Scheme.lean` (`doc/lean_xmss`) with precomputed keys: two layers of XMSS of
height 16. The bottom layer is a forest of `2^16` trees over the `2^32` bottom one-time keys, its node
indices global; top key `b` signs the root of bottom tree `b` once, at key generation. Every hash
input is byte for byte the one of `LeanXmss`.
-/

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

/-! ## The instance: parameters, types, and hash-input layout -/

def digestBits : Nat := 128
def hashOutputBits : Nat := 256
def messageBits : Nat := 256
def publicParameterBits : Nat := 128
def randomnessBits : Nat := 128
/-- Encoding attempts per signature, `A_max`. -/
def signingAttemptLimit : Nat := 2 ^ 32
/-- The height `h` of each layer's trees. -/
def treeHeight : Nat := 16
/-- Leaf indices `idx < 2^32`, the bottom one-time keys. -/
def lifetime : Nat := 2 ^ (2 * treeHeight)
/-- The top one-time keys, one per bottom tree. -/
def topLifetime : Nat := 2 ^ treeHeight
/-- Bit 23 of `hi`, set on the top layer. -/
def topFlag : Nat := 2 ^ 23
def winternitzBits : Nat := 2
def chainLength : Nat := 2 ^ winternitzBits
def numChains : Nat := 58
def targetSum : Nat := 106

abbrev MasterSeed := BitVec 256

abbrev Digest := BitVec digestBits
abbrev HashOutput := BitVec hashOutputBits
abbrev Message := BitVec messageBits
abbrev PublicParameter := BitVec publicParameterBits
abbrev Randomness := BitVec randomnessBits
/-- `idx < 2^32`, a bottom one-time key. -/
abbrev LeafIndex := Fin lifetime
/-- `b < 2^16`, a top one-time key and the bottom tree it signs. -/
abbrev TopIndex := Fin topLifetime
abbrev ChainIndex := Fin numChains
abbrev Digit := Fin chainLength
/-- A chain step; the tweak carries the step, and the chain index follows the value. -/
abbrev ChainStep := Fin (chainLength - 1)
/-- A level of the stored tree, `0` the leaves and `h` the root. -/
abbrev MerkleHeight := Fin (treeHeight + 1)
/-- A level of the authentication path, below the root; the tweak carries `level + 1`. -/
abbrev MerkleLevel := Fin treeHeight
/-- A bottom node within a level, numbered globally across the forest. Level `ℓ` only uses the values
below `2^(2h - ℓ)`. -/
abbrev MerkleNode := Fin lifetime
/-- A top node within a level. Level `ℓ` only uses the values below `2^(h - ℓ)`. -/
abbrev TopNode := Fin topLifetime
/-- A pair of chains `(2t, 2t + 1)`, `t < 29`: one seed derivation. -/
abbrev ChainPair := Fin (numChains / 2)
abbrev Encoding := ChainIndex → Digit
abbrev HashInput := List UInt8

/-- Keep the first 128 output bits, the low bits of the little-endian bit vector. -/
def truncateHash (output : HashOutput) : Digest :=
  output.extractLsb' 0 digestBits

/-- The second 16 bytes of a hash output. Only the seed derivations of chain starts use them. -/
def upperHash (output : HashOutput) : Digest :=
  output.extractLsb' digestBits digestBits

/-- The half of a derivation that starts chain `n`: the first for even `n`, the second for odd `n`. -/
def hashHalf (n : Nat) (output : HashOutput) : Digest :=
  if n % 2 = 0 then truncateHash output else upperHash output

/-- The pair of chains a chain belongs to. -/
def chainPair (chain : ChainIndex) : ChainPair :=
  ⟨chain.val / 2, by have h : chain.val < 58 := chain.isLt; show chain.val / 2 < 29; omega⟩

/-- The top key of a leaf index, `idx / 2^16`. -/
def topKeyOf (leafIndex : LeafIndex) : TopIndex :=
  ⟨leafIndex.val / 2 ^ treeHeight, by
    have h := leafIndex.isLt
    simp only [lifetime, topLifetime, treeHeight] at h ⊢
    omega⟩

/-- `pk = (root, P)`. -/
structure PublicKey where
  root : Digest
  parameter : PublicParameter
deriving DecidableEq

/-- One layer's signature: the randomizer, the `v` chain values and the authentication path. -/
structure LayerSignature where
  randomness : Randomness
  chainValue : ChainIndex → Digest
  authPath : Fin treeHeight → Digest
deriving DecidableEq

/-- Cached chain starts, chain values and Merkle nodes of both layers, the top signature of every
bottom tree (its randomizer and codeword, `none` if its grinding failed), and the public parameter. -/
structure SecretKey where
  parameter : PublicParameter
  chainStart : LeafIndex → ChainIndex → Digest
  chainValue : LeafIndex → ChainIndex → Digit → Digest
  treeValue : MerkleHeight → MerkleNode → Digest
  topChainStart : TopIndex → ChainIndex → Digest
  topChainValue : TopIndex → ChainIndex → Digit → Digest
  topTreeValue : MerkleHeight → TopNode → Digest
  topSigned : TopIndex → Option (Randomness × Encoding)

/-- The bottom layer's randomizer, chain values and path, then the top layer's signature. The leaf
index travels with the request and the forgery. -/
structure Signature where
  randomness : Randomness
  chainValue : ChainIndex → Digest
  authPath : Fin treeHeight → Digest
  top : LayerSignature
deriving DecidableEq

/-- Serialize a bit vector into a fixed number of bytes, least significant byte first. -/
def bytesLE (byteCount : Nat) (value : BitVec (8 * byteCount)) : List UInt8 :=
  List.ofFn fun index : Fin byteCount =>
    UInt8.ofBitVec (value.extractLsb' (8 * index.val) 8)

/-- The address of a hash call: its type `tag < 32`, a chain step `step < 8`, and two fields
`hi < 2^24` and `lo < 2^32`. -/
structure TweakFields where
  tag : BitVec 5
  step : BitVec 3
  hi : BitVec 24
  lo : BitVec 32
deriving DecidableEq

/-- The 16 address bytes `lo || hi || (tag + 32 * step) || 0^8`: `lo` on 4 bytes, `hi` on 3 bytes,
each least significant byte first, then the type byte, then 8 zero bytes. -/
def fieldBytes (fields : TweakFields) : List UInt8 :=
  bytesLE 4 fields.lo ++ bytesLE 3 fields.hi ++ bytesLE 1 (fields.step ++ fields.tag) ++ bytesLE 8 0

/-- Convert the four integer fields to their fixed widths. -/
def tweakFields (tag step hi lo : Nat) : TweakFields :=
  ⟨BitVec.ofNat 5 tag, BitVec.ofNat 3 step, BitVec.ofNat 24 hi, BitVec.ofNat 32 lo⟩

/-- The verification hash domains of both layers: `TWEAK_CHAIN = 1`, `TWEAK_LEAF = 2`,
`TWEAK_NODE = 3`, `TWEAK_MSG = 12`, the top layer's `hi` carrying `topFlag`. -/
inductive HashDomain where
  | chain (leafIndex : LeafIndex) (chain : ChainIndex) (step : ChainStep)
  | leaf (leafIndex : LeafIndex)
  | merkle (level : MerkleLevel) (node : MerkleNode)
  | encoding (leafIndex : LeafIndex)
  | topChain (key : TopIndex) (chain : ChainIndex) (step : ChainStep)
  | topLeaf (key : TopIndex)
  | topMerkle (level : MerkleLevel) (node : TopNode)
  | topEncoding (key : TopIndex)
deriving DecidableEq

/-- Serialize a typed hash domain into the fields of a tweak. -/
def hashDomainFields : HashDomain → TweakFields
  | .chain leafIndex _ step => tweakFields 1 step 0 leafIndex
  | .leaf leafIndex => tweakFields 2 0 0 leafIndex
  | .merkle level node => tweakFields 3 0 (level.val + 1) node
  | .encoding leafIndex => tweakFields 12 0 0 leafIndex
  | .topChain key _ step => tweakFields 1 step topFlag key
  | .topLeaf key => tweakFields 2 0 topFlag key
  | .topMerkle level node => tweakFields 3 0 (topFlag + level.val + 1) node
  | .topEncoding key => tweakFields 12 0 topFlag key

/-- The exact 16 bytes supplied by the specification as a hash tweak. -/
def tweakBytes (domain : HashDomain) : List UInt8 :=
  fieldBytes (hashDomainFields domain)

/-- What a domain appends after the payload: a chain step's `LE_128(i)`, nothing otherwise. The chain
index is not in the address, so a key's chains share their step addresses. -/
def domainSuffix : HashDomain → HashInput
  | .chain _ chain _ => bytesLE 16 (BitVec.ofNat 128 chain.val)
  | .topChain _ chain _ => bytesLE 16 (BitVec.ofNat 128 chain.val)
  | _ => []

/-- The random-oracle input of every tweakable hash call: `P || A || payload`, where a chain step's
payload is its value followed by `domainSuffix`. -/
def tweakableHashInput (parameter : PublicParameter) (domain : HashDomain)
    (message : HashInput) : HashInput :=
  bytesLE 16 parameter ++ tweakBytes domain ++ message ++ domainSuffix domain

/-- `P || A(7, 0, 0, leafIndex) || S || m`, the randomizer base `R0` of a message. -/
def randomizerHashInput (parameter : PublicParameter) (seed : MasterSeed)
    (leafIndex : LeafIndex) (message : Message) : HashInput :=
  bytesLE 16 parameter ++ fieldBytes (tweakFields 7 0 0 leafIndex.val) ++
    bytesLE 32 seed ++ bytesLE 32 message

/-- `P || A_rnd(1, b) || S || r_b`, the randomizer base of the top signature of bottom tree `b`. -/
def topRandomizerHashInput (parameter : PublicParameter) (seed : MasterSeed)
    (key : TopIndex) (root : Digest) : HashInput :=
  bytesLE 16 parameter ++ fieldBytes (tweakFields 7 0 topFlag key.val) ++
    bytesLE 32 seed ++ bytesLE 16 root

/-- The seed derivations: the parameter (under `P = 0`), and the starts of chains `2t` and `2t + 1`
of a one-time key of either layer, the two halves of one hash. -/
inductive KeygenDomain where
  | parameter
  | chain (leafIndex : LeafIndex) (pair : ChainPair)
  | topChain (key : TopIndex) (pair : ChainPair)
deriving DecidableEq

/-- `TWEAK_PARAMETER = 5`, `TWEAK_PRF = 0` (`hi` the pair, flagged on the top layer, `lo` the key). -/
def keygenDomainFields : KeygenDomain → TweakFields
  | .parameter => tweakFields 5 0 0 0
  | .chain leafIndex pair => tweakFields 0 0 pair leafIndex
  | .topChain key pair => tweakFields 0 0 (topFlag + pair) key

/-- `"leanXMSS" || S_0`, the input of the scheme's seed `S`. -/
def seedHashInput (keySeed : MasterSeed) : HashInput :=
  [0x6c, 0x65, 0x61, 0x6e, 0x58, 0x4d, 0x53, 0x53] ++ bytesLE 32 keySeed

/-- `P || A || S`; parameter derivation uses `P = 0`. -/
def keygenHashInput (parameter : PublicParameter) (domain : KeygenDomain)
    (seed : MasterSeed) : HashInput :=
  bytesLE 16 parameter ++ fieldBytes (keygenDomainFields domain) ++ bytesLE 32 seed

/-! ### The target-sum code

`v = 58` digits of `w = 2` bits, the low `2v = 116` bits of the digest; the code is the words of digit sum `T = 106` whose top `12` bits, the last `6` base-4 digits, are zero. -/

namespace TargetSum

/-- The digit sum of a word. -/
def sum (x : Encoding) : Nat := ∑ i, (x i).val

/-- Membership in the code `C`: digit sum `T`. -/
def Valid (x : Encoding) : Prop := sum x = targetSum

instance : DecidablePred Valid :=
  fun x => inferInstanceAs (Decidable (sum x = targetSum))

/-- The bits above the `v` digits: `128 - 2v = 12`, which a codeword holds at zero. -/
def zeroBits : Nat := digestBits - winternitzBits * numChains

/-- Offset of a two-bit digit. -/
def digitOffset (i : ChainIndex) : Nat := winternitzBits * i.val

/-- `x_i`, the two bits of the digest at the digit's offset. -/
def digestEncoding (digest : Digest) : Encoding :=
  fun i => (digest.extractLsb' (digitOffset i) winternitzBits).toFin

/-- The top `128 - 2v` bits of a digest. -/
def digestTop (digest : Digest) : BitVec zeroBits :=
  digest.extractLsb' (winternitzBits * numChains) zeroBits

/-- A digest is a codeword when its last `64 - v` base-4 digits, its top 12 bits, are zero and its
first `v` digits sum to `T`. -/
def decodeDigest (digest : Digest) : Option Encoding :=
  if digestTop digest = 0 ∧ Valid (digestEncoding digest)
  then some (digestEncoding digest) else none

end TargetSum

/-! ## The algorithms

`Concrete` contains the hash and verification routines; `Seeded` contains key generation and signing. Hashing routines work in any monad with access to `HashSpec`. The experiment samples the master seed and charges every hash call, including repeated calls. Out-of-range branches only make the definitions total; honest algorithms never reach them. -/

/-- A hash query takes an arbitrary byte string and returns 32 bytes. -/
abbrev HashSpec := HashInput →ₒ HashOutput

/-- Private uniform sampling and the shared hash oracle. Only hash calls count toward the query budget. -/
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

/-- `m || rho`: with `P || A`, 80 bytes, one block of the leanVM hash, so a trial is one Keccak-f
permutation. -/
def encodingPayload (message : Message) (randomness : Randomness) : HashInput :=
  bytesLE 32 message ++ bytesLE 16 randomness

/-- `pk_0 || ... || pk_{v-1}`. -/
def leafPayload (endpoints : ChainIndex → Digest) : HashInput :=
  (List.ofFn endpoints).flatMap (bytesLE 16)

/-- `r_b || rho`: the top layer signs a 16-byte bottom root. -/
def topEncodingPayload (root : Digest) (randomness : Randomness) : HashInput :=
  bytesLE 16 root ++ bytesLE 16 randomness

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

/-- The digest `D` of `IncEnc(P, m, rho, idx)`. -/
def encodingHash (parameter : PublicParameter) (leafIndex : LeafIndex)
    (message : Message) (randomness : Randomness) : m Digest :=
  tweakableHash parameter (.encoding leafIndex) (encodingPayload message randomness)

/-- One chain step, under `tweak_chain(idx, i, step + 1)`. -/
def chainHash (parameter : PublicParameter) (leafIndex : LeafIndex) (chain : ChainIndex)
    (step : ChainStep) (value : Digest) : m Digest :=
  tweakableHash parameter (.chain leafIndex chain step) (bytesLE 16 value)

/-- `X_{0,idx}`, the hash of the `v` public values. -/
def leafHash (parameter : PublicParameter) (leafIndex : LeafIndex)
    (endpoints : ChainIndex → Digest) : m Digest :=
  tweakableHash parameter (.leaf leafIndex) (leafPayload endpoints)

/-- `X_{level+1,node}` from its two children. -/
def nodeHash (parameter : PublicParameter) (level : MerkleLevel) (node : MerkleNode)
    (left right : Digest) : m Digest :=
  tweakableHash parameter (.merkle level node) (nodePayload left right)

/-- The top layer's message digest of a bottom root. -/
def topEncodingHash (parameter : PublicParameter) (key : TopIndex)
    (root : Digest) (randomness : Randomness) : m Digest :=
  tweakableHash parameter (.topEncoding key) (topEncodingPayload root randomness)

def topChainHash (parameter : PublicParameter) (key : TopIndex) (chain : ChainIndex)
    (step : ChainStep) (value : Digest) : m Digest :=
  tweakableHash parameter (.topChain key chain step) (bytesLE 16 value)

def topLeafHash (parameter : PublicParameter) (key : TopIndex)
    (endpoints : ChainIndex → Digest) : m Digest :=
  tweakableHash parameter (.topLeaf key) (leafPayload endpoints)

def topNodeHash (parameter : PublicParameter) (level : MerkleLevel) (node : TopNode)
    (left right : Digest) : m Digest :=
  tweakableHash parameter (.topMerkle level node) (nodePayload left right)

/-! ### Verification -/

/-- `A_level`, or `0` above the tree. -/
def signaturePath (signature : Signature) (level : Nat) : Digest :=
  if hlevel : level < treeHeight then signature.authPath ⟨level, hlevel⟩ else 0

/-- `Chain_{i,idx}(P, start, steps, value)`: the step onto position `start + steps + 1` carries step `start + steps` in its address and `i` after its value. -/
def chainWalk (parameter : PublicParameter) (leafIndex : LeafIndex) (chain : ChainIndex) :
    Nat → Nat → Digest → m Digest
  | _, 0, value => pure value
  | position, steps + 1, value => do
      let previous ← chainWalk parameter leafIndex chain position steps value
      if hposition : position + steps < chainLength - 1 then
        chainHash parameter leafIndex chain ⟨position + steps, hposition⟩ previous
      else
        pure 0

/-- The verifier's half of a chain: walk the remaining `2^w - 1 - x_i` steps. -/
def recoverChain (parameter : PublicParameter) (leafIndex : LeafIndex) (chain : ChainIndex)
    (digit : Digit) (value : Digest) : m Digest :=
  chainWalk parameter leafIndex chain digit.val (chainLength - 1 - digit.val) value

/-- `pk'_{idx,i}` for every chain. -/
def recoverEndpoints (parameter : PublicParameter) (leafIndex : LeafIndex)
    (encoding : Encoding) (signature : Signature) :
    m (ChainIndex → Digest) :=
  sequenceFin fun chain =>
    recoverChain parameter leafIndex chain (encoding chain) (signature.chainValue chain)

/-- The index of the Merkle node on the path of `leafIndex` one level above `level`. -/
def nodeIndex (leafIndex : LeafIndex) (level : Nat) : MerkleNode :=
  ⟨leafIndex.val / 2 ^ (level + 1), by
    have hle := Nat.div_le_self leafIndex.val (2 ^ (level + 1))
    exact hle.trans_lt leafIndex.isLt⟩

/-- `Z_{level+1}` from `Z_level` and `A_level`, in the order bit `level` of the leaf index dictates. -/
def authenticationNodeHash (parameter : PublicParameter) (leafIndex : LeafIndex)
    (level : Nat) (current sibling : Digest) : m Digest :=
  if hlevel : level < treeHeight then
    if leafIndex.val.testBit level then
      nodeHash parameter ⟨level, hlevel⟩ (nodeIndex leafIndex level) sibling current
    else
      nodeHash parameter ⟨level, hlevel⟩ (nodeIndex leafIndex level) current sibling
  else
    pure 0

/-- `Z_levels`, folded up from the leaf `Z_0`. -/
def authenticationRoot (parameter : PublicParameter) (leafIndex : LeafIndex)
    (signature : Signature) : Nat → Digest → m Digest
  | 0, leaf => pure leaf
  | levels + 1, leaf => do
      let current ← authenticationRoot parameter leafIndex signature levels leaf
      authenticationNodeHash parameter leafIndex levels current (signaturePath signature levels)

/-- A top chain walk, as `chainWalk`. -/
def topChainWalk (parameter : PublicParameter) (key : TopIndex) (chain : ChainIndex) :
    Nat → Nat → Digest → m Digest
  | _, 0, value => pure value
  | position, steps + 1, value => do
      let previous ← topChainWalk parameter key chain position steps value
      if hposition : position + steps < chainLength - 1 then
        topChainHash parameter key chain ⟨position + steps, hposition⟩ previous
      else
        pure 0

/-- The top node on the path of key `b` one level above `level`. -/
def topNodeIndex (key : TopIndex) (level : Nat) : TopNode :=
  ⟨key.val / 2 ^ (level + 1), by
    have hle := Nat.div_le_self key.val (2 ^ (level + 1))
    exact hle.trans_lt key.isLt⟩

/-- `Z_levels` of the top tree, folded up from the top leaf. -/
def topAuthenticationRoot (parameter : PublicParameter) (key : TopIndex)
    (path : Fin treeHeight → Digest) : Nat → Digest → m Digest
  | 0, leaf => pure leaf
  | levels + 1, leaf => do
      let current ← topAuthenticationRoot parameter key path levels leaf
      if hlevel : levels < treeHeight then
        let sibling := path ⟨levels, hlevel⟩
        if key.val.testBit levels then
          topNodeHash parameter ⟨levels, hlevel⟩ (topNodeIndex key levels) sibling current
        else
          topNodeHash parameter ⟨levels, hlevel⟩ (topNodeIndex key levels) current sibling
      else
        pure 0

/-- The top layer's check: its signature of bottom root `root` by key `b` reaches the public root. -/
def verifyTop (publicKey : PublicKey) (key : TopIndex) (root : Digest) (part : LayerSignature) :
    m Bool := do
  let digest ← topEncodingHash publicKey.parameter key root part.randomness
  let some encoding := TargetSum.decodeDigest digest | return false
  let endpoints ← sequenceFin fun chain =>
    topChainWalk publicKey.parameter key chain (encoding chain).val
      (chainLength - 1 - (encoding chain).val) (part.chainValue chain)
  let leaf ← topLeafHash publicKey.parameter key endpoints
  let topRoot ← topAuthenticationRoot publicKey.parameter key part.authPath treeHeight leaf
  return decide (topRoot = publicKey.root)

/-- Fold the bottom leaf to its tree's root, then check the top layer's signature of that root. -/
def verifyAfterLeaf
    (publicKey : PublicKey) (leafIndex : LeafIndex) (signature : Signature) (leaf : Digest) : m Bool := do
  let root ← authenticationRoot publicKey.parameter leafIndex signature treeHeight leaf
  verifyTop publicKey (topKeyOf leafIndex) root signature.top

/-- `Ver(pk, idx, m, sigma)`. -/
def verify (publicKey : PublicKey) (leafIndex : LeafIndex)
    (message : Message) (signature : Signature) : m Bool := do
  let digest ← encodingHash publicKey.parameter leafIndex message signature.randomness
  let some encoding := TargetSum.decodeDigest digest | return false
  let endpoints ← recoverEndpoints publicKey.parameter leafIndex encoding signature
  let leaf ← leafHash publicKey.parameter leafIndex endpoints
  verifyAfterLeaf publicKey leafIndex signature leaf

/-! ### Precomputed chains and tree -/

/-- `pk_{idx,i} = Chain(P, 0, 2^w - 1, sk_{idx,i})` for every chain. -/
def oneTimePublicKey (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (leafIndex : LeafIndex) : m (ChainIndex → Digest) :=
  sequenceFin fun chain =>
    chainWalk parameter leafIndex chain 0 (chainLength - 1) (secret leafIndex chain)

/-- `X_{0,idx}` from the secrets. -/
def leafAt (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (leafIndex : LeafIndex) : m Digest := do
  let endpoints ← oneTimePublicKey parameter secret leafIndex
  leafHash parameter leafIndex endpoints

/-- A natural read as a node index. -/
def merkleNodeOfNat (value : Nat) : MerkleNode :=
  ⟨value % lifetime,
    Nat.mod_lt _ (by simp [lifetime])⟩

/-- `2j` or `2j + 1`. -/
def childNode (node : MerkleNode) (right : Bool) : MerkleNode :=
  merkleNodeOfNat (2 * node.val + if right then 1 else 0)

/-- `X_{levels,node}`, the Merkle tree over the one-time leaves. -/
def treeNode (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest) :
    Nat → MerkleNode → m Digest
  | 0, node => leafAt parameter secret node
  | levels + 1, node => do
      let left ← treeNode parameter secret levels (childNode node false)
      let right ← treeNode parameter secret levels (childNode node true)
      if hlevel : levels < treeHeight then
        nodeHash parameter ⟨levels, hlevel⟩ node left right
      else
        pure 0

/-- The root of bottom tree `b`: node `b` of level `h`. -/
def bottomRootNode (key : TopIndex) : MerkleNode :=
  ⟨key.val, key.isLt.trans_le (Nat.pow_le_pow_right (by decide) (by simp [treeHeight]))⟩

/-- The top chain ends of key `b`. -/
def topOneTimePublicKey (parameter : PublicParameter) (topSecret : TopIndex → ChainIndex → Digest)
    (key : TopIndex) : m (ChainIndex → Digest) :=
  sequenceFin fun chain =>
    topChainWalk parameter key chain 0 (chainLength - 1) (topSecret key chain)

/-- The top leaf of key `b`. -/
def topLeafAt (parameter : PublicParameter) (topSecret : TopIndex → ChainIndex → Digest)
    (key : TopIndex) : m Digest := do
  let endpoints ← topOneTimePublicKey parameter topSecret key
  topLeafHash parameter key endpoints

def topNodeOfNat (value : Nat) : TopNode :=
  ⟨value % topLifetime, Nat.mod_lt _ (by simp [topLifetime])⟩

def topChildNode (node : TopNode) (right : Bool) : TopNode :=
  topNodeOfNat (2 * node.val + if right then 1 else 0)

/-- `X_{levels,node}` of the top tree. -/
def topTreeNode (parameter : PublicParameter) (topSecret : TopIndex → ChainIndex → Digest) :
    Nat → TopNode → m Digest
  | 0, node => topLeafAt parameter topSecret node
  | levels + 1, node => do
      let left ← topTreeNode parameter topSecret levels (topChildNode node false)
      let right ← topTreeNode parameter topSecret levels (topChildNode node true)
      if hlevel : levels < treeHeight then
        topNodeHash parameter ⟨levels, hlevel⟩ node left right
      else
        pure 0

/-- The public root is node `0` of the top tree's level `h`. -/
def rootNode : TopNode :=
  ⟨0, by simp [topLifetime]⟩

/-- The top grinding of bottom root `root` by key `b` from the base `R0`: the least trial whose digest
is a codeword, with that codeword. -/
def topSignFrom (parameter : PublicParameter) (key : TopIndex) (root : Digest) (base : Randomness) :
    Nat → Nat → m (Option (Randomness × Encoding))
  | 0, _ => pure none
  | attempts + 1, trial => do
      let randomness := base + BitVec.ofNat randomnessBits trial
      let digest ← topEncodingHash parameter key root randomness
      match TargetSum.decodeDigest digest with
      | some encoding => return some (randomness, encoding)
      | none => topSignFrom parameter key root base attempts (trial + 1)

/-- The honest computation of key generation: every bottom root and its top signature (from the base
`topBase b r_b`), then the top tree's root. -/
def honestKeygen (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (topSecret : TopIndex → ChainIndex → Digest) (topBase : TopIndex → Digest → m Randomness) :
    m (Digest × (TopIndex → Option (Randomness × Encoding))) := do
  let topSigned ← sequenceFin fun key => do
    let bottomRoot ← treeNode parameter secret treeHeight (bottomRootNode key)
    let base ← topBase key bottomRoot
    topSignFrom parameter key bottomRoot base signingAttemptLimit 0
  let root ← topTreeNode parameter topSecret treeHeight rootNode
  return (root, topSigned)

/-- Answer a hash query from a recorded query cache, and by 0 for an unrecorded input. -/
def replayHash (cache : QueryCache HashSpec) : QueryImpl HashSpec Id :=
  fun input => (cache input).getD 0

/-- Compute the stored chain values and nodes of both layers by replaying the key-generation query
log. -/
def precomputedSecretKey (parameter : PublicParameter)
    (secret : LeafIndex → ChainIndex → Digest) (topSecret : TopIndex → ChainIndex → Digest)
    (topSigned : TopIndex → Option (Randomness × Encoding)) (cache : QueryCache HashSpec) :
    SecretKey where
  parameter := parameter
  chainStart := secret
  chainValue := fun leafIndex chain digit =>
    evalWithAnswerFn (replayHash cache)
      (chainWalk parameter leafIndex chain 0 digit.val (secret leafIndex chain) :
        OracleComp HashSpec Digest)
  treeValue := fun height node =>
    evalWithAnswerFn (replayHash cache)
      (treeNode parameter secret height.val node : OracleComp HashSpec Digest)
  topChainStart := topSecret
  topChainValue := fun key chain digit =>
    evalWithAnswerFn (replayHash cache)
      (topChainWalk parameter key chain 0 digit.val (topSecret key chain) :
        OracleComp HashSpec Digest)
  topTreeValue := fun height node =>
    evalWithAnswerFn (replayHash cache)
      (topTreeNode parameter topSecret height.val node : OracleComp HashSpec Digest)
  topSigned := topSigned

/-! ### Signing -/

/-- `floor(idx / 2^level) xor 1`, the sibling on the path. -/
def authenticationPathNode (leafIndex : LeafIndex) (level : MerkleLevel) : MerkleNode :=
  merkleNodeOfNat (Nat.xor (leafIndex.val / 2 ^ level.val) 1)

/-- The sibling on the top path of key `b`. -/
def topPathNode (key : TopIndex) (level : MerkleLevel) : TopNode :=
  topNodeOfNat (Nat.xor (key.val / 2 ^ level.val) 1)

/-- The top layer's signature of bottom tree `b`, read from the key (zeros if its grinding failed). -/
def topPart (secretKey : SecretKey) (key : TopIndex) : LayerSignature :=
  match secretKey.topSigned key with
  | some (randomness, encoding) =>
      { randomness := randomness
        chainValue := fun chain => secretKey.topChainValue key chain (encoding chain)
        authPath := fun level => secretKey.topTreeValue level.castSucc (topPathNode key level) }
  | none => ⟨0, fun _ => 0, fun _ => 0⟩

/-- The signature once the encoding is found. -/
def precomputedSignWithEncoding (secretKey : SecretKey) (leafIndex : LeafIndex)
    (randomness : Randomness) (encoding : Encoding) : Signature :=
  { randomness := randomness
    chainValue := fun chain => secretKey.chainValue leafIndex chain (encoding chain)
    authPath := fun level => secretKey.treeValue level.castSucc (authenticationPathNode leafIndex level)
    top := topPart secretKey (topKeyOf leafIndex) }

/-- One attempt: hash once, and sign if the digest encodes. -/
def precomputedSignAttempt (secretKey : SecretKey) (leafIndex : LeafIndex)
    (message : Message) (randomness : Randomness) : m (Option Signature) := do
  let digest ← encodingHash secretKey.parameter leafIndex message randomness
  let some encoding := TargetSum.decodeDigest digest | return none
  return some (precomputedSignWithEncoding secretKey leafIndex randomness encoding)

/-- Signing fails at every leaf index of a bottom tree whose top grinding failed. -/
def topSignedAt (secretKey : SecretKey) (leafIndex : LeafIndex) : Bool :=
  (secretKey.topSigned (topKeyOf leafIndex)).isSome

attribute [irreducible] verifyAfterLeaf treeNode

end Concrete

variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]

def deriveKey (parameter : PublicParameter) (domain : KeygenDomain) (seed : MasterSeed) : m Digest := do
  return truncateHash (← Concrete.oracleHash (keygenHashInput parameter domain seed))

/-- One seed derivation, all 32 bytes: the starts of two chains are its halves. -/
def deriveOutput (parameter : PublicParameter) (domain : KeygenDomain) (seed : MasterSeed) :
    m HashOutput :=
  Concrete.oracleHash (keygenHashInput parameter domain seed)

/-- `R0 = Th(P, A_rnd(idx), S || m)`. -/
def deriveRandomizer (parameter : PublicParameter) (seed : MasterSeed) (leafIndex : LeafIndex)
    (message : Message) : m Randomness := do
  return (← Concrete.oracleHash (randomizerHashInput parameter seed leafIndex message)).extractLsb' 0 randomnessBits

/-- `R0` of the top signature of bottom tree `b`. -/
def deriveTopRandomizer (parameter : PublicParameter) (seed : MasterSeed) (key : TopIndex)
    (root : Digest) : m Randomness := do
  return truncateHash (← Concrete.oracleHash (topRandomizerHashInput parameter seed key root))

/-- The chain starts of every bottom key, from 29 derivations each. -/
def deriveSecrets (parameter : PublicParameter) (seed : MasterSeed) :
    m (LeafIndex → ChainIndex → Digest) := do
  let outputs ← Concrete.sequenceFin fun leafIndex => Concrete.sequenceFin fun pair =>
    deriveOutput parameter (.chain leafIndex pair) seed
  return fun leafIndex chain => hashHalf chain.val (outputs leafIndex (chainPair chain))

/-- The chain starts of every top key. -/
def deriveTopSecrets (parameter : PublicParameter) (seed : MasterSeed) :
    m (TopIndex → ChainIndex → Digest) := do
  let outputs ← Concrete.sequenceFin fun key => Concrete.sequenceFin fun pair =>
    deriveOutput parameter (.topChain key pair) seed
  return fun key chain => hashHalf chain.val (outputs key (chainPair chain))

noncomputable def sampleMasterSeed : ProbComp MasterSeed :=
  letI := SampleableType.ofFintype MasterSeed
  $ᵗ MasterSeed

namespace Seeded

/-- The scheme's seed `S` and the chain and tree values and top signatures computed during key
generation. -/
structure SecretKey where
  seed : MasterSeed
  precomputed : XmssSecurity.SecretKey

/-- Hash the key's seed `S_0` into `S = H("leanXMSS" || S_0)`, derive the parameter and the secrets,
then compute and store both layers. -/
def keygenFromSeed (keySeed : MasterSeed) : OracleComp HashSpec (PublicKey × SecretKey) := do
  let seed ← Concrete.oracleHash (seedHashInput keySeed)
  let parameter ← deriveKey 0 .parameter seed
  let secret ← deriveSecrets parameter seed
  let topSecret ← deriveTopSecrets parameter seed
  let result ← (Concrete.honestKeygen parameter secret topSecret
    (deriveTopRandomizer parameter seed) : OracleComp HashSpec _).withQueryLog
  let precomputed := Concrete.precomputedSecretKey parameter secret topSecret result.1.2
    (hashCacheOfLog result.2)
  return (⟨result.1.1, parameter⟩, ⟨seed, precomputed⟩)

/-- Try the randomizers `base + trial, base + trial + 1, ...`, stopping at the first admissible
encoding. -/
def signFrom (secretKey : SecretKey) (leafIndex : LeafIndex) (message : Message) (base : Randomness) :
    Nat → Nat → m (Option Signature)
  | 0, _ => pure none
  | attempts + 1, trial => do
      let randomness := base + BitVec.ofNat randomnessBits trial
      match ← Concrete.precomputedSignAttempt secretKey.precomputed leafIndex message randomness with
      | some signature => return some signature
      | none => signFrom secretKey leafIndex message base attempts (trial + 1)

/-- Derive `R0`, take the least admissible trial `R0 + c`, `c < A_max`, and attach the top signature;
fail if the bottom tree has none. -/
def sign (secretKey : SecretKey) (leafIndex : LeafIndex) (message : Message) : m (Option Signature) := do
  let base ← deriveRandomizer secretKey.precomputed.parameter secretKey.seed leafIndex message
  let result ← signFrom secretKey leafIndex message base signingAttemptLimit 0
  return if Concrete.topSignedAt secretKey.precomputed leafIndex then result else none

end Seeded

end XmssSecurity
