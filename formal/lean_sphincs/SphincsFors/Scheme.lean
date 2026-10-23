import VCVio.OracleComp.QueryTracking.LoggingOracle.Core
import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation

/-!
# The leanSPHINCS scheme

Adapted from leanVM, commit b7a107256, and the previous port draft.
The seeded signer models failure after 2^32 attempts explicitly. The Rust randomizer loop
is unbounded at the source level over a u32 counter; see PROOF.md for that mismatch.

Parameters, serialized hash inputs, key generation, signing, and verification of the scheme in
`leanSPHINCS.tex`, with the hash inputs of `crates/sphincs`: the 16-byte public parameter, the
16-byte address of the call (8 bytes of fields, then 8 zero bytes), then the payload. One XMSS tree of height
`h = 26`, WOTS+C with `64` chains of length `4` and target sum `120`, and FORS with `k = 24`
trees of `2^a = 1024` leaves, `a = 10`. A FORS tree has no root hash: the FORS key hashes the two
nodes of level `a - 1 = 9` of every tree. A pruned key keeps one subtree of `2^b` leaves, placed by the low bits of
the public parameter, and replaces the `26 - b` siblings above it by surrogates derived from the
seed; the signer grinds its randomizer until the leaf index lands in the kept subtree. `b = 26` is
the full key.
-/

open OracleComp OracleSpec ENNReal

namespace SphincsFors

/-! ## The instance: parameters, types, and hash-input layout -/

def digestBits : Nat := 128
def hashOutputBits : Nat := 256
def messageBits : Nat := 256
def publicParameterBits : Nat := 128
def counterBits : Nat := 32
def winternitzBits : Nat := 2
def chainLength : Nat := 2 ^ winternitzBits
def numChains : Nat := 64
def targetSum : Nat := 120
def numLayers : Nat := 1
def totalHeight : Nat := 26
/-- The height of the only XMSS layer, which bounds its leaf index. -/
def maxLayerHeight : Nat := 26
def ftsTreeHeight : Nat := 10
/-- The level of the two top nodes of a FORS tree, `a - 1 = 9`. The node of level `a` is not
computed. -/
def ftsTopLevel : Nat := ftsTreeHeight - 1
/-- The `k` FORS trees, one per index group of the digest. -/
def ftsTrees : Nat := 24
/-- Randomizers tried per signature (`ctr` is a `u32`), `A_max`. -/
def digestAttemptLimit : Nat := 2 ^ 32
/-- Encoding counters tried per signature, `C_max`. -/
def encodingAttemptLimit : Nat := 2 ^ 32

/-- The key's shape and lifetime: the kept subtree holds `2^subtreeHeight` leaves
(`subtreeHeight = 26` is the full key), and the key signs at most `signatureLimit` messages. -/
class Params where
  subtreeHeight : Nat
  signatureLimit : Nat
  subtreeHeight_le : subtreeHeight ≤ totalHeight

export Params (subtreeHeight signatureLimit)

abbrev MasterSeed := BitVec 256

abbrev Digest := BitVec digestBits
abbrev HashOutput := BitVec hashOutputBits
abbrev Message := BitVec messageBits
abbrev PublicParameter := BitVec publicParameterBits
abbrev Randomness := Digest
abbrev Counter := BitVec counterBits
abbrev Layer := Fin numLayers
/-- `idx`, the leaf and the FORS instance a digest selects. -/
abbrev Index := Fin (2 ^ totalHeight)
/-- `tau`, always `0`: the scheme has one tree, and a hash address has no tree field. -/
abbrev TreeIndex := Fin 1
/-- `e`, a leaf of the tree. -/
abbrev LeafIndex := Fin (2 ^ maxLayerHeight)
abbrev ChainIndex := Fin numChains
abbrev Digit := Fin chainLength
abbrev ChainStep := Fin (chainLength - 1)
/-- A FORS tree, `kappa < k`. -/
abbrev FtsTree := Fin ftsTrees
/-- An index group of the message digest, `kappa < k`; group `kappa` selects the leaf of tree `kappa`. -/
abbrev IndexGroup := Fin ftsTrees
abbrev FtsLeaf := Fin (2 ^ ftsTreeHeight)
abbrev Encoding := ChainIndex → Digit
abbrev HashInput := List UInt8

/-- The layer height, `h = 26`. -/
def layerHeight (_lay : Layer) : Nat := maxLayerHeight

def topLayer : Layer := ⟨0, by decide⟩

/-- `sum_{j < lay} h_j`, the index bits above layer `lay`. -/
def heightAbove (lay : Layer) : Nat := ∑ j : Layer, if j.val < lay.val then layerHeight j else 0

/-- `sum_{j > lay} h_j`, the index bits below layer `lay`. -/
def heightBelow (lay : Layer) : Nat := totalHeight - heightAbove lay - layerHeight lay

/-- Keep the first 128 output bits, the low bits of the little-endian bit vector. -/
def truncateHash (output : HashOutput) : Digest :=
  output.extractLsb' 0 digestBits

/-- The message digest is `h + k * a = 266` bits, an index and `k` leaf indices. -/
def messageDigestBits : Nat := totalHeight + ftsTrees * ftsTreeHeight

abbrev MessageDigest := BitVec messageDigestBits

/-- The FORS indices one digest call gives: `12` fields of `a = 10` bits, six in each of the first
two 64-bit words of the output (bits `0 .. 59` and `64 .. 123`). The top four bits of each word
are not used. -/
def callIndices (output : HashOutput) : BitVec 120 :=
  output.extractLsb' 64 60 ++ output.extractLsb' 0 60

/-- The fields call `0` gives, the index first: the low `h = 26` bits of the last 16 bytes of the
output (bits `128 .. 153`), then its `12` FORS indices. -/
def firstCallFields (first : HashOutput) : BitVec 146 :=
  callIndices first ++ first.extractLsb' 128 totalHeight

/-- The fields of the two digest calls, as one string of `h + k * a` bits: the index, then the
`k = 24` FORS indices in order (`digest_fields` in `crates/sphincs/src/scheme.rs`). The index is bits
`128 .. 153` of call `0`. FORS index `kappa` is in call `kappa / 12`, at bit
`64 * ((kappa % 12) / 6) + 10 * (kappa % 6)`: no field lies across two 64-bit words. -/
def truncateMessageDigest (first second : HashOutput) : MessageDigest :=
  (callIndices second ++ firstCallFields first).extractLsb' 0 messageDigestBits

/-- `pk = (root, P)`. -/
structure PublicKey where
  root : Digest
  parameter : PublicParameter
deriving DecidableEq

/-- The WOTS+C signature and authentication path. -/
structure LayerSignature (lay : Layer) where
  counter : Counter
  chainValues : ChainIndex → Digest
  path : Fin (layerHeight lay) → Digest
deriving DecidableEq

/-- The randomizer, the FORS openings, and the WOTS+C signature with its path: 5684 bytes. -/
structure Signature where
  randomness : Randomness
  ftsSecret : FtsTree → Digest
  ftsPath : FtsTree → Fin ftsTreeHeight → Digest
  layers : (lay : Layer) → LayerSignature lay
deriving DecidableEq

/-- Serialize a bit vector into a fixed number of bytes, least significant byte first. -/
def bytesLE (byteCount : Nat) (value : BitVec (8 * byteCount)) : List UInt8 :=
  List.ofFn fun index : Fin byteCount =>
    UInt8.ofBitVec (value.extractLsb' (8 * index.val) 8)

/-- The address of a hash call (`Tweak` in `crates/sphincs`): the hash type `tag < 32`, a chain step
`step < 8`, and two fields `hi < 2^24` and `lo < 2^32`. -/
structure TweakFields where
  tag : BitVec 5
  step : BitVec 3
  hi : BitVec 24
  lo : BitVec 32
deriving DecidableEq

/-- The 16 address bytes `A` that follow `P` in every hash input: `lo` (4 bytes) and `hi` (3 bytes),
least significant byte first, one byte `type + 32 * step`, then 8 zero bytes. With `P` they fill
half a block, so every value of a payload starts on a 16-byte boundary. -/
def fieldBytes (fields : TweakFields) : HashInput :=
  bytesLE 4 fields.lo ++ bytesLE 3 fields.hi ++
    bytesLE 1 (BitVec.ofNat 8 (fields.tag.toNat + 32 * fields.step.toNat)) ++ List.replicate 8 0

/-- Convert the four integer fields to their fixed widths. -/
def tweakFields (tag step hi lo : Nat) : TweakFields :=
  ⟨BitVec.ofNat 5 tag, BitVec.ofNat 3 step, BitVec.ofNat 24 hi, BitVec.ofNat 32 lo⟩

/-- The verification hash domains. Seed derivation uses `KeygenDomain`. -/
inductive HashDomain where
  | chain (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (chainIdx : ChainIndex) (step : ChainStep)
  | leaf (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
  | node (lay : Layer) (tree : TreeIndex) (level : Nat) (nodeIdx : Nat)
  | encoding (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
  | ftsLeaf (index : Index) (tree : FtsTree) (leaf : FtsLeaf)
  | ftsNode (index : Index) (tree : FtsTree) (level : Nat) (nodeIdx : Nat)
  /-- The FORS key hash of instance `index`, over the two top nodes of every tree. -/
  | ftsRoots (index : Index)
  | message (call : Fin 2)
deriving DecidableEq

/-- The address fields of a hash domain (`TWEAK_CHAIN = 1`, ..., `TWEAK_MSG = 12`). In the tree,
`lo` is the leaf or the node index and `hi` the chain or the level; the layer and the tree, always
`0`, are not serialized. In a FORS instance `lo` is the index `idx` and `hi` packs the tree `kappa`,
the level and the leaf or node index as `kappa + 32 * level + 512 * j`. -/
def hashDomainFields : HashDomain → TweakFields
  | .chain _ _ leaf chainIdx step => tweakFields 1 step chainIdx leaf
  | .leaf _ _ leaf => tweakFields 2 0 0 leaf
  | .node _ _ level nodeIdx => tweakFields 3 0 level nodeIdx
  | .encoding _ _ leaf => tweakFields 4 0 0 leaf
  | .ftsLeaf index tree leaf => tweakFields 9 0 (tree + 512 * leaf) index
  | .ftsNode index tree level nodeIdx => tweakFields 10 0 (tree + 32 * level + 512 * nodeIdx) index
  | .ftsRoots index => tweakFields 11 0 0 index
  | .message call => tweakFields 12 0 call 0

/-- The exact 16 address bytes of a hash domain. -/
def tweakBytes (domain : HashDomain) : HashInput :=
  fieldBytes (hashDomainFields domain)

/-- The random-oracle input `parameter || address || message` of every tweakable hash call and of
the message digest. -/
def tweakableHashInput (parameter : PublicParameter) (domain : HashDomain)
    (message : HashInput) : HashInput :=
  bytesLE 16 parameter ++ tweakBytes domain ++ message

/-- `P || A(7, 0, 0) || S || m` (`TWEAK_RANDOMIZER = 7`): the input of the base randomizer `R0` of a
message, one hash per message. -/
def randomizerHashInput (parameter : PublicParameter) (seed : MasterSeed)
    (message : Message) : HashInput :=
  bytesLE 16 parameter ++ fieldBytes ⟨7#5, 0#3, 0#24, 0#32⟩ ++
    bytesLE 32 seed ++ bytesLE 32 message

/-- Keep output bits `128 .. 255`, bytes `16 .. 31` of the hash output. -/
def truncateHashHigh (output : HashOutput) : Digest :=
  output.extractLsb' digestBits digestBits

/-- The values derived from the seed. A domain names one value; two values may share a hash. -/
inductive KeygenDomain where
  | parameter
  | ots (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (chain : ChainIndex)
  | fts (index : Index) (tree : FtsTree) (leaf : FtsLeaf)
  | surrogate (level : Fin totalHeight)
deriving DecidableEq

/-- `TWEAK_PARAMETER = 5`, `TWEAK_PRF = 0`, `TWEAK_FTS_PRF = 8`, `TWEAK_SURROGATE = 13`. One hash of
the seed gives two secrets: the starts of chains `2 t` and `2 t + 1` of a one-time key share the
address with `hi = t`, and the secrets of leaves `2 t` and `2 t + 1` of a FORS tree `kappa` share the
address with `hi = kappa + 512 * t` (`wots_secret_tweak`, `fors_secret_tweak`). -/
def keygenDomainFields : KeygenDomain → TweakFields
  | .parameter => tweakFields 5 0 0 0
  | .ots _ _ leaf chain => tweakFields 0 0 (chain / 2) leaf
  | .fts index tree leaf => tweakFields 8 0 (tree + 512 * (leaf / 2)) index
  | .surrogate level => tweakFields 13 0 level 0

/-- Whether a derived value is the second half (bytes `16 .. 31`) of its hash output: the odd chain
starts and the odd FORS secrets. Every other value is the first half. -/
def KeygenDomain.second : KeygenDomain → Bool
  | .ots _ _ _ chain => chain.val % 2 == 1
  | .fts _ _ leaf => leaf.val % 2 == 1
  | _ => false

/-- The half of the 32-byte output that is the value of this domain. -/
def secretHalf (domain : KeygenDomain) (output : HashOutput) : Digest :=
  if domain.second then truncateHashHigh output else truncateHash output

/-- `P || A || S`; parameter derivation uses `P = 0`. -/
def keygenHashInput (parameter : PublicParameter) (domain : KeygenDomain)
    (seed : MasterSeed) : HashInput :=
  bytesLE 16 parameter ++ fieldBytes (keygenDomainFields domain) ++ bytesLE 32 seed

/-! ### The target-sum code

`v = 64` chunks of `w = 2` bits covering the 128 digest bits, and the code is the words of digit sum
`T = 120`. Two distinct words of equal sum are incomparable, which is what removes the Winternitz
checksum and the reason why we need the counter. -/

namespace TargetSum

/-- The digit sum of a word. -/
def sum (x : Encoding) : Nat := ∑ i, (x i).val

/-- Membership in the code `C`: digit sum `T`. -/
def Valid (x : Encoding) : Prop := sum x = targetSum

instance : DecidablePred Valid :=
  fun x => inferInstanceAs (Decidable (sum x = targetSum))

/-- Offset of a two-bit digit. -/
def digitOffset (i : ChainIndex) : Nat := winternitzBits * i.val

/-- `x_i`, the two bits of the digest at the digit's offset. -/
def digestEncoding (digest : Digest) : Encoding :=
  fun i => (digest.extractLsb' (digitOffset i) winternitzBits).toFin

/-- A digest decodes exactly when its 64 digits reach the target sum. -/
def decodeDigest (digest : Digest) : Option Encoding :=
  if Valid (digestEncoding digest) then some (digestEncoding digest) else none

end TargetSum

/-! ## The algorithms

`Concrete` contains the hash and verification routines; `Seeded` contains key generation and
signing. Hashing routines work in any monad with access to `HashSpec`. The experiment samples the
master seed and charges every hash call, including repeated calls. Out-of-range branches only make
the definitions total; honest algorithms never reach them. -/

/-- A hash query takes an arbitrary byte string and returns 32 bytes. -/
abbrev HashSpec := HashInput →ₒ HashOutput

/-- Private uniform sampling and the shared hash oracle. Only hash calls count toward the query budget. -/
abbrev OracleWorld := unifSpec + HashSpec

namespace Concrete

/-- Run the `n` computations in index order and collect their results. -/
def sequenceFin {m : Type → Type} [Monad m] {α : Type} {n : Nat}
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

/-- `Th(P, tw, M) = Truncate_n(H(P || A(tw) || M))`. -/
def tweakableHash (parameter : PublicParameter) (domain : HashDomain) (payload : HashInput) :
    m Digest := do
  let output ← oracleHash (tweakableHashInput parameter domain payload)
  return truncateHash output

/-! ### The index -/

/-- `tau`, the tree: `0`. -/
def treeIndexAt (_index : Index) (_lay : Layer) : TreeIndex := 0

/-- `e = idx`, the leaf. -/
def leafIndexAt (index : Index) (lay : Layer) : LeafIndex :=
  ⟨index.val / 2 ^ heightBelow lay % 2 ^ layerHeight lay,
    Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _)) (le_refl _)⟩

/-! ### The one-time signature -/

/-- A node index at level `0` read as a leaf index. -/
def leafOfNat (value : Nat) : LeafIndex :=
  ⟨value % 2 ^ maxLayerHeight, Nat.mod_lt _ (Nat.two_pow_pos _)⟩

/-- `steps` chain steps from position `start`: the step onto position `start + steps + 1` carries
step field `start + steps` (`chain_tweak` with `to = start + steps + 1`). -/
def chainWalk (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (chainIdx : ChainIndex) : Nat → Nat → Digest → m Digest
  | _, 0, value => pure value
  | start, steps + 1, value => do
      let previous ← chainWalk parameter lay tree leaf chainIdx start steps value
      if hstep : start + steps < chainLength - 1 then
        tweakableHash parameter (.chain lay tree leaf chainIdx ⟨start + steps, hstep⟩)
          (bytesLE 16 previous)
      else
        pure 0

/-- The verifier's half of a chain: walk the remaining `3 - x_i` steps. -/
def recoverChain (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (chainIdx : ChainIndex) (digit : Digit) (value : Digest) : m Digest :=
  chainWalk parameter lay tree leaf chainIdx digit.val (chainLength - 1 - digit.val) value

/-- `pk_0 || ... || pk_{v-1}`. -/
def leafPayload (endpoints : ChainIndex → Digest) : HashInput :=
  (List.ofFn endpoints).flatMap (bytesLE 16)

/-- The one-time leaf: the hash of the `v` chain ends (`wots_leaf_hash`). -/
def leafHash (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (endpoints : ChainIndex → Digest) : m Digest :=
  tweakableHash parameter (.leaf lay tree leaf) (leafPayload endpoints)

/-- `Enc(P, e, M, c)`: hash the message with the counter under the leaf's encoding tweak, and decode. -/
def encode (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (message : Digest) (counter : Counter) : m (Option Encoding) := do
  let digest ← tweakableHash parameter (.encoding lay tree leaf)
    (bytesLE 16 message ++ bytesLE 4 counter)
  return TargetSum.decodeDigest digest

/-- `Ots.leaf` (`wots_recover`): the verifier's leaf, or nothing if the counter does not encode the message. -/
def otsLeaf (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (message : Digest) (counter : Counter) (values : ChainIndex → Digest) : m (Option Digest) := do
  let some encoding ← encode parameter lay tree leaf message counter | return none
  let endpoints ← sequenceFin fun chainIdx =>
    recoverChain parameter lay tree leaf chainIdx (encoding chainIdx) (values chainIdx)
  let value ← leafHash parameter lay tree leaf endpoints
  return some value

/-! ### The tree -/

/-- The two children of a Merkle node. -/
def nodePayload (left right : Digest) : HashInput :=
  bytesLE 16 left ++ bytesLE 16 right

/-- `Tree.fold` (`tree_fold`): fold a leaf and a path into the root. -/
def treeFold (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (path : Nat → Digest) : Nat → Digest → m Digest
  | 0, value => pure value
  | levels + 1, value => do
      let current ← treeFold parameter lay tree leaf path levels value
      let sibling := path levels
      let nodeIdx := leaf.val / 2 ^ (levels + 1)
      if leaf.val.testBit levels then
        tweakableHash parameter (.node lay tree (levels + 1) nodeIdx) (nodePayload sibling current)
      else
        tweakableHash parameter (.node lay tree (levels + 1) nodeIdx) (nodePayload current sibling)

/-! ### FORS -/

/-- A node index at level `0` read as a leaf index. -/
def ftsLeafOfNat (value : Nat) : FtsLeaf :=
  ⟨value % 2 ^ ftsTreeHeight, Nat.mod_lt _ (Nat.two_pow_pos _)⟩

/-- The index group of the digest that selects this tree's leaf: its own. -/
def ftsIndexOf (tree : FtsTree) : IndexGroup := tree

/-- The hash of one FORS secret (`fors_leaf`). -/
def ftsLeafHash (parameter : PublicParameter) (index : Index) (tree : FtsTree) (leaf : FtsLeaf)
    (secret : Digest) : m Digest :=
  tweakableHash parameter (.ftsLeaf index tree leaf) (bytesLE 16 secret)

/-- The payload of the FORS key hash: the two top nodes (level `a - 1`, node `0` then node `1`) of
each of the `k` trees, `48` values (`fors_key_of_tops`). -/
def ftsTopsPayload (tops : FtsTree → Digest × Digest) : HashInput :=
  (List.ofFn tops).flatMap fun pair => nodePayload pair.1 pair.2

/-- The two top nodes in node order: the node on the side of the opened leaf, and the other one,
which is the last element of the path. -/
def ftsTopPair (leaf : FtsLeaf) (node other : Digest) : Digest × Digest :=
  if leaf.val.testBit ftsTopLevel then (other, node) else (node, other)

/-- The verifier's half of one FORS tree. -/
def ftsFold (parameter : PublicParameter) (index : Index) (tree : FtsTree) (leaf : FtsLeaf)
    (path : Fin ftsTreeHeight → Digest) : Nat → Digest → m Digest
  | 0, value => pure value
  | levels + 1, value => do
      let current ← ftsFold parameter index tree leaf path levels value
      let sibling := if hlevel : levels < ftsTreeHeight then path ⟨levels, hlevel⟩ else 0
      let nodeIdx := leaf.val / 2 ^ (levels + 1)
      if leaf.val.testBit levels then
        tweakableHash parameter (.ftsNode index tree (levels + 1) nodeIdx)
          (nodePayload sibling current)
      else
        tweakableHash parameter (.ftsNode index tree (levels + 1) nodeIdx)
          (nodePayload current sibling)

/-- `Fts.recover` (`fors_recover`): the FORS key an opening reaches. Per tree, the leaf is folded
with path elements `0 .. a - 2` into the top node on its side; path element `a - 1` is the other
top node and is not hashed with it. The key is the hash of the `2 k` top nodes. -/
def ftsRecover (parameter : PublicParameter) (index : Index) (leaves : IndexGroup → FtsLeaf)
    (secrets : FtsTree → Digest) (paths : FtsTree → Fin ftsTreeHeight → Digest) : m Digest := do
  let tops ← sequenceFin fun tree => do
    let leaf := leaves (ftsIndexOf tree)
    let value ← ftsLeafHash parameter index tree leaf (secrets tree)
    let node ← ftsFold parameter index tree leaf (paths tree) ftsTopLevel value
    return ftsTopPair leaf node (paths tree ⟨ftsTopLevel, by decide⟩)
  tweakableHash parameter (.ftsRoots index) (ftsTopsPayload tops)

/-! ### The message digest -/

/-- `m || rho`, what the message digest hashes after the parameter and the address. The first
64-byte block is `P || A || m`, which a signer absorbs once per message; the second block is the
randomizer alone. `P` binds the key, so the root is not hashed: the argument is kept for the
callers. -/
def messageDigestPayload (_root : Digest) (message : Message) (randomness : Randomness) : HashInput :=
  bytesLE 32 message ++ bytesLE 16 randomness

/-- One untruncated digest call (`digest_block`). -/
def messageDigestCall (parameter : PublicParameter) (root : Digest) (message : Message)
    (randomness : Randomness) (call : Fin 2) : m HashOutput :=
  oracleHash (tweakableHashInput parameter (.message call) (messageDigestPayload root message randomness))

/-- `idx = N mod 2^h`. -/
def digestIndex (digest : MessageDigest) : Index :=
  (digest.extractLsb' 0 totalHeight).toFin

/-- The leaf index alone, from the first digest call (`index_of_block`): the low `h` bits of its
last 16 bytes. -/
def blockIndex (first : HashOutput) : Index :=
  (first.extractLsb' digestBits totalHeight).toFin

/-- `Digest(P, m, rho)` (`message_digest`): the `h + k * a` field bits of calls `0` and `1`. The
root is not hashed. -/
def messageDigest (parameter : PublicParameter) (root : Digest) (message : Message)
    (randomness : Randomness) : m MessageDigest := do
  let first ← messageDigestCall parameter root message randomness 0
  let second ← messageDigestCall parameter root message randomness 1
  return truncateMessageDigest first second

/-- `u_kappa = floor(N / 2^(h + kappa * a)) mod 2^a`. -/
def digestLeaves (digest : MessageDigest) : IndexGroup → FtsLeaf :=
  fun tree => (digest.extractLsb' (totalHeight + ftsTreeHeight * tree.val) ftsTreeHeight).toFin

/-! ### Verification -/

/-- Read a layer's path, returning zero outside its height. -/
def signaturePath (signature : Signature) (lay : Layer) (level : Nat) : Digest :=
  if hlevel : level < layerHeight lay then (signature.layers lay).path ⟨level, hlevel⟩ else 0

/-- The tree walk: `remaining + 1` enters at layer `remaining`, and layer `0`'s fold returns the
value compared against the public root. -/
def verifyLayers (parameter : PublicParameter) (index : Index) (signature : Signature) :
    Nat → Digest → m (Option Digest)
  | 0, message => pure (some message)
  | remaining + 1, message => do
      if hlayer : remaining < numLayers then
        let lay : Layer := ⟨remaining, hlayer⟩
        let tree := treeIndexAt index lay
        let leaf := leafIndexAt index lay
        let part := signature.layers lay
        let some value ← otsLeaf parameter lay tree leaf message part.counter part.chainValues
          | return none
        let root ← treeFold parameter lay tree leaf (signaturePath signature lay) (layerHeight lay) value
        verifyLayers parameter index signature remaining root
      else
        pure none

/-- `Ver(pk, m, sigma)`: recompute the digest, recover the FORS key, recover the one-time leaf, fold
the path and compare with the root. -/
def verify (publicKey : PublicKey) (message : Message) (signature : Signature) : m Bool := do
  let digest ← messageDigest publicKey.parameter publicKey.root message signature.randomness
  let index := digestIndex digest
  let ftsPublicKey ← ftsRecover publicKey.parameter index (digestLeaves digest)
    signature.ftsSecret signature.ftsPath
  let some root ← verifyLayers publicKey.parameter index signature numLayers ftsPublicKey | return false
  return decide (root = publicKey.root)

/-! ### Signing -/

/-- The scheme has one tree, at index `0`. -/
def rootTree : TreeIndex := 0

/-- Run the layer, stopping on failure. -/
def sequenceLayers {α : Layer → Type}
    (computation : (lay : Layer) → m (Option (α lay))) : m (Option ((lay : Layer) → α lay)) := do
  let some top ← computation topLayer | return none
  return some (Fin.cases top (fun i => Fin.elim0 i))

attribute [irreducible] verify

end Concrete

/-! ### Pruning -/

section Pruning

variable [Params]

/-- `s`, the kept subtree: the low `h - b` bits of `P` (`0` for a full key). -/
def subtreePosition (parameter : PublicParameter) : Nat :=
  parameter.toNat % 2 ^ (totalHeight - subtreeHeight)

/-- The kept subtree holds leaves `s * 2^b .. (s + 1) * 2^b` (`XmssTree::contains`). -/
def Landed (parameter : PublicParameter) (index : Index) : Prop :=
  index.val / 2 ^ subtreeHeight = subtreePosition parameter

instance (parameter : PublicParameter) (index : Index) : Decidable (Landed parameter index) :=
  inferInstanceAs (Decidable (index.val / 2 ^ subtreeHeight = subtreePosition parameter))

end Pruning

/-- One derived value: one hash of the seed, of which the value is one 16-byte half. -/
def deriveKey {m : Type → Type} [Monad m] [HasQuery HashSpec m]
    (parameter : PublicParameter) (domain : KeygenDomain) (seed : MasterSeed) : m Digest := do
  return secretHalf domain (← Concrete.oracleHash (keygenHashInput parameter domain seed))

/-- Two derived values for one hash of the seed (`th_pair`): the two 16-byte halves of the output at
the address of `domain`. -/
def derivePair {m : Type → Type} [Monad m] [HasQuery HashSpec m]
    (parameter : PublicParameter) (domain : KeygenDomain) (seed : MasterSeed) : m (Digest × Digest) := do
  let output ← Concrete.oracleHash (keygenHashInput parameter domain seed)
  return (truncateHash output, truncateHashHigh output)

def deriveRandomizer {m : Type → Type} [Monad m] [HasQuery HashSpec m]
    (parameter : PublicParameter) (seed : MasterSeed)
    (message : Message) : m Randomness := do
  return truncateHash (← Concrete.oracleHash (randomizerHashInput parameter seed message))

noncomputable def sampleMasterSeed : ProbComp MasterSeed :=
  letI := SampleableType.ofFintype MasterSeed
  $ᵗ MasterSeed

namespace Seeded

open Concrete

structure SecretKey where
  seed : MasterSeed
  parameter : PublicParameter
  root : Digest

variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]

/-- Chains `2 t` and `2 t + 1`. -/
def evenChain (pair : Fin (numChains / 2)) : ChainIndex := ⟨2 * pair.val, by have := pair.isLt; simp only [numChains] at *; omega⟩
def oddChain (pair : Fin (numChains / 2)) : ChainIndex := ⟨2 * pair.val + 1, by have := pair.isLt; simp only [numChains] at *; omega⟩
/-- The pair `t` of chain `2 t` or `2 t + 1`. -/
def chainPair (chainIdx : ChainIndex) : Fin (numChains / 2) :=
  ⟨chainIdx.val / 2, by have := chainIdx.isLt; simp only [numChains] at *; omega⟩

/-- Read 32 pairs as 64 values: pair `t` holds the values of chains `2 t` and `2 t + 1`. -/
def unpairChains {α : Type} (pairs : Fin (numChains / 2) → α × α) : ChainIndex → α :=
  fun chainIdx => if chainIdx.val % 2 = 0 then (pairs (chainPair chainIdx)).1 else (pairs (chainPair chainIdx)).2

/-- Walk every chain of the one-time key at `leaf` from its start by `steps` (`wots_secrets`, then
`chain`): 32 hashes of the seed give the 64 starts, two per hash. -/
def otsValues (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (seed : MasterSeed) (steps : ChainIndex → Nat) : m (ChainIndex → Digest) := do
  let pairs ← sequenceFin fun pair : Fin (numChains / 2) => do
    let secrets ← derivePair parameter (.ots lay tree leaf (evenChain pair)) seed
    let first ← chainWalk parameter lay tree leaf (evenChain pair) 0 (steps (evenChain pair)) secrets.1
    let second ← chainWalk parameter lay tree leaf (oddChain pair) 0 (steps (oddChain pair)) secrets.2
    return (first, second)
  return unpairChains pairs

def oneTimePublicKey (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (seed : MasterSeed) : m (ChainIndex → Digest) :=
  otsValues parameter lay tree leaf seed fun _ => chainLength - 1

def otsSignFrom (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (seed : MasterSeed) (message : Digest) :
    Nat → Nat → m (Option (Counter × (ChainIndex → Digest)))
  | 0, _ => pure none
  | attempts + 1, counter => do
      match ← encode parameter lay tree leaf message (BitVec.ofNat counterBits counter) with
      | some encoding => do
          let values ← otsValues parameter lay tree leaf seed fun chainIdx => (encoding chainIdx).val
          return some (BitVec.ofNat counterBits counter, values)
      | none => otsSignFrom parameter lay tree leaf seed message attempts (counter + 1)

/-- `wots_sign`: the least admissible counter, then the opened chain values. -/
def otsSign (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (seed : MasterSeed) (message : Digest) :
    m (Option (Counter × (ChainIndex → Digest))) :=
  otsSignFrom parameter lay tree leaf seed message encodingAttemptLimit 0

/-- A node of the tree, computed from the one-time keys below it. -/
def treeNode (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (seed : MasterSeed) : Nat → Nat → m Digest
  | 0, nodeIdx => do
      let leaf := leafOfNat nodeIdx
      let endpoints ← oneTimePublicKey parameter lay tree leaf seed
      leafHash parameter lay tree leaf endpoints
  | level + 1, nodeIdx => do
      let left ← treeNode parameter lay tree seed level (2 * nodeIdx)
      let right ← treeNode parameter lay tree seed level (2 * nodeIdx + 1)
      tweakableHash parameter (.node lay tree (level + 1) nodeIdx) (nodePayload left right)

variable [Params]

/-- The surrogate sibling at `level >= b`, derived from the seed (`TWEAK_SURROGATE`). Honest calls
have `level < h`. -/
def surrogate (parameter : PublicParameter) (seed : MasterSeed) (level : Nat) : m Digest :=
  if hlevel : level < totalHeight then deriveKey parameter (.surrogate ⟨level, hlevel⟩) seed else pure 0

/-- The node at level `b + steps` above the kept subtree: the subtree root folded with the first
`steps` surrogates (`XmssTree::from_leaves`). -/
def spineNode (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (seed : MasterSeed) :
    Nat → m Digest
  | 0 => treeNode parameter lay tree seed subtreeHeight (subtreePosition parameter)
  | steps + 1 => do
      let below ← spineNode parameter lay tree seed steps
      let sibling ← surrogate parameter seed (subtreeHeight + steps)
      let nodeIdx := subtreePosition parameter / 2 ^ steps
      if nodeIdx.testBit 0 then
        tweakableHash parameter (.node lay tree (subtreeHeight + steps + 1) (nodeIdx / 2))
          (nodePayload sibling below)
      else
        tweakableHash parameter (.node lay tree (subtreeHeight + steps + 1) (nodeIdx / 2))
          (nodePayload below sibling)

/-- The root: the spine's top. -/
def treeRoot (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (seed : MasterSeed) : m Digest :=
  spineNode parameter lay tree seed (totalHeight - subtreeHeight)

/-- The authentication path of a kept leaf (`XmssTree::path`): subtree nodes below level `b`,
surrogates from level `b` on. -/
def treePath (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (seed : MasterSeed) (leaf : LeafIndex) : m (Fin (layerHeight lay) → Digest) :=
  sequenceFin fun level =>
    if level.val < subtreeHeight then
      treeNode parameter lay tree seed level.val (Nat.xor (leaf.val / 2 ^ level.val) 1)
    else
      surrogate parameter seed level.val

end Seeded

namespace Seeded

open Concrete

variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]

/-- A node of a FORS tree, computed from the secrets below it. A single leaf takes one hash of the
seed and uses one half of it; the two leaves under a level-1 node share one hash of the seed
(`fors_secret_pair`), so a subtree of `2^level` leaves, `level >= 1`, takes `2^(level-1)` of them. -/
def ftsNode (parameter : PublicParameter) (index : Index) (tree : FtsTree)
    (seed : MasterSeed) : Nat → Nat → m Digest
  | 0, nodeIdx => do
      let leaf := ftsLeafOfNat nodeIdx
      let secret ← deriveKey parameter (.fts index tree leaf) seed
      ftsLeafHash parameter index tree leaf secret
  | 1, nodeIdx => do
      let secrets ← derivePair parameter (.fts index tree (ftsLeafOfNat (2 * nodeIdx))) seed
      let left ← ftsLeafHash parameter index tree (ftsLeafOfNat (2 * nodeIdx)) secrets.1
      let right ← ftsLeafHash parameter index tree (ftsLeafOfNat (2 * nodeIdx + 1)) secrets.2
      tweakableHash parameter (.ftsNode index tree 1 nodeIdx) (nodePayload left right)
  | level + 2, nodeIdx => do
      let left ← ftsNode parameter index tree seed (level + 1) (2 * nodeIdx)
      let right ← ftsNode parameter index tree seed (level + 1) (2 * nodeIdx + 1)
      tweakableHash parameter (.ftsNode index tree (level + 2) nodeIdx) (nodePayload left right)

/-- The FORS key of instance `idx`: the two top nodes of every tree, then their hash. No tree is
hashed up to a root. -/
def ftsKey (parameter : PublicParameter) (index : Index)
    (seed : MasterSeed) : m Digest := do
  let tops ← sequenceFin fun tree => do
    let left ← ftsNode parameter index tree seed ftsTopLevel 0
    let right ← ftsNode parameter index tree seed ftsTopLevel 1
    return (left, right)
  tweakableHash parameter (.ftsRoots index) (ftsTopsPayload tops)

def ftsOpen (parameter : PublicParameter) (index : Index) (leaves : IndexGroup → FtsLeaf)
    (seed : MasterSeed) : m (FtsTree → Fin ftsTreeHeight → Digest) :=
  sequenceFin fun tree =>
    sequenceFin fun level =>
      ftsNode parameter index tree seed level.val
        (Nat.xor ((leaves (ftsIndexOf tree)).val / 2 ^ level.val) 1)

variable [Params]

/-- `Gen` (`key_gen`): derive the public parameter, which places the kept subtree, and build the root. -/
def keygenFromSeed (seed : MasterSeed) : OracleComp HashSpec (PublicKey × SecretKey) := do
  let parameter ← deriveKey 0 .parameter seed
  let root ← treeRoot parameter topLayer rootTree seed
  return (⟨root, parameter⟩, ⟨seed, parameter, root⟩)

/-- One grinding attempt: the leaf index of the first digest call (`digest_index`). -/
def signAttempt (secretKey : SecretKey) (message : Message) (randomness : Randomness) :
    m (Option Index) := do
  let first ← messageDigestCall secretKey.parameter secretKey.root message randomness 0
  if Landed secretKey.parameter (blockIndex first) then
    return some (blockIndex first)
  else
    return none

def layerMessage (secretKey : SecretKey) (index : Index) (_lay : Layer) : m Digest :=
  ftsKey secretKey.parameter index secretKey.seed

def signLayer (secretKey : SecretKey) (index : Index) (lay : Layer) : m (Option (LayerSignature lay)) := do
  let tree := treeIndexAt index lay
  let leaf := leafIndexAt index lay
  let message ← layerMessage secretKey index lay
  let some (counter, values) ← otsSign secretKey.parameter lay tree leaf secretKey.seed message
    | return none
  let path ← treePath secretKey.parameter lay tree secretKey.seed leaf
  return some ⟨counter, values, path⟩

/-- Grind from a randomizer: try `rho`, `rho + 1`, ... (little-endian 128-bit addition modulo
`2^128`), stopping at the first that lands in the kept subtree. -/
def signDigestLoop (secretKey : SecretKey) (message : Message) : Nat → Randomness →
    m (Option (Randomness × Index))
  | 0, _ => pure none
  | attempts + 1, randomness => do
      match ← signAttempt secretKey message randomness with
      | some index => return some (randomness, index)
      | none => signDigestLoop secretKey message attempts (randomness + 1)

/-- `Sign`: derive the base randomizer `R0` of the message, grind `R0 + i` into the kept subtree,
compute the digest, open FORS, sign its key with WOTS+C and attach the path. -/
def sign (secretKey : SecretKey) (message : Message) : m (Option Signature) := do
  let base ← deriveRandomizer secretKey.parameter secretKey.seed message
  let some (randomness, _) ← signDigestLoop secretKey message digestAttemptLimit base
    | return none
  let digest ← messageDigest secretKey.parameter secretKey.root message randomness
  let index := digestIndex digest
  let leaves := digestLeaves digest
  -- one hash of the seed per revealed secret, of which the secret is one half (`fors_secret`)
  let secrets ← sequenceFin fun tree =>
    deriveKey secretKey.parameter (.fts index tree (leaves (ftsIndexOf tree))) secretKey.seed
  let ftsPath ← ftsOpen secretKey.parameter index leaves secretKey.seed
  let some layers ← sequenceLayers (fun lay => signLayer secretKey index lay) | return none
  return some ⟨randomness, secrets, ftsPath, layers⟩

end Seeded

end SphincsFors
