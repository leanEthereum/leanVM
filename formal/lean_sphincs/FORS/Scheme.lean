import VCVio.OracleComp.QueryTracking.LoggingOracle
import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation
import Mathlib.Data.BitVec

/-!
# leanSPHINCS: SLH-DSA (FIPS 205) on Keccak-256 with WOTS+C

The scheme has a height `h = totalHeight` and a hypertree of `numLayers = d` layers whose layers below
the top have one height (`lowerHeight`, at least 6); key generation builds the whole top layer
(`subtreeHeight = h`, `Params.full`). The few-time signature under every bottom leaf is **FORS** with
`k = forsTrees` trees of height `a = forsHeight`, as FIPS 205 has it:

* a FORS leaf is `F` of a secret, and every secret is one `PRF` call on `SK.seed`;
* a tree is hashed up to its root, and the FORS public key is `T_k` of the `k` roots, the 16-byte
  message the bottom WOTS+C key signs;
* the digest `H_msg` is `⌈m / 32⌉` calls on `R || PK.seed || PK.root || M || BE_32(i)`, the message unframed
  (only `PRF_msg` frames it as `M'`), split as FIPS 205's
  Algorithm 19: the FORS leaves read most significant bit first, then the tree index and the bottom
  leaf as big-endian integers;
* an opening reveals, per tree, the secret of the selected leaf and its `a` auth nodes.

At every layer a WOTS+C key (64 chains of length 4, target sum 128) signs the 16-byte message of the
layer below: the FORS public key at the bottom layer, the root of the tree below at a layer above.
Layers are numbered from the top (`topLayer = 0`), as in leanVM. The secret key is a 32-byte seed
`SK.seed`, which is also FIPS 205's `SK.seed`: `PK.seed = Trunc_16(H(leanSPHINCS || SK.seed || 0))` and
`SK.prf = H(leanSPHINCS || SK.seed || 1)`. An addressed hash input is `PK.seed || ADRS || payload`, ADRS
being FIPS 205's 32-byte address of eight big-endian words: layer, three words of tree, type, key pair,
chain or height, hash or index. The randomizer is `R = Trunc_16(H(SK.prf || PK.seed || M'))`, with
`M' = 0x00 || 11 || leanSPHINCS || M`.

The model is one random oracle on these inputs; only the costs depend on the hash
(`Scheme/VerificationCost.lean`).
-/

open OracleComp OracleSpec ENNReal

namespace FORS

/-! ## The instance: parameters, types, and hash-input layout -/

def digestBits : Nat := 128
def hashOutputBits : Nat := 256
def messageBits : Nat := 256
def publicParameterBits : Nat := 128
def counterBits : Nat := 32
def winternitzBits : Nat := 2
def chainLength : Nat := 2 ^ winternitzBits
def numChains : Nat := 64
def targetSum : Nat := 128
/-- Randomizers tried per signature (`ctr` is a `u32`), `A_max`. -/
def digestAttemptLimit : Nat := 2 ^ 32
/-- Encoding counters tried per signature, `C_max`. -/
def encodingAttemptLimit : Nat := 2 ^ 32

/-- The key's shape and lifetime. The index has `totalHeight = h` bits. The key is a hypertree of
`numLayers = d` layers, every layer below the top one of height `lowerHeight ≥ 6` (`d = 1` is one
tree of height `h`). Key generation builds the whole top layer (`full`: `subtreeHeight = h`), so every
index lands and the kept subtree of the model's signer is the whole top tree. The key signs at most
`signatureLimit` messages. -/
class Params where
  totalHeight : Nat
  numLayers : Nat
  /-- `k`, the number of FORS trees. -/
  forsTrees : Nat
  /-- `a`, the height of a FORS tree. -/
  forsHeight : Nat
  /-- The height of every layer below the top one. -/
  lowerHeight : Nat
  subtreeHeight : Nat
  signatureLimit : Nat
  numLayers_pos : 0 < numLayers
  lowerHeight_ge : 6 ≤ lowerHeight
  /-- The top layer is at least as tall as the others. -/
  lower_le : lowerHeight * numLayers ≤ totalHeight
  /-- The index fields fit the digest and the 32-bit address fields. -/
  totalHeight_le : totalHeight ≤ 28
  /-- The kept subtree lies in the top layer. -/
  below_le : lowerHeight * (numLayers - 1) ≤ subtreeHeight
  subtreeHeight_le : subtreeHeight ≤ totalHeight
  forsTrees_pos : 0 < forsTrees
  /-- The trees' node indices fit their address word (`forsTreeIndex`). -/
  forsTrees_le : forsTrees ≤ 64
  /-- A tree has at least two levels. -/
  forsHeight_ge : 2 ≤ forsHeight
  /-- A tree's node indices fit their address word. -/
  forsHeight_le : forsHeight ≤ 12
  /-- Key generation builds the whole top layer: every index lands. -/
  full : subtreeHeight = totalHeight

export Params (totalHeight numLayers forsTrees forsHeight lowerHeight subtreeHeight signatureLimit)

/-- A **layered key**: a hypertree of `d` layers and height `h` whose layers below the top have
height `ℓ` (the top layer has the rest, `h - ℓ (d - 1)`); key generation builds the whole top layer
(`subtreeHeight = h`), with FORS of `k` trees of height `a`. At most `N` signatures. -/
abbrev Params.layered (h d ℓ k a N : Nat) (hd : 0 < d := by decide) (hℓ : 6 ≤ ℓ := by decide)
    (hle : ℓ * d ≤ h := by decide) (hh : h ≤ 28 := by decide) (hk : 0 < k := by decide)
    (hk' : k ≤ 64 := by decide) (ha : 2 ≤ a := by decide) (ha' : a ≤ 12 := by decide) : Params where
  totalHeight := h
  numLayers := d
  forsTrees := k
  forsHeight := a
  lowerHeight := ℓ
  subtreeHeight := h
  signatureLimit := N
  numLayers_pos := hd
  lowerHeight_ge := hℓ
  lower_le := hle
  totalHeight_le := hh
  below_le := Nat.le_trans (Nat.mul_le_mul_left ℓ (Nat.sub_le d 1)) hle
  subtreeHeight_le := Nat.le_refl h
  forsTrees_pos := hk
  forsTrees_le := hk'
  forsHeight_ge := ha
  forsHeight_le := ha'
  full := rfl

variable [Params]

/-- The height of the top layer, the tallest: `h - lowerHeight (d - 1)`. -/
def maxLayerHeight : Nat := totalHeight - lowerHeight * (numLayers - 1)

abbrev MasterSeed := BitVec 256

abbrev Digest := BitVec digestBits
abbrev HashOutput := BitVec hashOutputBits
abbrev Message := BitVec messageBits
abbrev PublicParameter := BitVec publicParameterBits
abbrev Randomness := Digest
abbrev Counter := BitVec counterBits
/-- A layer, `0` being the top one. -/
abbrev Layer := Fin numLayers
/-- `idx`, the bottom leaf and the FORS instance a digest selects. -/
abbrev Index := Fin (2 ^ totalHeight)
/-- `tau`, a tree of a layer. Layer `lay` only uses the values below `2^heightAbove lay`. -/
abbrev TreeIndex := Fin (2 ^ totalHeight)
/-- `e`, a leaf of a tree. Layer `lay` only uses the values below `2^layerHeight lay`. -/
abbrev LeafIndex := Fin (2 ^ maxLayerHeight)
abbrev ChainIndex := Fin numChains
abbrev Digit := Fin chainLength
abbrev ChainStep := Fin (chainLength - 1)
abbrev Encoding := ChainIndex → Digit
abbrev HashInput := List UInt8

/-! ### FORS types -/

/-- `κ`, a FORS tree. -/
abbrev FTree := Fin forsTrees
/-- A leaf, or a node index at any level, of a FORS tree. -/
abbrev FLeaf := Fin (2 ^ forsHeight)
/-- A level of a FORS tree that is hashed, `1 .. a`, as `level - 1`: level `a` is the root. -/
abbrev FLevel := Fin forsHeight

/-- The height of a layer: `maxLayerHeight` at the top, `lowerHeight` below. -/
def layerHeight (lay : Layer) : Nat := if lay.val = 0 then maxLayerHeight else lowerHeight

def topLayer : Layer := ⟨0, Params.numLayers_pos⟩

/-- `sum_{j > lay} h_j`, the index bits below layer `lay`. -/
def heightBelow (lay : Layer) : Nat := lowerHeight * (numLayers - 1 - lay.val)

/-- The first 16 bytes of a hash output (`bytesLE 32` lays it out): its low 128 bits. -/
def truncateHash (output : HashOutput) : Digest :=
  output.extractLsb' 0 digestBits

/-- The second 16 bytes of a hash output (bytes 16 to 31): the step of the randomizer walk, which a
full key never takes. -/
def upperHash (output : HashOutput) : Digest :=
  output.extractLsb' digestBits digestBits

/-! ### The message digest: FIPS 205's split of `m` bytes from `⌈m / 32⌉` calls -/

/-- The digest's fields: an index and the `k` leaf indices, `h + k a` bits. -/
def messageDigestBits : Nat := totalHeight + forsTrees * forsHeight

/-- The height of the bottom layer, whose leaf is the digest's last field. -/
def bottomHeight : Nat := layerHeight ⟨numLayers - 1, Nat.sub_lt Params.numLayers_pos Nat.one_pos⟩

/-- FIPS 205's Algorithm 19: the bytes of the FORS leaves, of the tree index and of the bottom leaf,
whose total is `m`. -/
def mdBytes : Nat := (forsTrees * forsHeight + 7) / 8
def treeIndexBytes : Nat := (totalHeight - bottomHeight + 7) / 8
def leafIndexBytes : Nat := (bottomHeight + 7) / 8
def digestBytes : Nat := mdBytes + treeIndexBytes + leafIndexBytes

/-- The number of `H_msg` calls: `⌈m / 32⌉`. -/
def digestCalls : Nat := (digestBytes + 31) / 32

theorem digestCalls_pos : 0 < digestCalls := by
  have hk := Params.forsTrees_pos
  have ha := Params.forsHeight_ge
  have : 2 ≤ forsTrees * forsHeight := le_trans ha (Nat.le_mul_of_pos_left _ hk)
  unfold digestCalls digestBytes mdBytes
  omega

/-- A digest call. -/
abbrev DigestCall := Fin digestCalls

/-- The first digest call. -/
def firstCall : DigestCall := ⟨0, digestCalls_pos⟩

/-- The digest's fields, packed least significant first: the index in the low `h` bits, then the
leaf of tree `κ` at bit `h + a κ`. -/
abbrev MessageDigest := BitVec messageDigestBits

/-- The outputs of the digest calls as one number, call 0 in the low 256 bits. -/
def digestValue (outputs : DigestCall → HashOutput) : Nat :=
  ∑ call : DigestCall, (outputs call).toNat * 2 ^ (hashOutputBits * call.val)

/-- The FORS key of an instance: the roots of its `k` trees, which `T_k` compresses into the FORS
public key (`Concrete.forsPublicKey`). -/
abbrev ForsKey := FTree → Digest

/-- `pk = PK.seed || PK.root`, `parameter` being `PK.seed`. -/
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

/-- The opening of one FORS tree: the secret of the selected leaf and its `a` auth nodes. -/
structure TreeOpening where
  secret : Digest
  path : Fin forsHeight → Digest
deriving DecidableEq

/-- The randomizer, the FORS opening, and the WOTS+C signature with its path at every layer:
`16 + 16 k (a + 1) + 1028 d + 16 h` bytes (`Layout.signature_size`). -/
structure Signature where
  randomness : Randomness
  fors : FTree → TreeOpening
  layers : (lay : Layer) → LayerSignature lay
deriving DecidableEq

/-- Serialize a bit vector into a fixed number of bytes, least significant byte first. -/
def bytesLE (byteCount : Nat) (value : BitVec (8 * byteCount)) : List UInt8 :=
  List.ofFn fun index : Fin byteCount =>
    UInt8.ofBitVec (value.extractLsb' (8 * index.val) 8)

/-- Serialize a bit vector into a fixed number of bytes, most significant byte first: FIPS 205's
`toByte`, for the address words and the counters. -/
def bytesBE (byteCount : Nat) (value : BitVec (8 * byteCount)) : List UInt8 :=
  List.ofFn fun index : Fin byteCount =>
    UInt8.ofBitVec (value.extractLsb' (8 * (byteCount - 1 - index.val)) 8)

/-! ### Reading the digest (FIPS 205 Algorithm 19) -/

/-- The bytes of the digest calls, call 0 first, each in Keccak's output order. -/
def digestOutputBytes (outputs : DigestCall → HashOutput) : List UInt8 :=
  (List.ofFn fun call => bytesLE 32 (outputs call)).flatten

/-- Bit `p` of a byte string read most significant bit first, as `base_2b` reads it. -/
def msbBit (bytes : List UInt8) (p : Nat) : Nat :=
  (bytes.getD (p / 8) 0).toNat / 2 ^ (7 - p % 8) % 2

/-- The `width` bits from bit `offset`, most significant first: one value of `base_2b`. -/
def msbField (bytes : List UInt8) (offset width : Nat) : Nat :=
  (List.range width).foldl (fun value j => 2 * value + msbBit bytes (offset + j)) 0

/-- `toInt`: a big-endian integer. -/
def beInt (bytes : List UInt8) : Nat :=
  bytes.foldl (fun value byte => 256 * value + byte.toNat) 0

/-- The index of a digest: the tree index of its middle bytes, then the bottom leaf of its last
bytes, each cut to its bits. -/
def digestIndexValue (bytes : List UInt8) : Nat :=
  beInt ((bytes.drop mdBytes).take treeIndexBytes) % 2 ^ (totalHeight - bottomHeight) * 2 ^ bottomHeight +
    beInt ((bytes.drop (mdBytes + treeIndexBytes)).take leafIndexBytes) % 2 ^ bottomHeight

/-- The digest's fields packed as `MessageDigest` lays them out: the index, then each tree's leaf,
`base_2b(md, a, k)`. -/
def digestFieldsValue (bytes : List UInt8) : Nat :=
  digestIndexValue bytes +
    ∑ κ : FTree, msbField bytes (forsHeight * κ.val) forsHeight * 2 ^ (totalHeight + forsHeight * κ.val)

/-- The fields of the digest calls. -/
def truncateMessageDigest (outputs : DigestCall → HashOutput) : MessageDigest :=
  BitVec.ofNat messageDigestBits (digestFieldsValue (digestOutputBytes outputs))

/-- FIPS 205's address `ADRS` (`Adrs` in `crates/signatures`): the layer, counted from the bottom, the
tree, the type `tag`, the key pair, the chain or height, and the hash address or tree index. -/
structure TweakFields where
  layer : BitVec 32
  tree : BitVec 96
  tag : BitVec 32
  keyPair : BitVec 32
  height : BitVec 32
  index : BitVec 32
deriving DecidableEq

/-- The 32 address bytes: eight big-endian words, the tree taking three. -/
def fieldBytes (fields : TweakFields) : HashInput :=
  bytesBE 4 fields.layer ++ bytesBE 12 fields.tree ++ bytesBE 4 fields.tag ++ bytesBE 4 fields.keyPair ++
    bytesBE 4 fields.height ++ bytesBE 4 fields.index

/-- An address from its integer fields. -/
def tweakFields (tag layer tree keyPair height index : Nat) : TweakFields :=
  ⟨BitVec.ofNat 32 layer, BitVec.ofNat 96 tree, BitVec.ofNat 32 tag, BitVec.ofNat 32 keyPair,
    BitVec.ofNat 32 height, BitVec.ofNat 32 index⟩

/-- The layer word of layer `lay`: the layers are counted from the bottom on the wire. -/
def layerByte (lay : Layer) : Nat := numLayers - 1 - lay.val

/-- An address in tree `tree` of layer `lay`. -/
def treeFields (tag : Nat) (lay : Layer) (tree : TreeIndex) (keyPair height index : Nat) : TweakFields :=
  tweakFields tag (layerByte lay) tree.val keyPair height index

/-! ### FORS addresses -/

/-- The address of instance `idx` of type `tag`: the bottom layer, the bottom key's tree, its leaf as
the key pair (`fors_adrs`). -/
def forsFields (tag : Nat) (index : Index) (height treeIdx : Nat) : TweakFields :=
  tweakFields tag 0 (index.val / 2 ^ bottomHeight) (index.val % 2 ^ bottomHeight) height treeIdx

/-- The tree index of node `node` at height `height` of tree `κ`: FIPS 205's `κ 2^(a - height) + node`,
counting across the trees. A node index past its tree's width, which no algorithm computes, is placed
above `2^31`, so that every position has its own address. -/
def forsTreeIndex (κ : FTree) (height node : Nat) : Nat :=
  if node < 2 ^ (forsHeight - height) then κ.val * 2 ^ (forsHeight - height) + node
  else 2 ^ 31 + κ.val * 2 ^ 12 + node

/-- The verification hash domains. Seed derivation uses `KeygenDomain`. A `forsNode` at `level` is the
node of FORS tree level `level + 1`; at the last level, the tree's root. -/
inductive HashDomain where
  | chain (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (chainIdx : ChainIndex) (step : ChainStep)
  | leaf (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
  | node (lay : Layer) (tree : TreeIndex) (level : Nat) (nodeIdx : Nat)
  | encoding (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
  | forsLeaf (index : Index) (κ : FTree) (leaf : FLeaf)
  | forsNode (index : Index) (κ : FTree) (level : FLevel) (node : FLeaf)
  | forsRoots (index : Index)
deriving DecidableEq

/-- The address of a hash domain, with FIPS 205's types: `WOTS_HASH = 0` (the chain and the position
a step leaves), `WOTS_PK = 1`, `TREE = 2` (the height and the node index), `FORS_TREE = 3` (the height
and the tree index), `FORS_ROOTS = 4`, and WOTS+C's encoding, `7`. -/
def hashDomainFields : HashDomain → TweakFields
  | .chain lay tree leaf chainIdx step => treeFields 0 lay tree leaf chainIdx step
  | .leaf lay tree leaf => treeFields 1 lay tree leaf 0 0
  | .node lay tree level nodeIdx => treeFields 2 lay tree 0 level nodeIdx
  | .encoding lay tree leaf => treeFields 7 lay tree leaf 0 0
  | .forsLeaf index κ leaf => forsFields 3 index 0 (forsTreeIndex κ 0 leaf.val)
  | .forsNode index κ level node =>
      forsFields 3 index (level.val + 1) (forsTreeIndex κ (level.val + 1) node.val)
  | .forsRoots index => forsFields 4 index 0 0

/-- The exact 32 address bytes of a hash domain. -/
def tweakBytes (domain : HashDomain) : HashInput :=
  fieldBytes (hashDomainFields domain)

/-- The random-oracle input `PK.seed || ADRS || payload` of every tweakable hash call. -/
def tweakableHashInput (parameter : PublicParameter) (domain : HashDomain)
    (message : HashInput) : HashInput :=
  bytesLE 16 parameter ++ tweakBytes domain ++ message

/-- The seed derivations: `ots` gives the start of one chain of the one-time key at a leaf
(`WOTS_PRF = 5`), `fors` the secret of one leaf of tree `κ` of instance `idx` (`FORS_PRF = 6`), and
`surrogate`, a sibling above the kept subtree, which no key of `Params` computes, has a type of its own. -/
inductive KeygenDomain where
  | ots (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (chain : ChainIndex)
  | fors (index : Index) (κ : FTree) (leaf : FLeaf)
  | surrogate (level : Fin maxLayerHeight)
deriving DecidableEq

def keygenDomainFields : KeygenDomain → TweakFields
  | .ots lay tree leaf chain => treeFields 5 lay tree leaf chain 0
  | .fors index κ leaf => forsFields 6 index 0 (forsTreeIndex κ 0 leaf.val)
  | .surrogate level => tweakFields 8 0 0 0 level 0

/-- `SEED_TAG`, the 11 ASCII bytes of `leanSPHINCS`. -/
def seedTag : HashInput := [0x6c, 0x65, 0x61, 0x6e, 0x53, 0x50, 0x48, 0x49, 0x4e, 0x43, 0x53]

/-- `leanSPHINCS || SK.seed || domain`, 44 bytes: domain `0` gives `PK.seed`, its first 16 bytes, and
domain `1` gives `SK.prf`, all 32 (`expand_key`). It has no parameter and no address. -/
def keySeedInput (seed : MasterSeed) (domain : Nat) : HashInput :=
  seedTag ++ bytesLE 32 seed ++ [UInt8.ofNat domain]

/-- `PRF(PK.seed, SK.seed, ADRS)`'s input, `PK.seed || ADRS || SK.seed`. -/
def keygenHashInput (parameter : PublicParameter) (domain : KeygenDomain)
    (seed : MasterSeed) : HashInput :=
  bytesLE 16 parameter ++ fieldBytes (keygenDomainFields domain) ++ bytesLE 32 seed

/-- `M' = 0x00 || 11 || leanSPHINCS || M`, pure SLH-DSA's framing of the message under the context
`leanSPHINCS` (FIPS 205 Algorithms 22 and 24), 45 bytes. -/
def framedMessage (message : Message) : HashInput :=
  [0x00, 0x0b] ++ seedTag ++ bytesLE 32 message

/-- `PRF_msg(SK.prf, PK.seed, M')`'s input, `SK.prf || PK.seed || M'`, 93 bytes: the randomizer of a
message. -/
def randomizerHashInput (prf : HashOutput) (parameter : PublicParameter) (message : Message) : HashInput :=
  bytesLE 32 prf ++ bytesLE 16 parameter ++ framedMessage message

/-- Call `call` of `H_msg(R, PK.seed, PK.root, M)`: `R || PK.seed || PK.root || M || BE_32(call)`,
84 bytes, the 32-byte message unframed. -/
def messageDigestInput (parameter : PublicParameter) (root : Digest) (message : Message)
    (randomness : Randomness) (call : DigestCall) : HashInput :=
  bytesLE 16 randomness ++ bytesLE 16 parameter ++ bytesLE 16 root ++ bytesLE 32 message ++
    bytesBE 4 (BitVec.ofNat 32 call.val)

/-! ### The target-sum code

`v = 64` chunks of `w = 2` bits covering the 128 digest bits, and the code is the words of digit sum
`T = 128`. -/

namespace TargetSum

/-- The digit sum of a word. -/
def sum (x : Encoding) : Nat := ∑ i, (x i).val

/-- Membership in the code `C`: digit sum `T`. -/
def Valid (x : Encoding) : Prop := sum x = targetSum

instance : DecidablePred Valid :=
  fun x => inferInstanceAs (Decidable (sum x = targetSum))

/-- Offset of a two-bit digit: `base_2b` reads each byte's most significant bits first, digit `i` being
bits `6 - 2 (i mod 4)` and up of byte `i / 4`. -/
def digitOffset (i : ChainIndex) : Nat := 8 * (i.val / 4) + 6 - winternitzBits * (i.val % 4)

/-- `x_i`, the two bits of the digest at the digit's offset. -/
def digestEncoding (digest : Digest) : Encoding :=
  fun i => (digest.extractLsb' (digitOffset i) winternitzBits).toFin

/-- A digest decodes exactly when its 64 digits reach the target sum. -/
def decodeDigest (digest : Digest) : Option Encoding :=
  if Valid (digestEncoding digest) then some (digestEncoding digest) else none

end TargetSum

/-! ## The algorithms

`Concrete` contains the hash and verification routines; `Seeded` contains key generation and
signing. Hashing routines work in any monad with access to `HashSpec`. -/

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

/-- `Th(PK.seed, ADRS, M) = Trunc_16(H(PK.seed || ADRS || M))`. -/
def tweakableHash (parameter : PublicParameter) (domain : HashDomain) (payload : HashInput) :
    m Digest := do
  let output ← oracleHash (tweakableHashInput parameter domain payload)
  return truncateHash output

/-! ### The index -/

/-- `tau`, the tree of layer `lay` on the path of `idx`: the bits above the layer. -/
def treeIndexAt (index : Index) (lay : Layer) : TreeIndex :=
  ⟨index.val / 2 ^ (heightBelow lay + layerHeight lay),
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) index.isLt⟩

theorem layerHeight_le (lay : Layer) : layerHeight lay ≤ maxLayerHeight := by
  unfold layerHeight
  split
  · exact le_refl _
  · have h1 := Params.lower_le
    have h2 := Params.numLayers_pos
    unfold maxLayerHeight
    have : lowerHeight * numLayers = lowerHeight * (numLayers - 1) + lowerHeight := by
      rw [← Nat.mul_succ]; congr 1; omega
    omega

/-- The tree below the leaf `leaf` of tree `tree` of layer `lay` (the tree that leaf's key signs the
root of), or at the bottom layer the FORS instance it signs the key of: `tree · 2^h_lay + leaf`. -/
def childTree (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) : TreeIndex :=
  ⟨(tree.val * 2 ^ layerHeight lay + leaf.val) % 2 ^ totalHeight, Nat.mod_lt _ (Nat.two_pow_pos _)⟩

/-- `e`, the leaf of that tree on the path of `idx`: the layer's bits of the index. -/
def leafIndexAt (index : Index) (lay : Layer) : LeafIndex :=
  ⟨index.val / 2 ^ heightBelow lay % 2 ^ layerHeight lay,
    Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _))
      (Nat.pow_le_pow_right (by decide) (layerHeight_le lay))⟩

/-! ### The one-time signature -/

/-- A node index at level `0` read as a leaf index. -/
def leafOfNat (value : Nat) : LeafIndex :=
  ⟨value % 2 ^ maxLayerHeight, Nat.mod_lt _ (Nat.two_pow_pos _)⟩

/-- `steps` chain steps from position `start`: the step onto position `start + steps + 1` carries
step `start + steps`. -/
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

/-- The two children of a Merkle node. -/
def nodePayload (left right : Digest) : HashInput :=
  bytesLE 16 left ++ bytesLE 16 right

/-- `root_0 || ... || root_{k-1}`, the FORS key as bytes: what `T_k` compresses. -/
def rootsPayload (roots : ForsKey) : HashInput :=
  (List.ofFn roots).flatMap (bytesLE 16)

/-- The message a layer's WOTS+C key signs, as bytes: the 16-byte FORS public key at the bottom layer,
the 16-byte root of the tree below at a layer above. -/
def rootPayload (root : Digest) : HashInput := bytesLE 16 root

/-- `Enc(K, M, c)`: hash the message, then the counter, `BE_32(c)`, under the leaf's encoding address,
and decode: `PK.seed || ADRS || M || BE_32(c)`, 68 bytes. -/
def encode (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (message : HashInput) (counter : Counter) : m (Option Encoding) := do
  let digest ← tweakableHash parameter (.encoding lay tree leaf)
    (message ++ bytesBE 4 counter)
  return TargetSum.decodeDigest digest

/-- `Ots.leaf` (`wots_leaf`): the verifier's leaf, or nothing if the counter does not encode the message. -/
def otsLeaf (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (message : HashInput) (counter : Counter) (values : ChainIndex → Digest) : m (Option Digest) := do
  let some encoding ← encode parameter lay tree leaf message counter | return none
  let endpoints ← sequenceFin fun chainIdx =>
    recoverChain parameter lay tree leaf chainIdx (encoding chainIdx) (values chainIdx)
  let value ← leafHash parameter lay tree leaf endpoints
  return some value

/-! ### The tree -/

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

/-- A FORS leaf: the hash of its secret. -/
def forsLeafHash (parameter : PublicParameter) (index : Index) (κ : FTree) (leaf : FLeaf)
    (secret : Digest) : m Digest :=
  tweakableHash parameter (.forsLeaf index κ leaf) (bytesLE 16 secret)

/-- Fold a FORS leaf and a path over `levels` levels. -/
def forsFold (parameter : PublicParameter) (index : Index) (κ : FTree) (leaf : FLeaf)
    (path : Fin forsHeight → Digest) : Nat → Digest → m Digest
  | 0, value => pure value
  | levels + 1, value => do
      let current ← forsFold parameter index κ leaf path levels value
      if hlevel : levels < forsHeight then
        let sibling := path ⟨levels, hlevel⟩
        let node : FLeaf := ⟨leaf.val / 2 ^ (levels + 1),
          Nat.lt_of_le_of_lt (Nat.div_le_self _ _) leaf.isLt⟩
        if leaf.val.testBit levels then
          tweakableHash parameter (.forsNode index κ ⟨levels, hlevel⟩ node) (nodePayload sibling current)
        else
          tweakableHash parameter (.forsNode index κ ⟨levels, hlevel⟩ node) (nodePayload current sibling)
      else
        pure 0

/-- The root of a FORS tree that an opening reaches: the leaf folded `a` levels (`fors_pkFromSig`). -/
def treeRecover (parameter : PublicParameter) (index : Index) (κ : FTree) (leaf : FLeaf)
    (opening : TreeOpening) : m Digest := do
  let value ← forsLeafHash parameter index κ leaf opening.secret
  forsFold parameter index κ leaf opening.path forsHeight value

/-- The roots an opening reaches. -/
def forsRecover (parameter : PublicParameter) (index : Index) (leaves : FTree → FLeaf)
    (opening : FTree → TreeOpening) : m ForsKey :=
  sequenceFin fun κ => treeRecover parameter index κ (leaves κ) (opening κ)

/-- `T_k` of the roots: the FORS public key, which the bottom WOTS+C key signs. -/
def forsPublicKey (parameter : PublicParameter) (index : Index) (roots : ForsKey) : m Digest :=
  tweakableHash parameter (.forsRoots index) (rootsPayload roots)

/-! ### The message digest -/

/-- One untruncated digest call. -/
def messageDigestCall (parameter : PublicParameter) (root : Digest) (message : Message)
    (randomness : Randomness) (call : DigestCall) : m HashOutput :=
  oracleHash (messageDigestInput parameter root message randomness call)

/-- `idx`, the low `h` bits of the digest. -/
def digestIndex (digest : MessageDigest) : Index :=
  (digest.extractLsb' 0 totalHeight).toFin

/-- The low `h` bits of the first digest call, which the grinding loop tests for landing. Under
FIPS 205's digest layout these are FORS leaf bits, not the index (`digestIndex`); a full key
(`Params.full`) lands every index, so the test never decides anything and the signer signs at `R`. -/
def blockIndex (first : HashOutput) : Index :=
  (first.extractLsb' 0 totalHeight).toFin

/-- `H_msg(R, PK.seed, PK.root, M)`: the calls, read as FIPS 205's Algorithm 19 reads them. -/
def messageDigest (parameter : PublicParameter) (root : Digest) (message : Message)
    (randomness : Randomness) : m MessageDigest := do
  let outputs ← sequenceFin fun call => messageDigestCall parameter root message randomness call
  return truncateMessageDigest outputs

/-- Bit offset of the leaf index of tree `κ`: `h + a κ`. -/
def leafOffset (κ : FTree) : Nat := totalHeight + forsHeight * κ.val

/-- The leaf indices of a digest. -/
def digestLeaves (digest : MessageDigest) : FTree → FLeaf := fun κ =>
  (digest.extractLsb' (leafOffset κ) forsHeight).toFin

/-! ### Verification -/

/-- Read a layer's path, returning zero outside its height. -/
def signaturePath (signature : Signature) (lay : Layer) (level : Nat) : Digest :=
  if hlevel : level < layerHeight lay then (signature.layers lay).path ⟨level, hlevel⟩ else 0

/-- The walk up the layers: `remaining + 1` enters at layer `remaining`, whose WOTS+C key signs
`message` (the FORS public key at the bottom layer, the root of the tree below above it); the fold of
the top layer is the value compared against the public root. -/
def verifyLayers (parameter : PublicParameter) (index : Index) (signature : Signature) :
    Nat → HashInput → m (Option Digest)
  | 0, _ => pure none
  | remaining + 1, message => do
      if hlayer : remaining < numLayers then
        let lay : Layer := ⟨remaining, hlayer⟩
        let tree := treeIndexAt index lay
        let leaf := leafIndexAt index lay
        let part := signature.layers lay
        let some value ← otsLeaf parameter lay tree leaf message part.counter part.chainValues
          | return none
        let root ← treeFold parameter lay tree leaf (signaturePath signature lay) (layerHeight lay) value
        if remaining = 0 then
          return some root
        else
          verifyLayers parameter index signature remaining (rootPayload root)
      else
        pure none

/-- `Ver(pk, m, sigma)`: recompute the digest, recover the FORS roots and the FORS public key, walk the
layers (recover the one-time leaf, fold the path) and compare with the root. -/
def verify (publicKey : PublicKey) (message : Message) (signature : Signature) : m Bool := do
  let digest ← messageDigest publicKey.parameter publicKey.root message signature.randomness
  let index := digestIndex digest
  let roots ← forsRecover publicKey.parameter index (digestLeaves digest) signature.fors
  let forsKey ← forsPublicKey publicKey.parameter index roots
  let some root ← verifyLayers publicKey.parameter index signature numLayers (rootPayload forsKey)
    | return false
  return decide (root = publicKey.root)

/-! ### Signing -/

/-- The top layer holds one tree, at index `0`. -/
def rootTree : TreeIndex := ⟨0, Nat.two_pow_pos _⟩

/-- Run the `n` computations from the last index down, stopping on the first failure. -/
def sequenceDep : {n : Nat} → {α : Fin n → Type} →
    ((i : Fin n) → m (Option (α i))) → m (Option ((i : Fin n) → α i))
  | 0, _, _ => pure (some fun i => Fin.elim0 i)
  | _ + 1, α, computation => do
      let some last ← computation (Fin.last _) | return none
      let some init ← sequenceDep (α := fun i => α i.castSucc) fun i => computation i.castSucc
        | return none
      return some (Fin.lastCases last init)

/-- Run the `n` computations from the last index down, each from the state the one before it
returned, stopping on the first failure. -/
def sequenceThread {σ : Type} : {n : Nat} → {α : Fin n → Type} →
    ((i : Fin n) → σ → m (Option (α i × σ))) → σ → m (Option ((i : Fin n) → α i))
  | 0, _, _, _ => pure (some fun i => Fin.elim0 i)
  | _ + 1, α, computation, state => do
      let some (last, next) ← computation (Fin.last _) state | return none
      let some init ← sequenceThread (α := fun i => α i.castSucc) (fun i => computation i.castSucc)
        next | return none
      return some (Fin.lastCases last init)

/-- A layer signature's path as `treeFold` reads it, zero outside the layer's height. -/
def partPath {lay : Layer} (part : LayerSignature lay) (level : Nat) : Digest :=
  if hlevel : level < layerHeight lay then part.path ⟨level, hlevel⟩ else 0

/-- The root of its tree that a layer signature of `message` reaches, as the verifier computes it:
the one-time leaf, folded up the path. -/
def layerRecover (parameter : PublicParameter) (index : Index) (lay : Layer) (message : HashInput)
    (part : LayerSignature lay) : m (Option Digest) := do
  let tree := treeIndexAt index lay
  let leaf := leafIndexAt index lay
  let some value ← otsLeaf parameter lay tree leaf message part.counter part.chainValues
    | return none
  let root ← treeFold parameter lay tree leaf (partPath part) (layerHeight lay) value
  return some root

attribute [irreducible] verify

end Concrete

/-! ### Pruning -/

section Pruning

/-- `s`, the kept subtree of the top layer: `PK.seed` modulo `2^(h - b)`, `0` as `b = h` (`Params.full`). -/
def subtreePosition (parameter : PublicParameter) : Nat :=
  parameter.toNat % 2 ^ (totalHeight - subtreeHeight)

/-- The kept instances are `s * 2^b .. (s + 1) * 2^b`, read on the top layer's leaf
`idx >> heightBelow topLayer`. -/
def Landed (parameter : PublicParameter) (index : Index) : Prop :=
  index.val / 2 ^ subtreeHeight = subtreePosition parameter

instance (parameter : PublicParameter) (index : Index) : Decidable (Landed parameter index) :=
  inferInstanceAs (Decidable (index.val / 2 ^ subtreeHeight = subtreePosition parameter))

/-- The height of the kept part of a layer's tree: `b - heightBelow topLayer` at the top layer, the
whole tree below it. -/
def keptHeight (lay : Layer) : Nat := if lay.val = 0 then subtreeHeight - heightBelow lay else layerHeight lay

/-- The position of the kept part among the nodes of level `keptHeight`: `s` at the top layer, `0`
below it. -/
def keptPosition (parameter : PublicParameter) (lay : Layer) : Nat :=
  if lay.val = 0 then subtreePosition parameter else 0

end Pruning

/-- `PRF(PK.seed, SK.seed, ADRS)`: one seed derivation, the first 16 bytes of its hash. -/
def deriveKey {m : Type → Type} [Monad m] [HasQuery HashSpec m]
    (parameter : PublicParameter) (domain : KeygenDomain) (seed : MasterSeed) : m Digest := do
  return truncateHash (← Concrete.oracleHash (keygenHashInput parameter domain seed))

/-- The step of a randomizer walk: its lowest bit is set, so the walk `R0 + i * step` does not come
back before `2^128` attempts. -/
def walkStep (half : Randomness) : Randomness := half ||| 1#digestBits

/-- `PRF_msg(SK.prf, PK.seed, M')`, one hash per message: its first half is the randomizer `R`; its
second half gives the step of a walk, which a full key never takes. -/
def deriveRandomizer {m : Type → Type} [Monad m] [HasQuery HashSpec m]
    (prf : HashOutput) (parameter : PublicParameter)
    (message : Message) : m (Randomness × Randomness) := do
  let output ← Concrete.oracleHash (randomizerHashInput prf parameter message)
  return (truncateHash output, walkStep (upperHash output))

/-- `PK.seed`, the first 16 bytes of the hash of `leanSPHINCS || SK.seed || 0`. -/
def derivePublicSeed {m : Type → Type} [Monad m] [HasQuery HashSpec m] (seed : MasterSeed) :
    m PublicParameter := do
  return truncateHash (← Concrete.oracleHash (keySeedInput seed 0))

/-- `SK.prf`, the whole hash of `leanSPHINCS || SK.seed || 1`. -/
def derivePrf {m : Type → Type} [Monad m] [HasQuery HashSpec m] (seed : MasterSeed) : m HashOutput :=
  Concrete.oracleHash (keySeedInput seed 1)

noncomputable def sampleMasterSeed : ProbComp MasterSeed :=
  letI := SampleableType.ofFintype MasterSeed
  $ᵗ MasterSeed

namespace Seeded

open Concrete

/-- What the signer reads: `SK.seed`, `SK.prf`, `PK.seed` and `PK.root`. -/
structure SecretKey where
  seed : MasterSeed
  prf : HashOutput
  parameter : PublicParameter
  root : Digest

variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]

/-- `wots_secrets`: the starts of the 64 chains of the one-time key at a leaf, one `PRF` each. -/
def otsSecrets (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (seed : MasterSeed) : m (ChainIndex → Digest) :=
  sequenceFin fun chainIdx => deriveKey parameter (.ots lay tree leaf chainIdx) seed

def oneTimePublicKey (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (seed : MasterSeed) : m (ChainIndex → Digest) := do
  let secrets ← otsSecrets parameter lay tree leaf seed
  sequenceFin fun chainIdx =>
    chainWalk parameter lay tree leaf chainIdx 0 (chainLength - 1) (secrets chainIdx)

def otsSignFrom (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (seed : MasterSeed) (message : HashInput) :
    Nat → Nat → m (Option (Counter × (ChainIndex → Digest)))
  | 0, _ => pure none
  | attempts + 1, counter => do
      match ← encode parameter lay tree leaf message (BitVec.ofNat counterBits counter) with
      | some encoding => do
          let secrets ← otsSecrets parameter lay tree leaf seed
          let values ← sequenceFin fun chainIdx =>
            chainWalk parameter lay tree leaf chainIdx 0 (encoding chainIdx).val (secrets chainIdx)
          return some (BitVec.ofNat counterBits counter, values)
      | none => otsSignFrom parameter lay tree leaf seed message attempts (counter + 1)

/-- `wots_sign`: the least admissible counter, then the opened chain values. -/
def otsSign (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (seed : MasterSeed) (message : HashInput) :
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

/-- The surrogate sibling at `level >= b`, derived from the seed (type `8`). Honest calls have
`level < h`. -/
def surrogate (parameter : PublicParameter) (seed : MasterSeed) (level : Nat) : m Digest :=
  if hlevel : level < maxLayerHeight then deriveKey parameter (.surrogate ⟨level, hlevel⟩) seed else pure 0

/-- The node at level `k + steps` above the kept part (`k = keptHeight lay`): its root folded with
the first `steps` surrogates. -/
def spineNode (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (seed : MasterSeed) :
    Nat → m Digest
  | 0 => treeNode parameter lay tree seed (keptHeight lay) (keptPosition parameter lay)
  | steps + 1 => do
      let below ← spineNode parameter lay tree seed steps
      let sibling ← surrogate parameter seed (keptHeight lay + steps)
      let nodeIdx := keptPosition parameter lay / 2 ^ steps
      if nodeIdx.testBit 0 then
        tweakableHash parameter (.node lay tree (keptHeight lay + steps + 1) (nodeIdx / 2))
          (nodePayload sibling below)
      else
        tweakableHash parameter (.node lay tree (keptHeight lay + steps + 1) (nodeIdx / 2))
          (nodePayload below sibling)

/-- The root of a layer's tree: the spine's top (the whole tree's root below the top layer). -/
def treeRoot (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (seed : MasterSeed) : m Digest :=
  spineNode parameter lay tree seed (layerHeight lay - keptHeight lay)

/-- The authentication path of a kept leaf: nodes of the kept part below level
`keptHeight`, surrogates from that level on. -/
def treePath (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (seed : MasterSeed) (leaf : LeafIndex) : m (Fin (layerHeight lay) → Digest) :=
  sequenceFin fun level =>
    if level.val < keptHeight lay then
      treeNode parameter lay tree seed level.val (Nat.xor (leaf.val / 2 ^ level.val) 1)
    else
      surrogate parameter seed level.val

end Seeded

namespace Seeded

open Concrete

variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]

/-- `fors_skGen`: the secret of one FORS leaf, one `PRF`. -/
def forsSecret (parameter : PublicParameter) (index : Index) (κ : FTree) (leaf : FLeaf)
    (seed : MasterSeed) : m Digest :=
  deriveKey parameter (.fors index κ leaf) seed

/-- `fors_node`: a node of a FORS tree at tree level `level`, the root at level `a`. -/
def forsNode (parameter : PublicParameter) (index : Index) (κ : FTree) (seed : MasterSeed) :
    Nat → Nat → m Digest
  | 0, node => do
      let leaf : FLeaf := ⟨node % 2 ^ forsHeight, Nat.mod_lt _ (Nat.two_pow_pos _)⟩
      let secret ← forsSecret parameter index κ leaf seed
      forsLeafHash parameter index κ leaf secret
  | level + 1, node => do
      let left ← forsNode parameter index κ seed level (2 * node)
      let right ← forsNode parameter index κ seed level (2 * node + 1)
      if hlevel : level < forsHeight then
        tweakableHash parameter (.forsNode index κ ⟨level, hlevel⟩
          ⟨node % 2 ^ forsHeight, Nat.mod_lt _ (Nat.two_pow_pos _)⟩) (nodePayload left right)
      else
        pure 0

/-- The FORS public key of instance `idx`: `T_k` of the roots of its trees. -/
def forsKey (parameter : PublicParameter) (index : Index) (seed : MasterSeed) : m Digest := do
  let roots ← sequenceFin fun κ => forsNode parameter index κ seed forsHeight 0
  forsPublicKey parameter index roots

/-- The opening of one tree at a leaf: its secret and its path, the sibling at every level. -/
def treeOpen (parameter : PublicParameter) (index : Index) (κ : FTree) (leaf : FLeaf)
    (seed : MasterSeed) : m TreeOpening := do
  let secret ← forsSecret parameter index κ leaf seed
  let path ← sequenceFin fun level : Fin forsHeight =>
    forsNode parameter index κ seed level.val (Nat.xor (leaf.val / 2 ^ level.val) 1)
  return ⟨secret, path⟩

/-- `Fts.sign`: the opening of every tree. -/
def forsOpen (parameter : PublicParameter) (index : Index) (leaves : FTree → FLeaf)
    (seed : MasterSeed) : m (FTree → TreeOpening) :=
  sequenceFin fun κ => treeOpen parameter index κ (leaves κ) seed

/-- `slh_keygen_internal` from `SK.seed`: derive `PK.seed` and `SK.prf`, and build the root of the top
layer. -/
def keygenFromSeed (seed : MasterSeed) : OracleComp HashSpec (PublicKey × SecretKey) := do
  let parameter ← derivePublicSeed seed
  let prf ← derivePrf seed
  let root ← treeRoot parameter topLayer rootTree seed
  return (⟨root, parameter⟩, ⟨seed, prf, parameter, root⟩)

/-- `Gen` (`key_gen_from_seed`): the key's seed is `SK.seed`. -/
def keygen (seed : MasterSeed) : OracleComp HashSpec (PublicKey × SecretKey) :=
  keygenFromSeed seed

/-- One grinding attempt: whether the low `h` bits of the first digest call (`blockIndex`) land. They
are FORS leaf bits, not the index, and a full key (`Params.full`) lands every value. -/
def signAttempt (secretKey : SecretKey) (message : Message) (randomness : Randomness) :
    m (Option Index) := do
  let first ← messageDigestCall secretKey.parameter secretKey.root message randomness firstCall
  if Landed secretKey.parameter (blockIndex first) then
    return some (blockIndex first)
  else
    return none

/-- What the WOTS+C key at leaf `leaf` of tree `tree` of layer `lay` signs: the root of the tree
below it, or the FORS public key of its instance at the bottom layer. -/
def keyMessage (parameter : PublicParameter) (seed : MasterSeed) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) : m HashInput :=
  if hbelow : lay.val + 1 < numLayers then do
    let root ← treeRoot parameter ⟨lay.val + 1, hbelow⟩ (childTree lay tree leaf) seed
    return rootPayload root
  else do
    let key ← forsKey parameter (childTree lay tree leaf) seed
    return rootPayload key

/-- What the WOTS+C key of layer `lay` on the path of `idx` signs. -/
def layerMessage (secretKey : SecretKey) (index : Index) (lay : Layer) : m HashInput :=
  keyMessage secretKey.parameter secretKey.seed lay (treeIndexAt index lay) (leafIndexAt index lay)

/-- Sign `message` with the WOTS+C key of layer `lay` on the path of `index`, and attach the key's
path. -/
def signLayerWith (secretKey : SecretKey) (index : Index) (lay : Layer) (message : HashInput) :
    m (Option (LayerSignature lay)) := do
  let tree := treeIndexAt index lay
  let leaf := leafIndexAt index lay
  let some (counter, values) ← otsSign secretKey.parameter lay tree leaf secretKey.seed message
    | return none
  let path ← treePath secretKey.parameter lay tree secretKey.seed leaf
  return some ⟨counter, values, path⟩

/-- A layer's signature of its own message, computed from scratch: what the proof reasons about.
The signer computes the same signature without recomputing the message (`layerStep`). -/
def signLayer (secretKey : SecretKey) (index : Index) (lay : Layer) : m (Option (LayerSignature lay)) := do
  let message ← layerMessage secretKey index lay
  signLayerWith secretKey index lay message

/-- One layer of the signer, given what the layer below computed (the FORS public key at the bottom,
the root of the tree below above it): sign it, then, below the top layer, recover the root the
signature reaches, which the layer above signs. -/
def layerStep (secretKey : SecretKey) (index : Index) (lay : Layer) (below : Digest) :
    m (Option (LayerSignature lay × Digest)) := do
  let some part ← signLayerWith secretKey index lay (rootPayload below) | return none
  if lay.val = 0 then
    return some (part, below)
  else
    let some root ← layerRecover secretKey.parameter index lay (rootPayload below) part | return none
    return some (part, root)

/-- Try `randomness, randomness + step, randomness + 2 step, ...`, stopping at the first that lands
in the kept subtree. -/
def signDigestLoop (secretKey : SecretKey) (message : Message) (step : Randomness) : Nat → Randomness →
    m (Option (Randomness × Index))
  | 0, _ => pure none
  | attempts + 1, randomness => do
      match ← signAttempt secretKey message randomness with
      | some index => return some (randomness, index)
      | none => signDigestLoop secretKey message step attempts (randomness + step)

/-- `Sign` (`slh_sign`, deterministic): derive the randomizer `R` of the message (one hash), which a
full key lands at first, compute the digest, open FORS and recover its public key from the opening,
then from the bottom layer up sign the message of the layer below with WOTS+C, attach the path, and
recover the root the layer above signs. It returns the Rust signer's signature and, on every run,
makes no more hash calls than the Rust signer, which is what carrying the bound over to the crate
needs (`README.md`, "The signer's hash calls"); the calls themselves differ. -/
def sign (secretKey : SecretKey) (message : Message) : m (Option Signature) := do
  let walk ← deriveRandomizer secretKey.prf secretKey.parameter message
  let some (randomness, _) ← signDigestLoop secretKey message walk.2 digestAttemptLimit walk.1
    | return none
  let digest ← messageDigest secretKey.parameter secretKey.root message randomness
  let index := digestIndex digest
  let opening ← forsOpen secretKey.parameter index (digestLeaves digest) secretKey.seed
  let roots ← forsRecover secretKey.parameter index (digestLeaves digest) opening
  let forsKey ← forsPublicKey secretKey.parameter index roots
  let some layers ← sequenceThread (fun lay below => layerStep secretKey index lay below) forsKey
    | return none
  return some ⟨randomness, opening, layers⟩

end Seeded

end FORS
