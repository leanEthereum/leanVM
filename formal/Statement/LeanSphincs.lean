module

public import Statement.HashSignatures
public import VCVio.OracleComp.QueryTracking.LoggingOracle.Core
public import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation
public import VCVio.OracleComp.QueryTracking.WriterCost

/-!
# leanSPHINCS

The scheme of `crates/signatures/src/lean_sphincs` (`mod.rs`, `hash.rs`, `wots.rs`, `fors.rs`,
`scheme.rs`; the shared `hasher`, `path_fold` and `truncate` of `crates/signatures/src/lib.rs`),
specified in `doc/lean_sphincs`: SLH-DSA (FIPS 205) on Keccak-256, with
WOTS+C as its one-time signature and a hypertree of layers of different heights.

* Every hash of a tree, a chain or a secret is `Trunc_16(H(PK.seed ‖ ADRS ‖ M))` (`th`, `prf`),
  `ADRS` being FIPS 205's 32-byte address of eight big-endian words (§sec:parameters,
  §sec:address); `H` is Keccak-256.
* The secret key is `SK.seed`, 32 bytes, the only secret: `PK.seed = Trunc_16(H(leanSPHINCS ‖
  SK.seed ‖ 0))` and `SK.prf = H(leanSPHINCS ‖ SK.seed ‖ 1)` (§sec:keys). Every secret is one `PRF`
  call on `SK.seed`. Key generation builds the top tree; the public key is `(PK.seed, PK.root)`.
* A signature's randomizer is `R = PRF_msg(SK.prf, PK.seed, M')`, `M' = 0x00 ‖ 11 ‖ leanSPHINCS ‖
  M` pure SLH-DSA's framing of the message. The digest `H_msg(R, PK.seed, PK.root, M)` is two
  calls on `R ‖ PK.seed ‖ PK.root ‖ M`, the 32-byte message unframed, and a big-endian counter,
  whose first 34 bytes FIPS 205's Algorithm 19 reads as the leaves of the FORS trees (`base_2b`),
  the tree index and the bottom leaf (big-endian): an index `idx < 2^26` and one leaf in each of
  24 FORS trees of height 10.
* FORS (§sec:fts): every tree is hashed to its root, and the FORS public key is `T_k` of the 24
  roots; the bottom one-time key signs it.
* The hypertree has 3 layers, of heights 8, 8 and 10 from the bottom (§sec:layer). Index `idx`
  names one one-time key on every layer, `K_l(idx) = (l, τ, e)`. The key of each layer above the
  bottom signs the root of the tree below; the top tree's root is `PK.root`.
* A one-time key is WOTS+C (§sec:ots): `v = 64` chains of 4 positions, a codeword of digit sum
  `T = 128` read from the encoding hash by `base_2b`, and the least counter `c < 2^32` whose
  encoding is a codeword; the encoding hash has an address type of its own, `7`.

**The signer** is the crate's, hash call for hash call (`sign`, `sign_with`, `scheme.rs`):
`SK.seed` expanded (`SK.prf`, then `PK.seed`), the top tree built level by level (`keygen`, whose
levels the top layer's path is read from), the randomizer, the digest's two calls, each FORS tree
built once (its secrets, its leaves, its levels) and `T_k` of their roots, then the layers from the
bottom up, each a one-time signature (the counter search, the chain starts, the chains) followed by
its tree's levels (the top layer's from key generation). The crate computes a tree's one-time
leaves and the 24 FORS trees in parallel (`parallel::map_collect`, `scheme.rs`, `fors.rs`),
fixing no order among those calls: here they run in leaf order and in tree order, the calls and
their inputs the crate's. Every input of a counter search is 68 bytes, one Keccak block, so the
crate's search, which finishes a copy of the absorbed `PK.seed ‖ ADRS ‖ M` per counter, makes the
permutation calls this one does.

Then the SUF-CMA game of `Statement/SufCma.lean` with that signer, and the end statement
`Sphincs.LeanSphincsStronglyUnforgeable`, proved by `Sphincs.leanSphincsStronglyUnforgeable`
(`lean_sphincs`).
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace Sphincs

open HashSig

/-! ### The instance: parameters, types, and hash-input layout -/

/-- The encoding counter's bits, `32` (`COUNTER_LEN`, 4 bytes, `mod.rs`). -/
def counterBits : Nat := 32
/-- `v`, the chains of a one-time key, `64` (`V`, `mod.rs`). -/
def chainCount : Nat := 64
/-- `T`, the digit sum of a codeword, `128` (`TARGET_SUM`, `mod.rs`). -/
def targetSum : Nat := 128
/-- Encoding counters tried per one-time signature, `C_max` (`MAX_ENCODING_ATTEMPTS`,
`mod.rs`). -/
def encodingAttemptLimit : Nat := 2 ^ 32
/-- `d`, the layers of the hypertree, `3` (`LAYERS`, `mod.rs`). -/
def layerCount : Nat := 3
/-- `h`, the bits of an index, `8 + 8 + 10 = 26` (`H`, `mod.rs`). -/
def indexBits : Nat := 26
/-- `k`, the trees of a FORS instance, `24` (`FORS_TREES`, `mod.rs`). -/
def forsTreeCount : Nat := 24
/-- `a`, the height of a FORS tree, `10` (`FORS_HEIGHT`, `mod.rs`). -/
def forsTreeHeight : Nat := 10
/-- `N`, the signatures a key makes at most: the end statement's limit, `1,182,000,000`
(`doc/lean_sphincs` §sec:security, `main.tex`, the Lean proof's count; the crate's key is
for `2^30`, §sec:scheme). -/
def signatureLimit : Nat := 1182000000

/-- `l`, a layer of the hypertree, counted from the bottom. -/
abbrev Layer := Fin layerCount

instance : NeZero layerCount := ⟨by decide⟩

/-- `h_l`, the height of each tree of layer `l`: `8, 8, 10` from the bottom (`LAYER_HEIGHTS`,
`mod.rs`). -/
def layerHeight (layer : Layer) : Nat := if layer.val = 2 then 10 else 8

/-- The top layer, `d - 1`, whose single tree's root is `PK.root`. -/
def topLayer : Layer := ⟨2, by decide⟩

/-- `β_l = h_0 + ... + h_{l-1}`, the index bits below layer `l`. -/
def bitsBelowLayer (layer : Layer) : Nat := 8 * layer.val

/-- `idx`, an index: a bottom leaf, and the FORS instance it carries. -/
abbrev Index := Fin (2 ^ indexBits)
/-- `τ`, a tree of a layer. Layer `l` uses the values below `2^(h - β_l - h_l)`. -/
abbrev TreeIndex := Fin (2 ^ indexBits)
/-- `e`, a leaf of a tree. Layer `l` uses the values below `2^h_l`. -/
abbrev TreeLeafIndex := Fin (2 ^ layerHeight topLayer)
/-- `c`, the WOTS+C encoding counter. -/
abbrev EncodingCounter := BitVec counterBits
/-- `i`, a chain of a one-time key. -/
abbrev ChainIndex := Fin chainCount
/-- The `v` digits a codeword assigns to the chains: how far each chain is opened. -/
abbrev Encoding := ChainIndex → WinternitzDigit

/-- The secret key: `SK.seed`, 32 bytes, all of the key (`LeanSphincsSecretKey`, `scheme.rs`;
`Seed`, `mod.rs`). `PK.seed` and `SK.prf` are its hashes, which the signer derives again at
each signature, as the crate's does (`expand_key`). -/
abbrev SecretKey := MasterSeed

/-- `κ`, a tree of a FORS instance. -/
abbrev ForsTreeIndex := Fin forsTreeCount
/-- `s`, a leaf of a FORS tree. -/
abbrev ForsLeafIndex := Fin (2 ^ forsTreeHeight)

/-- `K_l(idx)`'s tree, `⌊idx / 2^(β_l + h_l)⌋` (`OtsKey::of_index`, `wots.rs`). -/
def treeOfIndex (layer : Layer) (index : Index) : TreeIndex :=
  ⟨index.val / 2 ^ (bitsBelowLayer layer + layerHeight layer),
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) index.isLt⟩

/-- `K_l(idx)`'s leaf, `⌊idx / 2^β_l⌋ mod 2^h_l` (`OtsKey::of_index`, `wots.rs`). -/
def leafOfIndex (layer : Layer) (index : Index) : TreeLeafIndex :=
  ⟨index.val / 2 ^ bitsBelowLayer layer % 2 ^ layerHeight layer,
    Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _))
      (Nat.pow_le_pow_right (by decide) (by unfold layerHeight topLayer; split <;> decide))⟩

/-- A number read as a leaf of a tree (below `2^h_l`, its own value). -/
def leafOfNat (value : Nat) : TreeLeafIndex :=
  ⟨value % 2 ^ layerHeight topLayer, Nat.mod_lt _ (Nat.two_pow_pos _)⟩

/-- A number read as a leaf of a FORS tree (below `2^a`, its own value). -/
def forsLeafOfNat (value : Nat) : ForsLeafIndex :=
  ⟨value % 2 ^ forsTreeHeight, Nat.mod_lt _ (Nat.two_pow_pos _)⟩

/-- Serialize a bit vector into a fixed number of bytes, most significant byte first: FIPS 205's
`toByte`, the `to_be_bytes` of the address words and the counters. -/
def bigEndianBytes (byteCount : Nat) (value : BitVec (8 * byteCount)) : List UInt8 :=
  List.ofFn fun index : Fin byteCount =>
    UInt8.ofBitVec (value.extractLsb' (8 * (byteCount - 1 - index.val)) 8)

/-! #### Keys and signatures -/

/-- The public key, `PK.seed` then `PK.root` (`LeanSphincsPublicKey`, `scheme.rs`). -/
structure PublicKey where
  /-- `PK.seed`, prefixed to every addressed hash. -/
  publicSeed : PublicParameter
  /-- `PK.root`, the root of the top tree. -/
  root : Digest
deriving DecidableEq

/-- `PK.seed ‖ PK.root`, 32 bytes (`to_bytes`, `scheme.rs`). -/
def PublicKey.toBytes (publicKey : PublicKey) : List UInt8 :=
  littleEndianBytes 16 publicKey.publicSeed ++ littleEndianBytes 16 publicKey.root

/-- One FORS tree's opening: the selected leaf's secret, and its path from the leaf up to the
root's other child (`ForsTreeOpening`, `fors.rs`). -/
structure ForsTreeOpening where
  /-- The selected leaf's secret. -/
  secret : Digest
  /-- The siblings from the leaf up, the sibling at height `z` first for `z = 0, ..., a - 1`. -/
  path : Fin forsTreeHeight → Digest
deriving DecidableEq

/-- What a signature carries for layer `l`: the one-time signature of what the layer below gives
(`LayerSignature`, `scheme.rs`), and the key's authentication path in its tree, from the leaf
up (`LeanSphincsSignature::path`, `scheme.rs`). -/
structure LayerSignature (layer : Layer) where
  /-- The WOTS+C counter `c_l`. -/
  counter : EncodingCounter
  /-- Chain `i` opened to its codeword digit. -/
  chainValues : ChainIndex → Digest
  /-- The siblings from the key's leaf up to its tree's root. -/
  authenticationPath : Fin (layerHeight layer) → Digest
deriving DecidableEq

/-- The randomizer, the FORS opening, and each layer's one-time signature and path, bottom first:
7740 bytes (`LeanSphincsSignature`, `scheme.rs`; `SIG_SIZE`, `mod.rs`). The crate
keeps the three paths in one array, `paths`, read by layer (`path`). -/
structure Signature where
  /-- The randomizer `R`. -/
  randomizer : Randomizer
  /-- The FORS opening, one per tree. -/
  forsOpening : ForsTreeIndex → ForsTreeOpening
  /-- Each layer's signature, bottom first. -/
  layers : (layer : Layer) → LayerSignature layer
deriving DecidableEq

/-! #### Addresses -/

/-- FIPS 205's address types (§4.2), and WOTS+C's encoding, which FIPS 205 has none of
(`hash.rs`). -/
inductive AddressType where
  /-- `WOTS_HASH = 0`: a step of a chain. -/
  | wotsHash
  /-- `WOTS_PK = 1`: a one-time key's leaf, the hash of its chain ends. -/
  | wotsPublicKey
  /-- `TREE = 2`: a node of a tree of the hypertree. -/
  | tree
  /-- `FORS_TREE = 3`: a leaf or a node of a FORS tree. -/
  | forsTree
  /-- `FORS_ROOTS = 4`: the FORS public key, the hash of the roots. -/
  | forsRoots
  /-- `WOTS_PRF = 5`: the start of a chain. -/
  | wotsPrf
  /-- `FORS_PRF = 6`: the secret of a FORS leaf. -/
  | forsPrf
  /-- `WOTS_ENC = 7`: a WOTS+C encoding. -/
  | wotsEncoding
deriving DecidableEq

/-- The type word of each address type (`hash.rs`). -/
def AddressType.word : AddressType → Nat
  | .wotsHash => 0
  | .wotsPublicKey => 1
  | .tree => 2
  | .forsTree => 3
  | .forsRoots => 4
  | .wotsPrf => 5
  | .forsPrf => 6
  | .wotsEncoding => 7

/-- `ADRS` (`Adrs`, `hash.rs`): the layer address (bytes 0..4), the tree address (bytes
4..16, of which the crate writes a 64-bit tree into bytes 8..16), the type (16..20), then three
words whose meaning the type gives: the key pair address, the chain address or tree height, and
the hash address or tree index. -/
structure Address where
  /-- The layer, counted from the bottom. -/
  layer : BitVec 32
  /-- The tree on that layer. -/
  tree : BitVec 64
  /-- The type. -/
  addressType : AddressType
  /-- The key pair address: a one-time key's leaf. -/
  keyPair : BitVec 32
  /-- The chain address, or the tree height. -/
  chainOrTreeHeight : BitVec 32
  /-- The hash address (the position a chain step leaves), or the tree index. -/
  hashOrTreeIndex : BitVec 32
deriving DecidableEq

/-- The 32 address bytes: eight big-endian words, the tree's 64 bits in the last two of the three
tree words (`Adrs::new`, `word`, `as_bytes`, `hash.rs`). -/
def Address.toBytes (address : Address) : HashInput :=
  bigEndianBytes 4 address.layer ++ bigEndianBytes 4 0 ++ bigEndianBytes 8 address.tree ++
    bigEndianBytes 4 (BitVec.ofNat 32 address.addressType.word) ++
    bigEndianBytes 4 address.keyPair ++ bigEndianBytes 4 address.chainOrTreeHeight ++
    bigEndianBytes 4 address.hashOrTreeIndex

/-- `Adrs::new(layer, tree).with_type(t)` with its last three words set (`new`, `with_type`,
`with_key_pair`, `with_chain`, `with_tree_height`, `with_hash`, `with_tree_index`,
`hash.rs`). -/
def makeAddress (layer tree : Nat) (addressType : AddressType)
    (keyPair chainOrTreeHeight hashOrTreeIndex : Nat) : Address :=
  ⟨BitVec.ofNat 32 layer, BitVec.ofNat 64 tree, addressType, BitVec.ofNat 32 keyPair,
    BitVec.ofNat 32 chainOrTreeHeight, BitVec.ofNat 32 hashOrTreeIndex⟩

/-- The tree index of node `node` at height `height` of FORS tree `κ`, counting across the trees:
`κ 2^(a - height) + node` (`fors_node_adrs`, `fors.rs`). -/
def forsTreeIndex (forsTree : ForsTreeIndex) (height node : Nat) : Nat :=
  forsTree.val * 2 ^ (forsTreeHeight - height) + node

/-- The hash domains of `F`, `H` and `T_l`; the secrets' `PRF` calls use `KeygenDomain`. -/
inductive HashDomain where
  /-- The step leaving position `step` of chain `chainIndex` of the one-time key
  `(layer, tree, leaf)`. -/
  | chain (layer : Layer) (tree : TreeIndex) (leaf : TreeLeafIndex) (chainIndex : ChainIndex)
      (step : ChainStep)
  /-- The one-time key's leaf, the hash of its chain ends. -/
  | leaf (layer : Layer) (tree : TreeIndex) (leaf : TreeLeafIndex)
  /-- Node `nodeIndex` at height `height` of tree `tree` of layer `layer`. -/
  | node (layer : Layer) (tree : TreeIndex) (height : Nat) (nodeIndex : Nat)
  /-- The WOTS+C encoding of the one-time key `(layer, tree, leaf)`. -/
  | encoding (layer : Layer) (tree : TreeIndex) (leaf : TreeLeafIndex)
  /-- Leaf `forsLeaf` of FORS tree `forsTree` of instance `index`, the hash of its secret. -/
  | forsLeaf (index : Index) (forsTree : ForsTreeIndex) (forsLeaf : ForsLeafIndex)
  /-- Node `node` at height `height` (`1` to `a`, the root) of FORS tree `forsTree` of instance
  `index`. -/
  | forsNode (index : Index) (forsTree : ForsTreeIndex) (height : Nat) (node : Nat)
  /-- The FORS public key of instance `index`, the hash of its trees' roots. -/
  | forsRoots (index : Index)
deriving DecidableEq

/-- The address of a hash domain. A one-time key's address is its tree's with its leaf as the key
pair (`OtsKey::adrs`, `wots.rs`); a chain step carries the chain and the position it leaves
(`chain`, `wots.rs`), the leaf has type `WOTS_PK` (`wots_leaf_hash`, `wots.rs`), the
encoding `WOTS_ENC` (`encoder`, `wots.rs`); a node of the hypertree its height and index,
key pair zero (`node`, `scheme.rs`). A FORS instance's address is that of the bottom key
of its index, `K_0(idx)` (`fors_adrs`, `fors.rs`): a leaf has height `0`, a node its height,
each the tree index of `forsTreeIndex` (`fors_node_adrs`, `fors_leaf`, `fors_node`,
`fors.rs`), and the roots' hash type `FORS_ROOTS` (`fors_key`, `fors.rs`). -/
def hashDomainFields : HashDomain → Address
  | .chain layer tree leaf chainIndex step =>
      makeAddress layer.val tree.val .wotsHash leaf.val chainIndex.val step.val
  | .leaf layer tree leaf => makeAddress layer.val tree.val .wotsPublicKey leaf.val 0 0
  | .node layer tree height nodeIndex => makeAddress layer.val tree.val .tree 0 height nodeIndex
  | .encoding layer tree leaf => makeAddress layer.val tree.val .wotsEncoding leaf.val 0 0
  | .forsLeaf index forsTree forsLeaf =>
      makeAddress 0 (treeOfIndex 0 index).val .forsTree (leafOfIndex 0 index).val 0
        (forsTreeIndex forsTree 0 forsLeaf.val)
  | .forsNode index forsTree height node =>
      makeAddress 0 (treeOfIndex 0 index).val .forsTree (leafOfIndex 0 index).val height
        (forsTreeIndex forsTree height node)
  | .forsRoots index =>
      makeAddress 0 (treeOfIndex 0 index).val .forsRoots (leafOfIndex 0 index).val 0 0

/-- The secrets, one `PRF` call on `SK.seed` each: `oneTimeChain` the start of a chain of a
one-time key, `forsSecret` the secret of a leaf of a FORS tree. -/
inductive KeygenDomain where
  /-- The start of chain `chainIndex` of the one-time key `(layer, tree, leaf)`. -/
  | oneTimeChain (layer : Layer) (tree : TreeIndex) (leaf : TreeLeafIndex)
      (chainIndex : ChainIndex)
  /-- The secret of leaf `forsLeaf` of FORS tree `forsTree` of instance `index`. -/
  | forsSecret (index : Index) (forsTree : ForsTreeIndex) (forsLeaf : ForsLeafIndex)
deriving DecidableEq

/-- `WOTS_PRF` at the one-time key with the chain (`wots_secrets`, `wots.rs`), `FORS_PRF` at
the instance with the leaf's tree index, height `0` (`fors_secret`, `fors.rs`). -/
def keygenDomainFields : KeygenDomain → Address
  | .oneTimeChain layer tree leaf chainIndex =>
      makeAddress layer.val tree.val .wotsPrf leaf.val chainIndex.val 0
  | .forsSecret index forsTree forsLeaf =>
      makeAddress 0 (treeOfIndex 0 index).val .forsPrf (leafOfIndex 0 index).val 0
        (forsTreeIndex forsTree 0 forsLeaf.val)

/-- `PK.seed ‖ ADRS ‖ M`, the input of every addressed hash (`hasher`, `lib.rs`,
`hash.rs`). -/
def addressedHashInput (publicSeed : PublicParameter) (address : Address) (payload : HashInput) :
    HashInput :=
  hasherInput publicSeed address.toBytes payload

/-- `SEED_TAG`, the 11 ASCII bytes of `leanSPHINCS` (`mod.rs`). -/
def seedTag : HashInput := [0x6c, 0x65, 0x61, 0x6e, 0x53, 0x50, 0x48, 0x49, 0x4e, 0x43, 0x53]

/-- `CONTEXT`, the context string `PRF_msg` frames the message under: the scheme's tag, `SEED_TAG`
(`hash.rs`). -/
def contextString : HashInput := seedTag

/-- `M' = 0x00 ‖ len(ctx) ‖ ctx ‖ M`, 45 bytes, pure SLH-DSA's framing, which only `PRF_msg` hashes
(`framed`, `hash.rs`). -/
def framedMessage (message : Message) : HashInput :=
  [0x00, UInt8.ofNat contextString.length] ++ contextString ++ littleEndianBytes 32 message

/-! #### The message digest: two calls, `m = 34` bytes -/

/-- `m`, the bytes of `H_msg`: `30 + 3 + 1 = 34` (`DIGEST_BYTES`, `mod.rs`). -/
def digestByteCount : Nat := 34
/-- `⌈k a / 8⌉ = 30`, the bytes of the FORS message `md` (`MD_BYTES`, `mod.rs`). -/
def forsMessageByteCount : Nat := 30
/-- `⌈(h - h_0) / 8⌉ = 3`, the bytes of the tree index (`TREE_INDEX_BYTES`, `mod.rs`). -/
def treeIndexByteCount : Nat := 3
/-- `⌈h_0 / 8⌉ = 1`, the bytes of the bottom leaf index (`LEAF_INDEX_BYTES`, `mod.rs`). -/
def leafIndexByteCount : Nat := 1

/-- The Keccak-256 calls that give them, `⌈34 / 32⌉ = 2` (`DIGEST_CALLS`, `mod.rs`). -/
def digestCallCount : Nat := 2

/-- A digest call `i`, which its counter carries. -/
abbrev DigestCall := Fin digestCallCount

instance : NeZero digestCallCount := ⟨by decide⟩

/-- `H_msg`'s `m` bytes, `g_0` the low byte (little-endian, as `littleEndianBytes` lays them out).
-/
abbrev MessageDigest := BitVec (8 * digestByteCount)

/-- `D_0 ‖ D_1` as one little-endian number, call `0` in the low `256` bits. -/
def digestValue (outputs : DigestCall → HashOutput) : Nat :=
  ∑ call : DigestCall, (outputs call).toNat * 2 ^ (256 * call.val)

/-- `Trunc_m(D_0 ‖ D_1)`, the first 34 bytes of the calls (`h_msg`, `hash.rs`: the crate
returns all 64, of which `digest_fields` reads these). -/
def truncateMessageDigest (outputs : DigestCall → HashOutput) : MessageDigest :=
  BitVec.ofNat (8 * digestByteCount) (digestValue outputs)

/-- Byte `g_position` of the digest. -/
def messageDigestByte (digest : MessageDigest) (position : Nat) : Nat :=
  (digest.extractLsb' (8 * position) 8).toNat

/-- Bit `position` of the digest, each byte's most significant bit first: `digest[p / 8] >>
(7 - p % 8) & 1` (`digest_fields`, `scheme.rs`). -/
def messageDigestBit (digest : MessageDigest) (position : Nat) : Nat :=
  messageDigestByte digest (position / 8) / 2 ^ (7 - position % 8) % 2

/-- `toInt`: the `count` bytes from byte `start`, a big-endian integer (`int`,
`scheme.rs`). -/
def messageDigestBigEndian (digest : MessageDigest) (start count : Nat) : Nat :=
  (List.range count).foldl (fun value j ↦ 256 * value + messageDigestByte digest (start + j)) 0

/-- `idx`: the tree index, the 3 bytes after `md` cut to `h - h_0 = 18` bits, then the bottom leaf,
the last byte cut to `h_0 = 8` bits (`digest_fields`, `scheme.rs`; FIPS 205 Algorithm 19).
-/
def digestIndex (digest : MessageDigest) : Index :=
  ⟨messageDigestBigEndian digest forsMessageByteCount treeIndexByteCount % 2 ^ 18 * 2 ^ 8 +
      messageDigestBigEndian digest (forsMessageByteCount + treeIndexByteCount)
        leafIndexByteCount % 2 ^ 8, by
    have htree := Nat.mod_lt
      (messageDigestBigEndian digest forsMessageByteCount treeIndexByteCount)
      (show 2 ^ 18 > 0 by decide)
    have hleaf := Nat.mod_lt
      (messageDigestBigEndian digest (forsMessageByteCount + treeIndexByteCount)
        leafIndexByteCount) (show 2 ^ 8 > 0 by decide)
    change _ < 2 ^ 26
    omega⟩

/-- `s_κ`, the `a` bits of `md` from bit `a κ`, most significant first: `base_2b(md, a, k)`
(`digest_fields`, `scheme.rs`; FIPS 205 Algorithms 4 and 19). -/
def digestForsLeaves (digest : MessageDigest) : ForsTreeIndex → ForsLeafIndex := fun forsTree =>
  forsLeafOfNat ((List.range forsTreeHeight).foldl
    (fun value j ↦ 2 * value + messageDigestBit digest (forsTreeHeight * forsTree.val + j)) 0)

/-! #### The target-sum code

`v = 64` chunks of `w = 2` bits covering the 128 digest bits, read as FIPS 205's `base_2b` reads
them, and the code is the words of digit sum `T = 128` (`codeword`, `wots.rs`). -/

namespace TargetSum

/-- The digit sum of a word. -/
def sum (x : Encoding) : Nat := ∑ i, (x i).val

/-- Membership in the code `C`: digit sum `T`. -/
abbrev Valid (x : Encoding) : Prop := sum x = targetSum

/-- `base_2b(D, w, v)` (FIPS 205 Algorithm 4): digit `i` is bits `6 - 2 (i mod 4)` and
`7 - 2 (i mod 4)` of byte `⌊i / 4⌋` of the digest, each byte's most significant bits first
(`codeword`, `wots.rs`). -/
def base2bDigits (digest : Digest) : Encoding := fun i =>
  (digest.extractLsb' (8 * (i.val / 4) + 6 - 2 * (i.val % 4)) winternitzBits).toFin

/-- A digest decodes exactly when its 64 digits reach the target sum. -/
def decodeDigest (digest : Digest) : Option Encoding :=
  if Valid (base2bDigits digest) then some (base2bDigits digest) else none

end TargetSum

/-! ### The algorithms, over a permutation `π` of the Keccak state in any monad -/

namespace Verification

open LeanVM.Semantics (KeccakState)
open HashSig.OverPermutation

variable {m : Type → Type} [Monad m] (π : KeccakState → m KeccakState)

/-- `Trunc_16(H(PK.seed ‖ ADRS ‖ M))` at an address (`th`, `hash.rs`; `truncate`,
`lib.rs`). -/
def addressedHash (publicSeed : PublicParameter) (address : Address) (payload : HashInput) :
    m Digest := do
  return truncateHash (← keccakHash π (addressedHashInput publicSeed address payload))

/-- `F`, `H` and `T_l` at a hash domain's address (`th`, `th_digests`, `hash.rs`). -/
abbrev tweakableHash (publicSeed : PublicParameter) (domain : HashDomain) (payload : HashInput) :
    m Digest :=
  addressedHash π publicSeed (hashDomainFields domain) payload

/-! #### The one-time signature -/

/-- Chain `i` of the one-time key `(layer, tree, leaf)`: the step onto position `t + 1` carries
step `t` (`chain`, `wots.rs`: a step carries the position it leaves). -/
def chainWalk (publicSeed : PublicParameter) (layer : Layer) (tree : TreeIndex)
    (leaf : TreeLeafIndex) (chainIndex : ChainIndex) : Nat → Nat → Digest → m Digest :=
  walkChain fun step value ↦
    tweakableHash π publicSeed (.chain layer tree leaf chainIndex step) (littleEndianBytes 16 value)

/-- The verifier's half of a chain: walk the remaining `3 - x_i` steps. -/
def recoverChain (publicSeed : PublicParameter) (layer : Layer) (tree : TreeIndex)
    (leaf : TreeLeafIndex) (chainIndex : ChainIndex) (digit : WinternitzDigit) (value : Digest) :
    m Digest :=
  chainWalk π publicSeed layer tree leaf chainIndex digit.val (chainLength - 1 - digit.val) value

/-- The one-time leaf: `T_v` of the `v` chain ends (`wots_leaf_hash`, `wots.rs`). -/
def leafHash (publicSeed : PublicParameter) (layer : Layer) (tree : TreeIndex)
    (leaf : TreeLeafIndex) (endpoints : ChainIndex → Digest) : m Digest :=
  tweakableHash π publicSeed (.leaf layer tree leaf) (digestsPayload endpoints)

/-- `Enc(K, M, c)` (`encoder`, `encode`, `wots.rs`): `Trunc_16(H(PK.seed ‖ ADRS_enc(K) ‖ M ‖
BE_32(c)))`, 68 bytes, decoded. -/
def encode (publicSeed : PublicParameter) (layer : Layer) (tree : TreeIndex)
    (leaf : TreeLeafIndex) (message : Digest) (counter : EncodingCounter) :
    m (Option Encoding) := do
  let digest ← tweakableHash π publicSeed (.encoding layer tree leaf)
    (littleEndianBytes 16 message ++ bigEndianBytes 4 counter)
  return TargetSum.decodeDigest digest

/-- `Wots.leaf` (`wots_leaf`, `wots.rs`): the leaf a claimed one-time signature of `M`
recovers, or nothing if the counter does not encode `M`. -/
def otsLeaf (publicSeed : PublicParameter) (layer : Layer) (tree : TreeIndex)
    (leaf : TreeLeafIndex) (message : Digest) (counter : EncodingCounter)
    (values : ChainIndex → Digest) : m (Option Digest) := do
  let some encoding ← encode π publicSeed layer tree leaf message counter | return none
  let endpoints ← sequenceFin fun chainIndex =>
    recoverChain π publicSeed layer tree leaf chainIndex (encoding chainIndex) (values chainIndex)
  let value ← leafHash π publicSeed layer tree leaf endpoints
  return some value

/-! #### The hypertree -/

/-- `Tree.fold` (`tree_fold`, `scheme.rs`; `path_fold`, `lib.rs`): fold the key's
leaf value and a path into its tree's root, the node at height `z + 1` hashing its children in index
order. -/
def treeFold (publicSeed : PublicParameter) (layer : Layer) (tree : TreeIndex)
    (leaf : TreeLeafIndex) (path : Nat → Digest) : Nat → Digest → m Digest :=
  foldPath
    (fun level nodeIndex ↦ tweakableHash π publicSeed (.node layer tree (level + 1) nodeIndex))
    leaf.val path

/-! #### FORS -/

/-- A FORS leaf: `F` of its secret (`fors_leaf`, `fors.rs`). -/
def forsLeafHash (publicSeed : PublicParameter) (index : Index) (forsTree : ForsTreeIndex)
    (leaf : ForsLeafIndex) (secret : Digest) : m Digest :=
  tweakableHash π publicSeed (.forsLeaf index forsTree leaf) (littleEndianBytes 16 secret)

/-- The root of a FORS tree an opening reaches: the leaf hashed, then folded up its `a` path
nodes, the node at height `z + 1` hashing its children in index order (`fors_recover`,
`fors.rs`; `path_fold`, `lib.rs`). -/
def forsTreeRecover (publicSeed : PublicParameter) (index : Index) (forsTree : ForsTreeIndex)
    (leaf : ForsLeafIndex) (opening : ForsTreeOpening) : m Digest := do
  let value ← forsLeafHash π publicSeed index forsTree leaf opening.secret
  foldPath
    (fun level node ↦ tweakableHash π publicSeed (.forsNode index forsTree (level + 1) node))
    leaf.val (fun level ↦ if h : level < forsTreeHeight then opening.path ⟨level, h⟩ else 0)
    forsTreeHeight value

/-- `T_k` of the roots: the FORS public key (`fors_key`, `fors.rs`). -/
def forsPublicKey (publicSeed : PublicParameter) (index : Index)
    (roots : ForsTreeIndex → Digest) : m Digest :=
  tweakableHash π publicSeed (.forsRoots index) (digestsPayload roots)

/-- `fors_pkFromSig` (`fors_recover`, `fors.rs`): the FORS public key an opening reaches at
the digest's leaves, `T_k` of the roots its trees reach. -/
def forsRecover (publicSeed : PublicParameter) (index : Index)
    (leaves : ForsTreeIndex → ForsLeafIndex) (opening : ForsTreeIndex → ForsTreeOpening) :
    m Digest := do
  let roots ← sequenceFin fun forsTree =>
    forsTreeRecover π publicSeed index forsTree (leaves forsTree) (opening forsTree)
  forsPublicKey π publicSeed index roots

/-! #### The message digest -/

/-- Digest call `i`, `D_i = H(R ‖ PK.seed ‖ PK.root ‖ M ‖ BE_32(i))`, 84 bytes, untruncated, the
32-byte message unframed (`h_msg`, `hash.rs`). -/
def messageDigestCall (randomizer : Randomizer) (publicSeed : PublicParameter) (root : Digest)
    (message : Message) (call : DigestCall) : m HashOutput :=
  keccakHash π (littleEndianBytes 16 randomizer ++ littleEndianBytes 16 publicSeed ++
    littleEndianBytes 16 root ++ littleEndianBytes 32 message ++
    bigEndianBytes 4 (BitVec.ofNat 32 call.val))

/-- `H_msg(R, PK.seed, PK.root, M)`, the key's (`message_digest`, `scheme.rs`). -/
def messageDigest (publicKey : PublicKey) (randomizer : Randomizer) (message : Message) :
    m MessageDigest := do
  let outputs ← sequenceFin fun call =>
    messageDigestCall π randomizer publicKey.publicSeed publicKey.root message call
  return truncateMessageDigest outputs

/-! #### Verification -/

/-- Layer `l`'s path, read as a function of the level (`0` past its height). -/
def layerPath (signature : Signature) (layer : Layer) (level : Nat) : Digest :=
  if h : level < layerHeight layer then (signature.layers layer).authenticationPath ⟨level, h⟩
  else 0

/-- The walk up the hypertree, `layersLeft + 1` layers from the top: at layer
`l = d - 1 - layersLeft`, whose one-time key `K_l(idx)` signs `message` (the FORS public key at the
bottom, the root of the tree below above it), recover the one-time leaf and fold its path; the top
layer's root is the result (the loop of `verify`, `scheme.rs`). -/
def verifyLayers (publicSeed : PublicParameter) (index : Index) (signature : Signature) :
    Nat → Digest → m (Option Digest)
  | 0, _ => pure none
  | layersLeft + 1, message => do
      if hlayer : layersLeft < layerCount then
        let layer : Layer := ⟨layerCount - 1 - layersLeft, by omega⟩
        let tree := treeOfIndex layer index
        let leaf := leafOfIndex layer index
        let some value ← otsLeaf π publicSeed layer tree leaf message
            (signature.layers layer).counter (signature.layers layer).chainValues
          | return none
        let root ← treeFold π publicSeed layer tree leaf (layerPath signature layer)
          (layerHeight layer) value
        if layersLeft = 0 then
          return some root
        else
          verifyLayers publicSeed index signature layersLeft root
      else
        pure none

/-- `Ver(pk, m, σ)` (`verify`, `scheme.rs`): compute the digest, recover the FORS public
key, walk the layers up (the one-time leaf, the path) and compare with `PK.root`. -/
def verify (publicKey : PublicKey) (message : Message) (signature : Signature) : m Bool := do
  let digest ← messageDigest π publicKey signature.randomizer message
  let index := digestIndex digest
  let forsKey ← forsRecover π publicKey.publicSeed index (digestForsLeaves digest)
    signature.forsOpening
  let some root ← verifyLayers π publicKey.publicSeed index signature layerCount forsKey
    | return false
  return decide (root = publicKey.root)

end Verification

/-- **leanSPHINCS verification as deployed**: over Keccak-f[1600], the hash Keccak-256. -/
def verifyWithKeccak (publicKey : PublicKey) (message : Message) (signature : Signature) : Bool :=
  Id.run (Verification.verify (m := Id) LeanVM.Semantics.keccakF1600 publicKey message signature)

namespace KeyGenerationAndSigning

open Verification HashSig.OverPermutation
open LeanVM.Semantics (KeccakState)

variable {m : Type → Type} [Monad m] (π : KeccakState → m KeccakState)

/-! #### The key -/

/-- What `slh_keygen_internal` takes (`ExpandedKey`, `hash.rs`). -/
structure ExpandedKey where
  /-- `SK.seed`, the secret key. -/
  secretSeed : MasterSeed
  /-- `SK.prf`, 32 bytes. -/
  secretPrfKey : HashOutput
  /-- `PK.seed`. -/
  publicSeed : PublicParameter

/-- `leanSPHINCS ‖ SK.seed ‖ domain`, 44 bytes. -/
def keyDerivationInput (secretSeed : MasterSeed) (domain : UInt8) : HashInput :=
  seedTag ++ littleEndianBytes 32 secretSeed ++ [domain]

/-- `expand_key` (`hash.rs`): `SK.prf = H(leanSPHINCS ‖ SK.seed ‖ 1)`, then
`PK.seed = Trunc_16(H(leanSPHINCS ‖ SK.seed ‖ 0))`, in the order the crate's struct literal
computes them. -/
def expandKey (secretSeed : SecretKey) : m ExpandedKey := do
  let secretPrfKey ← keccakHash π (keyDerivationInput secretSeed 1)
  let publicSeedOutput ← keccakHash π (keyDerivationInput secretSeed 0)
  return ⟨secretSeed, secretPrfKey, truncateHash publicSeedOutput⟩

/-- `PRF(PK.seed, SK.seed, ADRS) = Trunc_16(H(PK.seed ‖ ADRS ‖ SK.seed))` at a secret's address
(`prf`, `hash.rs`). -/
def prf (key : ExpandedKey) (domain : KeygenDomain) : m Digest :=
  addressedHash π key.publicSeed (keygenDomainFields domain) (littleEndianBytes 32 key.secretSeed)

/-- `PRF_msg(SK.prf, opt_rand, M') = Trunc_16(H(SK.prf ‖ opt_rand ‖ M'))`, 93 bytes (`prf_msg`,
`hash.rs`). -/
def prfMessage (secretPrfKey : HashOutput) (optionalRandomness : Digest) (message : Message) :
    m Randomizer := do
  return truncateHash (← keccakHash π (littleEndianBytes 32 secretPrfKey ++
    littleEndianBytes 16 optionalRandomness ++ framedMessage message))

/-! #### Trees -/

/-- Node `index` of a level, `0` past its end. -/
def levelNode (levels : List (List Digest)) (level index : Nat) : Digest :=
  (levels.getD level []).getD index 0

/-- The levels from `below`, at height `height`, up `remaining` levels: `below` first, then node
`j` of the level above hashing nodes `2j` and `2j + 1` (`node (height + 1) j children`). -/
def merkleLevelsFrom (node : Nat → Nat → HashInput → m Digest) (height : Nat)
    (below : List Digest) : Nat → m (List (List Digest))
  | 0 => pure [below]
  | remaining + 1 => do
      let above ← (List.range (below.length / 2)).mapM fun j ↦
        node (height + 1) j (nodePayload (below.getD (2 * j) 0) (below.getD (2 * j + 1) 0))
      return below :: (← merkleLevelsFrom node (height + 1) above remaining)

/-- `merkle_levels` (`scheme.rs`): the levels of a tree `height` levels over `leaves`, the
leaves first, each level hashed left to right before the next. -/
def merkleLevels (node : Nat → Nat → HashInput → m Digest) (leaves : List Digest)
    (height : Nat) : m (List (List Digest)) :=
  merkleLevelsFrom node 0 leaves height

/-! #### One-time keys and the hypertree -/

/-- `wots_secrets` (`wots.rs`): the starts of the 64 chains of the one-time key
`(layer, tree, leaf)`, one `PRF` each. -/
def otsSecrets (key : ExpandedKey) (layer : Layer) (tree : TreeIndex) (leaf : TreeLeafIndex) :
    m (ChainIndex → Digest) :=
  sequenceFin fun chainIndex ↦ prf π key (.oneTimeChain layer tree leaf chainIndex)

/-- `wots_public_leaf` (`wots.rs`): the leaf of a one-time key from its secrets, the chains
walked to their ends and hashed. -/
def otsPublicLeaf (key : ExpandedKey) (layer : Layer) (tree : TreeIndex) (leaf : TreeLeafIndex) :
    m Digest := do
  let secrets ← otsSecrets π key layer tree leaf
  let endpoints ← sequenceFin fun chainIndex =>
    chainWalk π key.publicSeed layer tree leaf chainIndex 0 (chainLength - 1) (secrets chainIndex)
  leafHash π key.publicSeed layer tree leaf endpoints

/-- The encoding counters `counter, counter + 1, ...`, at most `attempts` of them, stopping at the
first that encodes the message; then the chain starts and the chains opened to its digits. -/
def otsSignFrom (key : ExpandedKey) (layer : Layer) (tree : TreeIndex) (leaf : TreeLeafIndex)
    (message : Digest) : Nat → Nat → m (Option (EncodingCounter × (ChainIndex → Digest)))
  | 0, _ => pure none
  | attempts + 1, counter => do
      match ← encode π key.publicSeed layer tree leaf message
          (BitVec.ofNat counterBits counter) with
      | some encoding => do
          let secrets ← otsSecrets π key layer tree leaf
          let values ← sequenceFin fun chainIndex =>
            chainWalk π key.publicSeed layer tree leaf chainIndex 0 (encoding chainIndex).val
              (secrets chainIndex)
          return some (BitVec.ofNat counterBits counter, values)
      | none => otsSignFrom key layer tree leaf message attempts (counter + 1)

/-- `Wots.sign` (`wots_sign`, `wots.rs`): the least admissible counter below `C_max`, then
the opened chain values. -/
def otsSign (key : ExpandedKey) (layer : Layer) (tree : TreeIndex) (leaf : TreeLeafIndex)
    (message : Digest) : m (Option (EncodingCounter × (ChainIndex → Digest))) :=
  otsSignFrom π key layer tree leaf message encodingAttemptLimit 0

/-- `tree_levels` (`scheme.rs`): the levels of tree `tree` of layer `layer`, its leaves
first (each a one-time key's leaf; the crate computes them in parallel, here in leaf order) and
its root last. -/
def treeLevels (key : ExpandedKey) (layer : Layer) (tree : TreeIndex) :
    m (List (List Digest)) := do
  let leaves ← (List.range (2 ^ layerHeight layer)).mapM fun leaf ↦
    otsPublicLeaf π key layer tree (leafOfNat leaf)
  merkleLevels
    (fun height nodeIndex ↦ tweakableHash π key.publicSeed (.node layer tree height nodeIndex))
    leaves (layerHeight layer)

/-! #### FORS -/

/-- `fors_skGen` (`fors_secret`, `fors.rs`): the secret of leaf `s` of tree `κ`, one `PRF`.
-/
def forsSecret (key : ExpandedKey) (index : Index) (forsTree : ForsTreeIndex)
    (leaf : ForsLeafIndex) : m Digest :=
  prf π key (.forsSecret index forsTree leaf)

/-- FORS tree `forsTree` of instance `index`, built once (the closure of `fors_open`,
`fors.rs`): its secrets, its leaves, its levels; its root, and its opening at `leaf`. -/
def forsTreeOpen (key : ExpandedKey) (index : Index) (forsTree : ForsTreeIndex)
    (leaf : ForsLeafIndex) : m (Digest × ForsTreeOpening) := do
  let secrets ← (List.range (2 ^ forsTreeHeight)).mapM fun s ↦
    forsSecret π key index forsTree (forsLeafOfNat s)
  let leafHashes ← (List.range (2 ^ forsTreeHeight)).mapM fun s ↦
    forsLeafHash π key.publicSeed index forsTree (forsLeafOfNat s) (secrets.getD s 0)
  let levels ← merkleLevels
    (fun height node ↦ tweakableHash π key.publicSeed (.forsNode index forsTree height node))
    leafHashes forsTreeHeight
  return (levelNode levels forsTreeHeight 0,
    ⟨secrets.getD leaf.val 0, fun z ↦ levelNode levels z.val ((leaf.val >>> z.val) ^^^ 1)⟩)

/-- `fors_sign` and the FORS public key (`fors_open`, `fors.rs`): every tree of instance
`index` built once (the crate builds them in parallel, here in tree order), then `T_k` of their
roots; the key and the opening at the digest's leaves. -/
def forsOpen (key : ExpandedKey) (index : Index) (leaves : ForsTreeIndex → ForsLeafIndex) :
    m (Digest × (ForsTreeIndex → ForsTreeOpening)) := do
  let trees ← sequenceFin fun forsTree => forsTreeOpen π key index forsTree (leaves forsTree)
  let forsKey ← forsPublicKey π key.publicSeed index fun forsTree => (trees forsTree).1
  return (forsKey, fun forsTree => (trees forsTree).2)

/-! #### Key generation and signing -/

/-- `slh_keygen_internal` (`keygen`, `scheme.rs`): the public key, `PK.seed` and the root
of the top tree (tree `0` of the top layer, `OtsKey::of_index(LAYERS - 1, 0)`), with the top tree's
levels, which signing reuses. -/
def keygenInternal (key : ExpandedKey) : m (PublicKey × List (List Digest)) := do
  let top ← treeLevels π key topLayer 0
  return (⟨key.publicSeed, levelNode top (layerHeight topLayer) 0⟩, top)

/-- `Gen` (`key_gen_from_seed`, `scheme.rs`): the secret key is `SK.seed`, the public key
that of its expansion. -/
def keygenFromSeed (secretSeed : SecretKey) : m (PublicKey × SecretKey) := do
  let key ← expandKey π secretSeed
  let (publicKey, _) ← keygenInternal π key
  return (publicKey, secretSeed)

/-- Layer `l`'s one-time signature of `message` with `K_l(idx)` (`wots_sign`), then the key's
tree's levels, built here below the top layer and `top` (key generation's) at it: the layer's
signature with the key's path, and the tree's root, which the layer above signs (the loop of
`sign_with`, `scheme.rs`). -/
def signLayer (key : ExpandedKey) (top : List (List Digest)) (index : Index) (layer : Layer)
    (message : Digest) : m (Option (LayerSignature layer × Digest)) := do
  let tree := treeOfIndex layer index
  let leaf := leafOfIndex layer index
  let some (counter, values) ← otsSign π key layer tree leaf message | return none
  let levels ← if layer = topLayer then pure top else treeLevels π key layer tree
  return some (⟨counter, values, fun z ↦ levelNode levels z.val ((leaf.val >>> z.val) ^^^ 1)⟩,
    levelNode levels (layerHeight layer) 0)

/-- The three layers' signatures, bottom first. -/
def layerSignatures (bottom : LayerSignature 0) (middle : LayerSignature 1)
    (top : LayerSignature 2) : (layer : Layer) → LayerSignature layer
  | ⟨0, _⟩ => bottom
  | ⟨1, _⟩ => middle
  | ⟨2, _⟩ => top
  | ⟨_ + 3, h⟩ => absurd h (by unfold layerCount; omega)

/-- `slh_sign_internal`, deterministic (`opt_rand = PK.seed`; `sign_with`, `scheme.rs`):
key generation's top tree and public key, the randomizer `R = PRF_msg(SK.prf, PK.seed, M')`, the
digest's index and leaves, the FORS instance built once (its key and its opening), then the layers
from the bottom up, each signing what the layer below gives: the FORS public key at the bottom,
the root of the tree below above it. -/
def signWithExpandedKey (key : ExpandedKey) (message : Message) : m (Option Signature) := do
  let (publicKey, top) ← keygenInternal π key
  let randomizer ← prfMessage π key.secretPrfKey key.publicSeed message
  let digest ← messageDigest π publicKey randomizer message
  let index := digestIndex digest
  let (forsKey, forsOpening) ← forsOpen π key index (digestForsLeaves digest)
  let some (bottom, bottomRoot) ← signLayer π key top index 0 forsKey | return none
  let some (middle, middleRoot) ← signLayer π key top index 1 bottomRoot | return none
  let some (topSignature, _) ← signLayer π key top index 2 middleRoot | return none
  return some ⟨randomizer, forsOpening, layerSignatures bottom middle topSignature⟩

/-- `Sign` (`sign`, `scheme.rs`): the key's expansion (`expand_key`), then `sign_with`. -/
def sign (secretKey : SecretKey) (message : Message) : m (Option Signature) := do
  let key ← expandKey π secretKey
  signWithExpandedKey π key message

end KeyGenerationAndSigning

/-! ## Forgeries and transcripts -/

/-- A claimed forgery: a message and a signature. -/
structure Forgery where
  /-- The message. -/
  message : Message
  /-- Its claimed signature. -/
  signature : Signature
deriving DecidableEq

/-- The signing oracle answers a message with a signature, or `none` if the signer fails. -/
abbrev SigningOracleSpec := Message →ₒ Option Signature

namespace SigningTranscript

/-- A transcript is valid when it has at most `signatureLimit` requests. -/
abbrev WithinSignatureLimit (log : QueryLog SigningOracleSpec) : Prop :=
  log.length ≤ signatureLimit

end SigningTranscript

/-! ## Security in the random-permutation model -/

namespace RandomPermutationModel

open Common Common.SufCma

/-- leanSPHINCS in the generic SUF-CMA game, over `π` (`queryPermutation`): the seed `SK.seed`, key
generation, the deterministic signer, the verifier, and the winning condition: a valid transcript
without the forgery (`SignerReturnedForgery`). -/
noncomputable def sufCmaScheme :
    Scheme MasterSeed PublicKey SecretKey Message (Option Signature) Forgery where
  sampleSeed := sampleMasterSeed
  generateKeys := KeyGenerationAndSigning.keygenFromSeed queryPermutation
  sign sk message := KeyGenerationAndSigning.sign queryPermutation sk message
  verify pk forgery := Verification.verify queryPermutation pk forgery.message forgery.signature
  winningCondition log forgery :=
    decide (SigningTranscript.WithinSignatureLimit log ∧ ¬SignerReturnedForgery id log
        forgery.message forgery.signature)

end RandomPermutationModel

/-! ### The end statement -/

section EndStatement

open Common.SufCma

/-- The additive constant of leanSPHINCS's bound, in units of `2^-127`, while `q` counts
permutation calls: the random-oracle step's `265072` hash calls (key generation's `264193` and the
forgery's verification's `879`), carried over by the transfer, plus its indifferentiability term's
one unit, rounded up. -/
def securitySlack : Nat := 2 ^ 19

/-- **leanSPHINCS in the random-permutation model**: an adversary that itself makes at most `q`
calls of `π` and `π⁻¹` and at most `N = 1,182,000,000` signing requests forges with probability at
most `(q + 2^19) · 2^-127` (`StronglyUnforgeable` at 127 bits). The signer's hashing, its WOTS+C
counter search included, key generation and the forgery's verification are not charged to `q`.
Proved by `Sphincs.leanSphincsStronglyUnforgeable`. A key past its signature limit, which the signer
does not count, is not covered: keeping within it is the key holder's duty. -/
abbrev LeanSphincsStronglyUnforgeable : Prop :=
  StronglyUnforgeable RandomPermutationModel.sufCmaScheme signatureLimit securitySlack 127

end EndStatement

end Sphincs

end
