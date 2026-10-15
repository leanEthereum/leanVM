import VCVio.OracleComp.QueryTracking.LoggingOracle
import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation

/-!
# leanSPHINCS with a two-level WOTS forest

The scheme of `SphincsFors.Scheme` (one height-26 tree of WOTS+C keys with 64 chains of length 4 and
target sum 120, pruning with surrogate siblings, randomizer grinding, tweakable hash with 16-byte
outputs) with the few-time signature under each tree leaf replaced by a **two-level WOTS forest**:

* 8 independent coordinates; a coordinate is a top Merkle tree of height 4 over 16 super-children,
  hashed up to level 3 only: its two level-3 nodes `t_c[0]`, `t_c[1]` are not hashed into a root. The
  forest public key is `Th(roots(idx), t_0[0] || t_0[1] || ... || t_7[0] || t_7[1])`, the message
  WOTS+C signs;
* a sub-tree is a Merkle tree of height 3 over 8 children, hashed up to level 2 only; super-child `s`
  is `Th(super(idx, c, s), m_0[0] || m_0[1] || m_1[0] || m_1[1])` where `m_j[0]`, `m_j[1]` are the two
  level-2 nodes of sub-tree `j`;
* a child is 6 hash chains of length 5: `x_{i,0}` is derived from the seed (one hash of the seed
  gives the two starts `x_{2t,0}` and `x_{2t+1,0}`, its two 16-byte halves), `x_{i,t+1} = Th(x_{i,t})`,
  and the child leaf hashes the 6 chain tops `x_{i,4}`;
* a codeword is a deficit vector `d ∈ {0..4}^6` with `Σ d_i = 5` (246 of them); `lut` is a fixed list
  of 256 of them (`codewordCodes`): the codewords sorted by decreasing `Σ d_i²`, then
  lexicographically, entry `t` being codeword number `t mod 214`;
* one digest call gives `26 + 8 · 26 = 234` bits. The first 16 bytes are the 16 codeword indices
  (byte `2c + j` for sub-tree `j` of coordinate `c`); then, from bit 128, the index (26 bits), the 8
  super-children (4 bits each, from bit 154) and the 16 children (3 bits each, from bit 186, in the
  order `2c + j`). No field lies across two 64-bit words;
* an opening reveals, per coordinate and sub-tree, `x_{i, 4 - d_i}` for the 6 chains and the 3 auth
  nodes of the sub-tree, then the 4 auth nodes of the top tree. The last auth node of a tree is its
  other top node: the verifier folds all levels but the last and hashes the two top nodes, in index
  order, into the hash above.

Everything that is not the forest (parameters, WOTS+C, the tree, pruning, grinding, key generation)
is `SphincsFors.Scheme` verbatim. Every hash input is `P || A || payload`: the 16-byte public
parameter, then the 16-byte address of the call (a 32-bit field `lo`, a 24-bit field `hi`, one byte
holding the type and a chain step, then 8 zero bytes), so the payload starts at byte 32. Forest
hashes use types 14 (secret derivation) and 15 to 20, with the instance `idx` in `lo` and the
position inside the instance in `hi`. The message digest hashes `m || rho` (the root is not hashed:
`P` binds the key) and the randomizer base `S || m`: the randomizer, which changes between two
grinding attempts, comes last, alone in the second block.
-/

open OracleComp OracleSpec ENNReal

namespace Sphincs

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
/-- `idx`, the leaf and the forest instance a digest selects. -/
abbrev Index := Fin (2 ^ totalHeight)
/-- `tau`, always `0`: the scheme has one tree, and a hash address has no tree field. -/
abbrev TreeIndex := Fin 1
/-- `e`, a leaf of the tree. -/
abbrev LeafIndex := Fin (2 ^ maxLayerHeight)
abbrev ChainIndex := Fin numChains
/-- A pair of chains `(2t, 2t + 1)` of a one-time key, `t < 32`: one seed derivation. -/
abbrev ChainPair := Fin 32
abbrev Digit := Fin chainLength
abbrev ChainStep := Fin (chainLength - 1)
abbrev Encoding := ChainIndex → Digit
abbrev HashInput := List UInt8

/-! ### Forest parameters and types -/

/-- Number of coordinates. -/
def forestCoords : Nat := 8
/-- Height of a coordinate's top tree (16 super-children). -/
def topHeight : Nat := 4
/-- Height of a sub-tree (8 children). -/
def subHeight : Nat := 3
/-- Chains per child. -/
def childChains : Nat := 6
/-- The top position of a chain: positions `0 .. 4`. -/
def chainTop : Nat := 4
/-- The deficit sum of a codeword. -/
def codewordSum : Nat := 5

abbrev Coord := Fin forestCoords
abbrev SuperIdx := Fin (2 ^ topHeight)
abbrev SubIdx := Fin 2
abbrev ChildIdx := Fin (2 ^ subHeight)
abbrev FChain := Fin childChains
/-- A pair of chains `(2t, 2t + 1)` of a forest WOTS key, `t < 3`: one seed derivation. -/
abbrev FPair := Fin 3
/-- A forest chain position, `0 .. 4`. -/
abbrev FPos := Fin (chainTop + 1)
/-- A forest chain step, from position `t` to `t + 1`, `t < 4`. -/
abbrev FStep := Fin chainTop
/-- A codeword: the deficit `d_i ∈ {0..4}` of every chain. -/
abbrev Codeword := FChain → FPos
/-- A codeword index, 8 digest bits. -/
abbrev LutIdx := Fin 256

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

/-- The second 16 bytes of a hash output (bytes 16 to 31). Only the seed derivations of chain starts
use them. -/
def upperHash (output : HashOutput) : Digest :=
  output.extractLsb' digestBits digestBits

/-- The half of a hash output that starts chain `n`: the first for even `n`, the second for odd `n`. -/
def hashHalf (n : Nat) (output : HashOutput) : Digest :=
  if n % 2 = 0 then truncateHash output else upperHash output

/-! ### The codeword table -/

/-- The 256 entries of the codeword table as base-5 numbers with `d_0` the most significant digit; a
codeword listed twice is chosen by two digest values. The table is `codewordRule`
(`codewordCodes_eq_rule`): the codewords sorted by decreasing `Σ d_i²`, then lexicographically, entry
`t` being codeword number `t mod 214`. By digit pattern: the 30 codewords with digits `{4,1}` twice
each; of the 30 with `{3,2}`, 12 twice and 18 once; the 60 with `{3,1,1}` and the 60 with `{2,2,1}`
once; 34 of the 60 with `{2,1,1,1}` once; none of the 6 with `{1,1,1,1,1}`. Written by
`scripts/forest_table.py`. -/
def codewordCodes : List Nat :=
  [9, 21, 29, 45, 101, 105, 129, 145, 225, 501, 505, 525, 629, 645, 725, 1125,
   2501, 2505, 2525, 2625, 3129, 3145, 3225, 3625, 5625, 12501, 12505, 12525, 12625, 13125, 13, 17,
   53, 65, 77, 85, 253, 265, 325, 377, 385, 425, 1253, 1265, 1325, 1625, 1877, 1885,
   1925, 2125, 6253, 6265, 6325, 6625, 8125, 9377, 9385, 9425, 9625, 10625, 33, 41, 81, 133,
   141, 153, 165, 201, 205, 381, 401, 405, 633, 641, 653, 665, 701, 705, 753, 765,
   825, 1001, 1005, 1025, 1881, 1901, 1905, 2001, 2005, 2025, 3133, 3141, 3153, 3165, 3201, 3205,
   3253, 3265, 3325, 3501, 3505, 3525, 3753, 3765, 3825, 4125, 5001, 5005, 5025, 5125, 9381, 9401,
   9405, 9501, 9505, 9525, 10001, 10005, 10025, 10125, 37, 57, 61, 137, 177, 185, 257, 261,
   277, 285, 301, 305, 637, 677, 685, 877, 885, 925, 1257, 1261, 1277, 1285, 1301, 1305,
   1377, 1385, 1425, 1501, 1505, 1525, 3137, 3177, 3185, 3377, 3385, 3425, 4377, 4385, 4425, 4625,
   6257, 6261, 6277, 6285, 6301, 6305, 6377, 6385, 6425, 6501, 6505, 6525, 6877, 6885, 6925, 7125,
   7501, 7505, 7525, 7625, 157, 161, 181, 281, 657, 661, 681, 757, 761, 777, 785, 801,
   805, 881, 901, 905, 1281, 1381, 1401, 1405, 3157, 3161, 3181, 3257, 3261, 3277, 3285, 3301,
   3305, 3381, 3401, 3405, 3757, 3761, 9, 21, 29, 45, 101, 105, 129, 145, 225, 501,
   505, 525, 629, 645, 725, 1125, 2501, 2505, 2525, 2625, 3129, 3145, 3225, 3625, 5625, 12501,
   12505, 12525, 12625, 13125, 13, 17, 53, 65, 77, 85, 253, 265, 325, 377, 385, 425]

/-- The table as a rule. The codewords are the base-5 numbers below `5^6` with digit sum 5, in
increasing (that is, lexicographic) order; they are sorted by decreasing sum of squared digits (at
most 17), and entry `t` is codeword number `t mod 214`. -/
def codewordRule : List Nat :=
  let digit (c i : Nat) : Nat := c / 5 ^ i % 5
  let words := (List.range (5 ^ 6)).filter fun c => ((List.range 6).map (digit c)).sum = 5
  let sorted := (List.range 18).reverse.flatMap fun k =>
    words.filter fun c => ((List.range 6).map fun i => digit c i ^ 2).sum = k
  (List.range 256).map fun t => sorted.getD (t % 214) 0

theorem codewordCodes_eq_rule : codewordCodes = codewordRule := by decide +kernel

/-- Digit `i` (`i = 0` most significant) of a base-5 code with 6 digits. -/
def codeDigit (code : Nat) (i : FChain) : FPos :=
  ⟨code / 5 ^ (5 - i.val) % 5, Nat.mod_lt _ (by decide)⟩

/-- `lut t`: entry `t` of the table. -/
def lut (t : LutIdx) : Codeword := codeDigit (codewordCodes.getD t.val 0)

/-! ### The message digest: one call, 234 bits -/

/-- Digest bits of one coordinate: super-child 4, and child 3 and codeword 8 for each sub-tree. -/
def coordBits : Nat := 26

/-- The message digest is `h + 8 · 26 = 234` bits: an index and the fields of 8 coordinates. -/
def messageDigestBits : Nat := totalHeight + forestCoords * coordBits

abbrev MessageDigest := BitVec messageDigestBits

/-- The first 234 bits of the single digest call. -/
def truncateMessageDigest (first : HashOutput) : MessageDigest :=
  first.extractLsb' 0 messageDigestBits

/-- What a digest selects in one coordinate: the super-child, and per sub-tree a child and a codeword
index. -/
structure CoordMark where
  super : SuperIdx
  child : SubIdx → ChildIdx
  word : SubIdx → LutIdx
deriving DecidableEq

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

/-- The opening of one sub-tree: the 6 revealed chain values and the 3 auth nodes. -/
structure SubOpening where
  values : FChain → Digest
  path : Fin subHeight → Digest
deriving DecidableEq

/-- The opening of one coordinate: both sub-trees, then the 4 auth nodes of the top tree. -/
structure CoordOpening where
  sub : SubIdx → SubOpening
  top : Fin topHeight → Digest
deriving DecidableEq

/-- The randomizer, the forest opening, and the WOTS+C signature with its path: 4276 bytes. -/
structure Signature where
  randomness : Randomness
  forest : Coord → CoordOpening
  layers : (lay : Layer) → LayerSignature lay
deriving DecidableEq

/-- Serialize a bit vector into a fixed number of bytes, least significant byte first. -/
def bytesLE (byteCount : Nat) (value : BitVec (8 * byteCount)) : List UInt8 :=
  List.ofFn fun index : Fin byteCount =>
    UInt8.ofBitVec (value.extractLsb' (8 * index.val) 8)

/-- The address of a hash call (`Tweak` in `crates/sphincs`): its type `tag < 32`, a chain step
`step < 8`, and two fields `hi < 2^24` and `lo < 2^32`. -/
structure TweakFields where
  tag : BitVec 5
  step : BitVec 3
  hi : BitVec 24
  lo : BitVec 32
deriving DecidableEq

/-- The 16 address bytes `lo || hi || (tag + 32 * step) || 0^8`: `lo` on 4 bytes, `hi` on 3 bytes,
each least significant byte first, then the type byte, then 8 zero bytes. -/
def fieldBytes (fields : TweakFields) : HashInput :=
  bytesLE 4 fields.lo ++ bytesLE 3 fields.hi ++ bytesLE 1 (fields.step ++ fields.tag) ++ bytesLE 8 0

/-- Convert the four integer fields to their fixed widths. -/
def tweakFields (tag step hi lo : Nat) : TweakFields :=
  ⟨BitVec.ofNat 5 tag, BitVec.ofNat 3 step, BitVec.ofNat 24 hi, BitVec.ofNat 32 lo⟩

/-! ### Forest addresses -/

/-- `c + 8 s + 128 j`, a sub-tree of the instance (3 + 4 + 1 bits). -/
def subSlot (c : Coord) (s : SuperIdx) (j : SubIdx) : Nat := c.val + 8 * s.val + 128 * j.val

/-- `c + 8 s + 128 j + 256 a`, a child of the instance (11 bits). -/
def childSlot (c : Coord) (s : SuperIdx) (j : SubIdx) (a : ChildIdx) : Nat :=
  subSlot c s j + 256 * a.val

/-- `c + 8 s + 128 j + 256 a + 2048 i`, a chain of the instance. -/
def chainSlot (c : Coord) (s : SuperIdx) (j : SubIdx) (a : ChildIdx) (i : FChain) : Nat :=
  childSlot c s j a + 2048 * i.val

/-- The verification hash domains. Seed derivation uses `KeygenDomain`. Forest levels count from the
leaves: a `subNode` at `level` is the node of sub-tree level `level + 1`, a `topNode` at `level` the
node of top-tree level `level + 1`. The scheme hashes sub-tree levels 1 and 2 and top-tree levels 1
to 3: the address of a tree's root exists and no algorithm uses it. -/
inductive HashDomain where
  | chain (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (chainIdx : ChainIndex) (step : ChainStep)
  | leaf (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
  | node (lay : Layer) (tree : TreeIndex) (level : Nat) (nodeIdx : Nat)
  | encoding (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
  | fchain (index : Index) (c : Coord) (s : SuperIdx) (j : SubIdx) (a : ChildIdx) (i : FChain) (t : FStep)
  | childLeaf (index : Index) (c : Coord) (s : SuperIdx) (j : SubIdx) (a : ChildIdx)
  | subNode (index : Index) (c : Coord) (s : SuperIdx) (j : SubIdx) (level : Fin subHeight) (node : ChildIdx)
  | superChild (index : Index) (c : Coord) (s : SuperIdx)
  | topNode (index : Index) (c : Coord) (level : Fin topHeight) (node : SuperIdx)
  | roots (index : Index)
  | message
deriving DecidableEq

/-- The address of a hash domain: types `TWEAK_CHAIN = 1`, ..., `TWEAK_MSG = 12`, forest types 15 to
20. In the tree `lo` is the leaf (or the node index) and `hi` the chain (or the node level); a chain
step carries its step. In a forest instance `lo` is `idx` and `hi` the packed position; a forest chain
step from position `t` carries step `t`. The layer and the tree, always `0`, are not addressed. -/
def hashDomainFields : HashDomain → TweakFields
  | .chain _ _ leaf chainIdx step => tweakFields 1 step chainIdx leaf
  | .leaf _ _ leaf => tweakFields 2 0 0 leaf
  | .node _ _ level nodeIdx => tweakFields 3 0 level nodeIdx
  | .encoding _ _ leaf => tweakFields 4 0 0 leaf
  | .fchain index c s j a i t => tweakFields 15 t (chainSlot c s j a i) index
  | .childLeaf index c s j a => tweakFields 16 0 (childSlot c s j a) index
  | .subNode index c s j level node =>
      tweakFields 17 0 (subSlot c s j + 256 * (level.val + 1) + 1024 * node.val) index
  | .superChild index c s => tweakFields 18 0 (c.val + 8 * s.val) index
  | .topNode index c level node => tweakFields 19 0 (c.val + 8 * (level.val + 1) + 64 * node.val) index
  | .roots index => tweakFields 20 0 0 index
  | .message => tweakFields 12 0 0 0

/-- The exact 16 address bytes of a hash domain. -/
def tweakBytes (domain : HashDomain) : HashInput :=
  fieldBytes (hashDomainFields domain)

/-- The random-oracle input `P || A || payload` of every tweakable hash call and of the message
digest. -/
def tweakableHashInput (parameter : PublicParameter) (domain : HashDomain)
    (message : HashInput) : HashInput :=
  bytesLE 16 parameter ++ tweakBytes domain ++ message

/-- `P || A(7, 0, 0) || S || m` (`TWEAK_RANDOMIZER = 7`): the randomizer base of a message. -/
def randomizerHashInput (parameter : PublicParameter) (seed : MasterSeed)
    (message : Message) : HashInput :=
  bytesLE 16 parameter ++ fieldBytes ⟨7#5, 0#3, 0#24, 0#32⟩ ++
    bytesLE 32 seed ++ bytesLE 32 message

/-- The pair of chains a chain of a one-time key belongs to. -/
def chainPair (chain : ChainIndex) : ChainPair :=
  ⟨chain.val / 2, by have h : chain.val < 64 := chain.isLt; omega⟩

/-- The pair of chains a chain of a forest WOTS key belongs to. -/
def fchainPair (i : FChain) : FPair :=
  ⟨i.val / 2, by have h : i.val < 6 := i.isLt; omega⟩

/-- `c + 8 s + 128 j + 256 a + 2048 t`, a pair of chains of the instance. -/
def pairSlot (c : Coord) (s : SuperIdx) (j : SubIdx) (a : ChildIdx) (pair : FPair) : Nat :=
  childSlot c s j a + 2048 * pair.val

/-- The seed derivations, one hash each. `ots` gives the starts of chains `2t` and `2t + 1` of the
one-time key at a leaf, `forest` the starts `x_{2t,0}` and `x_{2t+1,0}` of chains `2t` and `2t + 1`
of child `(idx, c, s, j, a)`: the two 16-byte halves of the hash. The parameter and a surrogate are
the first 16 bytes of their hash. -/
inductive KeygenDomain where
  | parameter
  | ots (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (pair : ChainPair)
  | forest (index : Index) (c : Coord) (s : SuperIdx) (j : SubIdx) (a : ChildIdx) (pair : FPair)
  | surrogate (level : Fin totalHeight)
deriving DecidableEq

/-- `TWEAK_PARAMETER = 5`, `TWEAK_PRF = 0` (`hi` the pair of chains, `lo` the leaf),
`TWEAK_FOREST_PRF = 14` (`hi` the packed pair of chains, `lo = idx`), `TWEAK_SURROGATE = 13` (`hi`
the level). -/
def keygenDomainFields : KeygenDomain → TweakFields
  | .parameter => tweakFields 5 0 0 0
  | .ots _ _ leaf pair => tweakFields 0 0 pair leaf
  | .forest index c s j a pair => tweakFields 14 0 (pairSlot c s j a pair) index
  | .surrogate level => tweakFields 13 0 level 0

/-- `P || A || S`; parameter derivation uses `P = 0`. -/
def keygenHashInput (parameter : PublicParameter) (domain : KeygenDomain)
    (seed : MasterSeed) : HashInput :=
  bytesLE 16 parameter ++ fieldBytes (keygenDomainFields domain) ++ bytesLE 32 seed

/-! ### The target-sum code

`v = 64` chunks of `w = 2` bits covering the 128 digest bits, and the code is the words of digit sum
`T = 120`. -/

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

/-- `Th(P, tw, M) = Truncate_n(H(P || tw || M))`. -/
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
step `start + steps` (`chain_tweak` with `to = start + steps + 1`). -/
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

/-! ### The forest -/

/-- `steps` forest chain steps from position `start`; the step onto position `start + steps + 1`
carries step `start + steps`. -/
def forestWalk (parameter : PublicParameter) (index : Index) (c : Coord) (s : SuperIdx) (j : SubIdx)
    (a : ChildIdx) (i : FChain) : Nat → Nat → Digest → m Digest
  | _, 0, value => pure value
  | start, steps + 1, value => do
      let previous ← forestWalk parameter index c s j a i start steps value
      if hstep : start + steps < chainTop then
        tweakableHash parameter (.fchain index c s j a i ⟨start + steps, hstep⟩) (bytesLE 16 previous)
      else
        pure 0

/-- The verifier's half of a forest chain: from position `4 - d` walk `d` steps. -/
def forestRecoverChain (parameter : PublicParameter) (index : Index) (c : Coord) (s : SuperIdx) (j : SubIdx)
    (a : ChildIdx) (i : FChain) (deficit : FPos) (value : Digest) : m Digest :=
  forestWalk parameter index c s j a i (chainTop - deficit.val) deficit.val value

/-- `x_{0,4} || ... || x_{5,4}`. -/
def childPayload (ends : FChain → Digest) : HashInput :=
  (List.ofFn ends).flatMap (bytesLE 16)

/-- The child leaf: the hash of the 6 chain tops. -/
def childLeafHash (parameter : PublicParameter) (index : Index) (c : Coord) (s : SuperIdx) (j : SubIdx)
    (a : ChildIdx) (ends : FChain → Digest) : m Digest :=
  tweakableHash parameter (.childLeaf index c s j a) (childPayload ends)

/-- The child leaf an opening at codeword `word` reaches. -/
def childRecover (parameter : PublicParameter) (index : Index) (c : Coord) (s : SuperIdx) (j : SubIdx)
    (a : ChildIdx) (word : Codeword) (values : FChain → Digest) : m Digest := do
  let ends ← sequenceFin fun i => forestRecoverChain parameter index c s j a i (word i) (values i)
  childLeafHash parameter index c s j a ends

/-- Fold a child leaf and a sub-tree path into the sub-tree root. -/
def subFold (parameter : PublicParameter) (index : Index) (c : Coord) (s : SuperIdx) (j : SubIdx)
    (a : ChildIdx) (path : Fin subHeight → Digest) : Nat → Digest → m Digest
  | 0, value => pure value
  | levels + 1, value => do
      let current ← subFold parameter index c s j a path levels value
      if hlevel : levels < subHeight then
        let sibling := path ⟨levels, hlevel⟩
        let node : ChildIdx := ⟨a.val / 2 ^ (levels + 1),
          Nat.lt_of_le_of_lt (Nat.div_le_self _ _) a.isLt⟩
        if a.val.testBit levels then
          tweakableHash parameter (.subNode index c s j ⟨levels, hlevel⟩ node) (nodePayload sibling current)
        else
          tweakableHash parameter (.subNode index c s j ⟨levels, hlevel⟩ node) (nodePayload current sibling)
      else
        pure 0

/-- The two top nodes of a tree in index order, from the one the fold reached and the last path
element: the reached node is node 1 exactly when `bit`, the top bit of the leaf index, is set. -/
def orderTops (bit : Bool) (current sibling : Digest) : Digest × Digest :=
  if bit then (sibling, current) else (current, sibling)

/-- `m_0[0] || m_0[1] || m_1[0] || m_1[1]`, the level-2 nodes of the two sub-trees. -/
def superPayload (tops : SubIdx → Digest × Digest) : HashInput :=
  nodePayload (tops 0).1 (tops 0).2 ++ nodePayload (tops 1).1 (tops 1).2

/-- The super-child `Th(super(idx, c, s), m_0[0] || m_0[1] || m_1[0] || m_1[1])`: the hash of the two
level-2 nodes of each of its sub-trees. A sub-tree has no root hash. -/
def superHash (parameter : PublicParameter) (index : Index) (c : Coord) (s : SuperIdx)
    (tops : SubIdx → Digest × Digest) : m Digest :=
  tweakableHash parameter (.superChild index c s) (superPayload tops)

/-- Fold a super-child and a top path into the coordinate root. -/
def topFold (parameter : PublicParameter) (index : Index) (c : Coord) (s : SuperIdx)
    (path : Fin topHeight → Digest) : Nat → Digest → m Digest
  | 0, value => pure value
  | levels + 1, value => do
      let current ← topFold parameter index c s path levels value
      if hlevel : levels < topHeight then
        let sibling := path ⟨levels, hlevel⟩
        let node : SuperIdx := ⟨s.val / 2 ^ (levels + 1),
          Nat.lt_of_le_of_lt (Nat.div_le_self _ _) s.isLt⟩
        if s.val.testBit levels then
          tweakableHash parameter (.topNode index c ⟨levels, hlevel⟩ node) (nodePayload sibling current)
        else
          tweakableHash parameter (.topNode index c ⟨levels, hlevel⟩ node) (nodePayload current sibling)
      else
        pure 0

/-- The last level of a sub-tree path: the other level-2 node. -/
def subTopLevel : Fin subHeight := ⟨subHeight - 1, by decide⟩

/-- The last level of a top-tree path: the other level-3 node. -/
def topTopLevel : Fin topHeight := ⟨topHeight - 1, by decide⟩

/-- The two level-3 nodes of a coordinate's top tree that an opening reaches. In each sub-tree the
child leaf is folded 2 levels and the last path element is the other level-2 node; the four level-2
nodes hash into the super-child, which is folded 3 levels, and the last top path element is the
other level-3 node. -/
def coordRecover (parameter : PublicParameter) (index : Index) (c : Coord) (mark : CoordMark)
    (opening : CoordOpening) : m (Digest × Digest) := do
  let tops ← sequenceFin fun j => do
    let leaf ← childRecover parameter index c mark.super j (mark.child j) (lut (mark.word j))
      (opening.sub j).values
    let node ← subFold parameter index c mark.super j (mark.child j) (opening.sub j).path (subHeight - 1) leaf
    return orderTops ((mark.child j).val.testBit (subHeight - 1)) node ((opening.sub j).path subTopLevel)
  let super ← superHash parameter index c mark.super tops
  let node ← topFold parameter index c mark.super opening.top (topHeight - 1) super
  return orderTops (mark.super.val.testBit (topHeight - 1)) node (opening.top topTopLevel)

/-- `t_0[0] || t_0[1] || ... || t_7[0] || t_7[1]`, the level-3 nodes of the 8 top trees. -/
def rootsPayload (tops : Coord → Digest × Digest) : HashInput :=
  (List.ofFn tops).flatMap fun pair => nodePayload pair.1 pair.2

/-- `Fts.recover`: the forest key an opening reaches, the hash of the sixteen level-3 nodes. A top
tree has no root hash. -/
def forestRecover (parameter : PublicParameter) (index : Index) (marks : Coord → CoordMark)
    (opening : Coord → CoordOpening) : m Digest := do
  let tops ← sequenceFin fun c => coordRecover parameter index c (marks c) (opening c)
  tweakableHash parameter (.roots index) (rootsPayload tops)

/-! ### The message digest -/

/-- `m || rho`, what the message digest hashes after the parameter and the address. The first block
is `P || A || m` (64 bytes); the second block is the randomizer alone. The root is not hashed (`P`
binds the key); the argument is kept for the callers. -/
def messageDigestPayload (_root : Digest) (message : Message) (randomness : Randomness) : HashInput :=
  bytesLE 32 message ++ bytesLE 16 randomness

/-- The single untruncated digest call (`digest_block`). -/
def messageDigestCall (parameter : PublicParameter) (root : Digest) (message : Message)
    (randomness : Randomness) : m HashOutput :=
  oracleHash (tweakableHashInput parameter .message (messageDigestPayload root message randomness))

/-- Bit offset of the index: the low 26 bits of the last 16 bytes of the digest. -/
def indexOffset : Nat := 128

/-- `idx`, the 26 bits of the digest from bit 128. -/
def digestIndex (digest : MessageDigest) : Index :=
  (digest.extractLsb' indexOffset totalHeight).toFin

/-- The leaf index of the digest call (`index_of_block`). -/
def blockIndex (first : HashOutput) : Index :=
  (first.extractLsb' indexOffset totalHeight).toFin

/-- `Digest(P, m, rho)` (`message_digest`): the single call, truncated to 234 bits. The root is not
an input of the hash. -/
def messageDigest (parameter : PublicParameter) (root : Digest) (message : Message)
    (randomness : Randomness) : m MessageDigest := do
  let first ← messageDigestCall parameter root message randomness
  return truncateMessageDigest first

/-- Bit offset of the codeword index of sub-tree `j` of coordinate `c`: byte `2c + j` of the digest. -/
def wordOffset (c : Coord) (j : SubIdx) : Nat := 8 * (2 * c.val + j.val)

/-- Bit offset of coordinate `c`'s super-child (4 bits), after the index. -/
def superOffset (c : Coord) : Nat := 154 + 4 * c.val

/-- Bit offset of the child of sub-tree `j` of coordinate `c` (3 bits), after the super-children. -/
def childOffset (c : Coord) (j : SubIdx) : Nat := 186 + 3 * (2 * c.val + j.val)

/-- The coordinate fields of a digest. -/
def digestMarks (digest : MessageDigest) : Coord → CoordMark := fun c =>
  { super := (digest.extractLsb' (superOffset c) topHeight).toFin
    child := fun j => (digest.extractLsb' (childOffset c j) subHeight).toFin
    word := fun j => (digest.extractLsb' (wordOffset c j) 8).toFin }

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

/-- `Ver(pk, m, sigma)`: recompute the digest, recover the forest key, recover the one-time leaf,
fold the path and compare with the root. -/
def verify (publicKey : PublicKey) (message : Message) (signature : Signature) : m Bool := do
  let digest ← messageDigest publicKey.parameter publicKey.root message signature.randomness
  let index := digestIndex digest
  let ftsPublicKey ← forestRecover publicKey.parameter index (digestMarks digest) signature.forest
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

/-- `s`, the kept subtree: the low `h - b` bits of `P`, read as a little-endian number (`0` for a
full key). -/
def subtreePosition (parameter : PublicParameter) : Nat :=
  parameter.toNat % 2 ^ (totalHeight - subtreeHeight)

/-- The kept subtree holds leaves `s * 2^b .. (s + 1) * 2^b` (`XmssTree::contains`). -/
def Landed (parameter : PublicParameter) (index : Index) : Prop :=
  index.val / 2 ^ subtreeHeight = subtreePosition parameter

instance (parameter : PublicParameter) (index : Index) : Decidable (Landed parameter index) :=
  inferInstanceAs (Decidable (index.val / 2 ^ subtreeHeight = subtreePosition parameter))

end Pruning

/-- One seed derivation, first 16 bytes: the parameter and the surrogates. -/
def deriveKey {m : Type → Type} [Monad m] [HasQuery HashSpec m]
    (parameter : PublicParameter) (domain : KeygenDomain) (seed : MasterSeed) : m Digest := do
  return truncateHash (← Concrete.oracleHash (keygenHashInput parameter domain seed))

/-- One seed derivation, all 32 bytes (`th_pair`): the starts of two chains are its two halves. -/
def deriveOutput {m : Type → Type} [Monad m] [HasQuery HashSpec m]
    (parameter : PublicParameter) (domain : KeygenDomain) (seed : MasterSeed) : m HashOutput :=
  Concrete.oracleHash (keygenHashInput parameter domain seed)

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

/-- `wots_secrets`: the starts of the 64 chains of the one-time key at a leaf, from 32 seed
derivations. Chains `2t` and `2t + 1` start at the two halves of derivation `t`. -/
def otsSecrets (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (seed : MasterSeed) : m (ChainIndex → Digest) := do
  let outputs ← sequenceFin fun pair : ChainPair => deriveOutput parameter (.ots lay tree leaf pair) seed
  return fun chainIdx => hashHalf chainIdx.val (outputs (chainPair chainIdx))

/-- The start of one chain of a one-time key, by its own derivation. The signer calls `otsSecrets`;
this is the value of each of its entries (`Completeness.eval_otsSecrets`). -/
def otsStart (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (chainIdx : ChainIndex) (seed : MasterSeed) : m Digest := do
  let output ← deriveOutput parameter (.ots lay tree leaf (chainPair chainIdx)) seed
  return hashHalf chainIdx.val output

def oneTimePublicKey (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (seed : MasterSeed) : m (ChainIndex → Digest) := do
  let secrets ← otsSecrets parameter lay tree leaf seed
  sequenceFin fun chainIdx =>
    chainWalk parameter lay tree leaf chainIdx 0 (chainLength - 1) (secrets chainIdx)

def otsSignFrom (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (seed : MasterSeed) (message : Digest) :
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

/-- The starts `x_{i,0}` of the 6 chains of a child, from 3 seed derivations. Chains `2t` and
`2t + 1` start at the two halves of derivation `t`. -/
def forestSecrets (parameter : PublicParameter) (index : Index) (c : Coord) (s : SuperIdx)
    (j : SubIdx) (a : ChildIdx) (seed : MasterSeed) : m (FChain → Digest) := do
  let outputs ← sequenceFin fun pair : FPair => deriveOutput parameter (.forest index c s j a pair) seed
  return fun i => hashHalf i.val (outputs (fchainPair i))

/-- The start `x_{i,0}` of one chain of a child, by its own derivation. The signer calls
`forestSecrets`; this is the value of each of its entries (`Completeness.eval_forestSecrets`). -/
def forestStart (parameter : PublicParameter) (index : Index) (c : Coord) (s : SuperIdx) (j : SubIdx)
    (a : ChildIdx) (i : FChain) (seed : MasterSeed) : m Digest := do
  let output ← deriveOutput parameter (.forest index c s j a (fchainPair i)) seed
  return hashHalf i.val output

/-- The forest chain value `x_{i,pos}` of a child, by its own derivation. The signer computes the 6
chains of a child from one call of `forestSecrets` (`childLeaf`, `coordOpen`); this is the value of
each of them. -/
def chainValue (parameter : PublicParameter) (index : Index) (c : Coord) (s : SuperIdx) (j : SubIdx)
    (a : ChildIdx) (i : FChain) (seed : MasterSeed) (pos : Nat) : m Digest := do
  let secret ← forestStart parameter index c s j a i seed
  forestWalk parameter index c s j a i 0 pos secret

/-- The leaf of a child, from its 6 chain tops. -/
def childLeaf (parameter : PublicParameter) (index : Index) (c : Coord) (s : SuperIdx) (j : SubIdx)
    (a : ChildIdx) (seed : MasterSeed) : m Digest := do
  let secrets ← forestSecrets parameter index c s j a seed
  let ends ← sequenceFin fun i => forestWalk parameter index c s j a i 0 chainTop (secrets i)
  childLeafHash parameter index c s j a ends

/-- A node of a sub-tree at tree level `level`. -/
def subNode (parameter : PublicParameter) (index : Index) (c : Coord) (s : SuperIdx) (j : SubIdx)
    (seed : MasterSeed) : Nat → Nat → m Digest
  | 0, node => childLeaf parameter index c s j ⟨node % 2 ^ subHeight, Nat.mod_lt _ (Nat.two_pow_pos _)⟩ seed
  | level + 1, node => do
      let left ← subNode parameter index c s j seed level (2 * node)
      let right ← subNode parameter index c s j seed level (2 * node + 1)
      if hlevel : level < subHeight then
        tweakableHash parameter (.subNode index c s j ⟨level, hlevel⟩
          ⟨node % 2 ^ subHeight, Nat.mod_lt _ (Nat.two_pow_pos _)⟩) (nodePayload left right)
      else
        pure 0

/-- A super-child, from the two level-2 nodes of each of its two sub-trees. -/
def superNode (parameter : PublicParameter) (index : Index) (c : Coord) (s : SuperIdx)
    (seed : MasterSeed) : m Digest := do
  let tops ← sequenceFin fun j => do
    let left ← subNode parameter index c s j seed (subHeight - 1) 0
    let right ← subNode parameter index c s j seed (subHeight - 1) 1
    return (left, right)
  superHash parameter index c s tops

/-- A node of a coordinate's top tree at tree level `level`. -/
def topNode (parameter : PublicParameter) (index : Index) (c : Coord) (seed : MasterSeed) :
    Nat → Nat → m Digest
  | 0, node => superNode parameter index c ⟨node % 2 ^ topHeight, Nat.mod_lt _ (Nat.two_pow_pos _)⟩ seed
  | level + 1, node => do
      let left ← topNode parameter index c seed level (2 * node)
      let right ← topNode parameter index c seed level (2 * node + 1)
      if hlevel : level < topHeight then
        tweakableHash parameter (.topNode index c ⟨level, hlevel⟩
          ⟨node % 2 ^ topHeight, Nat.mod_lt _ (Nat.two_pow_pos _)⟩) (nodePayload left right)
      else
        pure 0

/-- The forest key of instance `idx`: the two level-3 nodes of every coordinate, then their hash. -/
def forestKey (parameter : PublicParameter) (index : Index) (seed : MasterSeed) : m Digest := do
  let tops ← sequenceFin fun c => do
    let left ← topNode parameter index c seed (topHeight - 1) 0
    let right ← topNode parameter index c seed (topHeight - 1) 1
    return (left, right)
  tweakableHash parameter (.roots index) (rootsPayload tops)

/-- The opening of one coordinate at a mark. The last element of each path (level 2 of a sub-tree,
level 3 of the top tree) is the top node the verifier does not compute. -/
def coordOpen (parameter : PublicParameter) (index : Index) (c : Coord) (mark : CoordMark)
    (seed : MasterSeed) : m CoordOpening := do
  let sub ← sequenceFin fun j => do
    let secrets ← forestSecrets parameter index c mark.super j (mark.child j) seed
    let values ← sequenceFin fun i =>
      forestWalk parameter index c mark.super j (mark.child j) i 0
        (chainTop - (lut (mark.word j) i).val) (secrets i)
    let path ← sequenceFin fun level : Fin subHeight =>
      subNode parameter index c mark.super j seed level.val (Nat.xor ((mark.child j).val / 2 ^ level.val) 1)
    return (⟨values, path⟩ : SubOpening)
  let top ← sequenceFin fun level : Fin topHeight =>
    topNode parameter index c seed level.val (Nat.xor (mark.super.val / 2 ^ level.val) 1)
  return ⟨sub, top⟩

/-- `Fts.sign`: the opening of every coordinate. -/
def forestOpen (parameter : PublicParameter) (index : Index) (marks : Coord → CoordMark)
    (seed : MasterSeed) : m (Coord → CoordOpening) :=
  sequenceFin fun c => coordOpen parameter index c (marks c) seed

variable [Params]

/-- `Gen` (`key_gen`): derive the public parameter, which places the kept subtree, and build the root. -/
def keygenFromSeed (seed : MasterSeed) : OracleComp HashSpec (PublicKey × SecretKey) := do
  let parameter ← deriveKey 0 .parameter seed
  let root ← treeRoot parameter topLayer rootTree seed
  return (⟨root, parameter⟩, ⟨seed, parameter, root⟩)

/-- One grinding attempt: the leaf index of the digest call (`digest_index`). -/
def signAttempt (secretKey : SecretKey) (message : Message) (randomness : Randomness) :
    m (Option Index) := do
  let first ← messageDigestCall secretKey.parameter secretKey.root message randomness
  if Landed secretKey.parameter (blockIndex first) then
    return some (blockIndex first)
  else
    return none

def layerMessage (secretKey : SecretKey) (index : Index) (_lay : Layer) : m Digest :=
  forestKey secretKey.parameter index secretKey.seed

def signLayer (secretKey : SecretKey) (index : Index) (lay : Layer) : m (Option (LayerSignature lay)) := do
  let tree := treeIndexAt index lay
  let leaf := leafIndexAt index lay
  let message ← layerMessage secretKey index lay
  let some (counter, values) ← otsSign secretKey.parameter lay tree leaf secretKey.seed message
    | return none
  let path ← treePath secretKey.parameter lay tree secretKey.seed leaf
  return some ⟨counter, values, path⟩

/-- Try `randomness, randomness + 1, ...`, stopping at the first that lands in the kept subtree. -/
def signDigestLoop (secretKey : SecretKey) (message : Message) : Nat → Randomness →
    m (Option (Randomness × Index))
  | 0, _ => pure none
  | attempts + 1, randomness => do
      match ← signAttempt secretKey message randomness with
      | some index => return some (randomness, index)
      | none => signDigestLoop secretKey message attempts (randomness + 1)

/-- `Sign`: derive the randomizer base `R0` of the message (one hash), scan `R0, R0 + 1, ...` into
the kept subtree, compute the digest, open the forest, sign its key with WOTS+C and attach the path. -/
def sign (secretKey : SecretKey) (message : Message) : m (Option Signature) := do
  let base ← deriveRandomizer secretKey.parameter secretKey.seed message
  let some (randomness, _) ← signDigestLoop secretKey message digestAttemptLimit base
    | return none
  let digest ← messageDigest secretKey.parameter secretKey.root message randomness
  let index := digestIndex digest
  let opening ← forestOpen secretKey.parameter index (digestMarks digest) secretKey.seed
  let some layers ← sequenceLayers (fun lay => signLayer secretKey index lay) | return none
  return some ⟨randomness, opening, layers⟩

end Seeded

end Sphincs
