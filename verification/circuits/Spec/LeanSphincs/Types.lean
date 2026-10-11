import LeanSphincs.Constants
import EthCryptographySpecs.Xmss.Types

/-!
# `LeanSphincs.Types`

The objects of `programs/leansphincs/guest/src/lib.rs` lines 30 to 185, as fixed-size byte vectors.

The guest holds every value as little-endian 64-bit words, "whose bytes are the specification's" (lib.rs line 15):
here they are those bytes. The one exception is an encoding counter, a word in the guest's memory and 4 bytes in
the specification's serialization (`Signature::to_bytes`, lib.rs lines 155 to 177), which is what this holds. So the
guest's rejection of a counter word of 2^32 or more (lib.rs line 250) has no counterpart here: such a word has no
serialization.
-/

namespace LeanSphincs

open LeanSphincs.Constants
open EthCryptographySpecs.Xmss (packBytes)

/-! ## Values -/

/-- `n`: a hash value. Chain values, tree nodes, leaves and secrets are all digests. -/
abbrev Digest := Vector UInt8 DIGEST_LEN

/-- `P`: the per-key public parameter, which every hash of the key is taken under. -/
abbrev PublicParam := Vector UInt8 PUBLIC_PARAM_LEN

/-- What the message digest is taken under, ground by the signer. -/
abbrev Randomizer := Vector UInt8 RANDOMIZER_LEN

/-- The message to sign: a 256-bit message hash. -/
abbrev Message := Vector UInt8 MESSAGE_LEN

/-- The label hashed in front of every input. -/
abbrev Tweak := Vector UInt8 TWEAK_LEN

/-- An encoding counter, a 32-bit value as its 4 little-endian bytes. -/
abbrev Counter := Vector UInt8 COUNTER_LEN

/-! ## Keys and signatures -/

/-- A public key (`PublicKey`, lib.rs lines 93 to 102). -/
structure PublicKey where
  /-- The root of the top layer's tree. -/
  root : Digest
  /-- `P`, which every hash of the key is taken under. -/
  publicParam : PublicParam
  deriving DecidableEq

/-- One few-time tree's part of a signature (`FtsOpening`, lib.rs lines 104 to 112). -/
structure FtsOpening where
  /-- The secret of the leaf the digest picks. -/
  secret : Digest
  /-- The sibling at each level, leaf first. -/
  path : Vector Digest A
  deriving DecidableEq

/-- One hypertree layer's part of a signature, for a tree of height `height` (`LayerSignature`, lib.rs lines 114 to
124). -/
structure LayerSignature (height : Nat) where
  /-- The encoding counter. -/
  counter : Counter
  /-- The one-time signature: chain `i` opened at chunk `i`. -/
  ots : Vector Digest V
  /-- The sibling at each level of the layer's tree, leaf first. -/
  path : Vector Digest height
  deriving DecidableEq

/-- A signature, in the specification's order (`Signature`, lib.rs lines 126 to 141). -/
structure Signature where
  /-- What the message digest is taken under. -/
  randomizer : Randomizer
  /-- The few-time signature, one opening per tree. -/
  fts : Vector FtsOpening FTS_TREES
  /-- The top layer, of height 12. -/
  layer0 : LayerSignature HEIGHTS[0]
  /-- The middle layer, of height 7. -/
  layer1 : LayerSignature HEIGHTS[1]
  /-- The bottom layer, of height 7, which signs the few-time key. -/
  layer2 : LayerSignature HEIGHTS[2]
  deriving DecidableEq

/-- A layer's counter, one-time signature and path (`Signature::layer`, lib.rs lines 144 to 152). -/
def Signature.layer (sig : Signature) (lay : Fin D) : Counter × Vector Digest V × List Digest :=
  match lay.val with
  | 0 => (sig.layer0.counter, sig.layer0.ots, sig.layer0.path.toList)
  | 1 => (sig.layer1.counter, sig.layer1.ots, sig.layer1.path.toList)
  | _ => (sig.layer2.counter, sig.layer2.ots, sig.layer2.path.toList)

/-! ## Serialization -/

/-- Digests concatenated, in order. -/
def concatDigests (ds : List Digest) : ByteArray :=
  ds.foldl (fun acc d => acc ++ packBytes d) ByteArray.empty

/-- The `n` bytes of `b` from `offset`, zero past its end: every caller checks the size first. -/
def bytesAt (b : ByteArray) (offset n : Nat) : Vector UInt8 n :=
  Vector.ofFn fun i => b.data.getD (offset + i.val) 0

/-- `count` digests of `b` from `offset`. -/
def digestsAt (b : ByteArray) (offset count : Nat) : Vector Digest count :=
  Vector.ofFn fun i => bytesAt b (offset + DIGEST_LEN * i.val) DIGEST_LEN

/-- A public key's 32 bytes, `root | public_param` (the guest's `repr(C)` layout, lib.rs line 63). -/
def PublicKey.toBytes (pk : PublicKey) : ByteArray :=
  packBytes pk.root ++ packBytes pk.publicParam

/-- A public key from its 32 bytes; nothing for any other length. -/
def PublicKey.ofBytes? (b : ByteArray) : Option PublicKey :=
  if b.size = PUB_KEY_SIZE then some { root := bytesAt b 0 DIGEST_LEN, publicParam := bytesAt b DIGEST_LEN DIGEST_LEN }
  else none

/-- A layer's bytes: the counter's 4, then its one-time signature and its path. -/
def LayerSignature.toBytes {height : Nat} (l : LayerSignature height) : ByteArray :=
  packBytes l.counter ++ concatDigests l.ots.toList ++ concatDigests l.path.toList

/-- The layer of height `height` whose bytes start at `offset`. -/
def LayerSignature.at (b : ByteArray) (offset height : Nat) : LayerSignature height where
  counter := bytesAt b offset COUNTER_LEN
  ots := digestsAt b (offset + COUNTER_LEN) V
  path := digestsAt b (offset + COUNTER_LEN + DIGEST_LEN * V) height

/-- The specification's serialization, each counter in 4 bytes (`Signature::to_bytes`, lib.rs lines 155 to 177):
the randomizer, each opening's secret and path, then layers 0, 1 and 2. -/
def Signature.toBytes (sig : Signature) : ByteArray :=
  packBytes sig.randomizer
    ++ sig.fts.toList.foldl (fun acc o => acc ++ packBytes o.secret ++ concatDigests o.path.toList) ByteArray.empty
    ++ sig.layer0.toBytes ++ sig.layer1.toBytes ++ sig.layer2.toBytes

/-- Where layer `lay`'s bytes start. -/
def layerOffset (lay : Nat) : Nat :=
  RANDOMIZER_LEN + FTS_TREES * FTS_OPENING_SIZE + ((List.range lay).map fun l => layerSize (HEIGHTS.toList.getD l 0)).sum

/-- A signature from its `SIG_SIZE` bytes, `Signature.toBytes` read back; nothing for any other length. -/
def Signature.ofBytes? (b : ByteArray) : Option Signature :=
  if b.size = SIG_SIZE then
    some {
      randomizer := bytesAt b 0 RANDOMIZER_LEN
      fts := Vector.ofFn fun kappa =>
        let offset := RANDOMIZER_LEN + FTS_OPENING_SIZE * kappa.val
        { secret := bytesAt b offset DIGEST_LEN, path := digestsAt b (offset + DIGEST_LEN) A }
      layer0 := LayerSignature.at b (layerOffset 0) HEIGHTS[0]
      layer1 := LayerSignature.at b (layerOffset 1) HEIGHTS[1]
      layer2 := LayerSignature.at b (layerOffset 2) HEIGHTS[2] }
  else none

end LeanSphincs
