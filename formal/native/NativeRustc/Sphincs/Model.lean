module

public import NativeRustc.Keccak.Hasher

/-!
# leanSPHINCS verification as the Rust code computes it

`crates/lean_sphincs` transcribed over byte strings, one definition per Rust function, for the
machine code of `rustc/sphincs.rs` to refine: FIPS 205's 32-byte address (`Adrs`: `adrsNew`,
`withType`, `withKeyPair`, `withChain`, `withHash`, `withTreeHeight`, `withTreeIndex`,
`hash.rs`), the tweakable hash `th` (Keccak-256 of `PK.seed | ADRS | M`, truncated: the `Hasher`
of `NativeRustc.Keccak.Hasher` new, updated and finalized), `H_msg` (`hMsg`) and
`digest_fields` (`digestFields`, `scheme.rs`), a one-time key of the hypertree (`OtsKey`), a chain
(`chain`), the encoding (`encodeDigest`, `codeword`, `encode`), the one-time leaf (`wotsLeaf`,
`wots.rs`), FORS (`forsRecover`, `fors.rs`), a Merkle node and `tree_fold` (`node`,
`treeFold`), `verify` (its loop over the layers `layersFrom`, `scheme.rs`), the signature's
parsing (`Signature.fromBytes`) and the wrapper `sphincs_verify`'s bytes of the 977 input words
(`sphincsVerify`). `NativeRustc.Sphincs.Verify` proves `sphincsVerify` equal to
`Sphincs.verifyWithKeccak`.

A digest, `PK.seed` and a node are 16 bytes, a message 32, an address 32; the integers are Rust's
(`u32`, `u64`), a `usize` a `Nat`.
-/

@[expose] public section

namespace NativeRustc.Sphincs

open LeanVM.Protocol.KeccakHash NativeRustc.Keccak Native.Keccak

/-! ## Big-endian integers -/

/-- `u32::to_be_bytes`. -/
def be32 (x : UInt32) : List UInt8 :=
  [(x >>> 24).toUInt8, (x >>> 16).toUInt8, (x >>> 8).toUInt8, x.toUInt8]

/-- `u64::to_be_bytes`. -/
def be64 (x : UInt64) : List UInt8 :=
  [(x >>> 56).toUInt8, (x >>> 48).toUInt8, (x >>> 40).toUInt8, (x >>> 32).toUInt8,
    (x >>> 24).toUInt8, (x >>> 16).toUInt8, (x >>> 8).toUInt8, x.toUInt8]

/-- `u128::from_be_bytes`: the big-endian number of the bytes. -/
def beNat (b : List UInt8) : Nat := leNat b.reverse

/-- `u32::from_be_bytes` of the first four bytes. -/
def be32Of (b : List UInt8) : UInt32 := UInt32.ofNat (beNat (b.take 4))

/-! ## The address (`hash.rs`) -/

/-- `Adrs::new(layer, tree)`: the layer in bytes `0..4`, the tree in `8..16`, type `WOTS_HASH`,
the rest zero. -/
def adrsNew (layer : UInt32) (tree : UInt64) : List UInt8 :=
  writeAt (writeAt (List.replicate 32 0) 0 (be32 layer)) 8 (be64 tree)

/-- `Adrs::word`: the big-endian `value` at byte `pos`. -/
def adrsWord (a : List UInt8) (pos : Nat) (value : UInt32) : List UInt8 := writeAt a pos (be32 value)

/-- `with_type` (`setTypeAndClear`): bytes `20..32` zero, then the type at `16`. -/
def withType (a : List UInt8) (t : UInt32) : List UInt8 :=
  adrsWord (writeAt a 20 (List.replicate 12 0)) 16 t

/-- `with_key_pair`: the word at `20`. -/
def withKeyPair (a : List UInt8) (i : UInt32) : List UInt8 := adrsWord a 20 i

/-- `with_chain`: the word at `24`. -/
def withChain (a : List UInt8) (i : UInt32) : List UInt8 := adrsWord a 24 i

/-- `with_tree_height`: the word at `24`. -/
def withTreeHeight (a : List UInt8) (z : UInt32) : List UInt8 := adrsWord a 24 z

/-- `with_hash`: the word at `28`. -/
def withHash (a : List UInt8) (j : UInt32) : List UInt8 := adrsWord a 28 j

/-- `with_tree_index`: the word at `28`. -/
def withTreeIndex (a : List UInt8) (j : UInt32) : List UInt8 := adrsWord a 28 j

/-- `th`: `Trunc_16(H(PK.seed | ADRS | M))` (`hasher(pk_seed, adrs).update(m).finalize()`). -/
def th (seed adrs m : List UInt8) : List UInt8 := (hashBytes (seed ++ adrs ++ m)).take 16

/-! ## The one-time keys (`wots.rs`) -/

/-- `LAYER_HEIGHTS`. -/
def layerHeights : List Nat := [8, 8, 10]

/-- `OtsKey`: a layer, a tree on it, a leaf of the tree. -/
structure OtsKey where
  /-- `layer`. -/
  layer : Nat
  /-- `tree`. -/
  tree : UInt64
  /-- `leaf`. -/
  leaf : UInt32

/-- `OtsKey::of_index`: the bits of `idx` below the layer dropped, the rest split into a tree and
a leaf. -/
def OtsKey.ofIndex (layer : Nat) (idx : UInt64) : OtsKey :=
  let height := layerHeights.getD layer 0
  let e := idx >>> ((layerHeights.take layer).sum).toUInt64
  ⟨layer, e >>> height.toUInt64, (e &&& ((1 <<< height.toUInt64) - 1)).toUInt32⟩

/-- `tree_adrs`: the key's tree's address, type `WOTS_HASH`. -/
def OtsKey.treeAdrs (key : OtsKey) : List UInt8 := adrsNew key.layer.toUInt32 key.tree

/-- `OtsKey::adrs`: type `t`, the leaf as the key pair. -/
def OtsKey.adrs (key : OtsKey) (t : UInt32) : List UInt8 := withKeyPair (withType key.treeAdrs t) key.leaf

/-- `chain`: `steps` steps of chain `i` from position `start`; a step's hash address is the
position it leaves. -/
def chain (seed : List UInt8) (key : OtsKey) (i start steps : Nat) (value : List UInt8) :
    List UInt8 :=
  (List.range' start steps).foldl (fun current pos ↦
    th seed (withHash (withChain (key.adrs 0) i.toUInt32) pos.toUInt32) current) value

/-- `wots_leaf_hash`: `T_v` over the chain ends. -/
def wotsLeafHash (seed : List UInt8) (key : OtsKey) (ends : List (List UInt8)) : List UInt8 :=
  th seed (key.adrs 1) ends.flatten

/-- `encode`'s digest: `Trunc_16(H(PK.seed | ADRS_enc | M | BE_32(c)))` (the `encoder` hasher,
which has absorbed `PK.seed | ADRS_enc | M`, cloned and updated with the counter). -/
def encodeDigest (seed : List UInt8) (key : OtsKey) (message : List UInt8) (c : UInt32) :
    List UInt8 :=
  (hashBytes (seed ++ key.adrs 7 ++ message ++ be32 c)).take 16

/-- `codeword`'s 64 two-bit chunks of `d`, most significant first. -/
def digits (d : Nat) : List UInt8 :=
  (List.range 64).map fun i ↦ UInt8.ofNat (d >>> (2 * (63 - i)) &&& 3)

/-- `codeword`: the digest's chunks (`u128::from_be_bytes`), if they sum to `128`. -/
def codeword (digest : List UInt8) : Option (List UInt8) :=
  if ((digits (beNat digest)).map UInt8.toNat).sum = 128 then some (digits (beNat digest))
  else none

/-- `encode`. -/
def encode (seed : List UInt8) (key : OtsKey) (message : List UInt8) (c : UInt32) :
    Option (List UInt8) :=
  codeword (encodeDigest seed key message c)

/-- `wots_leaf`: the codeword of counter `c` and the leaf of the chains walked from the signature's
values to their ends, or `None`. -/
def wotsLeaf (seed : List UInt8) (key : OtsKey) (message : List UInt8) (c : UInt32)
    (signature : List (List UInt8)) : Option (List UInt8 × List UInt8) :=
  match encode seed key message c with
  | none => none
  | some x =>
    let ends := (List.range 64).map fun i ↦
      chain seed key i (x.getD i 0).toNat (3 - (x.getD i 0).toNat) (signature.getD i [])
    some (x, wotsLeafHash seed key ends)

/-! ## FORS (`fors.rs`) -/

/-- `fors_adrs`: the bottom key's address of type `t`. -/
def forsAdrs (idx : UInt64) (t : UInt32) : List UInt8 := (OtsKey.ofIndex 0 idx).adrs t

/-- `fors_node_adrs`: node `j` at height `z` of tree `c`, its tree index counted across the
trees. -/
def forsNodeAdrs (idx : UInt64) (c z j : Nat) : List UInt8 :=
  withTreeIndex (withTreeHeight (forsAdrs idx 3) z.toUInt32) ((c <<< (10 - z)) + j).toUInt32

/-- `fors_leaf`: `F` of the secret. -/
def forsLeaf (seed : List UInt8) (idx : UInt64) (c s : Nat) (secret : List UInt8) : List UInt8 :=
  th seed (forsNodeAdrs idx c 0 s) secret

/-- `fors_node`. -/
def forsNode (seed : List UInt8) (idx : UInt64) (c z j : Nat) (children : List UInt8) :
    List UInt8 :=
  th seed (forsNodeAdrs idx c z j) children

/-- `fors_key`: `T_k` over the roots. -/
def forsKey (seed : List UInt8) (idx : UInt64) (roots : List (List UInt8)) : List UInt8 :=
  th seed (forsAdrs idx 4) roots.flatten

/-- `ForsTreeOpening`. -/
structure ForsTreeOpening where
  /-- `secret`. -/
  secret : List UInt8
  /-- `path`. -/
  path : List (List UInt8)

/-- `fors_recover`: tree `c`'s leaf `leaves[c]` hashed and folded up its path, then `fors_key` of
the 24 roots. -/
def forsRecover (seed : List UInt8) (idx : UInt64) (leaves : List Nat)
    (opening : List ForsTreeOpening) : List UInt8 :=
  forsKey seed idx ((List.range 24).map fun c ↦
    pathFold (forsLeaf seed idx c (leaves.getD c 0) (opening.getD c ⟨[], []⟩).secret)
      (leaves.getD c 0) (opening.getD c ⟨[], []⟩).path fun z j pair ↦ forsNode seed idx c z j pair)

/-! ## The message digest (`hash.rs`, `scheme.rs`) -/

/-- `h_msg`: the two calls `H(R | PK.seed | PK.root | M | BE_32(i))` (the hasher of the first four
cloned per call), 64 bytes. -/
def hMsg (r seed root m : List UInt8) : List UInt8 :=
  (List.range 2).flatMap fun i ↦ hashBytes (r ++ seed ++ root ++ m ++ be32 i.toUInt32)

/-- `digest_fields`' `int`: the bytes big-endian, cut to `bits` bits. -/
def digestInt (bytes : List UInt8) (bits : Nat) : UInt64 :=
  bytes.foldl (fun (v : UInt64) b ↦ v <<< 8 ||| b.toUInt64) 0 &&& ((1 <<< bits.toUInt64) - 1)

/-- `digest_fields`' `bit`: bit `p`, each byte's most significant first. -/
def digestBit (digest : List UInt8) (p : Nat) : Nat :=
  ((digest.getD (p / 8) 0) >>> (7 - p % 8).toUInt8 &&& 1).toNat

/-- `digest_fields`: the index (the tree, bytes `30..33` cut to 18 bits, then the leaf, byte
`33`) and the 24 FORS leaves, ten bits each from the first 30 bytes. -/
def digestFields (digest : List UInt8) : UInt64 × List Nat :=
  (digestInt (slice digest 30 3) 18 <<< 8 ||| digestInt (slice digest 33 1) 8,
    (List.range 24).map fun c ↦
      (List.range 10).foldl (fun v j ↦ v <<< 1 ||| digestBit digest (10 * c + j)) 0)

/-! ## The hypertree and verification (`scheme.rs`) -/

/-- `node`: node `j` at height `z` of the key's tree. -/
def node (seed : List UInt8) (key : OtsKey) (z j : Nat) (children : List UInt8) : List UInt8 :=
  th seed (withTreeIndex (withTreeHeight (withType key.treeAdrs 2) z.toUInt32) j.toUInt32) children

/-- `tree_fold`: `path_fold` of the key's leaf up its path. -/
def treeFold (seed : List UInt8) (key : OtsKey) (leaf : List UInt8) (path : List (List UInt8)) :
    List UInt8 :=
  pathFold leaf key.leaf.toNat path fun z j pair ↦ node seed key z j pair

/-- `LeanSphincsPublicKey`. -/
structure PublicKey where
  /-- `pk_seed`. -/
  pkSeed : List UInt8
  /-- `root`. -/
  root : List UInt8

/-- `LayerSignature`. -/
structure LayerSignature where
  /-- `counter`. -/
  counter : UInt32
  /-- `wots`. -/
  wots : List (List UInt8)

/-- `LeanSphincsSignature`. -/
structure Signature where
  /-- `randomizer`. -/
  randomizer : List UInt8
  /-- `fors`. -/
  fors : List ForsTreeOpening
  /-- `layers`. -/
  layers : List LayerSignature
  /-- `paths`: the three layers' paths, bottom first. -/
  paths : List (List UInt8)

/-- `LeanSphincsSignature::path`: layer `layer`'s nodes of `paths` (`path_range`). -/
def Signature.path (sig : Signature) (layer : Nat) : List (List UInt8) :=
  (sig.paths.drop (layerHeights.take layer).sum).take (layerHeights.getD layer 0)

/-- `message_digest`: `digest_fields` of `h_msg`. -/
def messageDigest (pk : PublicKey) (r m : List UInt8) : UInt64 × List Nat :=
  digestFields (hMsg r pk.pkSeed pk.root m)

/-- `verify`'s loop over the layers `layers`, from `signed`: each key's one-time leaf of what the
layer below gives, folded up its path; `None` at the first counter that gives no codeword. -/
def layersFrom (seed : List UInt8) (idx : UInt64) (sig : Signature) :
    List Nat → List UInt8 → Option (List UInt8)
  | [], signed => some signed
  | layer :: rest, signed =>
    match wotsLeaf seed (OtsKey.ofIndex layer idx) signed (sig.layers.getD layer ⟨0, []⟩).counter
        (sig.layers.getD layer ⟨0, []⟩).wots with
    | none => none
    | some (_, leaf) =>
      layersFrom seed idx sig rest (treeFold seed (OtsKey.ofIndex layer idx) leaf (sig.path layer))

/-- **`verify`**: the digest's index and leaves, the FORS key, the three layers, then the
comparison with `PK.root`. -/
def verify (pk : PublicKey) (message : List UInt8) (sig : Signature) : Bool :=
  match layersFrom pk.pkSeed (messageDigest pk sig.randomizer message).1 sig [0, 1, 2]
      (forsRecover pk.pkSeed (messageDigest pk sig.randomizer message).1
        (messageDigest pk sig.randomizer message).2 sig.fors) with
  | none => false
  | some root => root == pk.root

/-! ## Parsing (`scheme.rs`) -/

/-- `LeanSphincsPublicKey::from_bytes`: `PK.seed`, then `PK.root`. -/
def PublicKey.fromBytes (bytes : List UInt8) : PublicKey := ⟨bytes.take 16, bytes.drop 16⟩

/-- Where layer `l`'s signature starts in the signature's bytes: after `R` and the FORS
openings (4240 bytes), the layers before it (`4 + 1024 + 16 h` bytes each). -/
def sigLayerOff (l : Nat) : Nat := [4240, 5396, 6552].getD l 0

/-- **`LeanSphincsSignature::from_bytes`**: `R`, the 24 FORS openings (secret, 10 path nodes), then
per layer the counter (big-endian), the 64 chain values and the layer's path. -/
def Signature.fromBytes (bytes : List UInt8) : Signature :=
  ⟨slice bytes 0 16,
    (List.range 24).map fun c ↦ ⟨slice bytes (16 + 176 * c) 16,
      (List.range 10).map fun z ↦ slice bytes (32 + 176 * c + 16 * z) 16⟩,
    (List.range 3).map fun l ↦ ⟨be32Of (slice bytes (sigLayerOff l) 4),
      (List.range 64).map fun i ↦ slice bytes (sigLayerOff l + 4 + 16 * i) 16⟩,
    (List.range 3).flatMap fun l ↦ (List.range (layerHeights.getD l 0)).map fun z ↦
      slice bytes (sigLayerOff l + 1028 + 16 * z) 16⟩

/-! ## The wrapper (`rustc/sphincs.rs`) -/

/-- Where layer `l`'s words start in the input: its counter. -/
def layerWordOff (l : Nat) : Nat := 538 + 145 * l

/-- The public key's 32 bytes: words `0 .. 3`, little-endian. -/
def pkBytes (w : Nat → UInt64) : List UInt8 := wordsBytes ((List.range 4).map w)

/-- The message's 32 bytes: words `4 .. 7`. -/
def messageBytes (w : Nat → UInt64) : List UInt8 :=
  wordsBytes ((List.range 4).map fun k ↦ w (4 + k))

/-- The signature's 7740 bytes: words `8 .. 537` (`R` and the FORS openings), then per layer its
counter word as a big-endian `u32` and its `2 (64 + h)` words. -/
def sigBytes (w : Nat → UInt64) : List UInt8 :=
  wordsBytes ((List.range 530).map fun k ↦ w (8 + k)) ++
    (List.range 3).flatMap fun l ↦ be32 (w (layerWordOff l)).toUInt32 ++
      wordsBytes ((List.range (2 * (64 + layerHeights.getD l 0))).map fun k ↦
        w (layerWordOff l + 1 + k))

/-- **`sphincs_verify`** on the input words `w`: `verify` of the key, the message and the
signature parsed from their bytes. -/
def sphincsVerify (w : Nat → UInt64) : Bool :=
  verify (PublicKey.fromBytes (pkBytes w)) (messageBytes w) (Signature.fromBytes (sigBytes w))

end NativeRustc.Sphincs
