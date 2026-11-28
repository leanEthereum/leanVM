module

public import NativeRustc.Keccak.Hasher

/-!
# leanXMSS verification as the Rust code computes it

`crates/lean_xmss` transcribed over byte strings, one definition per Rust function, for the
machine code of `rustc/xmss.rs` to refine: the address of a hash call (`Tweak`, `address`,
`hash.rs`), the tweakable hash `th` (`hashBytes`, Keccak-256, of `P | A | payload`, truncated: the
`Hasher` of `NativeRustc.Keccak.Hasher` new, updated and finalized), a chain (`chain`), the message
digest (`messageDigest`), the codeword (`codeword`, `is_codeword` with its `count_ones`), the
one-time leaf (`wotsLeaf`, `wots.rs`), a Merkle node (`node`, `tree.rs`), a layer with
`keccak256`'s `path_fold` (`layerRoot`, `NativeRustc.Keccak.pathFold`) and `verify`
(`scheme.rs`); the signature's parsing (`Signature.fromBytes`, `LayerSignature::read` modeled by `takeLayer`) and the
wrapper `xmss_verify`'s bytes of the 309 input words (`xmssVerify`). The layouts rustc chose for
the structures the machine code passes in memory are `LayerSignature.memBytes`,
`Signature.memBytes` and `WotsLeafOut`. `NativeRustc.Xmss.Verify` proves `xmssVerify` equal to
`LeanXmss.verifyWithKeccak`.

A digest, a randomizer, the public parameter and a chain value are 16 bytes, a message 32, the
codeword 58 digits of a byte each; the integers are Rust's (`u8`, `u32`), a `usize` a `Nat`.
-/

@[expose] public section

namespace NativeRustc.Xmss

open LeanVM.Protocol.KeccakHash NativeRustc.Keccak Native.Keccak

/-! ## The tweakable hash (`hash.rs`) -/

/-- `Tweak`: the hash call's type `t < 32`, a chain step `step < 8`, `hi < 2^24` and `lo`. -/
structure Tweak where
  /-- The hash type. -/
  t : UInt8
  /-- The chain step. -/
  step : UInt8
  /-- The high field. -/
  hi : UInt32
  /-- The low field. -/
  lo : UInt32

/-- `TOP`: the top layer's flag in `hi`. -/
def top : UInt32 := (1 : UInt32) <<< 23

/-- `layer_hi`: `hi` for `field` on layer `layer`. -/
def layerHi (layer : Nat) (field : UInt32) : UInt32 := field ||| layer.toUInt32 * top

/-- `tweak(t, hi, lo)`, at step `0`. -/
def tweak (t : UInt8) (hi lo : UInt32) : Tweak := ⟨t, 0, hi, lo⟩

/-- `Tweak::step`: the same address at chain step `step`. -/
def Tweak.withStep (tw : Tweak) (step : Nat) : Tweak := { tw with step := step.toUInt8 }

/-- `address`: `lo` (4 bytes), `hi`'s low 3 bytes, `t | step << 5`, 8 zero bytes. -/
def address (tw : Tweak) : List UInt8 :=
  u32Bytes tw.lo ++ (u32Bytes tw.hi).take 3 ++ [tw.t ||| tw.step <<< 5] ++ List.replicate 8 0

/-- `th`: `Truncate_16` of the hash of `P | A | payload` (`hasher(pp, tw).update(payload)
.finalize()`). -/
def th (pp : List UInt8) (tw : Tweak) (payload : List UInt8) : List UInt8 :=
  (hashBytes (pp ++ address tw ++ payload)).take 16

/-- `(i as u128).to_le_bytes()` of a `usize`. -/
def u128Bytes (i : Nat) : List UInt8 := wordBytes i.toUInt64 ++ List.replicate 8 0

/-! ## WOTS+C (`wots.rs`) -/

/-- `chain`: `steps` steps of chain `i` of key `e` on `layer` from position `start`; the step
leaving position `from` hashes `current | (i as u128)` at the chain address at step `from`. -/
def chain (pp : List UInt8) (layer : Nat) (e : UInt32) (i start steps : Nat)
    (value : List UInt8) : List UInt8 :=
  (List.range' start steps).foldl (fun current pos ↦
    th pp ((tweak 1 (layerHi layer 0) e).withStep pos) (current ++ u128Bytes i)) value

/-- `wots_leaf_hash`: the leaf, `Th` over the chain ends. -/
def wotsLeafHash (pp : List UInt8) (layer : Nat) (e : UInt32) (ends : List (List UInt8)) :
    List UInt8 :=
  th pp (tweak 2 (layerHi layer 0) e) ends.flatten

/-- `message_digest`: `Th(P, A_msg, M | R)`, the hasher updated with the message, then the
randomizer. -/
def messageDigest (pp : List UInt8) (layer : Nat) (e : UInt32) (randomizer message : List UInt8) :
    List UInt8 :=
  (hashBytes (pp ++ address (tweak 12 (layerHi layer 0) e) ++ message ++ randomizer)).take 16

/-- `LOW = u128::MAX / 3`: the low bit of every two-bit digit. -/
def low : Nat := (2 ^ 128 - 1) / 3

/-- `!LOW` in `u128`: the high bit of every digit. -/
def notLow : Nat := 2 ^ 128 - 1 - low

/-- `u128::count_ones`. -/
def countOnes (x : Nat) : Nat := ∑ j ∈ Finset.range 128, (x.testBit j).toNat

/-- `is_codeword`: the digits past the 58th zero, and the 58 digits (each its low bit plus twice
its high bit) summing to `106`. -/
def isCodeword (d : Nat) : Bool :=
  d >>> 116 == 0 && countOnes (d &&& low) + 2 * countOnes (d &&& notLow) == 106

/-- The first 58 two-bit digits of `d`, a byte each (`codeword`'s `from_fn`). -/
def digits (d : Nat) : List UInt8 := (List.range 58).map fun i ↦ UInt8.ofNat (d >>> (2 * i) &&& 3)

/-- `codeword`: the digest's first 58 digits, if it is a codeword. -/
def codeword (digest : List UInt8) : Option (List UInt8) :=
  if isCodeword (leNat digest) then some (digits (leNat digest)) else none

/-- `wots_leaf`: the codeword of the message digest and the leaf of the chains walked from the
signature's values to their ends, or `None` if the digest is not a codeword. -/
def wotsLeaf (pp : List UInt8) (layer : Nat) (e : UInt32) (message randomizer : List UInt8)
    (values : List (List UInt8)) : Option (List UInt8 × List UInt8) :=
  match codeword (messageDigest pp layer e randomizer message) with
  | none => none
  | some x =>
    let ends := (List.range 58).map fun i ↦
      chain pp layer e i (x.getD i 0).toNat (3 - (x.getD i 0).toNat) (values.getD i [])
    some (x, wotsLeafHash pp layer e ends)

/-! ## The tree (`tree.rs`, `keccak256`'s `path_fold`) -/

/-- `node`: the Merkle parent at `level` and index `j` of `layer`, `Th` over its two children. -/
def node (pp : List UInt8) (layer level : Nat) (j : UInt32) (children : List UInt8) : List UInt8 :=
  th pp (tweak 3 (layerHi layer level.toUInt32) j) children

/-! ## Verification (`scheme.rs`) -/

/-- `LayerSignature`: the randomizer, the 58 chain values and the 16 path nodes. -/
structure LayerSignature where
  /-- `randomizer`. -/
  randomizer : List UInt8
  /-- `chain_values`. -/
  chainValues : List (List UInt8)
  /-- `path`. -/
  path : List (List UInt8)

/-- `LeanXmssPublicKey`. -/
structure PublicKey where
  /-- `merkle_root`. -/
  merkleRoot : List UInt8
  /-- `public_param`. -/
  publicParam : List UInt8

/-- `LeanXmssSignature`. -/
structure Signature where
  /-- `leaf_index`. -/
  leafIndex : UInt32
  /-- `bottom`. -/
  bottom : LayerSignature
  /-- `top`. -/
  top : LayerSignature

/-- `layer_root`: the codeword of a layer's signature by key `e` of `message` and the root its
path reaches, or `None`. -/
def layerRoot (pp : List UInt8) (layer : Nat) (e : UInt32) (message : List UInt8)
    (sig : LayerSignature) : Option (List UInt8 × List UInt8) :=
  match wotsLeaf pp layer e message sig.randomizer sig.chainValues with
  | none => none
  | some (x, leaf) =>
    some (x, pathFold leaf e.toNat sig.path fun level j children ↦
      node pp layer level j.toUInt32 children)

/-- `layer_index`: the key of `leaf_index` on `layer`. -/
def layerIndex (leafIndex : UInt32) (layer : Nat) : UInt32 :=
  (leafIndex.toUInt64 >>> (layer * 16).toUInt64).toUInt32

/-- **`verify`**: the bottom root from the message, the top root from the bottom root, compared
with the key's root. -/
def verify (pk : PublicKey) (message : List UInt8) (sig : Signature) : Bool :=
  match layerRoot pk.publicParam 0 (layerIndex sig.leafIndex 0) message sig.bottom with
  | none => false
  | some (_, bottomRoot) =>
    match layerRoot pk.publicParam 1 (layerIndex sig.leafIndex 1) bottomRoot sig.top with
    | none => false
    | some (_, root) => root == pk.merkleRoot

/-! ## Parsing -/

/-- `LeanXmssPublicKey::from_bytes`: the root, then the public parameter. -/
def PublicKey.fromBytes (bytes : List UInt8) : PublicKey := ⟨bytes.take 16, bytes.drop 16⟩

/-- `LayerSignature::read` on the slice cursor, modeled by an offset: the randomizer, the 58 chain values and the 16 path nodes from byte `cursor`, and the offset past them. -/
def takeLayer (bytes : List UInt8) (cursor : Nat) : LayerSignature × Nat :=
  (⟨slice bytes cursor 16, (List.range 58).map fun i ↦ slice bytes (cursor + 16 + 16 * i) 16,
      (List.range 16).map fun j ↦ slice bytes (cursor + 944 + 16 * j) 16⟩, cursor + 1200)

/-- `LeanXmssSignature::from_bytes`: the leaf index, then the bottom and the top layer. -/
def Signature.fromBytes (bytes : List UInt8) : Signature :=
  ⟨u32Of (bytes.take 4), (takeLayer bytes 4).1, (takeLayer bytes (takeLayer bytes 4).2).1⟩

/-! ## The layouts in memory -/

/-- A `LayerSignature`'s 1200 bytes as rustc lays out `LayerSignature::read`'s result: the path at `0`, the chain values at `256`, the randomizer at `1184`. -/
def LayerSignature.memBytes (ls : LayerSignature) : List UInt8 :=
  ls.path.flatten ++ ls.chainValues.flatten ++ ls.randomizer

/-- A `LeanXmssSignature`'s 2404 bytes as rustc lays it out (`xmss_verify`): the bottom layer at
`0`, the top at `1200`, the leaf index at `2400`. -/
def Signature.memBytes (sig : Signature) : List UInt8 :=
  sig.bottom.memBytes ++ sig.top.memBytes ++ u32Bytes sig.leafIndex

/-- `wots_leaf`'s result `Option<([u8; 58], [u8; 16])>` in its 75 bytes: the tag (`0` for
`None`) at `0`, the codeword at `1`, the leaf at `59`. -/
def WotsLeafOut (out : List UInt8) : Option (List UInt8 × List UInt8) → Prop
  | none => out.head? = some 0
  | some (x, leaf) => ∃ tag, tag ≠ 0 ∧ out.take 75 = tag :: (x ++ leaf)

/-! ## The wrapper (`rustc/xmss.rs`) -/

/-- The public key's 32 bytes: words `0 .. 3`, little-endian. -/
def pkBytes (w : Nat → UInt64) : List UInt8 := wordsBytes ((List.range 4).map w)

/-- The message's 32 bytes: words `4 .. 7`. -/
def messageBytes (w : Nat → UInt64) : List UInt8 :=
  wordsBytes ((List.range 4).map fun k ↦ w (4 + k))

/-- The signature's 2404 bytes: word `8` as a `u32`, then words `9 .. 308`. -/
def sigBytes (w : Nat → UInt64) : List UInt8 :=
  u32Bytes (w 8).toUInt32 ++ wordsBytes ((List.range 300).map fun k ↦ w (9 + k))

/-- **`xmss_verify`** on the input words `w`: `verify` of the key, the message and the signature
parsed from their bytes. -/
def xmssVerify (w : Nat → UInt64) : Bool :=
  verify (PublicKey.fromBytes (pkBytes w)) (messageBytes w) (Signature.fromBytes (sigBytes w))

end NativeRustc.Xmss
