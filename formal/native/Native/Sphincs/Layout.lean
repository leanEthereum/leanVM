module

public import Native.Bytes
public import Statement.LeanSphincs

/-!
# leanSPHINCS's input words

The public key, message and signature occupy 977 words:
a 128-bit value as two words, low first (`digestLo`, `digestHi`); the message as four, low first;
a counter as one.

| words | hold |
|---|---|
| `0, 1` | `PK.seed` |
| `2, 3` | `PK.root` |
| `4 .. 7` | the message |
| `8, 9` | the randomizer `R` |
| `10 + 22 κ ..` | FORS tree `κ`'s opening: the secret (2 words), the path's height `z` at `2 + 2 z` (10 heights) |
| `538`, `683`, `828` | layer `0`, `1`, `2`'s signature: the counter (1 word), chain `i` at `1 + 2 i` (64 chains), the path's level `j` at `129 + 2 j` (8, 8, 10 levels) |
-/

@[expose] public section

namespace Native.SphincsVerifier

open _root_.Sphincs HashSig

/-- The input's words. -/
def inputWords : Nat := 977

/-- Where FORS tree `κ`'s opening starts. -/
def forsOff (κ : Nat) : Nat := 10 + 22 * κ

/-- Where layer `l`'s signature starts. -/
def layerOff (l : Nat) : Nat := 538 + 145 * l

/-- Word `k` of a 128-bit value: `0` the low word, `1` the high. -/
def digestWord (d : BitVec 128) (k : Nat) : UInt64 := if k = 0 then Native.digestLo d else Native.digestHi d

/-- Word `k < 22` of a FORS tree's opening. -/
def forsWord (o : ForsTreeOpening) (k : Nat) : UInt64 :=
  if k < 2 then digestWord o.secret k
  else if h : k < 22 then digestWord (o.path ⟨(k - 2) / 2, by unfold forsTreeHeight; omega⟩) (k % 2)
  else 0

/-- Word `k` of layer `l`'s signature. -/
def layerWord {l : Layer} (ls : LayerSignature l) (k : Nat) : UInt64 :=
  if k = 0 then ls.counter.toNat.toUInt64
  else if h : k < 129 then digestWord (ls.chainValues ⟨(k - 1) / 2, by unfold chainCount; omega⟩) ((k - 1) % 2)
  else if h : k < 129 + 2 * layerHeight l then
    digestWord (ls.authenticationPath ⟨(k - 129) / 2, by omega⟩) ((k - 129) % 2)
  else 0

/-- Word `i` of the input. -/
def encode (pk : _root_.Sphincs.PublicKey) (message : Message) (sig : Signature) (i : Nat) : UInt64 :=
  if i < 2 then digestWord pk.publicSeed i
  else if i < 4 then digestWord pk.root (i - 2)
  else if i < 8 then Native.word256 message (i - 4)
  else if i < 10 then digestWord sig.randomizer (i - 8)
  else if h : i < layerOff 0 then
    forsWord (sig.forsOpening ⟨(i - 10) / 22, by unfold forsTreeCount; unfold layerOff at h; omega⟩)
      ((i - 10) % 22)
  else if i < layerOff 1 then layerWord (sig.layers 0) (i - layerOff 0)
  else if i < layerOff 2 then layerWord (sig.layers 1) (i - layerOff 1)
  else if i < inputWords then layerWord (sig.layers 2) (i - layerOff 2)
  else 0

/-- Decode the wrapper's words, discarding each counter's high 32 bits as Rust does. -/
def decode (w : Nat → UInt64) : _root_.Sphincs.PublicKey × Message × Signature :=
  let d := fun i => Native.ofWords (w i) (w (i + 1))
  ({ publicSeed := d 0, root := d 2 },
    BitVec.ofNat 256 ((w 4).toNat + 2 ^ 64 * (w 5).toNat +
      2 ^ 128 * (w 6).toNat + 2 ^ 192 * (w 7).toNat),
    { randomizer := d 8
      forsOpening := fun c =>
        { secret := d (forsOff c.val)
          path := fun z => d (forsOff c.val + 2 + 2 * z.val) }
      layers := fun l =>
        { counter := (w (layerOff l.val)).toUInt32.toBitVec
          chainValues := fun i => d (layerOff l.val + 1 + 2 * i.val)
          authenticationPath := fun j => d (layerOff l.val + 129 + 2 * j.val) } })

/-- Little-endian natural number of a byte list. -/
def leNatBytes (bs : List UInt8) : Nat := bs.foldr (fun b acc => b.toNat + 256 * acc) 0

/-- Slice `bytes[off..off + len]`. -/
def sliceBytes (bytes : List UInt8) (off len : Nat) : List UInt8 := (bytes.drop off).take len

/-- Byte offset of layer `l` in the 7740-byte canonical signature encoding. -/
def sigByteLayerOff (l : Nat) : Nat := [4240, 5396, 6552].getD l 0

/-- Decode a 32-byte canonical public key (`PK.seed || PK.root`). -/
def decodePk (pk : List UInt8) : _root_.Sphincs.PublicKey :=
  { publicSeed := BitVec.ofNat 128 (leNatBytes (sliceBytes pk 0 16))
    root := BitVec.ofNat 128 (leNatBytes (sliceBytes pk 16 16)) }

/-- Decode a 32-byte message. -/
def decodeMsg (msg : List UInt8) : Message :=
  BitVec.ofNat 256 (leNatBytes (sliceBytes msg 0 32))

/-- Decode a 7740-byte canonical leanSPHINCS signature. -/
def decodeSig (sig : List UInt8) : Signature :=
  let d := fun off => BitVec.ofNat 128 (leNatBytes (sliceBytes sig off 16))
  { randomizer := d 0
    forsOpening := fun c =>
      { secret := d (16 + 176 * c.val)
        path := fun z => d (32 + 176 * c.val + 16 * z.val) }
    layers := fun l =>
      { counter := BitVec.ofNat 32 (leNatBytes (sliceBytes sig (sigByteLayerOff l.val) 4).reverse)
        chainValues := fun i => d (sigByteLayerOff l.val + 4 + 16 * i.val)
        authenticationPath := fun j => d (sigByteLayerOff l.val + 1028 + 16 * j.val) } }

end Native.SphincsVerifier
