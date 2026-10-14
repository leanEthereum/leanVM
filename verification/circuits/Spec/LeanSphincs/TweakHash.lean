import EthCryptographySpecs.Xmss.Blake2s
import LeanSphincs.Types

/-!
# `LeanSphincs.TweakHash`

The tweak and the tweakable hash `Th(P, tw, M)`: standard BLAKE2s of `tw | P | M`, cut to `n = 128` bits
(`programs/leansphincs/guest/src/lib.rs` lines 12, 74 to 89 and 259 to 287).
-/

namespace LeanSphincs

open LeanSphincs.Constants
open EthCryptographySpecs.Xmss (packBytes)
open EthCryptographySpecs.Xmss.Blake2s.Internal (wordBytes)

/-! ## Call sites -/

/-- Which call site a hash belongs to: byte 1 of a tweak (lib.rs lines 77 to 89). -/
inductive TweakType where
  /-- A one-time chain's secret start (`TWEAK_PRF`). -/
  | prf
  /-- A step along a hash chain (`TWEAK_CHAIN`). -/
  | chain
  /-- A one-time key's Merkle leaf (`TWEAK_LEAF`). -/
  | leaf
  /-- A hypertree node (`TWEAK_NODE`). -/
  | node
  /-- The target-sum encoding (`TWEAK_ENC`). -/
  | enc
  /-- The public parameter (`TWEAK_PARAMETER`). -/
  | parameter
  /-- A signing attempt's randomizer (`TWEAK_RANDOMIZER`). -/
  | randomizer
  /-- A few-time leaf's secret (`TWEAK_FTS_PRF`). -/
  | ftsPrf
  /-- A few-time leaf (`TWEAK_FTS_LEAF`). -/
  | ftsLeaf
  /-- A few-time tree's node (`TWEAK_FTS_NODE`). -/
  | ftsNode
  /-- The few-time key over the roots (`TWEAK_FTS_ROOTS`). -/
  | ftsRoots
  /-- The message digest (`TWEAK_MSG`). -/
  | msg
  deriving DecidableEq, Repr

/-- The byte each tweak type is assigned (lib.rs lines 78 to 89). -/
def TweakType.toByte : TweakType → UInt8
  | .prf        => 0
  | .chain      => 1
  | .leaf       => 2
  | .node       => 3
  | .enc        => 4
  | .parameter  => 5
  | .randomizer => 7
  | .ftsPrf     => 8
  | .ftsLeaf    => 9
  | .ftsNode    => 10
  | .ftsRoots   => 11
  | .msg        => 12

/-- Byte 0 of every tweak: 1 for leanSPHINCS, so none of its hashes is a leanXMSS one (lib.rs line 75). -/
def PROTOCOL_DOMAIN_SEP : UInt8 := 1

/-! ## The tweak -/

/-- A tweak (`tweak`, lib.rs lines 259 to 274):

```text
bytes  0      1     2    3     4..8  8..12  12..16
       domain type  lay  zero  p     tau    j
```

`lay` is a hypertree layer or a few-time tree, below 14 at every call, so the guest's `(lay as u64) << 16` is byte
2 alone. -/
def tweak (t : TweakType) (lay : Nat) (tau p j : UInt32) : Tweak :=
  #v[PROTOCOL_DOMAIN_SEP, t.toByte, UInt8.ofNat lay, 0] ++ wordBytes p ++ wordBytes tau ++ wordBytes j

/-! ## The tweakable hash -/

/-- `Th(P, tw, M)`: BLAKE2s of `tw | P | M`, its first 16 bytes (`th` and `digest`, lib.rs lines 276 to 287). -/
def th (pp : PublicParam) (tw : Tweak) (payload : ByteArray) : Digest :=
  (EthCryptographySpecs.Xmss.Blake2s.hash (packBytes tw ++ packBytes pp ++ payload)).take DIGEST_LEN

/-- A tree node: `Th` of `left | right` (`NodeHash::hash`, lib.rs lines 328 to 335). -/
def nodeHash (pp : PublicParam) (tw : Tweak) (left right : Digest) : Digest :=
  th pp tw (packBytes left ++ packBytes right)

/-! ## Trees -/

/-- `Tree.fold`: leaf `e`'s value folded up its path to its tree's root (`fold`, lib.rs lines 343 to 365).

The node at level `l + 1` is hashed under `tweak t lay tau (l + 1) (e >> (l + 1))`, the current node on the side
bit `l` of `e` names. The guest builds that tweak by adding `1 << 32` to the first word and shifting `j` into the
second's high half, which is the same bytes while `p` and `j` fit 32 bits (they are at most 12 and `2^12`). -/
def fold (pp : PublicParam) (t : TweakType) (lay : Nat) (tau : UInt32) (e : Nat) (leaf : Digest)
    (path : List Digest) : Digest :=
  (path.zipIdx).foldl (fun current (sibling, l) =>
    let tw := tweak t lay tau (UInt32.ofNat (l + 1)) (UInt32.ofNat (e >>> (l + 1)))
    if (e >>> l) % 2 == 0 then nodeHash pp tw current sibling else nodeHash pp tw sibling current) leaf

end LeanSphincs
