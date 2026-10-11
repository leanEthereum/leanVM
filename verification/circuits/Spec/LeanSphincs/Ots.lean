import LeanSphincs.TweakHash

/-!
# `LeanSphincs.Ots`

The one-time signature (WOTS+C): `v` hash chains and the target-sum code, the verifier's half
(`programs/leansphincs/guest/src/ots.rs` lines 15 to 136).
-/

namespace LeanSphincs

open LeanSphincs.Constants
open EthCryptographySpecs.Xmss (packBytes)

/-- One one-time key's place: the layer, the tree within it, the leaf within that tree (`Pos`, lib.rs lines 199 to
209). -/
structure Pos where
  /-- `lay`: the layer, 0 at the top. -/
  lay : Fin D
  /-- `tau`: the tree within the layer. -/
  tau : UInt32
  /-- `e`: the leaf within the tree. -/
  e : UInt32
  deriving DecidableEq, Repr

/-- The one-time key an index uses on a layer (`Pos::of`, lib.rs lines 215 to 227):

```text
idx = [ tau_0 = 0 | e_0 : 12 bits | e_1 : 7 bits | e_2 : 7 bits ]
```
-/
def Pos.of (idx : Nat) (lay : Fin D) : Pos where
  lay := lay
  tau := UInt32.ofNat (idx >>> SUFFIX[lay.val]'(by have := lay.isLt; omega))
  e := UInt32.ofNat ((idx >>> SUFFIX[lay.val + 1]'(by have := lay.isLt; omega)) % 2 ^ HEIGHTS[lay])

namespace Ots

/-! ## The encoding -/

/-- One half of a digest, read as a little-endian 64-bit word. -/
def digestWord (d : Digest) (half : Fin 2) : UInt64 :=
  (List.range 8).foldr (fun k acc =>
    acc <<< 8 ||| (d[8 * half.val + k]?.getD 0).toUInt64) 0

/-- Chunk `i` of a codeword: bits `3r .. 3r + 2` of word `i / 21`, `r = i % 21` (`Digits::get`, ots.rs lines 112
to 115). -/
def digits (d : Digest) : Vector (Fin CHAIN_LEN) V :=
  Vector.ofFn fun i =>
    let half : Fin 2 := ⟨i.val / (V / 2), by have := i.isLt; simp only [V] at this ⊢; omega⟩
    ⟨((digestWord d half) >>> UInt64.ofNat (W * (i.val % (V / 2)))).toNat % CHAIN_LEN,
      Nat.mod_lt _ (by decide)⟩

/-- `Enc`: the codeword of `message` under `counter`, or nothing if it has none (`Ots::encode`, ots.rs lines 44 to
60).

The hash is of the 52 bytes `tw | P | M | counter`. Bit 63 of both 64-bit halves of its first 16 bytes is zero, and
the chunks sum to `T`. The guest sums the chunks by adding neighbouring fields in place (`Digits::sum`, ots.rs lines
117 to 135), which with bit 63 zero is the sum of the chunks: no field overflows into the next. -/
def encode (pp : PublicParam) (pos : Pos) (message : Digest) (counter : Counter) :
    Option (Vector (Fin CHAIN_LEN) V) :=
  let d := th pp (tweak .enc pos.lay pos.tau 0 pos.e) (packBytes message ++ packBytes counter)
  if (digestWord d 0 ||| digestWord d 1) >>> 63 != 0 then none
  else
    let x := digits d
    if x.foldl (fun s c => s + c.val) 0 == TARGET_SUM then some x else none

/-! ## Chains and the leaf -/

/-- `Chain`: walk chain `i` for `steps` steps from value number `start` (`Ots::walk`, ots.rs lines 62 to 71).

The step out of value `s` is hashed at position `8i + s`. -/
def walk (pp : PublicParam) (pos : Pos) (i : Fin V) (start steps : Nat) (value : Digest) : Digest :=
  (List.range' start steps).foldl (fun v s =>
    th pp (tweak .chain pos.lay pos.tau (UInt32.ofNat (CHAIN_LEN * i.val + s)) pos.e) (packBytes v)) value

/-- The Merkle leaf of a one-time key: `Th` over its `v` chain ends in order (`leaf_hash`, ots.rs lines 93 to
105). -/
def leafHash (pp : PublicParam) (pos : Pos) (ends : List Digest) : Digest :=
  th pp (tweak .leaf pos.lay pos.tau 0 pos.e) (concatDigests ends)

/-- `Ots.leaf`: the leaf a one-time signature of the key at `pos` recovers, or nothing if `counter` gives no
codeword (`Ots::leaf`, ots.rs lines 73 to 90). Chain `i`, opened at value `x_i`, is walked the rest of the way to
value 7. -/
def leaf (pp : PublicParam) (pos : Pos) (message : Digest) (counter : Counter) (ots : Vector Digest V) :
    Option Digest :=
  (encode pp pos message counter).map fun x =>
    leafHash pp pos (List.ofFn fun i : Fin V =>
      walk pp pos i x[i].val (CHAIN_LEN - 1 - x[i].val) ots[i])

end Ots

end LeanSphincs
