import Aeneas
import EthCryptographySpecs.Xmss.Blake2s

/-!
# Bytes of words, and BLAKE2s on them

What the models of the SDK functions are written in: the guest's values are little-endian 64-bit words, the
specification's are bytes, and BLAKE2s is the specification's `Blake2s.hash`.
-/

open Aeneas Aeneas.Std

namespace leanxmss.Bytes

/-- The `n` little-endian bytes of the natural number `x`, cut to `n` bytes. -/
def le : Nat → Nat → List UInt8
  | 0, _ => []
  | n + 1, x => UInt8.ofNat x :: le n (x / 256)

/-- The little-endian bytes of words, in order: how the machine lays them out in memory. -/
def ofWords (ws : List U64) : List UInt8 :=
  ws.flatMap fun w => le 8 w.val

/-- The natural number whose little-endian bytes are `bs`. -/
def toNat (bs : List UInt8) : Nat :=
  bs.foldr (fun b acc => b.toNat + 256 * acc) 0

/-- The word whose little-endian bytes are `bs`, the first eight of them. -/
def word (bs : List UInt8) : U64 :=
  ⟨BitVec.ofNat 64 (toNat (bs.take 8))⟩

/-- A 32-byte digest as four little-endian words. -/
def digestWords (d : Vector UInt8 32) : Std.Array U64 4#usize :=
  Std.Array.make 4#usize [word (d.toList.drop 0), word (d.toList.drop 8), word (d.toList.drop 16),
    word (d.toList.drop 24)]

/-- `bs` with `xs` written over it from byte `pos`, its length kept when `xs` fits. -/
def splice (bs : List UInt8) (pos : Nat) (xs : List UInt8) : List UInt8 :=
  bs.take pos ++ xs ++ bs.drop (pos + xs.length)

/-- BLAKE2s-256 of a byte string, as four little-endian words. -/
def blake2s (bs : List UInt8) : Std.Array U64 4#usize :=
  digestWords (EthCryptographySpecs.Xmss.Blake2s.hash ⟨bs.toArray⟩)

end leanxmss.Bytes
