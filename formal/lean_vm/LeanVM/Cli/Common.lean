/-
  LeanVM.Cli.Common

  What the command-line drivers of `cli/` share. No proof imports it.
-/

module

public import LeanVM.Wire.Encoding

/-!
# What the drivers share

The reader and the writer of the plain rendering of a proof's openings (`merkle_phases.bin`, which
`leanvm-verify` reads and `leanvm-prove` writes, and the openings of `wire-diff`'s plain files),
and the hexadecimal digits and little-endian bit vectors of the test cases (`guest-diff`,
`scheme-vectors`). No proof imports this module.
-/

@[expose] public section

namespace LeanVM.Cli

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.KeccakHash

/-! ## The plain rendering: every count a little-endian `u32`, every word and position a `u64` -/

/-- A reader: the value and the offset after it, or `none` past the end. -/
abbrev Read (α : Type) := ByteArray → ℕ → Option (α × ℕ)

/-- A little-endian word of `size` bytes. -/
def readLE (size : ℕ) : Read ℕ := fun bytes offset ↦
  if offset + size ≤ bytes.size then
    some ((List.range size).foldr (fun k acc ↦ acc * 256 + (bytes.get! (offset + k)).toNat) 0,
      offset + size)
  else none

/-- `count` values, in order. -/
def readMany {α : Type} (read : Read α) : ℕ → Read (List α)
  | 0, _, offset => some ([], offset)
  | count + 1, bytes, offset => do
    let (value, offset) ← read bytes offset
    let (values, offset) ← readMany read count bytes offset
    some (value :: values, offset)

/-- A `u32` count, then that many values. -/
def readCounted {α : Type} (read : Read α) : Read (List α) := fun bytes offset ↦ do
  let (count, offset) ← readLE 4 bytes offset
  readMany read count bytes offset

/-- A `K` word. -/
def readK : Read K := fun bytes offset ↦
  (readLE 8 bytes offset).map fun (w, offset) ↦ (K.ofLane (UInt64.ofNat w), offset)

/-- A digest, its 32 bytes: four little-endian words. -/
def readDigest : Read Digest := fun bytes offset ↦ do
  let (w0, offset) ← readLE 8 bytes offset
  let (w1, offset) ← readLE 8 bytes offset
  let (w2, offset) ← readLE 8 bytes offset
  let (w3, offset) ← readLE 8 bytes offset
  some (#v[UInt64.ofNat w0, UInt64.ofNat w1, UInt64.ofNat w2, UInt64.ofNat w3], offset)

/-- A Merkle path: its `u64` position, its leaf's `u32` length and words, its siblings' `u32`
count and digests. -/
def readOpening : Read Opening := fun bytes offset ↦ do
  let (leafIndex, offset) ← readLE 8 bytes offset
  let (leaf, offset) ← readCounted readK bytes offset
  let (path, offset) ← readCounted readDigest bytes offset
  some (⟨leafIndex, leaf, path⟩, offset)

/-- The openings, the Rust `Vec<Vec<MerklePath>>`: the `u32` phase count, then per phase its
`u32` path count and the paths. -/
def readPhases : Read (List (List Opening)) := readCounted (readCounted readOpening)

/-- The bytes `readPhases` reads. -/
def phasesBytes (openings : List (List Opening)) : List UInt8 :=
  LeanVM.Prover.u32Bytes openings.length ++ openings.flatMap fun phase ↦
    LeanVM.Prover.u32Bytes phase.length ++ phase.flatMap fun opening ↦
      wordBytes (UInt64.ofNat opening.leafIndex) ++ LeanVM.Prover.u32Bytes opening.leaf.length ++
        opening.leaf.flatMap K.toBytes ++ LeanVM.Prover.u32Bytes opening.path.length ++
        opening.path.flatMap digestBytes

/-! ## Test cases -/

/-- A hexadecimal digit's value. -/
def hexDigit? (c : Char) : Option ℕ :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10) else none

/-- The little-endian number of `n` bits of some bytes. -/
def bitsLE (n : ℕ) (bytes : List ℕ) : BitVec n :=
  BitVec.ofNat n (bytes.foldr (fun b acc ↦ b + 256 * acc) 0)

end LeanVM.Cli
