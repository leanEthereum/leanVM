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

/-! ## Programs -/

section

open LeanVM.Semantics LeanVM.Arithmetization
/-- The opcode of a code. -/
def opcodeOf? (c : K) : Option Opcode :=
  [Opcode.xor, .mulNative, .setConstant, .deref, .jump, .keccak].find? (·.busCode = c)

/-- A flag word. -/
def flagOf? (c : K) : Option Bool :=
  if c = 0 then some false else if c = 1 then some true else none

/-- The `DEREF` mode of its two flags. -/
def derefModeOf? (fpc ffp : K) : Option DerefMode :=
  if fpc = 0 ∧ ffp = 0 then some .cell
  else if fpc = 1 ∧ ffp = 0 then some .pc
  else if fpc = 0 ∧ ffp = 1 then some .fp
  else none

/-- The `KECCAK` output cells of its two flags `(out_two, out_all)`. -/
def outCellsOf? (two all : K) : Option KeccakOutputCells :=
  if two = 0 ∧ all = 0 then some .one
  else if two = 1 ∧ all = 0 then some .two
  else if two = 1 ∧ all = 1 then some .all
  else none

/-- The instruction of a bus entry (the inverse of `entry`, where it is one). -/
def instrOf? (e : Array K) : Option LeanIsaInstruction := do
  let op ← opcodeOf? (e.getD 0 0)
  let x (i : ℕ) : K := e.getD i 0
  match op with
  | .xor => some (.xor (x 1) (x 2) (x 3))
  | .mulNative => some (.mulNative (x 1) (x 2) (x 3))
  | .setConstant => some (.setConstant (x 1) (E.ofLimbs (x 2) (x 3)))
  | .deref => do
    let mode ← derefModeOf? (x 4) (x 5)
    some (.deref (x 1) (x 2) (x 3) mode)
  | .jump => some (.jump (x 1) (x 2) (x 3))
  | .keccak => do
    let inOdd ← flagOf? (x 9)
    let outOdd ← flagOf? (x 10)
    let outCells ← outCellsOf? (x 11) (x 12)
    some (.keccak ![x 1, x 2, x 3, x 4] (x 5) (x 6) (x 7) (x 8) inOdd outOdd outCells)

/-- The program a bytecode table encodes: `16 · 2^logSize` words, word `i + 2^logSize · s` slot
`s` of instruction `i`; checked to re-encode to the same words. -/
def decodeProgram (words : Array K) : Except String LeanIsaProgram := do
  let n := words.size / 16
  let logSize := Nat.log2 n
  unless 16 * 2 ^ logSize = words.size do throw "the bytecode is not 16 · 2^k words"
  if h : logSize ≤ maxLogBytecode then
    let mut code : Array LeanIsaInstruction := #[]
    for i in [0:n] do
      let e := (Array.range 13).map fun j ↦ words.getD (i + n * (3 + j)) 0
      match instrOf? e with
      | some ins => code := code.push ins
      | none => throw s!"instruction {i} does not decode"
    let prog : LeanIsaProgram := ⟨logSize, h, fun i ↦ code.getD i.val (.jump 0 0 0)⟩
    unless (LeanVM.bytecodeWords prog).toArray == words do throw "the bytecode does not re-encode"
    return prog
  else throw "the bytecode is too long"

end

end LeanVM.Cli
