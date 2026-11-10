import LeanVM.Wire.Encoding
import LeanVM.Cli.Common

/-!
# `wire-diff`: the proof's wire encoding on byte files

lean_vm's transcription of leanVM's one encoding of a proof (`crates/fiat_shamir/src/wire.rs`,
each Merkle phase pruned to the siblings no other path gives, scaraven's idea,
https://github.com/scaraven):
`Proof.fromBytes` (`LeanVM.Wire.Encoding`), over Keccak-f[1600] in `Id`, and
`Proof.toBytes` (`LeanVM.Wire.Encoding`), compiled, on byte files, so that
`scripts/wire-diff.py` can set its results beside the Rust's (`scripts/wire-diff`,
`leanvm-rust-wire`) on the same bytes:

    wire-diff decode <wire> <plain out>
    wire-diff encode <plain> <wire out>
    wire-diff vector <wire out>
    wire-diff --batch < lines of tab-separated commands

`decode` runs `Proof.fromBytes` and prints `none`, or `some`, writing the proof in the plain
rendering below, followed by `reencode-ok` when `Proof.toBytes` of it gives back the input and
`reencode-differs` otherwise. `encode` reads a proof in the plain rendering and writes
`Proof.toBytes` of it, printing `encoded`, followed by `roundtrip-ok` when `Proof.fromBytes` gives
back the proof (`roundtrip-differs` otherwise); `malformed` for a file that is no plain rendering.
`vector` builds the proof of wire.rs's test `proof_round_trips_through_its_one_encoding` (its
paths computed here, as the Rust's `open` gives them), checks the test's assertions on
`Proof.toBytes` of it (its length, that `Proof.fromBytes` gives the proof back, and refuses one
byte more), writes the bytes and prints `vector <length>`, or `vector-fails <what>`. In `--batch`
mode every line of standard input is one command, its words separated by tabs, and one result
line is printed for it, in order.

The plain rendering of a proof is the Rust's (`scripts/wire-diff/src/main.rs`): every count a
little-endian 32-bit word, every word and position a little-endian 64-bit word; the stream's
length and its elements, each two words `c0, c1`; the number of phases, and for each its
number of paths, and for each path its position, its leaf's length and words, its siblings' count
and their 32 bytes each. Two proofs are equal exactly when their plain renderings are.
-/

namespace WireDiff

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Cli

/-- Keccak-f[1600] in `Id`, the permutation decoding hashes with. -/
def permutation (state : KeccakState) : Id KeccakState := pure (keccakF1600 state)

/-- The plain rendering of a proof. -/
def plain (proof : Proof) : List UInt8 :=
  LeanVM.Prover.u32Bytes proof.stream.length ++ proof.stream.flatMap E.toBytes ++
    phasesBytes proof.openings

/-- An `E` word, its limbs `c0, c1`. -/
def readE : Read E := fun bytes offset ↦ do
  let (c0, offset) ← readK bytes offset
  let (c1, offset) ← readK bytes offset
  some (E.ofLimbs c0 c1, offset)

/-- The proof whose plain rendering the bytes are, if they are one. -/
def fromPlain (bytes : ByteArray) : Option Proof := do
  let (stream, offset) ← readCounted readE bytes 0
  let (openings, offset) ← readPhases bytes offset
  if offset = bytes.size then some ⟨stream, openings⟩ else none

/-! ## The commands -/

/-- The bytes of a list, as an array. -/
def toArray (bytes : List UInt8) : ByteArray := ⟨bytes.toArray⟩

/-- `decode`: `Proof.fromBytes`, and `Proof.toBytes` of what it gives. -/
def decode (input output : String) : IO String := do
  let bytes := (← IO.FS.readBinFile input).toList
  match Proof.fromBytes (m := Id) permutation bytes with
  | none => return "none"
  | some proof =>
    IO.FS.writeBinFile output (toArray (plain proof))
    return if proof.toBytes = bytes then "some reencode-ok" else "some reencode-differs"

/-- `encode`: `Proof.toBytes` of a plain proof, and `Proof.fromBytes` of it. -/
def encode (input output : String) : IO String := do
  match fromPlain (← IO.FS.readBinFile input) with
  | none => return "malformed"
  | some proof =>
    let bytes := proof.toBytes
    IO.FS.writeBinFile output (toArray bytes)
    let again := Proof.fromBytes (m := Id) permutation bytes
    return if (again.map plain) = some (plain proof) then "encoded roundtrip-ok"
      else "encoded roundtrip-differs"

/-- The proof of wire.rs's test `proof_round_trips_through_its_one_encoding`: the stream
`[F128::new(1, 2)]`, and one phase, `open(4, &[3, 1, 3], 3, node, row)` on the rows
`[0, 0, 1], [0, 2, 3], [0, 0, 4], [0, 5, 0]`: each query's position, its row (three words, so
unpadded), and its siblings, the leaf `q ^ 1` and the node `(q >> 1) ^ 1` above. -/
def vectorProof : Proof :=
  let rows : List (List K) :=
    [[0, 0, 1], [0, 2, 3], [0, 0, 4], [0, 5, 0]].map (·.map fun w ↦ K.ofLane (UInt64.ofNat w))
  let row (q : ℕ) : List K := rows.getD q []
  let leaf (q : ℕ) : Digest := keccak256 ((row q).flatMap K.toBytes)
  let node : ℕ → ℕ → Digest
    | 0, i => leaf i
    | _, i => keccak256 (digestBytes (leaf (2 * i)) ++ digestBytes (leaf (2 * i + 1)))
  let path (q : ℕ) : Opening :=
    ⟨q, row q, (List.range 2).map fun level ↦ node level ((q >>> level) ^^^ 1)⟩
  ⟨[E.ofLimbs (K.ofLane 1) (K.ofLane 2)], [[3, 1, 3].map path]⟩

/-- `vector`: the test's assertions on `Proof.toBytes vectorProof`, then its bytes. -/
def vector (output : String) : IO String := do
  let bytes := vectorProof.toBytes
  let decoded := (Proof.fromBytes (m := Id) permutation bytes).map plain
  let longer := Proof.fromBytes (m := Id) permutation (bytes ++ [0])
  if bytes.length ≠ (4 + 16) + 4 + (4 + 3 * 4) + 3 * 4 + 2 * 2 * 8 + 2 * 32 then
    return s!"vector-fails length {bytes.length}"
  if decoded ≠ some (plain vectorProof) then return "vector-fails round trip"
  if longer.isSome then return "vector-fails a byte more decodes"
  IO.FS.writeBinFile output (toArray bytes)
  return s!"vector {bytes.length}"

/-- One command. -/
def run : List String → IO String
  | ["decode", input, output] => decode input output
  | ["encode", input, output] => encode input output
  | ["vector", output] => vector output
  | words => return s!"error unknown command: {" ".intercalate words}"

/-- Read standard input's lines, one command each, and print one result line for each. -/
partial def batch (stdin : IO.FS.Stream) (stdout : IO.FS.Stream) : IO Unit := do
  let line ← stdin.getLine
  if line.isEmpty then return
  let line : String := String.ofList (line.toList.filter (· ≠ '\n'))
  unless line.isEmpty do
    let result ← try run (line.splitOn "\t") catch e => pure s!"error {e}"
    stdout.putStrLn result
    stdout.flush
  batch stdin stdout

end WireDiff

/-- The driver. -/
def main (args : List String) : IO UInt32 := do
  match args with
  | ["--batch"] =>
    WireDiff.batch (← IO.getStdin) (← IO.getStdout)
    return 0
  | [] =>
    IO.eprintln "usage: wire-diff decode <wire> <plain out> | encode <plain> <wire out>"
    IO.eprintln "       wire-diff vector <wire out> | --batch < lines of tab-separated commands"
    return 2
  | words =>
    let result ← try WireDiff.run words catch e => pure s!"error {e}"
    IO.println result
    return if result.startsWith "error" || result.startsWith "vector-fails" then 1 else 0
