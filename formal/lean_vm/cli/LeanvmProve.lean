import Statement.Prover.Prove
import LeanVM.Prover.Fast.Prover
import LeanVM.Protocol.Verifier
import LeanVM.Wire.Encoding
import LeanVM.Cli.Common

/-!
# `leanvm-prove`: the statement's honest prover on a program, an input and a trace

`lake exe leanvm-prove <case dir> [fuel]` reads, from the case directory
(`scripts/export-prover-traces-rust.sh` writes them):

* `bytecode.bin`: the program's bytecode table (the sixteen slots of every instruction, slot by
  slot), decoded into a `Program` (`decodeProgram`, checked to re-encode to the same words);
* `public_input.bin`: the public input's 32 bytes;
* `memory.bin`: the execution's memory, 16 bytes per cell;
* `trace.txt`: `<log2 cells> <steps> <rate>`;

runs `LeanVM.Prover.prove` with Keccak-256 and Keccak-f[1600] (the deployed hashes, `Id`),
compiled as its copy with `E`'s arithmetic on machine words (`LeanVM.Prover.Fast.Prover`), at
`fuel` nonces per proof of work (default `2^64`, every `u64` nonce the Rust's search tries), and writes the proof in the case directory in
the forms of the Rust prover's fixtures, which `leanvm-verify` and the Rust verifier read:

* `lean_stream.bin`: the scalars, two little-endian `u64` limbs each;
* `lean_merkle_phases.bin`: the structured unpruned openings, the Rust `Vec<Vec<MerklePath>>`, all
  little-endian: the `u32` phase count; per phase its `u32` path count; per path its `u64` position,
  its `u32` leaf length and that many `u64` words, its `u32` sibling count and that many 32-byte
  digests;
* `lean_proof.wire`: the proof's one wire encoding, `Proof.toBytes` (`Proof::to_bytes`,
  `crates/fiat_shamir/src/wire.rs`).

It prints the time taken; if the prover makes no proof (`none`), it says so and exits with `1`.
-/

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization LeanVM.Protocol
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakHash

namespace LeanvmProve

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

def main (args : List String) : IO UInt32 := do
  match args with
  | dir :: rest =>
    let fuel := (rest.head?.bind String.toNat?).getD (2 ^ 64)
    let read := fun (p : String) => do return (← IO.FS.readBinFile (dir ++ "/" ++ p)).toList
    let some words := decodeWords (← read "bytecode.bin") | do IO.eprintln "bad bytecode"; return 2
    let some digest := decodeDigest (← read "public_input.bin") | do
      IO.eprintln "bad public input"; return 2
    let prog ← match decodeProgram words.toArray with
      | .ok p => pure p
      | .error e => do IO.eprintln e; return 2
    let input : PublicInput := ⟨fun i ↦ K.ofLane digest[i]⟩
    let some mem := decodeScalars (← read "memory.bin") | do IO.eprintln "bad memory"; return 2
    let mem := mem.toArray
    let nums := (((← IO.FS.readFile (dir ++ "/trace.txt")).trimAscii.toString.splitOn " ")).filterMap String.toNat?
    let [κ, steps, ρ] := nums | do IO.eprintln "bad trace.txt"; return 2
    unless mem.size = 2 ^ κ do IO.eprintln "the memory is not 2^κ cells"; return 2
    let t : Execution prog := ⟨κ, fun i ↦ mem.getD i.val 0, steps⟩
    let start ← IO.monoMsNow
    let some proof := LeanVM.Prover.prove (m := Id) keccakF1600 prog input t ρ fuel
      | do
        IO.eprintln s!"{dir}: no proof (the trace is no valid execution within the cap, the rate \
          is invalid, or a proof of work found no nonce below {fuel})"
        return 1
    IO.FS.writeBinFile (dir ++ "/lean_stream.bin") ⟨(proof.stream.flatMap E.toBytes).toArray⟩
    IO.FS.writeBinFile (dir ++ "/lean_merkle_phases.bin")
      ⟨(LeanVM.Cli.phasesBytes proof.openings).toArray⟩
    IO.FS.writeBinFile (dir ++ "/lean_proof.wire") ⟨proof.toBytes.toArray⟩
    let stop ← IO.monoMsNow
    IO.println s!"{dir}: {proof.stream.length} scalars, {proof.openings.length} phases, \
      {proof.openings.flatten.length} openings, {(stop - start).toFloat / 1000} s"
    return 0
  | _ =>
    IO.eprintln "usage: leanvm-prove <case dir> [fuel]"
    return 2

end LeanvmProve

def main (args : List String) : IO UInt32 := LeanvmProve.main args
