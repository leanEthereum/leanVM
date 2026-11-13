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

def main (args : List String) : IO UInt32 := do
  match args with
  | dir :: rest =>
    let fuel := (rest.head?.bind String.toNat?).getD (2 ^ 64)
    let read := fun (p : String) => do return (← IO.FS.readBinFile (dir ++ "/" ++ p)).toList
    let some words := decodeWords (← read "bytecode.bin") | do IO.eprintln "bad bytecode"; return 2
    let some digest := decodeDigest (← read "public_input.bin") | do
      IO.eprintln "bad public input"; return 2
    let prog ← match LeanVM.Cli.decodeProgram words.toArray with
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
