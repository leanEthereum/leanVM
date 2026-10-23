import LeanVM.Protocol.Verifier.Load

/-!
# `leanvm-verify`: the deployed verifier on a proof's four files

`lake exe leanvm-verify <bytecode> <public input> <stream> <openings>` runs
`LeanVM.Protocol.Verifier.verifyFiles`, the Lean transcription of `python-verifier/verifier.py`
at leanVM `127510d14c98ade4e8a97646c44fa7f1ff5e752d` (the `verify` of `LeanVM/Protocol/LeanVM.lean`
on the program's bytecode words), compiled, on the four files the Rust prover writes
(`scripts/export-verifier-fixtures-rust.sh`), and prints the verdict; the exit code is `0` on
acceptance. `scripts/fuzz-verifier.py` compares it with the Rust verifier on mutated proofs.
-/

open LeanVM.Protocol.Verifier

/-- The driver. -/
def main (args : List String) : IO UInt32 := do
  match args with
  | [bytecode, publicInput, stream, openings] =>
    let read := fun (p : String) => do return (← IO.FS.readBinFile p).toList
    if verifyFiles (← read bytecode) (← read publicInput) (← read stream) (← read openings) then
      IO.println "verification succeeded"
      return 0
    else
      IO.println "verification failed"
      return 1
  | _ =>
    IO.eprintln "usage: leanvm-verify <bytecode> <public input> <stream> <openings>"
    return 2
