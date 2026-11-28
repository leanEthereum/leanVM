/-
  LeanVM.Protocol.Verifier

  The leanVM verifier (`Statement.Verifier.Lib`) on its files: the compiled verifier and the
  decoders of the bytecode, the public input and the scalar stream.
-/

module

public import Statement.Verifier.Lib
public import LeanVM.Protocol.Files
import LeanVM.Facts.Verifier

/-!
# The verifier on its files

The verifier is `Statement.Verifier.Lib`. This module gathers what `lake exe leanvm-verify` and
`lake exe leanvm-prove` need to run it on the files the Rust prover's proofs are written to
(`scripts/export-verifier-fixtures-rust.sh`): the compiled verifier (`LeanVM.Facts.Verifier`) and
the decoders (`LeanVM.Protocol.Files`).
-/
