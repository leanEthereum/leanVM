/-
  RunModel: the Model mirror of the guest's `main` beside the statement's verifier, on a real input.

    lake exe rv64mc-model WORDS

  `WORDS` is the input as little-endian 64-bit words (`scripts/input-words.py`). It prints `decodeInput`'s result
  and, where the input decodes, `mainVerdictRust` (`Rv64mc/Model/Walk.lean`, `ACCEPT` as `true`) next to the
  statement's `verify` (`notes/non-vacuity.md`).
-/

import Rv64mc.EndStatement
import Rv64mc.Model.Walk

open Rv64mc Rv64mc.Model

/-- The input file's little-endian 64-bit words. -/
def readModelWords (bs : ByteArray) : List (BitVec 64) :=
  (List.range (bs.size / 8)).map fun k =>
    BitVec.ofNat 64 ((List.range 8).foldl (fun acc j => acc + (bs.get! (8 * k + j)).toNat * 256 ^ j) 0)

def main (args : List String) : IO UInt32 := do
  let wordsPath ← match args with
    | w :: _ => pure w
    | _ => IO.eprintln "usage: rv64mc-model WORDS"; return 2
  let words := readModelWords (← IO.FS.readBinFile wordsPath)
  IO.println s!"input: {words.length} words"
  match decodeInput words with
  | none => IO.println "decodeInput: none"
  | some (bc, pi, proof) =>
    IO.println s!"decodeInput: some (bytecode {bc.length} words, stream {proof.stream.length} scalars, \
      {proof.openings.length} phases)"
    IO.println s!"mainVerdictRust: {mainVerdictRust (bc.map BF64.toBitVec) (digestBits pi) proof}"
    IO.println s!"verify: {verify bc pi proof}"
  return 0
