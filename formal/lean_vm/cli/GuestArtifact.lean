import LeanVM.Guest.Data.Source
import LeanVM.Compiler.Lines
import Statement.Keccak
import Statement.LeanVmVerifier

/-!
# `guest-artifact`: the guest the Rust prover loads

Run from `lean_vm`.

* `lake exe guest-artifact FILE` compiles the guest's source (`Data.guest`, its placeholders at
  `Data.bytecodeLog`) with `Compiler.compile` and writes `FILE`, the repository's
  `guests/lean_ethereum.compiled`: an `input` line, `Data.inputDigest`, the digest of the source
  and the placeholders it was compiled from; an `iv` line, the program's Fiat-Shamir IV
  (`fiatShamirIv` of its `bytecodeWords`, the statement's `deployedSeed`); then the program in the
  line format of `crates/isa/src/text.rs` (`Compiler.render`), and the source line of each
  instruction (`L` lines, `Compiler.renderLines`, from the line pass `Compiler.Lines.compileLines`).
  `crates/aggregation/src/guest.rs` loads it and checks both header lines against what it
  compiles and proves.
* `lake exe guest-artifact FILE --check` writes nothing and fails when `FILE` differs.

The guest is compiled at the fixed point on its own size: its placeholders are computed for a log
size, and the program must have that many slots. When it does not, nothing is written or checked,
the program's log size is printed as `log size N`, and the exit code is `3`;
`scripts/guest-artifact` then exports the source at that size and runs this again.
-/

open LeanVM LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Guest
  LeanVM.Compiler

namespace GuestArtifact

/-- Bytes as lowercase hexadecimal, two digits each. -/
def hex (bytes : List UInt8) : String :=
  let digit (n : Nat) : Char := "0123456789abcdef".toList.getD n '0'
  String.ofList (bytes.flatMap fun b => [digit (b.toNat / 16), digit (b.toNat % 16)])

/-- The Fiat-Shamir IV of the program of `2^logSize` slots holding `c`'s code, padded. -/
def iv (c : Assembled) (logSize : Nat) (h : logSize ≤ maxLogBytecode) : Digest :=
  let code : Array LeanIsaInstruction := Array.ofFn fun i : Fin (2 ^ logSize) ↦
    (c.code.getD i.val .padding).toLeanIsaInstruction
  fiatShamirIv (bytecodeWords ⟨logSize, h, fun i ↦ code[i.val]'(by simp [code])⟩)

def run (file : String) (checkOnly : Bool) : IO UInt32 := do
  let (c, lines) ← match Lines.compileLines Data.guest with
    | .ok r => pure r
    | .error e => throw (IO.userError s!"the guest does not compile: {e}")
  let logSize := c.size.log2
  if c.size != 2 ^ Data.bytecodeLog then
    IO.println s!"log size {logSize}"
    IO.eprintln s!"not at the fixed point: compiled with the placeholders at 2^{Data.bytecodeLog}, \
      the guest has {c.size} slots; export the source at {logSize} (`scripts/guest-artifact` does)"
    return 3
  if h : logSize > maxLogBytecode then
    throw (IO.userError s!"the guest's {c.size} slots exceed the ISA's")
  else
  let text := s!"input {Data.inputDigest}\niv {hex (iv c logSize (Nat.le_of_not_gt h)).toBytes.toList}\n" ++
    render c ++ renderLines lines
  if checkOnly then
    let current ← if ← System.FilePath.pathExists file then IO.FS.readFile file else pure ""
    if current == text then
      IO.println s!"{file} is current"
      return 0
    IO.eprintln s!"{file} is stale: run `scripts/guest-artifact`"
    return 1
  IO.FS.writeFile file text
  IO.println s!"{file}: {c.code.size} instructions in {c.fns.size} functions, size 2^{logSize}, \
    main frame {c.mainFrame}"
  return 0

end GuestArtifact

def main (args : List String) : IO UInt32 := do
  match args with
  | [file] => GuestArtifact.run file false
  | [file, "--check"] => GuestArtifact.run file true
  | _ =>
      IO.eprintln "usage: guest-artifact FILE [--check]"
      return 2
