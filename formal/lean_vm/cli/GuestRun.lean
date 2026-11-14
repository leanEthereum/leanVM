import LeanVM.Guest.Executor
import LeanVM.Cli.GuestCase
import Statement.Prover.Prove
import LeanVM.Prover.Fast.Prover
import LeanVM.Facts.Verifier

/-!
# `guest-run`: the guest's prover in Lean, from a node's statement and witness

`lake exe guest-run [--rust DIR] [--prove] <case>...` reads cases written by the exporter's test
`guest_diff` (`scripts/guest-export`, format `leanvm-guest-diff 4`: a real aggregation's seed,
statement and witness) and, from the statement and the witness alone,

* runs the guest (`LeanVM.Guest.guestExecution`: the honest streams, the compiler's hints, the
  statement's executor);
* with `--rust DIR`, compares the execution with the Rust interpreter's, `DIR/<case>/memory.bin`
  and `trace.txt` (`LEANVM_GUEST_EXEC=DIR` on the exporter writes them): the memory's size, every
  cell and the step count;
* with `--prove`, proves it with the statement's honest prover (`LeanVM.Prover.prove`, compiled as
  `leanvm-prove` runs it, at inverse rate `2`) and verifies the proof with the deployed verifier
  (`Verifier.verify`) on the guest's bytecode and the statement's digest.

It prints each stage's time and exits with `1` if a stage fails or differs.
-/

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Node LeanVM.Guest LeanVM.Cli.GuestCase

namespace GuestRun

def timed {α : Type} (f : Unit → α) : IO (α × Float) := do
  let start ← IO.monoMsNow
  let a := f ()
  return (a, ((← IO.monoMsNow) - start).toFloat / 1000)

/-- The first cell where the execution differs from the Rust's in `dir`, or a size or step mismatch. -/
def compare (t : Execution guestProgram) (dir : String) : IO (Option String) := do
  let read := fun (p : String) => do return (← IO.FS.readBinFile (dir ++ "/" ++ p)).toList
  let some mem := decodeScalars (← read "memory.bin") | return some "bad memory.bin"
  let mem := mem.toArray
  let nums := ((← IO.FS.readFile (dir ++ "/trace.txt")).trimAscii.toString.splitOn " ").filterMap
    String.toNat?
  let [κ, steps, _] := nums | return some "bad trace.txt"
  if h : t.logMemorySize = κ then
    if t.stepCount ≠ steps then return some s!"{t.stepCount} steps, Rust {steps}"
    for h' : i in [0:2 ^ κ] do
      if t.memory ⟨i, h ▸ h'.upper⟩ ≠ mem.getD i 0 then return some s!"cell {i} differs"
    return none
  else return some s!"2^{t.logMemorySize} cells, Rust 2^{κ}"

def main (args : List String) : IO UInt32 := do
  let rec parse : List String → Option String → Bool → List String → Option (Option String × Bool × List String)
    | "--rust" :: d :: rest, _, p, cs => parse rest (some d) p cs
    | "--prove" :: rest, r, _, cs => parse rest r true cs
    | c :: rest, r, p, cs => if c.startsWith "--" then none else parse rest r p (cs ++ [c])
    | [], r, p, cs => some (r, p, cs)
  let some (rust, prove, cases) := parse args none false [] | do
    IO.eprintln "usage: guest-run [--rust DIR] [--prove] <case>..."; return 2
  if cases.isEmpty then IO.eprintln "usage: guest-run [--rust DIR] [--prove] <case>..."; return 2
  let mut ok := true
  for path in cases do
    let c ← readCase path
    let digest := statementDigest c.seed c.statement
    let (r, time) ← timed fun _ => guestExecution c.seed c.statement c.witness
    match r with
    | .error e =>
      IO.println s!"{c.name}: FAIL: {e} ({time} s)"
      ok := false
    | .ok t =>
      IO.println s!"{c.name}: executed, {t.stepCount} steps, 2^{t.logMemorySize} cells ({time} s)"
      if let some dir := rust then
        match ← compare t (dir ++ "/" ++ c.name) with
        | none => IO.println s!"  as the Rust interpreter's: ok"
        | some d => IO.println s!"  as the Rust interpreter's: DIFFERS: {d}"; ok := false
      if prove then
        let (π, time) ← timed fun _ =>
          LeanVM.Prover.prove (m := Id) keccakF1600 guestProgram (End.publicInputOf digest) t 2 (2 ^ 64)
        match π with
        | none => IO.println s!"  proved: FAIL, no proof ({time} s)"; ok := false
        | some π =>
          IO.println s!"  proved: {π.stream.length} scalars ({time} s)"
          let (v, time) ← timed fun _ => Verifier.verify (LeanVM.bytecodeWords guestProgram) digest π
          IO.println s!"  verified: {if v then "accepted" else "REJECTED"} ({time} s)"
          ok := ok && v
    (← IO.getStdout).flush
  return if ok then 0 else 1

end GuestRun

def main (args : List String) : IO UInt32 := GuestRun.main args
