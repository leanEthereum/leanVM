import NativeVm.Test.Transcript
import LeanVM.Cli.Common

/-!
# `vm-transcript-test`: the transcript's gadgets on the verifier fixtures

For each fixture directory (`scripts/export-verifier-fixtures-rust.sh`) under the given directory
(default `$LEANVM_FIXTURES`, then `/tmp/vmfix`): the seed against `spongeSeedWith`; the announced
sizes read, two challenges sampled and a scalar read; the stack's root read and its first phase
opened at the fixture's positions, and at positions with one changed (rejected), each against the
statement's `run` (`NativeVm.Test.TranscriptTest`). `--no-queries` skips the openings.
-/

namespace NativeVm.Test.TranscriptTest

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile

/-- Little-endian words of `n` bytes each. -/
def leWords (b : ByteArray) (n : Nat) : List Nat :=
  (List.range (b.size / n)).map fun i ↦
    (List.range n).foldr (fun k acc ↦ acc * 256 + (b.get! (n * i + k)).toNat) 0

/-- A fixture's bytecode, public input and structured proof. -/
def readFixture (dir : System.FilePath) : IO (List K × Digest × Proof) := do
  let bc := (leWords (← IO.FS.readBinFile (dir / "bytecode.bin")) 8).map fun w ↦ K.ofLane w.toUInt64
  let pubWords := (leWords (← IO.FS.readBinFile (dir / "public_input.bin")) 8).map Nat.toUInt64
  let stream := (leWords (← IO.FS.readBinFile (dir / "stream.bin")) 8).toChunks 2 |>.map fun c ↦
    E.ofLimbs (K.ofLane (c.getD 0 0).toUInt64) (K.ofLane (c.getD 1 0).toUInt64)
  let some phases := LeanVM.Cli.readPhases (← IO.FS.readBinFile (dir / "merkle_phases.bin")) 0
    | throw (IO.userError s!"{dir}: merkle_phases.bin")
  return (bc, Vector.ofFn fun i : Fin 4 ↦ pubWords.getD i 0, ⟨stream, phases.1⟩)

/-- The fixtures' directory. -/
def fixtureDir : IO System.FilePath := do
  return (← IO.getEnv "LEANVM_FIXTURES").getD "/tmp/vmfix"

/-- The announced sizes, the stack's root and its first phase opened (the fixture's own positions),
or the same with a position changed, which must reject. -/
def fixturePrograms (π : Proof) : List (List Op) :=
  let phase := π.openings.headD []
  let h := (phase.head?.map (·.path.length)).getD 0
  let w := (phase.head?.map (·.leaf.length)).getD 0
  let ps := phase.map (·.leafIndex)
  [List.replicate 8 .read ++ [.sample, .sample, .read],
    List.replicate 8 .read ++ [.commit h w, .query 0 ps],
    List.replicate 8 .read ++ [.commit h w, .query 0 (ps.modifyHead (· ^^^ 1))]]

def run (dir : System.FilePath) (queries : Bool) : IO Unit := do
  let names := (← dir.readDir).map (·.fileName) |>.qsort (· < ·)
  for name in names do
    let (bc, pub, π) ← readFixture (dir / name)
    let L := 16 * π.stream.length + 5
    unless seedAgrees L bc pub π do throw (IO.userError s!"{name}: seed")
    let p := fixturePrograms π
    unless agree L bc pub π p[0]! do throw (IO.userError s!"{name}: reads and samples")
    if queries then
      unless agree L bc pub π p[1]! && (specRun bc pub π p[1]!).isSome do
        throw (IO.userError s!"{name}: commit and query")
      unless agree L bc pub π p[2]! && (specRun bc pub π p[2]!).isNone do
        throw (IO.userError s!"{name}: a wrong position")
    IO.println s!"{name}: agree"



end NativeVm.Test.TranscriptTest

def main (args : List String) : IO UInt32 := do
  let queries := !args.contains "--no-queries"
  let dir ← match args.filter (· != "--no-queries") with
    | [d] => pure (System.FilePath.mk d)
    | _ => NativeVm.Test.TranscriptTest.fixtureDir
  NativeVm.Test.TranscriptTest.run dir queries
  return 0
