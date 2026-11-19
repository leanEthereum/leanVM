import NativeVm.Test.Phase25
import NativeVm.Code.Phase1

/-!
# Phase 1's code against the model

From a verifier fixture, the machine state after the seed (`Code.start`: the transcript at the
stream's start, the bytecode's length in its context word) runs `phase1`; it must end as
`readAnnouncedSizes` does: the layout's words (`layoutImage`, and the announced row counts at words
`10 ..`) and the transcript's (sponge, cursor) the model's when it accepts, a failure when it
rejects. Then the announced scalars mutated: the rate exponent out of range, a high limb set, the
memory's log-size `0` (all reject), and a row count changed (both accept, another layout).
-/

namespace NativeVm.Test.Phase1Test

open Native Native.Test NativeVm NativeVm.Transcript NativeVm.Model NativeVm.Code
open NativeVm.Test.TranscriptTest NativeVm.Test.Phase25Test
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile

/-- Phase 1's run against `readAnnouncedSizes`: `some true` when both accept with the same layout
and transcript, `some false` when both reject, `none` on a disagreement. -/
def check1 (L : Nat) (π : Proof) (bc : Array UInt64) (pub : Vector UInt64 4) (t : TState) :
    Option Bool := do
  let s0 := startState L π pub t []
  let s := { s0 with mem := s0.mem.insert (wd ctxA ctxBytecodeLen) bc.size.toUInt64 }
  let r ← Native.Test.run 1000000000 phase1 s
  match (readAnnouncedSizes bc).run t, r with
  | none, (.err _, _) => some false
  | some ((layout, rate), t'), (.ok s', _) =>
    let rows := (List.range nTables).map fun i ↦
      (layoutR.off + 10 + i, (t.stream.getD (t.cursor + 1 + i) 0).c0)
    let ok := (layoutImage layout rate ++ rows).all (fun (k, v) ↦ s'.word (wd workA k) == v) &&
      transcriptAgrees L s' t'
    if ok then some true else none
  | _, _ => none

def runDir (dir : System.FilePath) : IO Unit := do
  let bc := ((leWords (← IO.FS.readBinFile (dir / "bytecode.bin")) 8).map Nat.toUInt64).toArray
  let pubWords := (leWords (← IO.FS.readBinFile (dir / "public_input.bin")) 8).map Nat.toUInt64
  let pub : Vector UInt64 4 := Vector.ofFn fun i : Fin 4 ↦ pubWords.getD i 0
  let stream : Array EW := ((leWords (← IO.FS.readBinFile (dir / "stream.bin")) 8).toChunks 2 |>.map
    fun c ↦ (⟨(c.getD 0 0).toUInt64, (c.getD 1 0).toUInt64⟩ : EW)).toArray
  let some phases := LeanVM.Cli.readPhases (← IO.FS.readBinFile (dir / "merkle_phases.bin")) 0
    | throw (IO.userError s!"{dir}: merkle_phases.bin")
  let openings := phases.1.toArray.map fun ph ↦
    ph.toArray.map fun o ↦ (⟨o.leafIndex.toUInt64, o.leaf.toArray.map K.lane, o.path.toArray⟩ : OpeningW)
  let L := 16 * stream.size + 5
  let check := fun (stream : Array EW) ↦
    check1 L ⟨stream.toList.map EW.toE, phases.1⟩ bc pub (Code.start ⟨0, bc, pub⟩ stream openings)
  unless check stream == some true do throw (IO.userError s!"{dir}: phase 1")
  -- the rate exponent `9`, a high limb set, the memory's log-size `0`: rejected
  for (i, x, what) in [(7, (⟨9, 0⟩ : EW), "rate"), (3, ⟨(stream.getD 3 0).c0, 1⟩, "high limb"),
      (0, ⟨0, 0⟩, "log-memory")] do
    unless check (stream.set! i x) == some false do
      throw (IO.userError s!"{dir}: phase 1, {what} changed")
  -- another row count: accepted, another layout
  unless check (stream.modify 1 fun x ↦ { x with c0 := x.c0 + 1000 }) == some true do
    throw (IO.userError s!"{dir}: phase 1, a row count changed")
  IO.println s!"{dir.fileName.getD ""}: agree"

end NativeVm.Test.Phase1Test
