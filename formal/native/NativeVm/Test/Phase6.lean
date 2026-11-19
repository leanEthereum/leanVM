import NativeVm.Test.Phase25
import NativeVm.Code.Phase6
import NativeVm.Model.Verify
import LeanVM.Cli.Common

/-!
# Phase 6's code against the model

From a verifier fixture, the model runs up to phase 6 (`readAnnouncedSizes`, `phase2M`,
`verifyBusBalance`, `tablePhase`, `publicInputPhase`); its transcript state, layout, the tables'
points and evaluations and the column claims are laid out as `CodeRel`, `LayoutAt`, `EvalsAt` and
`ClaimsAt` say, and `phase6` runs from there. `q_keccak`'s point and slices at `keccakR`
(`KeccakOutAt`), the claims appended at `claimsR` (`ClaimsAt`) and the transcript must be the
model's (`keccakPhase`); then again with the committed-outputs scalar and with one of the first
layer's product coefficients changed, which both reject.
-/

namespace NativeVm.Test.Phase6Test

open Native Native.Test NativeVm NativeVm.Transcript NativeVm.Model NativeVm.Code
open NativeVm.Test.TranscriptTest NativeVm.Test.Phase25Test
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Protocol.Compile

/-- The model's state before phase 6: the layout, the rate, the tables' evaluations, the column
claims so far. -/
def upTo5 (bc : Array UInt64) (pub : Vector UInt64 4) (stream : Array EW)
    (openings : Array (Array OpeningW)) :
    Option (LayoutW × Nat × Array (Array EW × Array EW) × Array ColumnClaimW × TState) := do
  let ((layout, rate), t1) ← (readAnnouncedSizes bc).run (Code.start ⟨0, bc, pub⟩ stream openings)
  let ((_ : StackClaimW), t2) ← (phase2M layout rate).run t1
  let (bus, t3) ← (verifyBusBalance layout).run t2
  let (ev, t4) ← (tablePhase layout bus).run t3
  let (pc, t5) ← (publicInputPhase layout pub).run t4
  pure (layout, rate, ev, bus.claims ++ tableColumnClaims ev ++ pc, t5)

/-- `EvalsAt`'s words. -/
def evalsImage (ev : Array (Array EW × Array EW)) : List (Nat × UInt64) :=
  (List.range nTables).flatMap fun t ↦
    let (point, values) := ev.getD t (#[], #[])
    vecW (evalsR.off + evalStride * t) point ++
      vecW (evalsR.off + evalStride * t + vecWords tablePointCap) values

/-- `KeccakOutAt`'s point and `kBits` slices. -/
def readKeccakOut (s : RState) : Array EW × Array EW :=
  (readVec s keccakR.off, (Array.range kBits).map fun i ↦
    let b := keccakR.off + vecWords pointCap + 2 * i
    ⟨s.word (wd workA b), s.word (wd workA (b + 1))⟩)

/-- Phase 6's run against `keccakPhase`: `ok true` when both accept with the same outputs,
`ok false` when both reject, an error describing the disagreement otherwise. -/
def check (L : Nat) (π : Proof) (pub : Vector UInt64 4) (layout : LayoutW) (rate : Nat)
    (ev : Array (Array EW × Array EW)) (acc : Array ColumnClaimW) (t : TState) :
    Except String Bool := do
  let s := startState L π pub t (layoutImage layout rate ++ evalsImage ev ++ claimsImage acc)
  let some (r, _) := Native.Test.run 1000000000 phase6 s
    | throw "the code runs out of fuel or faults"
  match (keccakPhase layout ev).run t, r with
  | none, .err _ => pure false
  | some _, .err _ => throw "model accepts, code rejects"
  | none, .ok _ => throw "model rejects, code accepts"
  | some ((outs, point, slices), t'), .ok s' =>
    let (point', slices') := readKeccakOut s'
    unless point' == point && slices' == slices do throw "KeccakOutAt differs"
    let cl := readClaims s'
    let want := acc ++ outs
    unless cl.size == want.size && (cl.zip want).all (fun (a, b) ↦ eqClaim a b) do
      throw "ClaimsAt differs"
    unless transcriptAgrees L s' t' do throw "the transcript differs"
    pure true

/-- The cursor once phase 6 has ground and sampled its segment and lane challenges, where the
committed-outputs scalar is. -/
def challengesCursor (t : TState) : Option Nat := do
  let pre : VM Unit := do
    Model.grind (Model.grindingBits (keccakSegmentBits + keccakLaneBits))
    let _ ← sampleChallenges keccakSegmentBits
    let _ ← sampleChallenges keccakLaneBits
  let ((), t') ← pre.run t
  pure t'.cursor

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
  let π : Proof := ⟨stream.toList.map EW.toE, phases.1⟩
  let L := 16 * stream.size + 5
  let name := dir.fileName.getD dir.toString
  let some (layout, rate, ev, acc, t5) := upTo5 bc pub stream openings
    | throw (IO.userError s!"{name}: the model rejects before phase 6")
  match check L π pub layout rate ev acc t5 with
  | .ok true => pure ()
  | .ok false => throw (IO.userError s!"{name}: phase 6 rejects the honest proof (model and code)")
  | .error e => throw (IO.userError s!"{name}: phase 6 disagrees ({e})")
  -- the committed-outputs scalar (when there is one), then the first layer's first product
  -- coefficient, changed
  let some c := challengesCursor t5
    | throw (IO.userError s!"{name}: the model rejects phase 6's challenges")
  let mutated := if 1 < keccakSegments then [c, c + 1] else [c]
  for i in mutated do
    let stream' := stream.modify i fun x ↦ { x with c0 := x.c0 ^^^ 1 }
    let π' : Proof := ⟨stream'.toList.map EW.toE, phases.1⟩
    match check L π' pub layout rate ev acc { t5 with stream := stream' } with
    | .ok false => pure ()
    | .ok true => throw (IO.userError s!"{name}: phase 6, scalar {i} changed: both accept")
    | .error e => throw (IO.userError s!"{name}: phase 6, scalar {i} changed: disagrees ({e})")
  IO.println s!"{name}: agree"

end NativeVm.Test.Phase6Test
