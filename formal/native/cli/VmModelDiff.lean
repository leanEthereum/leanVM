module

import NativeVm.Model.Verify
import LeanVM.Cli.Common

/-!
# `vm-model-diff`

`lake exe vm-model-diff [--random N] DIR...`: for each verifier fixture directory (the files
`formal/lean_vm/scripts/export-verifier-fixtures-rust.sh` writes: `bytecode.bin`,
`public_input.bin`, `stream.bin`, `merkle_phases.bin`), runs the word model
`NativeVm.Model.verify` and the statement's verifier `verifyWith (m := Id) keccakF1600` on the
proof and on mutations of it (a stream element flipped, at fixed and at `N` pseudo-random
positions; the stream truncated or extended; a leaf word, a sibling digest or a leaf index flipped
in each phase; an opening or a phase dropped), and reports per directory how many verdicts agree
and how many each accepts. The exit code is `0` when every verdict agrees and every honest proof
is accepted.
-/

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakHash
open NativeVm.Model

namespace VmModelDiff

/-- The little-endian word at a byte offset. -/
def laneAt (b : ByteArray) (o : Nat) : UInt64 :=
  (List.range 8).foldr (fun k acc ↦ (acc <<< 8) ||| (b.get! (o + k)).toUInt64) 0

/-- `bytecode.bin`: the bytecode's words. -/
def readWords (b : ByteArray) : Option (Array UInt64) :=
  if b.size % 8 = 0 then some ((Array.range (b.size / 8)).map fun i ↦ laneAt b (8 * i)) else none

/-- `public_input.bin`: four words. -/
def readDigest (b : ByteArray) : Option (Vector UInt64 4) :=
  if b.size = 32 then some #v[laneAt b 0, laneAt b 8, laneAt b 16, laneAt b 24] else none

/-- `stream.bin`: the scalars, two little-endian limbs each. -/
def readStream (b : ByteArray) : Option (Array EW) :=
  if b.size % 16 = 0 then
    some ((Array.range (b.size / 16)).map fun i ↦ ⟨laneAt b (16 * i), laneAt b (16 * i + 8)⟩)
  else none

/-- `merkle_phases.bin` (`LeanVM.Cli.readPhases`), the whole file. -/
def readPhasesFile (b : ByteArray) : Option (List (List Opening)) := do
  let (phases, pos) ← LeanVM.Cli.readPhases b 0
  if pos = b.size then some phases else none

/-- A proof with its statement. -/
structure Case where
  bytecode : Array UInt64
  publicInput : Vector UInt64 4
  stream : Array EW
  phases : List (List Opening)

/-- The statement's verifier on the structured proof. -/
def specVerdict (c : Case) : Bool :=
  Id.run (verifyWith (m := Id) keccakF1600 (c.bytecode.toList.map K.ofLane) c.publicInput
    ⟨c.stream.toList.map EW.toE, c.phases⟩)

/-- The word model on the decoded proof. -/
def modelVerdict (c : Case) : Bool :=
  verify c.bytecode c.publicInput c.stream (c.phases.toArray.map fun phase ↦
    phase.toArray.map fun o ↦ ⟨o.leafIndex.toUInt64, o.leaf.toArray.map K.lane, o.path.toArray⟩)

/-! ## Mutations -/

/-- Flip bit `0` of limb `0` of stream element `i`. -/
def flipStream (c : Case) (i : Nat) : Case :=
  { c with stream := c.stream.modify i fun x ↦ { x with c0 := x.c0 ^^^ 1 } }

/-- Change opening `j` of phase `k`. -/
def modifyOpening (c : Case) (k j : Nat) (f : Opening → Opening) : Case :=
  { c with phases := c.phases.modify k fun phase ↦ phase.modify j f }

/-- Flip the first leaf word of opening `j` of phase `k`. -/
def flipLeaf (c : Case) (k j : Nat) : Case :=
  modifyOpening c k j fun o ↦ { o with leaf := o.leaf.modify 0 fun w ↦ w + 1 }

/-- Flip the first word of the last sibling of opening `j` of phase `k`. -/
def flipPath (c : Case) (k j : Nat) : Case :=
  modifyOpening c k j fun o ↦
    { o with path := o.path.modify (o.path.length - 1) fun d ↦ d.set 0 (d[0] ^^^ 1) }

/-- Flip the leaf index of opening `j` of phase `k`. -/
def flipIndex (c : Case) (k j : Nat) : Case :=
  modifyOpening c k j fun o ↦ { o with leafIndex := o.leafIndex ^^^ 1 }

/-- A pseudo-random sequence (a linear congruential generator). -/
def lcg (seed : Nat) : Nat := (seed * 6364136223846793005 + 1442695040888963407) % 2 ^ 64

/-- The mutations of a case, each named. -/
def mutations (c : Case) (random seed : Nat) : List (String × Case) :=
  let n := c.stream.size
  let fixed := [0, 1, 2, 7, 8, 9, 10, 11, 12, n / 4, n / 2, 3 * n / 4, n - 2, n - 1].filter (· < n)
  let randoms := ((List.range random).foldl (fun (acc : List Nat × Nat) _ ↦
    let s := lcg acc.2
    (acc.1 ++ [(s >>> 11) % n], s)) ([], seed)).1
  let streamFlips := (fixed ++ randoms).map fun i ↦ (s!"stream[{i}]", flipStream c i)
  let phaseCases := (List.range c.phases.length).flatMap fun k ↦
    let q := (c.phases.getD k []).length
    [(s!"leaf[{k}][0]", flipLeaf c k 0), (s!"leaf[{k}][{q - 1}]", flipLeaf c k (q - 1)),
      (s!"path[{k}][0]", flipPath c k 0), (s!"path[{k}][{q / 2}]", flipPath c k (q / 2)),
      (s!"index[{k}][0]", flipIndex c k 0),
      (s!"drop-opening[{k}]", { c with phases := c.phases.modify k List.dropLast }),
      (s!"drop-phase[{k}]", { c with phases := c.phases.eraseIdx k })]
  streamFlips ++
    [("truncate-1", { c with stream := c.stream.pop }),
      ("truncate-half", { c with stream := c.stream.extract 0 (n / 2) }),
      ("extend", { c with stream := c.stream.push 0 })] ++
    phaseCases

/-- Read a fixture directory. -/
def readCase (dir : String) : IO Case := do
  let file := fun (name : String) ↦ IO.FS.readBinFile (dir ++ "/" ++ name)
  match readWords (← file "bytecode.bin"), readDigest (← file "public_input.bin"),
      readStream (← file "stream.bin"), readPhasesFile (← file "merkle_phases.bin") with
  | some bytecode, some publicInput, some stream, some phases =>
    pure ⟨bytecode, publicInput, stream, phases⟩
  | _, _, _, _ => throw (IO.userError s!"{dir}: a file does not decode")

end VmModelDiff

open VmModelDiff in
/-- The driver. -/
public def main (args : List String) : IO UInt32 := do
  let (random, dirs) := match args with
    | "--random" :: n :: rest => (n.toNat!, rest)
    | rest => (16, rest)
  if dirs.isEmpty then
    IO.eprintln "usage: vm-model-diff [--random N] DIR..."
    return 2
  let mut ok := true
  let mut totalAgree := 0
  let mut total := 0
  for (dir, index) in dirs.zipIdx do
    let c ← readCase dir
    let honestSpec := specVerdict c
    let honestModel := modelVerdict c
    let mut agree := if honestSpec == honestModel then 1 else 0
    let mut count := 1
    let mut specAccepts := if honestSpec then 1 else 0
    let mut modelAccepts := if honestModel then 1 else 0
    let mut disagreements : Array String := #[]
    if honestSpec != honestModel then disagreements := disagreements.push "honest"
    for (name, m) in mutations c random (index + 1) do
      let s := specVerdict m
      let v := modelVerdict m
      count := count + 1
      if s == v then agree := agree + 1 else disagreements := disagreements.push name
      if s then specAccepts := specAccepts + 1
      if v then modelAccepts := modelAccepts + 1
    IO.println s!"{dir}: honest spec={honestSpec} model={honestModel}; agree {agree}/{count}; \
      accepted spec {specAccepts}, model {modelAccepts}\
      {if disagreements.isEmpty then "" else s!"; disagree on {disagreements}"}"
    totalAgree := totalAgree + agree
    total := total + count
    ok := ok && agree == count && honestSpec && honestModel
  IO.println s!"total: agree {totalAgree}/{total}"
  return if ok then 0 else 1
