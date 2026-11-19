import NativeVm.Test.Phase6
import NativeVm.Code.Phase7
import NativeVm.Model.Verify
import LeanVM.Cli.Common

/-!
# Phase 7's code against the model

From a verifier fixture, the model runs up to phase 7 (`readAnnouncedSizes`, `phase2M`,
`verifyBusBalance`, `tablePhase`, `publicInputPhase`, `keccakPhase`); its transcript state, layout,
out-of-domain claim, column claims and `q_keccak`'s point and slices are laid out as `CodeRel`,
`LayoutAt`, `EqClaimAt`, `ClaimsAt` and `KeccakOutAt` say, and `phase7` runs from there. Both must
accept with the model's transcript (`phase7M`), or both reject; then again with a path digest of
phase 7's first opening changed and with the last stream scalar phase 7 reads changed, which both
reject.
-/

namespace NativeVm.Test.Phase7Test

open Native Native.Test NativeVm NativeVm.Transcript NativeVm.Model NativeVm.Code
open NativeVm.Test.TranscriptTest NativeVm.Test.Phase25Test NativeVm.Test.Phase6Test
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Protocol.Compile

/-- Phase 7's arguments and the model's state before it. -/
structure Pre where
  layout : LayoutW
  rate : Nat
  ood : StackClaimW
  claims : Array ColumnClaimW
  point : Array EW
  slices : Array EW
  t : TState

/-- The model's state before phase 7 (`verifyExecution_eq`). -/
def upTo6 (bc : Array UInt64) (pub : Vector UInt64 4) (stream : Array EW)
    (openings : Array (Array OpeningW)) : Option Pre := do
  let ((layout, rate), t1) ← (readAnnouncedSizes bc).run (Code.start ⟨0, bc, pub⟩ stream openings)
  let (ood, t2) ← (phase2M layout rate).run t1
  let (bus, t3) ← (verifyBusBalance layout).run t2
  let (ev, t4) ← (tablePhase layout bus).run t3
  let (pc, t5) ← (publicInputPhase layout pub).run t4
  let ((outs, point, slices), t6) ← (keccakPhase layout ev).run t5
  pure ⟨layout, rate, ood, bus.claims ++ tableColumnClaims ev ++ pc ++ outs, point, slices, t6⟩

/-- `LayoutAt`'s row counts: the announced ones, the stream's scalars `1 .. nTables`. -/
def rowsImage (stream : Array EW) : List (Nat × UInt64) :=
  (List.range nTables).map fun i ↦ (layoutR.off + 10 + i, (stream.getD (1 + i) ⟨0, 0⟩).c0)

/-- `EqClaimAt`'s words. -/
def oodImage (ood : StackClaimW) : Except String (List (Nat × UInt64)) :=
  match ood.weight with
  | .eq z => pure (vecW oodR.off z ++
      [(oodR.off + vecWords stackCap, ood.value.c0), (oodR.off + vecWords stackCap + 1, ood.value.c1)])
  | _ => throw "phase 2's claim is not an equality claim"

/-- `KeccakOutAt`'s words. -/
def keccakImage (point slices : Array EW) : List (Nat × UInt64) :=
  vecW keccakR.off point ++ (slices.toList.zipIdx.flatMap fun (x, i) ↦
    [(keccakR.off + vecWords pointCap + 2 * i, x.c0), (keccakR.off + vecWords pointCap + 2 * i + 1, x.c1)])

/-- Phase 7's run against `phase7M`: `ok (some t')` when both accept, the machine's transcript the
model's `t'`; `ok none` when both reject; an error describing the disagreement otherwise. -/
def check (L : Nat) (π : Proof) (pub : Vector UInt64 4) (stream : Array EW) (p : Pre) :
    Except String (Option TState) := do
  let s := startState L π pub p.t (layoutImage p.layout p.rate ++ rowsImage stream ++
    (← oodImage p.ood) ++ claimsImage p.claims ++ keccakImage p.point p.slices)
  let some (r, _) := Native.Test.run 1000000000000 phase7 s
    | throw "the code runs out of fuel or faults"
  match (phase7M p.layout p.rate p.ood p.claims p.point p.slices).run p.t, r with
  | none, .err _ => pure none
  | some _, .err _ => throw "model accepts, code rejects"
  | none, .ok _ => throw "model rejects, code accepts"
  | some ((), t'), .ok s' =>
    unless transcriptAgrees L s' t' do
      let bad := (spongeWords t'.sponge).filter (fun (k, v) ↦ s'.word (wd ctxA k) != v)
      let bad' := (transcriptImage L t').filter (fun (k, v) ↦ s'.word (wd workA k) != v)
      throw s!"the transcript differs: context words {bad.map (·.1)}, working words \
        {bad'.map fun (k, v) ↦ (k, v, s'.word (wd workA k))}"
    pure (some t')

/-- The openings' words of the decoded phases. -/
def openingsOf (phases : List (List Opening)) : Array (Array OpeningW) :=
  phases.toArray.map fun ph ↦
    ph.toArray.map fun o ↦ (⟨o.leafIndex.toUInt64, o.leaf.toArray.map K.lane, o.path.toArray⟩ : OpeningW)

def runDir (dir : System.FilePath) : IO Unit := do
  let bc := ((leWords (← IO.FS.readBinFile (dir / "bytecode.bin")) 8).map Nat.toUInt64).toArray
  let pubWords := (leWords (← IO.FS.readBinFile (dir / "public_input.bin")) 8).map Nat.toUInt64
  let pub : Vector UInt64 4 := Vector.ofFn fun i : Fin 4 ↦ pubWords.getD i 0
  let stream : Array EW := ((leWords (← IO.FS.readBinFile (dir / "stream.bin")) 8).toChunks 2 |>.map
    fun c ↦ (⟨(c.getD 0 0).toUInt64, (c.getD 1 0).toUInt64⟩ : EW)).toArray
  let some phases := LeanVM.Cli.readPhases (← IO.FS.readBinFile (dir / "merkle_phases.bin")) 0
    | throw (IO.userError s!"{dir}: merkle_phases.bin")
  let openings := openingsOf phases.1
  let π : Proof := ⟨stream.toList.map EW.toE, phases.1⟩
  let L := 16 * stream.size + 5
  let name := dir.fileName.getD dir.toString
  let some p := upTo6 bc pub stream openings
    | throw (IO.userError s!"{name}: the model rejects before phase 7")
  let t7 ← match check L π pub stream p with
    | .ok (some t7) => pure t7
    | .ok none => throw (IO.userError s!"{name}: phase 7 rejects the honest proof (model and code)")
    | .error e => throw (IO.userError s!"{name}: phase 7 disagrees ({e})")
  -- the first path digest of phase 7's first opening changed
  let phases' := phases.1.zipIdx.map fun (ph, j) ↦
    if j = p.t.phase then
      ph.zipIdx.map fun (o, k) ↦
        if k = 0 then
          { o with path := o.path.zipIdx.map fun (d, m) ↦
              if m = 0 then Vector.ofFn fun i ↦ if i.val = 0 then d[i] ^^^ 1 else d[i] else d }
        else o
    else ph
  unless ((phases.1[p.t.phase]?.bind (·.head?)).map (·.path.length)).getD 0 > 0 do
    throw (IO.userError s!"{name}: phase 7's first opening has no path")
  let π' : Proof := ⟨stream.toList.map EW.toE, phases'⟩
  match check L π' pub stream { p with t := { p.t with openings := openingsOf phases' } } with
  | .ok none => pure ()
  | .ok (some _) => throw (IO.userError s!"{name}: phase 7, a path digest changed: both accept")
  | .error e => throw (IO.userError s!"{name}: phase 7, a path digest changed: disagrees ({e})")
  -- the last stream scalar phase 7 reads changed
  unless p.t.cursor < t7.cursor do throw (IO.userError s!"{name}: phase 7 reads no scalar")
  let i := t7.cursor - 1
  let stream' := stream.modify i fun x ↦ { x with c0 := x.c0 ^^^ 1 }
  let π' : Proof := ⟨stream'.toList.map EW.toE, phases.1⟩
  match check L π' pub stream' { p with t := { p.t with stream := stream' } } with
  | .ok none => pure ()
  | .ok (some _) => throw (IO.userError s!"{name}: phase 7, scalar {i} changed: both accept")
  | .error e => throw (IO.userError s!"{name}: phase 7, scalar {i} changed: disagrees ({e})")
  IO.println s!"{name}: agree"

end NativeVm.Test.Phase7Test
