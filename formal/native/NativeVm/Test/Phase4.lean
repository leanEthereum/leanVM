import NativeVm.Test.Transcript
import NativeVm.Code.Phase4.Code
import NativeVm.Code.Contracts
import NativeVm.Model.Verify
import LeanVM.Cli.Common

/-!
# Phase 4's code against the model

From a verifier fixture, the model runs up to phase 4 (`readAnnouncedSizes`, `phase2M`,
`verifyBusBalance`); its transcript state, layout and bus result are laid out as `CodeRel`,
`LayoutAt` and `BusAt` say, and `P4.phase4Code` runs from there. Its outcome, the tables' points
and evaluations at `evalsR` (`EvalsAt`), the column claims appended at `claimsR` (`ClaimsAt`) and
the transcript's sponge and cursor must be the model's (`tablePhase`, `tableColumnClaims`); then
again with one of phase 4's stream elements changed, which both reject.
-/

namespace NativeVm.Test.Phase4Test

open Native Native.Test NativeVm NativeVm.Transcript NativeVm.Model NativeVm.Code NativeVm.Code.P4
open NativeVm.Test.TranscriptTest
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile

/-- The model up to phase 4: the layout, the bus's result, the transcript's state. -/
def upTo3 (bc : Array UInt64) (pub : Vector UInt64 4) (stream : Array EW)
    (openings : Array (Array OpeningW)) : Option (LayoutW × BusResultW × TState) := do
  let t0 := Code.start ⟨0, bc, pub⟩ stream openings
  let ((layout, rate), t1) ← (readAnnouncedSizes bc).run t0
  let ((_ : StackClaimW), t2) ← (phase2M layout rate).run t1
  let (bus, t3) ← (verifyBusBalance layout).run t2
  pure (layout, bus, t3)

/-- The sponge's context words. -/
def spongeWords (sp : SpongeW) : List (Nat × UInt64) :=
  let lane := fun i ↦ match sp.pending[i / 4]? with
    | some (x, tag) => if i % 4 = 0 then x.c0 else if i % 4 = 1 then x.c1 else if i % 4 = 2 then 0 else tag
    | none => 0
  (List.range 25).map (fun i ↦ (laneW + i, sp.state[i]!)) ++
    (List.range 16).map (fun i ↦ (rateW + i, lane i)) ++ [(countW, sp.pending.size.toUInt64)] ++
    match sp.ground with
    | none => [(groundW, 0)]
    | some c => [(groundW, 1), (groundW + 1, c.c0), (groundW + 2, c.c1)]

/-- An array of `E` from word `k`: the count, then the elements. -/
def vecW (k : Nat) (xs : Array EW) : List (Nat × UInt64) :=
  (k, xs.size.toUInt64) :: (xs.toList.zipIdx.flatMap fun (x, i) ↦ [(k + 1 + 2 * i, x.c0), (k + 2 + 2 * i, x.c1)])

/-- A form from word `k`. -/
def formW (k : Nat) (f : FormW) : List (Nat × UInt64) :=
  (k, f.size.toUInt64) :: (f.toList.zipIdx.flatMap fun (tm, i) ↦
    let b := k + 1 + termWords * i
    [(b, tm.cols.size.toUInt64)] ++ (tm.cols.toList.zipIdx.map fun (c, j) ↦ (b + 1 + j, c.toUInt64)) ++
      [(b + 3, tm.coeff.c0), (b + 4, tm.coeff.c1)])

/-- The working area's words phase 4 starts from. -/
def workImage (L : Nat) (layout : LayoutW) (bus : BusResultW) (t : TState) : List (Nat × UInt64) :=
  [(workCursor, t.cursor.toUInt64), (workPhase, t.phase.toUInt64),
    (workPhasePtr, wd decA (phaseBase L t.phase)), (workPhaseCount, t.openings.size.toUInt64),
    (workRootCount, t.roots.size.toUInt64)] ++
  (t.roots.toList.zipIdx.flatMap fun (r, j) ↦
    (List.range 4).map (fun k ↦ (workRoots + rootStride * j + k, r.digest[k]!)) ++
      [(workRoots + rootStride * j + 4, r.height.toUInt64),
        (workRoots + rootStride * j + 5, r.width.toUInt64)]) ++
  ((List.range nTables).map fun i ↦ (layoutR.off + 4 + i, (layout.tableLogHeights.getD i 0).toUInt64)) ++
  ((List.range nTables).flatMap fun tb ↦ (List.range 3).flatMap fun side ↦
    formW (busR.off + formOff tb side) ((bus.forms.getD tb #[]).getD side #[])) ++
  vecW (busR.off + busPointOff) bus.point ++
  (bus.totals.toList.zipIdx.flatMap fun (x, i) ↦
    [(busR.off + busTotalsOff + 2 * i, x.c0), (busR.off + busTotalsOff + 2 * i + 1, x.c1)]) ++
  [(claimsR.off, bus.claims.size.toUInt64)] ++
  (bus.claims.toList.zipIdx.flatMap fun (c, i) ↦
    let b := claimsR.off + 1 + claimWords * i
    [(b, c.column.toUInt64)] ++ vecW (b + 1) c.point ++
      [(b + 1 + vecWords pointCap, c.value.c0), (b + 2 + vecWords pointCap, c.value.c1)])

/-- The machine state before phase 4. -/
def startState (L : Nat) (π : Proof) (layout : LayoutW) (bus : BusResultW) (t : TState) : RState :=
  let ctxWords : List (Nat × UInt64) := (List.range ctxEnd).map fun k ↦
    (k, if k = ctxDecoded then decA else if k = ctxWork then workA else 0)
  RState.ofWords ctxA <|
    (ctxWords ++ spongeWords t.sponge).map (fun (k, v) ↦ (wd ctxA k, v)) ++
    (decodedImage L π).map (fun (k, v) ↦ (wd decA k, v)) ++
    (List.range dataEnd).map (fun k ↦ (wd workA k, 0)) ++
    (workImage L layout bus t).map fun (k, v) ↦ (wd workA k, v)

/-- The words of an array of `E` from word `k` of the working area. -/
def readVec (s : RState) (k : Nat) : Array EW :=
  let n := (s.word (wd workA k)).toNat
  (Array.range n).map fun i ↦ ⟨s.word (wd workA (k + 1 + 2 * i)), s.word (wd workA (k + 2 + 2 * i))⟩

/-- The tables' points and evaluations at `evalsR`. -/
def readEvals (s : RState) : Array (Array EW × Array EW) :=
  (Array.range nTables).map fun t ↦
    (readVec s (evalsR.off + evalStride * t), readVec s (evalsR.off + evalStride * t + evOff))

/-- The column claims at `claimsR`. -/
def readClaims (s : RState) : Array ColumnClaimW :=
  let n := (s.word (wd workA claimsR.off)).toNat
  (Array.range n).map fun i ↦
    let b := claimsR.off + 1 + claimWords * i
    ⟨(s.word (wd workA b)).toNat, readVec s (b + 1),
      ⟨s.word (wd workA (b + 1 + vecWords pointCap)), s.word (wd workA (b + 2 + vecWords pointCap))⟩⟩

def eqClaim (a b : ColumnClaimW) : Bool := a.column == b.column && a.point == b.point && a.value == b.value

/-- The sponge's words after the run, as the model's state would put them. -/
def spongeAgrees (s : RState) (sp : SpongeW) : Bool :=
  (spongeWords sp).all fun (k, v) ↦ s.word (wd ctxA k) == v

/-- The code's run against the model's from the state after phase 3: `some true` when both accept
with the same outputs, `some false` when both reject, `none` on a disagreement. -/
def check (L : Nat) (π : Proof) (layout : LayoutW) (bus : BusResultW) (t : TState) : Option Bool := do
  let s := startState L π layout bus t
  let r ← Native.Test.run 1000000000 phase4Code s
  match (tablePhase layout bus).run t, r with
  | none, (.err _, _) => some false
  | some (ev, t'), (.ok s', _) =>
    let evOk := readEvals s' == ev
    let cl := readClaims s'
    let want := bus.claims ++ tableColumnClaims ev
    let clOk := cl.size == want.size && (cl.zip want).all fun (a, b) ↦ eqClaim a b
    let tOk := spongeAgrees s' t'.sponge && s'.word (wd workA workCursor) == t'.cursor.toUInt64
    if evOk && clOk && tOk then some true else none
  | _, _ => none

/-- Little-endian words of `n` bytes each. -/
def leWords (b : ByteArray) (n : Nat) : List Nat :=
  (List.range (b.size / n)).map fun i ↦
    (List.range n).foldr (fun k acc ↦ acc * 256 + (b.get! (n * i + k)).toNat) 0

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
  let some (layout, bus, t) := upTo3 bc pub stream openings
    | throw (IO.userError s!"{dir}: the model rejects before phase 4")
  unless check L π layout bus t == some true do throw (IO.userError s!"{dir}: honest run")
  -- one of phase 4's scalars changed: a sumcheck coefficient, then an evaluation
  for k in [1, 3 * layout.tableLogHeights.foldl max 0 + 5] do
    let i := t.cursor + k
    let stream' := stream.modify i fun x ↦ { x with c0 := x.c0 ^^^ 1 }
    let π' : Proof := ⟨stream'.toList.map EW.toE, phases.1⟩
    let t' := { t with stream := stream' }
    unless check L π' layout bus t' == some false do
      throw (IO.userError s!"{dir}: scalar {i} changed")
  IO.println s!"{dir.fileName.getD ""}: agree"

end NativeVm.Test.Phase4Test
