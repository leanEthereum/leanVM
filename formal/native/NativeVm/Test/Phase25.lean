import NativeVm.Test.Transcript
import NativeVm.Code.Phase2
import NativeVm.Code.Phase5
import NativeVm.Model.Verify
import LeanVM.Cli.Common

/-!
# Phases 2 and 5's code against the model

From a verifier fixture, the model runs up to phase 2 (`readAnnouncedSizes`) and up to phase 5
(`phase2M`, `verifyBusBalance`, `tablePhase`); its transcript state, layout and column claims are
laid out as `CodeRel`, `LayoutAt` and `ClaimsAt` say, and `phase2` and `phase5` run from there.
Phase 2's out-of-domain claim at `oodR` (`EqClaimAt`), the roots and the transcript's sponge and
cursor must be the model's (`phase2M`); phase 5's claims appended at `claimsR` (`ClaimsAt`) and the
sponge the model's (`publicInputPhase`). Then phase 2 with its grind's nonce changed (both reject)
and with its value changed (both accept, the value the new one), and phase 5 with another public
input.
-/

namespace NativeVm.Test.Phase25Test

open Native Native.Test NativeVm NativeVm.Transcript NativeVm.Model NativeVm.Code
open NativeVm.Test.TranscriptTest
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile

/-! ## The model -/

/-- The model's state before phase 2, with the layout and the rate. -/
def upTo1 (bc : Array UInt64) (pub : Vector UInt64 4) (stream : Array EW)
    (openings : Array (Array OpeningW)) : Option (LayoutW × Nat × TState) := do
  let ((layout, rate), t1) ← (readAnnouncedSizes bc).run (Code.start ⟨0, bc, pub⟩ stream openings)
  pure (layout, rate, t1)

/-- The model's state before phase 5, with the column claims so far. -/
def upTo4 (bc : Array UInt64) (pub : Vector UInt64 4) (stream : Array EW)
    (openings : Array (Array OpeningW)) :
    Option (LayoutW × Nat × Array ColumnClaimW × TState) := do
  let (layout, rate, t1) ← upTo1 bc pub stream openings
  let ((_ : StackClaimW), t2) ← (phase2M layout rate).run t1
  let (bus, t3) ← (verifyBusBalance layout).run t2
  let (ev, t4) ← (tablePhase layout bus).run t3
  pure (layout, rate, bus.claims ++ tableColumnClaims ev, t4)

/-! ## The memory -/

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
  (k, xs.size.toUInt64) ::
    (xs.toList.zipIdx.flatMap fun (x, i) ↦ [(k + 1 + 2 * i, x.c0), (k + 2 + 2 * i, x.c1)])

/-- The transcript's words of the working area. -/
def transcriptImage (L : Nat) (t : TState) : List (Nat × UInt64) :=
  [(workCursor, t.cursor.toUInt64), (workPhase, t.phase.toUInt64),
    (workPhasePtr, wd decA (phaseBase L t.phase)), (workPhaseCount, t.openings.size.toUInt64),
    (workRootCount, t.roots.size.toUInt64)] ++
  (t.roots.toList.zipIdx.flatMap fun (r, j) ↦
    (List.range 4).map (fun k ↦ (workRoots + rootStride * j + k, r.digest[k]!)) ++
      [(workRoots + rootStride * j + 4, r.height.toUInt64),
        (workRoots + rootStride * j + 5, r.width.toUInt64)])

/-- `LayoutAt`'s words (the row counts, which neither phase reads, left zero). -/
def layoutImage (layout : LayoutW) (rate : Nat) : List (Nat × UInt64) :=
  let o := layoutR.off
  [(o, layout.logMemory.toUInt64), (o + 1, layout.logBytecode.toUInt64),
    (o + 2, layout.stackLog.toUInt64), (o + 3, rate.toUInt64)] ++
  ((List.range nTables).map fun i ↦ (o + 4 + i, (layout.tableLogHeights.getD i 0).toUInt64)) ++
  ((List.range columnCount).flatMap fun c ↦
    match layout.placements.getD c none with
    | none => [(o + 16 + 3 * c, 0)]
    | some pl => [(o + 16 + 3 * c, 1), (o + 17 + 3 * c, pl.variableCount.toUInt64),
        (o + 18 + 3 * c, pl.index.toUInt64)])

/-- `ClaimsAt`'s words. -/
def claimsImage (cs : Array ColumnClaimW) : List (Nat × UInt64) :=
  [(claimsR.off, cs.size.toUInt64)] ++
  (cs.toList.zipIdx.flatMap fun (c, i) ↦
    let b := claimsR.off + 1 + claimWords * i
    [(b, c.column.toUInt64)] ++ vecW (b + 1) c.point ++
      [(b + 1 + vecWords pointCap, c.value.c0), (b + 2 + vecWords pointCap, c.value.c1)])

/-- A machine state holding `t`, the public input and the working area's words `work`. -/
def startState (L : Nat) (π : Proof) (pub : Vector UInt64 4) (t : TState)
    (work : List (Nat × UInt64)) : RState :=
  let ctxWords : List (Nat × UInt64) := (List.range ctxEnd).map fun k ↦
    (k, if k = ctxDecoded then decA else if k = ctxWork then workA
      else if ctxPublic ≤ k ∧ k < ctxPublic + 4 then pub.toList.getD (k - ctxPublic) 0 else 0)
  RState.ofWords ctxA <|
    (ctxWords ++ spongeWords t.sponge).map (fun (k, v) ↦ (wd ctxA k, v)) ++
    (decodedImage L π).map (fun (k, v) ↦ (wd decA k, v)) ++
    (List.range dataEnd).map (fun k ↦ (wd workA k, 0)) ++
    (transcriptImage L t ++ work).map fun (k, v) ↦ (wd workA k, v)

/-- The words of an array of `E` from word `k` of the working area. -/
def readVec (s : RState) (k : Nat) : Array EW :=
  let n := (s.word (wd workA k)).toNat
  (Array.range n).map fun i ↦ ⟨s.word (wd workA (k + 1 + 2 * i)), s.word (wd workA (k + 2 + 2 * i))⟩

/-- The column claims at `claimsR`. -/
def readClaims (s : RState) : Array ColumnClaimW :=
  let n := (s.word (wd workA claimsR.off)).toNat
  (Array.range n).map fun i ↦
    let b := claimsR.off + 1 + claimWords * i
    ⟨(s.word (wd workA b)).toNat, readVec s (b + 1),
      ⟨s.word (wd workA (b + 1 + vecWords pointCap)), s.word (wd workA (b + 2 + vecWords pointCap))⟩⟩

def eqClaim (a b : ColumnClaimW) : Bool :=
  a.column == b.column && a.point == b.point && a.value == b.value

/-- The machine's transcript words are the model's state `t`. -/
def transcriptAgrees (L : Nat) (s : RState) (t : TState) : Bool :=
  (spongeWords t.sponge).all (fun (k, v) ↦ s.word (wd ctxA k) == v) &&
    (transcriptImage L t).all fun (k, v) ↦ s.word (wd workA k) == v

/-! ## The checks -/

/-- Phase 2's run against `phase2M`: `some true` when both accept with the same outputs, `some false`
when both reject, `none` on a disagreement. -/
def check2 (L : Nat) (π : Proof) (pub : Vector UInt64 4) (layout : LayoutW) (rate : Nat)
    (t : TState) : Option Bool := do
  let s := startState L π pub t (layoutImage layout rate)
  let r ← Native.Test.run 1000000000 phase2 s
  match (phase2M layout rate).run t, r with
  | none, (.err _, _) => some false
  | some (ood, t'), (.ok s', _) =>
    let z := match ood.weight with | .eq z => some z | _ => none
    let ok := z == some (readVec s' oodR.off) &&
      s'.word (wd workA (oodR.off + vecWords stackCap)) == ood.value.c0 &&
      s'.word (wd workA (oodR.off + vecWords stackCap + 1)) == ood.value.c1 &&
      transcriptAgrees L s' t'
    if ok then some true else none
  | _, _ => none

/-- Phase 5's run against `publicInputPhase`, as `check2`. -/
def check5 (L : Nat) (π : Proof) (pub : Vector UInt64 4) (layout : LayoutW) (rate : Nat)
    (acc : Array ColumnClaimW) (t : TState) : Option Bool := do
  let s := startState L π pub t (layoutImage layout rate ++ claimsImage acc)
  let r ← Native.Test.run 1000000000 phase5 s
  match (Model.publicInputPhase layout pub).run t, r with
  | none, (.err _, _) => some false
  | some (pc, t'), (.ok s', _) =>
    let cl := readClaims s'
    let want := acc ++ pc
    let ok := cl.size == want.size && (cl.zip want).all (fun (a, b) ↦ eqClaim a b) &&
      transcriptAgrees L s' t'
    if ok then some true else none
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
  -- phase 2
  let some (layout, rate, t1) := upTo1 bc pub stream openings
    | throw (IO.userError s!"{dir}: the model rejects before phase 2")
  unless check2 L π pub layout rate t1 == some true do throw (IO.userError s!"{dir}: phase 2")
  -- the grind's nonce, then the value, changed
  for (k, want) in [(2, false), (3 + layout.stackLog, true)] do
    let i := t1.cursor + k
    let stream' := stream.modify i fun x ↦ { x with c0 := x.c0 ^^^ 1 }
    let π' : Proof := ⟨stream'.toList.map EW.toE, phases.1⟩
    unless check2 L π' pub layout rate { t1 with stream := stream' } == some want do
      throw (IO.userError s!"{dir}: phase 2, scalar {i} changed")
  -- phase 5
  let some (layout, rate, acc, t4) := upTo4 bc pub stream openings
    | throw (IO.userError s!"{dir}: the model rejects before phase 5")
  unless check5 L π pub layout rate acc t4 == some true do throw (IO.userError s!"{dir}: phase 5")
  let pub' : Vector UInt64 4 := pub.map (· ^^^ 0x5555555555555555)
  unless check5 L π pub' layout rate acc t4 == some true do
    throw (IO.userError s!"{dir}: phase 5, another public input")
  IO.println s!"{dir.fileName.getD ""}: agree"

end NativeVm.Test.Phase25Test
