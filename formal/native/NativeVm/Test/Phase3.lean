import NativeVm.Test.Phase25
import NativeVm.Code.Phase3.Code

/-!
# Phase 3's code against the model

From a verifier fixture, the model runs up to phase 3 (`readAnnouncedSizes`, `phase2M`); its
transcript state and layout (with the announced row counts) are laid out as `CodeRel` and `LayoutAt`
say, the bytecode as `Inputs` says, and `P3.code` runs from there. Its outcome, the bus's forms,
point and totals at `busR` (`BusAt`), the column claims at `claimsR` (`ClaimsAt`) and the
transcript's sponge and cursor must be `verifyBusBalance`'s; then again with one of phase 3's stream
elements changed (the grind's nonce, a GKR scalar, phase 3's last scalar), which both reject.
-/

namespace NativeVm.Test.Phase3Test

open Native Native.Test NativeVm NativeVm.Transcript NativeVm.Model NativeVm.Code
open NativeVm.Test.TranscriptTest NativeVm.Test.Phase25Test
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

/-- The model up to phase 3: the layout, the rate, the row counts phase 1 read, the transcript's
state. -/
def t3_upTo2 (bc : Array UInt64) (pub : Vector UInt64 4) (stream : Array EW)
    (openings : Array (Array OpeningW)) : Option (LayoutW × Nat × List UInt64 × TState) := do
  let t0 := Code.start ⟨0, bc, pub⟩ stream openings
  let ((layout, rate), t1) ← (readAnnouncedSizes bc).run t0
  let ((_ : StackClaimW), t2) ← (phase2M layout rate).run t1
  let rows := (List.range nTables).map fun i ↦ (t0.stream.getD (t0.cursor + 1 + i) 0).c0
  pure (layout, rate, rows, t2)

/-- The machine state before phase 3: the context (with the bytecode's pointer and length), the
sponge, the decoded proof, the bytecode, the working area zeroed with the transcript's and the
layout's words. -/
def t3_startState (L : Nat) (π : Proof) (bc : Array UInt64) (pub : Vector UInt64 4)
    (layout : LayoutW) (rate : Nat) (rows : List UInt64) (t : TState) : RState :=
  let ctxWords : List (Nat × UInt64) := (List.range ctxEnd).map fun k ↦
    (k, if k = ctxWireLen then L.toUInt64 else if k = ctxBytecode then bcA
      else if k = ctxBytecodeLen then bc.size.toUInt64
      else if ctxPublic ≤ k ∧ k < ctxPublic + 4 then pub.toList.getD (k - ctxPublic) 0
      else if k = ctxDecoded then decA else if k = ctxWork then workA else 0)
  RState.ofWords ctxA <|
    (ctxWords ++ spongeWords t.sponge).map (fun (k, v) ↦ (wd ctxA k, v)) ++
    (decodedImage L π).map (fun (k, v) ↦ (wd decA k, v)) ++
    bc.toList.zipIdx.map (fun (x, k) ↦ (wd bcA k, x)) ++
    (List.range (workWords bc.size)).map (fun k ↦ (wd workA k, 0)) ++
    (transcriptImage L t ++ layoutImage layout rate ++
      (rows.zipIdx.map fun ((r : UInt64), i) ↦ (layoutR.off + 10 + i, r))).map fun (k, v) ↦
      (wd workA k, v)

/-- The form at word `k` of the working area. -/
def t3_readForm (s : RState) (k : Nat) : FormW :=
  let n := (s.word (wd workA k)).toNat
  (Array.range n).map fun i ↦
    let b := k + 1 + termWords * i
    let c := (s.word (wd workA b)).toNat
    ⟨(Array.range c).map fun j ↦ (s.word (wd workA (b + 1 + j))).toNat,
      ⟨s.word (wd workA (b + 1 + monoCap)), s.word (wd workA (b + 2 + monoCap))⟩⟩

def t3_eqForm (a b : FormW) : Bool :=
  a.size == b.size && (a.zip b).all fun (x, y) ↦ x.cols == y.cols && x.coeff == y.coeff

/-- `BusAt`: every table's three forms, the point, the totals. -/
def t3_busAgrees (s : RState) (bus : BusResultW) : Bool :=
  bus.forms.size == nTables &&
    (List.range nTables).all (fun tb ↦ (List.range 3).all fun side ↦
      t3_eqForm (t3_readForm s (busR.off + formOff tb side)) ((bus.forms.getD tb #[]).getD side #[])) &&
    readVec s (busR.off + busPointOff) == bus.point &&
    bus.totals.size == nTrees &&
    (bus.totals.toList.zipIdx.all fun (x, i) ↦
      s.word (wd workA (busR.off + busTotalsOff + 2 * i)) == x.c0 &&
        s.word (wd workA (busR.off + busTotalsOff + 2 * i + 1)) == x.c1)

/-- The code's run against `verifyBusBalance` from `t`: `some true` when both accept with the same
outputs, `some false` when both reject, `none` on a disagreement. -/
def t3_check (L : Nat) (π : Proof) (bc : Array UInt64) (pub : Vector UInt64 4) (layout : LayoutW)
    (rate : Nat) (rows : List UInt64) (t : TState) : Option Bool := do
  let s := t3_startState L π bc pub layout rate rows t
  let r ← Native.Test.run 1000000000 P3.code s
  match (verifyBusBalance layout).run t, r with
  | none, (.err _, _) => some false
  | some (bus, t'), (.ok s', _) =>
    let cl := readClaims s'
    let clOk := cl.size == bus.claims.size && (cl.zip bus.claims).all fun (a, b) ↦ eqClaim a b
    let tOk := (spongeWords t'.sponge).all (fun (k, v) ↦ s'.word (wd ctxA k) == v) &&
      s'.word (wd workA workCursor) == t'.cursor.toUInt64
    if t3_busAgrees s' bus && clOk && tOk then some true else none
  | _, _ => none

/-- A statement's instructions. -/
def t3_size : Stmt → Nat
  | .skip | .fail => 0
  | .ins _ => 1
  | .seq a b | .ite _ a b => t3_size a + t3_size b
  | .loop _ b => t3_size b

/-- `Native.Test.run`, counting the instructions executed. -/
partial def t3_runCount : Nat → Stmt → RState → Option (ROutcome × Nat × Nat)
  | fuel, .skip, s => some (.ok s, fuel, 0)
  | fuel, .ins i, s => (stepI i s).map fun s ↦ (.ok s, fuel, 1)
  | fuel, .fail, s => some (.err s, fuel, 0)
  | fuel, .seq a b, s => do
    match ← t3_runCount fuel a s with
    | (.ok s, fuel, n) => (t3_runCount fuel b s).map fun (r, f, m) ↦ (r, f, n + m)
    | r => some r
  | fuel, .ite c t e, s => if c.eval s.toQ then t3_runCount fuel t s else t3_runCount fuel e s
  | 0, .loop _ _, _ => none
  | fuel + 1, .loop c b, s =>
    if c.eval s.toQ then do
      match ← t3_runCount fuel b s with
      | (.ok s, fuel, n) => (t3_runCount fuel (.loop c b) s).map fun (r, f, m) ↦ (r, f, n + m)
      | r => some r
    else some (.ok s, fuel, 0)

def t3_runDir (dir : System.FilePath) : IO Unit := do
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
  let some (layout, rate, rows, t) := t3_upTo2 bc pub stream openings
    | throw (IO.userError s!"{dir}: the model rejects before phase 3")
  let some (_, t') := (verifyBusBalance layout).run t
    | throw (IO.userError s!"{dir}: the model rejects phase 3")
  unless t3_check L π bc pub layout rate rows t == some true do
    throw (IO.userError s!"{dir}: honest run")
  let steps := match t3_runCount 1000000000 P3.code (t3_startState L π bc pub layout rate rows t) with
    | some (.ok _, _, n) => toString n
    | _ => "?"
  -- one of phase 3's scalars changed: the grind's nonce, a GKR scalar, the last one
  let used := t'.cursor - t.cursor
  for k in [0, 3, used - 1] do
    let i := t.cursor + k
    let stream' := stream.modify i fun x ↦ { x with c0 := x.c0 ^^^ 1 }
    let π' : Proof := ⟨stream'.toList.map EW.toE, phases.1⟩
    unless t3_check L π' bc pub layout rate rows { t with stream := stream' } == some false do
      throw (IO.userError s!"{dir}: scalar {i} changed")
  IO.println s!"{dir.fileName.getD ""}: agree ({used} scalars, {steps} instructions run; \
    scalars {t.cursor}, {t.cursor + 3}, {t.cursor + used - 1} changed: both reject)"

end NativeVm.Test.Phase3Test
