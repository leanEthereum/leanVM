module

public import NativeRustcVmArm.Code.Vm.FirstClaim.Names
public import NativeRustcVmArm.Code.Vm.InstanceWeights.Names
public import NativeRustcVmArm.Code.Vm.KeccakOpen.Names
public import NativeRustcVmArm.Code.Vm.KeccakPhase.Names
public import NativeRustcVmArm.Code.Vm.KeccakPi.Names
public import NativeRustcVmArm.Code.Vm.LinearTranspose.Names
public import NativeRustcVmArm.Code.Vm.Names
public import NativeRustcVmArm.Code.Vm.SlotWeights.Names
public import NativeRustcVmArm.Code.Vm.VerifyKeccak.Names
public import NativeRustcVmArm.Code.Vm.VerifyLayer.Names
public import NativeRustcVmArm.Spec.Sumcheck
public import NativeRustcVm.KeccakGkr.Rep
public import NativeRustcVm.Layout.Rep
public import NativeRustcVm.Tables.Rep
public import NativeRustcVm.Rodata
public import NativeRustcVmArm.Spec.Layout

/-!
# The contracts of `keccak_gkr.rs`'s functions on AArch64 (phase 6)

Each function uses the stack below SP (`<fn>Stack` bytes, its callees' included; `StackOk` in its
precondition) and returns with the callee-saved registers and SP kept (`Saved`), no byte changed
outside the regions it writes and that stack (`Writes`). The regions it writes and the stack are
data memory, pairwise apart and apart from the regions it reads (`Areas`). The transcript's state
is `TStateAt` (`NativeRustcVm.Transcript`), a claim but its bit weights `ClaimAt`, the bit weights
`WeightsAt`, `KeccakOutW` `KeccakOutAt` (`NativeRustcVm.KeccakGkr`), the column claims
`ClaimsWAt` (`NativeRustcVm.Layout`), the tables' evaluations `TableEvalsAt`
(`NativeRustcVm.Tables`). Results are the model's (`NativeVm/Model/KeccakGkr.lean`); a `VM` step's
`none` is the Rust's `None` and on it the contract says nothing more than the frame. The read-only
data read: `RMFE_PROJECT` (`ProjectAt`), `KECCAK_RHO` (`RhoAt`), `KECCAK_RC` (`RcAt`).

- `keccak_pi(i)` (X0, `i < 25`): `keccakPi i` in X0.
- `linear_transpose(w, g, columns, out)` (X0 to X3): `out` holds `keccakLinearTranspose` of the
  1600 elements at `w`; `g` and `columns` scratch.
- `instance_weights(out, s)` (X0; `s` in X1, X2; the `Buf<EW, 16>` result at X0): the `Buf` holds
  `keccakInstanceWeights s`.
- `slot_weights(logSteps, point, weights, first, count, rows)` (X0 to X6; rustc specialised the
  segment loop to its callers' `count ∈ {1, 2}`, `first + count ≤ 2`): `Some` (W0 = 1) and the 64
  rows at `rows` hold `keccakSlotWeights logSteps c first count` of the claim `c` whose point and
  bit weights are at `point` and `weights`. The segment kernel exists: `|point| - (logSteps - 4)
  ≤ 2`.
- `keccak_open(out, t, logSteps, point, weights, first, count, value, slot, rows)` (X0 to X7, then
  `value`, `slot`, `rows` at SP, SP + 16, SP + 24): `keccakOpen logSteps c first count value`, the
  value left the `Option<EW>` at `out`, the slot point at `slot`, the weights on the slices in row
  `0` of `rows`.
- `first_claim(out, inst, segment, lanePoint, output, committed, weights)` (X0 to X7, `weights` at
  SP; `|inst| ≤ 30`): `Some` of `keccakFirstClaim`, the `Option<KeccakClaimW>` at `out` (tag word
  `1`, the claim from byte `8`), its bit weights at `weights`.
- `verify_layer(t, logSteps, step, claim, scratch)` (X0 to X4; `step < 12`, the segment kernel
  exists): `verifyKeccakLayer logSteps step c`, the claim at `claim`, its bit weights at
  `scratch.weights`; the first claim's bit weights and the slot weights kept.
- `verify_keccak(t, logSteps, inst, output, scratch, claims, out)` (X0 to X7; `|inst| = logSteps ≤
  30`, room for one more column claim): `verifyKeccak logSteps inst output`, its column claims
  appended to `claims`, the point and slices at `out`.
- `keccak_phase(t, logSteps, evals, scratch, claims, out)` (X0 to X5; rustc passed
  `layout.table_log_heights[OP_KECCAK]` by value and fixed the evaluations' slice to its 6
  entries; `KECCAK`'s point has `logSteps` coordinates, as `tablePhase` gives it): `keccakPhase
  layout evals`.
-/

namespace NativeRustcVmArm

open NativeRustcArm NativeVm.Model LeanVM.Parameters LeanVM.Protocol.Verifier
open NativeRustcVm.Transcript
open NativeRustcVm.KeccakGkr (ClaimAt WeightsAt KeccakOutAt rowsFlat claimBytes scratchBytes
  weightsBytes weightsOff rowsOff rowsBytes outBytes)
open NativeRustcVm (Region Disjoint InAny)

@[expose] public section

/-! ## Symbols -/


/-! ## Stacks -/

/-- `keccak_pi` uses no stack. -/
def keccakPiStack : Nat := 0
/-- The stack `linear_transpose` uses: its 80-byte frame (`keccak_pi` uses none). -/
def linearTransposeStack : Nat := 80 + keccakPiStack
/-- The stack `instance_weights` uses: its 976-byte frame and `powers`'s (`memcpy` uses none). -/
def instanceWeightsStack : Nat := 976 + powersStack
/-- The stack `slot_weights` uses: its 176-byte frame and the larger of `eq_kernel`'s and
`EW::mul`'s. -/
def slotWeightsStack : Nat := 176 + max eqKernelStack ewMulStack
/-- The stack `keccak_open` uses: its 2224-byte frame and the largest of its callees'. -/
def keccakOpenStack : Nat := 2224 + max sumcheckPlainStack (max slotWeightsStack ewMulStack)
/-- The stack `first_claim` uses: its 1408-byte frame and the largest of its callees'. -/
def firstClaimStack : Nat := 1408 + max eqKernelStack (max ewMulStack dotStack)
/-- The stack `verify_layer` uses: its 2032-byte frame and the largest of its callees'. -/
def verifyLayerStack : Nat :=
  2032 + max (max (max readScalarsStack grindStack) (max squeezeStack instanceWeightsStack))
    (max (max sumcheckPlainStack sumcheckLayerStack)
      (max (max polyEvalStack eqKernelStack) (max dotStack linearTransposeStack)))
/-- The stack `verify_keccak` uses: its 3360-byte frame and the largest of its callees'. -/
def verifyKeccakStack : Nat :=
  3360 + max (max (max grindStack sampleChallengesStack) (max readScalarStack readScalarsStack))
    (max (max (max firstClaimStack verifyLayerStack) (max keccakOpenStack sumcheckPlainStack))
      (max (max mleStack dotStack) pushClaimStack))
/-- The stack `keccak_phase` uses: its 480-byte frame and `verify_keccak`'s. -/
def keccakPhaseStack : Nat := 480 + verifyKeccakStack

section
variable [Labels]

/-! ## Read-only data -/

/-- The address of `RMFE_PROJECT`. -/
def projectAddr : BitVec 64 := (label NativeRustcVmArm.Vm.Symbols.rodata0Label).toBitVec

/-- The address of `KECCAK_RHO`. -/
def rhoAddr : BitVec 64 := (label NativeRustcVmArm.Vm.Symbols.rodata2Label).toBitVec

/-- `KECCAK_RHO`'s bytes: each offset a little-endian `u32` (`RodataAt`'s `.keccakRho` item). -/
def rhoBytes : List UInt8 := NativeRustcVm.Data.Item.bytes .keccakRho

/-- `RMFE_PROJECT` is at its label. -/
def ProjectAt (m : MachineData) : Prop :=
  NativeRustcVm.WordsAt m.dmem projectAddr rmfeProjectW.toList

/-- `KECCAK_RHO` is at its label. -/
def RhoAt (m : MachineData) : Prop := BytesAt m.dmem rhoAddr rhoBytes

/-- The round constants' region. -/
def rcRegion : Region := ⟨rcAddr, 192⟩
/-- `RMFE_PROJECT`'s region. -/
def projectRegion : Region := ⟨projectAddr, 128⟩
/-- `KECCAK_RHO`'s region. -/
def rhoRegion : Region := ⟨rhoAddr, 100⟩

/-! ## Footprints -/

/-- The `n` bytes of stack below SP as a region. -/
def stackRegion (m : MachineData) (n : Nat) : Region := ⟨stackBelow m n, n⟩

/-- The regions a function using `n` bytes of stack writes (`ws`) and reads (`rs`): data memory,
not wrapping; the written ones and the stack pairwise apart, and apart from the read ones. -/
def Areas (m : MachineData) (n : Nat) (ws rs : List Region) : Prop :=
  (∀ r ∈ ws ++ rs, r.Ok m.dmem) ∧ Disjoint (stackRegion m n :: ws) ∧
    ∀ w ∈ stackRegion m n :: ws, ∀ r ∈ rs, Apart w.addr w.size r.addr r.size

/-- Memory changes only in the regions `ws` and the `n` bytes of stack below SP. -/
def Writes (m m' : MachineData) (n : Nat) (ws : List Region) : Prop :=
  SameOutside m.dmem m'.dmem (InAny (stackRegion m n :: ws))

/-- `n` elements of `E` from `a` as a region. -/
def ewsRegion (a : BitVec 64) (n : Nat) : Region := ⟨a, 16 * n⟩

/-- The segment kernel of a claim's point exists (`eq_kernel` into four elements): one or two
coordinates past the pack's. -/
def SegmentsFit (logSteps : Nat) (c : KeccakClaimW) : Prop :=
  logSteps - 4 < c.point.size ∧ c.point.size - (logSteps - 4) ≤ 2

/-! ## `keccak_pi` -/

/-- `keccak_pi`'s precondition. -/
def KeccakPiPre (m : MachineData) : Prop := m.regs.X0.toNat < 25

/-- `keccak_pi`'s postcondition. -/
def KeccakPiPost (m m' : MachineData) : Prop :=
  m'.regs.X0.toNat = keccakPi m.regs.X0.toNat ∧ m'.dmem = m.dmem ∧ Saved m m'

/-! ## `linear_transpose` -/

/-- `linear_transpose`'s precondition: the 1600 elements `ws` at `w` (X0); `g` (X1), `columns`
(X2), `out` (X3) written. -/
def LinearTransposePre (ws : Array EW) (m : MachineData) : Prop :=
  let w := m.regs.X0.toBitVec; let g := m.regs.X1.toBitVec; let col := m.regs.X2.toBitVec
  let out := m.regs.X3.toBitVec
  StackOk m linearTransposeStack ∧ RhoAt m ∧ ws.size = keccakBits ∧
    NativeRustcVm.EWsAt m.dmem w ws.toList ∧
    Areas m linearTransposeStack [⟨g, weightsBytes⟩, ⟨col, 5120⟩, ⟨out, weightsBytes⟩]
      [⟨w, weightsBytes⟩, rhoRegion]

/-- `linear_transpose`'s postcondition. -/
def LinearTransposePost (ws : Array EW) (m m' : MachineData) : Prop :=
  let g := m.regs.X1.toBitVec; let col := m.regs.X2.toBitVec; let out := m.regs.X3.toBitVec
  NativeRustcVm.EWsAt m'.dmem out (keccakLinearTranspose ws).toList ∧
    Writes m m' linearTransposeStack [⟨g, weightsBytes⟩, ⟨col, 5120⟩, ⟨out, weightsBytes⟩] ∧
    Saved m m'

/-! ## `instance_weights` -/

/-- `instance_weights`'s precondition: the result's `Buf<EW, 16>` (264 bytes) at X0. -/
def InstanceWeightsPre (m : MachineData) : Prop :=
  StackOk m instanceWeightsStack ∧ Areas m instanceWeightsStack [⟨m.regs.X0.toBitVec, 264⟩] []

/-- `instance_weights`'s postcondition. -/
def InstanceWeightsPost (m m' : MachineData) : Prop :=
  NativeRustcVm.BufEWAt m'.dmem m.regs.X0.toBitVec 16 (keccakInstanceWeights ⟨m.regs.X1, m.regs.X2⟩).toList ∧
    Writes m m' instanceWeightsStack [⟨m.regs.X0.toBitVec, 264⟩] ∧ Saved m m'

/-! ## `slot_weights` -/

/-- `slot_weights`'s precondition: the claim `c`'s point at X1 (X2 elements) and bit weights at X3;
`first` (X4) and `count` (X5) with `1 ≤ count`, `first + count ≤ 2`; the rows at X6 written. -/
def SlotWeightsPre (c : KeccakClaimW) (m : MachineData) : Prop :=
  let pt := m.regs.X1.toBitVec; let w := m.regs.X3.toBitVec; let rows := m.regs.X6.toBitVec
  StackOk m slotWeightsStack ∧ c.point.size = m.regs.X2.toNat ∧
    NativeRustcVm.EWsAt m.dmem pt c.point.toList ∧ WeightsAt m.dmem w c ∧
    SegmentsFit m.regs.X0.toNat c ∧ 1 ≤ m.regs.X5.toNat ∧
    m.regs.X4.toNat + m.regs.X5.toNat ≤ keccakSegments ∧
    Areas m slotWeightsStack [⟨rows, rowsBytes⟩] [ewsRegion pt c.point.size, ⟨w, weightsBytes⟩]

/-- `slot_weights`'s postcondition. -/
def SlotWeightsPost (c : KeccakClaimW) (m m' : MachineData) : Prop :=
  let rows := m.regs.X6.toBitVec
  m'.regs.X0 = 1 ∧
    NativeRustcVm.EWsAt m'.dmem rows
      (rowsFlat (keccakSlotWeights m.regs.X0.toNat c m.regs.X4.toNat m.regs.X5.toNat)) ∧
    Writes m m' slotWeightsStack [⟨rows, rowsBytes⟩] ∧ Saved m m'

/-! ## `keccak_open` -/

/-- `keccak_open`'s stack arguments: the value, the slot point's and the rows' addresses. -/
def openValue (m : MachineData) : EW :=
  ⟨NativeRustcVm.wordOf m.dmem m.regs.SP.toBitVec, NativeRustcVm.wordOf m.dmem (off m.regs.SP.toBitVec 8)⟩
/-- The slot point's address. -/
def openSlot (m : MachineData) : BitVec 64 := (NativeRustcVm.wordOf m.dmem (off m.regs.SP.toBitVec 16)).toBitVec
/-- The rows' address. -/
def openRows (m : MachineData) : BitVec 64 := (NativeRustcVm.wordOf m.dmem (off m.regs.SP.toBitVec 24)).toBitVec

/-- `keccak_open`'s precondition: the `TState` at X1, the claim `c`'s point (X3, X4) and bit
weights (X5), `first` (X6) and `count` (X7) as `slot_weights` takes them; the output (X0), the
slot point (6 elements) and the rows written. -/
def KeccakOpenPre (a : DecArea) (s : TState) (c : KeccakClaimW) (m : MachineData) : Prop :=
  let out := m.regs.X0.toBitVec; let t := m.regs.X1.toBitVec; let pt := m.regs.X3.toBitVec
  let w := m.regs.X5.toBitVec
  StackOk m keccakOpenStack ∧ RcAt m keccakOpenStack ∧ TStateAt m.dmem t a s ∧
    c.point.size = m.regs.X4.toNat ∧ NativeRustcVm.EWsAt m.dmem pt c.point.toList ∧
    WeightsAt m.dmem w c ∧ SegmentsFit m.regs.X2.toNat c ∧ 1 ≤ m.regs.X7.toNat ∧
    m.regs.X6.toNat + m.regs.X7.toNat ≤ keccakSegments ∧
    Areas m keccakOpenStack
      [⟨out, 24⟩, ⟨t, tstateBytes⟩, ewsRegion (openSlot m) qkeccakSlotBits, ⟨openRows m, rowsBytes⟩]
      [a.region, ewsRegion pt c.point.size, ⟨w, weightsBytes⟩, rcRegion, ⟨m.regs.SP.toBitVec, 32⟩]

/-- `keccak_open`'s postcondition. -/
def KeccakOpenPost (a : DecArea) (s : TState) (c : KeccakClaimW) (m m' : MachineData) : Prop :=
  let out := m.regs.X0.toBitVec; let t := m.regs.X1.toBitVec
  let r := (keccakOpen m.regs.X2.toNat c m.regs.X6.toNat m.regs.X7.toNat (openValue m)).run s
  OptEWAt m'.dmem out (r.map (·.1.2.2)) ∧
    (∀ sl ws v s', r = some ((sl, ws, v), s') →
      NativeRustcVm.EWsAt m'.dmem (openSlot m) sl.toList ∧
        NativeRustcVm.EWsAt m'.dmem (openRows m) ws.toList ∧ TStateAt m'.dmem t a s') ∧
    Writes m m' keccakOpenStack
      [⟨out, 24⟩, ⟨t, tstateBytes⟩, ewsRegion (openSlot m) qkeccakSlotBits, ⟨openRows m, rowsBytes⟩] ∧
    Saved m m'

/-! ## `first_claim` -/

/-- `first_claim`'s bit weights' address: the word at SP. -/
def firstWeights (m : MachineData) : BitVec 64 := (NativeRustcVm.wordOf m.dmem m.regs.SP.toBitVec).toBitVec

/-- `first_claim`'s precondition: `inst` at X1 (X2 elements, at most 30), the segment (X3, one
element), the lane point (X4, five), the output lanes (X5, 25); the result (X0, 776 bytes) and the
bit weights written. -/
def FirstClaimPre (inst segment lanePoint output : Array EW) (m : MachineData) : Prop :=
  let out := m.regs.X0.toBitVec; let ip := m.regs.X1.toBitVec
  StackOk m firstClaimStack ∧ inst.size = m.regs.X2.toNat ∧ inst.size ≤ 30 ∧
    NativeRustcVm.EWsAt m.dmem ip inst.toList ∧
    segment.size = keccakSegmentBits ∧ NativeRustcVm.EWsAt m.dmem m.regs.X3.toBitVec segment.toList ∧
    lanePoint.size = keccakLaneBits ∧
    NativeRustcVm.EWsAt m.dmem m.regs.X4.toBitVec lanePoint.toList ∧
    output.size = 25 ∧ NativeRustcVm.EWsAt m.dmem m.regs.X5.toBitVec output.toList ∧
    Areas m firstClaimStack [⟨out, 8 + claimBytes⟩, ⟨firstWeights m, weightsBytes⟩]
      [ewsRegion ip inst.size, ewsRegion m.regs.X3.toBitVec 1, ewsRegion m.regs.X4.toBitVec 5,
        ewsRegion m.regs.X5.toBitVec 25, ⟨m.regs.SP.toBitVec, 8⟩]

/-- `first_claim`'s postcondition. -/
def FirstClaimPost (inst segment lanePoint output : Array EW) (m m' : MachineData) : Prop :=
  let out := m.regs.X0.toBitVec
  let c := keccakFirstClaim inst segment lanePoint output ⟨m.regs.X6, m.regs.X7⟩
  NativeRustcVm.WordAt m'.dmem out 1 ∧ ClaimAt m'.dmem (off out 8) c ∧
    WeightsAt m'.dmem (firstWeights m) c ∧
    Writes m m' firstClaimStack [⟨out, 8 + claimBytes⟩, ⟨firstWeights m, weightsBytes⟩] ∧
    Saved m m'

/-! ## `verify_layer` -/

/-- The part of the scratch `verify_layer` writes: the running claim's bit weights, the layer's
weights, `g`, the columns, the local equality kernel. -/
def layerRegion (scratch : BitVec 64) : Region := ⟨off scratch weightsOff, rowsOff - weightsOff⟩

/-- `verify_layer`'s precondition: the `TState` at X0, `logSteps` (X1), `step < 12` (X2), the
claim `c` at X3, its bit weights at the scratch's (X4) `weights`. -/
def VerifyLayerPre (a : DecArea) (s : TState) (c : KeccakClaimW) (m : MachineData) : Prop :=
  let t := m.regs.X0.toBitVec; let cp := m.regs.X3.toBitVec; let sc := m.regs.X4.toBitVec
  StackOk m verifyLayerStack ∧ RcAt m verifyLayerStack ∧ ProjectAt m ∧ RhoAt m ∧
    TStateAt m.dmem t a s ∧ ClaimAt m.dmem cp c ∧ WeightsAt m.dmem (off sc weightsOff) c ∧
    m.regs.X2.toNat < keccakDepth ∧ SegmentsFit m.regs.X1.toNat c ∧
    Areas m verifyLayerStack [⟨t, tstateBytes⟩, ⟨cp, claimBytes⟩, ⟨sc, scratchBytes⟩]
      [a.region, rcRegion, projectRegion, rhoRegion]

/-- `verify_layer`'s postcondition. -/
def VerifyLayerPost (a : DecArea) (s : TState) (c : KeccakClaimW) (m m' : MachineData) : Prop :=
  let t := m.regs.X0.toBitVec; let cp := m.regs.X3.toBitVec; let sc := m.regs.X4.toBitVec
  let r := (verifyKeccakLayer m.regs.X1.toNat m.regs.X2.toNat c).run s
  m'.regs.X0 = okWord r.isSome ∧
    (∀ c' s', r = some (c', s') → TStateAt m'.dmem t a s' ∧ ClaimAt m'.dmem cp c' ∧
      WeightsAt m'.dmem (off sc weightsOff) c') ∧
    Writes m m' verifyLayerStack [⟨t, tstateBytes⟩, ⟨cp, claimBytes⟩, layerRegion sc] ∧ Saved m m'

/-! ## `verify_keccak` -/

/-- `verify_keccak`'s precondition: the `TState` at X0, `logSteps` (X1) at most 30, `inst` at X2
(X3 = `logSteps` elements), the 25 output lanes at X4; the scratch (X5), the column claims `cs`
(X6, one short of full at most) and `KeccakOutW` (X7) written. -/
def VerifyKeccakPre (a : DecArea) (s : TState) (cs : Array ColumnClaimW) (inst output : Array EW)
    (m : MachineData) : Prop :=
  let t := m.regs.X0.toBitVec; let ip := m.regs.X2.toBitVec; let op := m.regs.X4.toBitVec
  let sc := m.regs.X5.toBitVec; let cl := m.regs.X6.toBitVec; let out := m.regs.X7.toBitVec
  StackOk m verifyKeccakStack ∧ RcAt m verifyKeccakStack ∧ ProjectAt m ∧ RhoAt m ∧
    TStateAt m.dmem t a s ∧ NativeRustcVm.Layout.ClaimsWAt m.dmem cl cs ∧
    cs.size < NativeRustcVm.Layout.claimCap ∧
    inst.size = m.regs.X3.toNat ∧ inst.size = m.regs.X1.toNat ∧ inst.size ≤ 30 ∧
    NativeRustcVm.EWsAt m.dmem ip inst.toList ∧
    output.size = 25 ∧ NativeRustcVm.EWsAt m.dmem op output.toList ∧
    Areas m verifyKeccakStack
      [⟨t, tstateBytes⟩, ⟨sc, scratchBytes⟩, ⟨cl, NativeRustcVm.Layout.claimsBytes⟩, ⟨out, outBytes⟩]
      [a.region, ewsRegion ip inst.size, ewsRegion op 25, rcRegion, projectRegion, rhoRegion]

/-- `verify_keccak`'s postcondition. -/
def VerifyKeccakPost (a : DecArea) (s : TState) (cs : Array ColumnClaimW) (inst output : Array EW)
    (m m' : MachineData) : Prop :=
  let t := m.regs.X0.toBitVec; let sc := m.regs.X5.toBitVec; let cl := m.regs.X6.toBitVec
  let out := m.regs.X7.toBitVec
  let r := (verifyKeccak m.regs.X1.toNat inst output).run s
  m'.regs.X0 = okWord r.isSome ∧
    (∀ outs pt sl s', r = some ((outs, pt, sl), s') → TStateAt m'.dmem t a s' ∧
      NativeRustcVm.Layout.ClaimsWAt m'.dmem cl (cs ++ outs) ∧ KeccakOutAt m'.dmem out pt sl) ∧
    Writes m m' verifyKeccakStack
      [⟨t, tstateBytes⟩, ⟨sc, scratchBytes⟩, ⟨cl, NativeRustcVm.Layout.claimsBytes⟩, ⟨out, outBytes⟩] ∧
    Saved m m'

/-! ## `keccak_phase` -/

/-- `keccak_phase`'s precondition: the `TState` at X0, `logSteps` (X1) `layout`'s log-height of
`KECCAK`, the tables' evaluations `evals` at X2, `KECCAK`'s point of `logSteps` coordinates; the
scratch (X3), the column claims `cs` (X4) and `KeccakOutW` (X5) written. -/
def KeccakPhasePre (a : DecArea) (s : TState) (cs : Array ColumnClaimW) (layout : LayoutW)
    (evals : Array (Array EW × Array EW)) (m : MachineData) : Prop :=
  let t := m.regs.X0.toBitVec; let ev := m.regs.X2.toBitVec; let sc := m.regs.X3.toBitVec
  let cl := m.regs.X4.toBitVec; let out := m.regs.X5.toBitVec
  StackOk m keccakPhaseStack ∧ RcAt m keccakPhaseStack ∧ ProjectAt m ∧ RhoAt m ∧
    TStateAt m.dmem t a s ∧ NativeRustcVm.Layout.ClaimsWAt m.dmem cl cs ∧
    cs.size < NativeRustcVm.Layout.claimCap ∧
    NativeRustcVm.Tables.TableEvalsAt m.dmem ev evals ∧
    m.regs.X1.toNat = layout.tableLogHeights.getD opKeccak 0 ∧
    (evals.getD opKeccak (#[], #[])).1.size = m.regs.X1.toNat ∧
    keccakOut ≤ (evals.getD opKeccak (#[], #[])).2.size ∧
    Areas m keccakPhaseStack
      [⟨t, tstateBytes⟩, ⟨sc, scratchBytes⟩, ⟨cl, NativeRustcVm.Layout.claimsBytes⟩, ⟨out, outBytes⟩]
      [a.region, ⟨ev, NativeRustcVm.Tables.tableEvalsBytes⟩, rcRegion, projectRegion, rhoRegion]

/-- `keccak_phase`'s postcondition. -/
def KeccakPhasePost (a : DecArea) (s : TState) (cs : Array ColumnClaimW) (layout : LayoutW)
    (evals : Array (Array EW × Array EW)) (m m' : MachineData) : Prop :=
  let t := m.regs.X0.toBitVec; let sc := m.regs.X3.toBitVec; let cl := m.regs.X4.toBitVec
  let out := m.regs.X5.toBitVec
  let r := (keccakPhase layout evals).run s
  m'.regs.X0 = okWord r.isSome ∧
    (∀ outs pt sl s', r = some ((outs, pt, sl), s') → TStateAt m'.dmem t a s' ∧
      NativeRustcVm.Layout.ClaimsWAt m'.dmem cl (cs ++ outs) ∧ KeccakOutAt m'.dmem out pt sl) ∧
    Writes m m' keccakPhaseStack
      [⟨t, tstateBytes⟩, ⟨sc, scratchBytes⟩, ⟨cl, NativeRustcVm.Layout.claimsBytes⟩, ⟨out, outBytes⟩] ∧
    Saved m m'

end

end

end NativeRustcVmArm
