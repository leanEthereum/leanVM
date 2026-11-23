module

public import NativeRustcVmX64.Spec.Sumcheck
public import NativeRustcVmX64.Spec.Layout
public import NativeRustcX64.Spec.Got
public import NativeRustcVm.KeccakGkr.Rep
public import NativeRustcVm.Layout.Rep
public import NativeRustcVm.Tables.Rep
public import NativeRustcVm.Rodata
public import NativeRustcVmX64.Code.Vm.FirstClaim.Names
public import NativeRustcVmX64.Code.Vm.InstanceWeights.Names
public import NativeRustcVmX64.Code.Vm.KeccakOpen.Names
public import NativeRustcVmX64.Code.Vm.KeccakPhase.Names
public import NativeRustcVmX64.Code.Vm.KeccakPi.Names
public import NativeRustcVmX64.Code.Vm.LinearTranspose.Names
public import NativeRustcVmX64.Code.Vm.Names
public import NativeRustcVmX64.Code.Vm.SlotWeights.Names
public import NativeRustcVmX64.Code.Vm.VerifyKeccak.Names
public import NativeRustcVmX64.Code.Vm.VerifyLayer.Names

/-!
# The contracts of `keccak_gkr.rs`'s functions on x86-64

The AArch64 contracts (`NativeRustcVmArm.Spec.KeccakGkr`) with the System V registers: arguments in
RDI, RSI, RDX, RCX, R8, R9, then on the stack above the return address (`stackArg`, mapped by
`ArgsOk`, a region the function reads); an `Option<()>` result in AL (`OkAl`). Each function uses
the stack below RSP (`<fn>Stack` bytes: its pushes, its frame, the stack arguments it pushes for a
call, its callees' return addresses and stacks; `StackOk` also maps its return address at RSP)
and returns with the callee-saved registers kept (and RSP 8 above, `Spec`), no byte changed
outside the regions it writes and that stack (`Writes`). The regions it writes and the stack with
the return address are data memory, pairwise apart and apart from the regions it reads (`Areas`).
Functions that call `memcpy`, directly or through transcript and sumcheck callees, additionally
require its actual loader slot bytes (`GotAt`). That read-only slot is protected from the same
caller areas, stack arguments and read-only tables; it is never a writable region. The GKR call
graph does not reach `memset`. Pure arithmetic and permutation helpers have no loader premise.
The transcript's state is `TStateAt` (`NativeRustcVm.Transcript`), a claim but its bit weights
`ClaimAt`, the bit weights `WeightsAt`, `KeccakOutW` `KeccakOutAt` (`NativeRustcVm.KeccakGkr`),
the column claims `ClaimsWAt` (`NativeRustcVm.Layout`), the tables' evaluations `TableEvalsAt`
(`NativeRustcVm.Tables`). Results are the model's (`NativeVm/Model/KeccakGkr.lean`); a `VM`
step's `none` is the Rust's `None` and on it the contract says nothing more than the frame. The
read-only data read: `RMFE_PROJECT` (`ProjectAt`), `KECCAK_RHO` (`RhoAt`), `KECCAK_RC` (`RcAt`).

- `keccak_pi(i)` (RDI, `i < 25`): `keccakPi i` in RAX.
- `linear_transpose(w, g, columns, out)` (RDI to RCX): `out` holds `keccakLinearTranspose` of the
  1600 elements at `w`; `g` and `columns` scratch.
- `instance_weights(out, s)` (RDI; `s` in RSI, RDX; the `Buf<EW, 16>` result at RDI): the `Buf`
  holds `keccakInstanceWeights s`.
- `slot_weights(logSteps, point, weights, first, count, rows)` (RDI to R9, `rows` the stack
  argument; rustc specialised the segment loop to its callers' `count ∈ {1, 2}`,
  `first + count ≤ 2`): `Some` (AL = 1) and the 64 rows at `rows` hold
  `keccakSlotWeights logSteps c first count` of the claim `c` whose point and bit weights are at
  `point` and `weights`. The segment kernel exists: `|point| - (logSteps - 4) ≤ 2`.
- `keccak_open(out, t, logSteps, point, weights, first, count, value, slot, rows)` (RDI to R9 up to
  `weights`, then the stack arguments `first`, `count`, `value` (two words), `slot`, `rows`):
  `keccakOpen logSteps c first count value`, the value left the `Option<EW>` at `out`, the slot
  point at `slot`, the weights on the slices in row `0` of `rows`.
- `first_claim(out, inst, segment, lanePoint, output, committed, weights)` (RDI to R9 up to
  `output`, then the stack arguments `committed` (two words) and `weights`; `|inst| ≤ 30`): `Some`
  of `keccakFirstClaim`, the `Option<KeccakClaimW>` at `out` (tag word `1`, the claim from byte
  `8`), its bit weights at `weights`.
- `verify_layer(t, logSteps, step, claim, scratch)` (RDI to R8; `step < 12`, the segment kernel
  exists): `verifyKeccakLayer logSteps step c`, AL its `Option<()>`, the claim at `claim`, its bit
  weights at `scratch.weights`; the first claim's bit weights and the slot weights kept.
- `verify_keccak(t, logSteps, inst, output, scratch, claims, out)` (RDI to R9 up to `scratch`, then
  the stack arguments `claims`, `out`; `|inst| = logSteps ≤ 30`, room for one more column claim):
  `verifyKeccak logSteps inst output`, AL its `Option<()>`, its column claims appended to `claims`,
  the point and slices at `out`.
- `keccak_phase(t, logSteps, evals, scratch, claims, out)` (RDI to R9; rustc passed
  `layout.table_log_heights[OP_KECCAK]` by value and fixed the evaluations' slice to its 6
  entries; `KECCAK`'s point has `logSteps` coordinates, as `tablePhase` gives it): `keccakPhase
  layout evals`, AL its `Option<()>`.
-/

namespace NativeRustcVmX64

open NativeRustcX64 NativeVm.Model LeanVM.Parameters LeanVM.Protocol.Verifier
open NativeRustcVm.Transcript
open NativeRustcVm.KeccakGkr (ClaimAt WeightsAt KeccakOutAt rowsFlat claimBytes scratchBytes
  weightsBytes weightsOff rowsOff rowsBytes outBytes)
open NativeRustcVm (Region Disjoint InAny)

@[expose] public section

/-! ## Stacks -/

/-- `keccak_pi` uses no stack. -/
def keccakPiStack : Nat := 0
/-- The stack `linear_transpose` uses: 7 pushes, `keccak_pi`'s return address and stack. -/
def linearTransposeStack : Nat := 56 + 8 + keccakPiStack
/-- The stack `instance_weights` uses: 6 pushes, its 984-byte frame, `powers`' return address
and stack (above `memcpy`'s). -/
def instanceWeightsStack : Nat := 48 + 984 + 8 + powersStack
/-- The stack `slot_weights` uses: 6 pushes, its 104-byte frame, the return address and the larger
stack of `eq_kernel`'s and `EW::mul`'s. -/
def slotWeightsStack : Nat := 48 + 104 + 8 + max eqKernelStack ewMulStack
/-- The stack `keccak_open` uses: 6 pushes, its 2152-byte frame (`sumcheck`'s and
`slot_weights`' stack argument within), the return address and the largest stack of its
callees' (`memcpy` uses none). -/
def keccakOpenStack : Nat :=
  48 + 2152 + 8 + max sumcheckPlainStack (max slotWeightsStack ewMulStack)
/-- The stack `first_claim` uses: 6 pushes, its 1320-byte frame, the return address and the
largest stack of its callees' (`memcpy` uses none). -/
def firstClaimStack : Nat :=
  48 + 1320 + 8 + max eqKernelStack (max ewMulStack (max dotStack bufEWExtendStack))
/-- The stack `verify_layer` uses: 6 pushes, its 1944-byte frame, then the 16 bytes of stack
arguments (and padding) it pushes for the two `sumcheck`s, or none for the other callees, a
return address and the callee's stack (`memcpy` uses none). -/
def verifyLayerStack : Nat :=
  48 + 1944 + 8 + max (16 + max sumcheckPlainStack sumcheckLayerStack)
    (max (max (max readScalarsStack grindStack) (max squeezeStack instanceWeightsStack))
      (max (max (max polyEvalStack eqKernelStack) (max dotStack linearTransposeStack))
        (max (max sumEStack bitLengthStack) (max ewMulStack bufEWExtendStack))))
/-- The stack `verify_keccak` uses: 6 pushes, its 3240-byte frame, then the stack arguments (and
padding) it pushes for a call (32 bytes for `first_claim`, 48 for `keccak_open`, 16 for
`sumcheck`, none for the others), a return address and the callee's stack (`memcpy` uses none). -/
def verifyKeccakStack : Nat :=
  48 + 3240 + 8 + max (max (32 + firstClaimStack) (48 + keccakOpenStack))
    (max (max (16 + sumcheckPlainStack) verifyLayerStack)
      (max (max (max grindStack sampleChallengesStack) (max readScalarStack readScalarsStack))
        (max (max (max mleStack dotStack) pushClaimStack)
          (max (max bitLengthStack bufEWExtendStack) ewMulStack))))
/-- The stack `keccak_phase` uses: 6 pushes, its 408-byte frame, the 16 bytes of stack arguments
it pushes for `verify_keccak`, its return address and stack (above `memcpy`'s). -/
def keccakPhaseStack : Nat := 48 + 408 + 16 + 8 + verifyKeccakStack

section
variable [Labels]

/-! ## Read-only data -/

/-- The address of `RMFE_PROJECT`. -/
def projectAddr : BitVec 64 := (label NativeRustcVmX64.Vm.Symbols.rodata0Label).toBitVec

/-- The address of `KECCAK_RHO`. -/
def rhoAddr : BitVec 64 := (label NativeRustcVmX64.Vm.Symbols.rodata2Label).toBitVec

/-- `KECCAK_RHO`'s bytes: each offset a little-endian `u32` (`RodataAt`'s `.keccakRho` item). -/
def rhoBytes : List UInt8 := NativeRustcVm.Data.Item.bytes .keccakRho

/-- `RMFE_PROJECT` is at its label. -/
def ProjectAt (m : MachineData) : Prop :=
  NativeRustcVm.WordsAt m.dmem projectAddr rmfeProjectW.toList

/-- `KECCAK_RHO` is at its label. -/
def RhoAt (m : MachineData) : Prop := NativeRustcVm.BytesAt m.dmem rhoAddr rhoBytes

/-- The round constants' region. -/
def rcRegion : Region := ⟨rcAddr, 192⟩
/-- `RMFE_PROJECT`'s region. -/
def projectRegion : Region := ⟨projectAddr, 128⟩
/-- `KECCAK_RHO`'s region. -/
def rhoRegion : Region := ⟨rhoAddr, 100⟩

/-! ## Footprints -/

/-- The `n` bytes of stack below RSP and the return address at RSP as a region. -/
def stackRegion (m : MachineData) (n : Nat) : Region := ⟨stackBelow m n, n + 8⟩

/-- The `k` argument words on the stack above the return address as a region. -/
def argsRegion (m : MachineData) (k : Nat) : Region := ⟨rspOf m + 8#64, 8 * k⟩

/-- The regions a function using `n` bytes of stack writes (`ws`) and reads (`rs`): data memory,
not wrapping; the written ones and the stack (with the return address) pairwise apart, and apart
from the read ones. -/
def Areas (m : MachineData) (n : Nat) (ws rs : List Region) : Prop :=
  (∀ r ∈ ws ++ rs, r.Ok m.dmem) ∧ Disjoint (stackRegion m n :: ws) ∧
    ∀ w ∈ stackRegion m n :: ws, ∀ r ∈ rs, NativeRustcVm.Apart w.addr w.size r.addr r.size

/-- Memory changes only in the regions `ws` and the `n` bytes of stack below RSP. -/
def Writes (m m' : MachineData) (n : Nat) (ws : List Region) : Prop :=
  NativeRustcVm.SameOutside m.dmem m'.dmem (InAny (⟨stackBelow m n, n⟩ :: ws))

/-- `n` elements of `E` from `a` as a region. -/
def ewsRegion (a : BitVec 64) (n : Nat) : Region := ⟨a, 16 * n⟩

/-- The segment kernel of a claim's point exists (`eq_kernel` into four elements): one or two
coordinates past the pack's. -/
def SegmentsFit (logSteps : Nat) (c : KeccakClaimW) : Prop :=
  logSteps - 4 < c.point.size ∧ c.point.size - (logSteps - 4) ≤ 2

/-! ## `keccak_pi` -/

/-- `keccak_pi`'s precondition. -/
def KeccakPiPre (m : MachineData) : Prop := StackOk m keccakPiStack ∧ (reg m .rdi).toNat < 25

/-- `keccak_pi`'s postcondition. -/
def KeccakPiPost (m m' : MachineData) : Prop :=
  (reg m' .rax).toNat = keccakPi (reg m .rdi).toNat ∧ m'.dmem = m.dmem ∧ Saved m m'

/-! ## `linear_transpose` -/

/-- `linear_transpose`'s precondition: the 1600 elements `ws` at `w` (RDI); `g` (RSI), `columns`
(RDX), `out` (RCX) written. -/
def LinearTransposePre (ws : Array EW) (m : MachineData) : Prop :=
  let w := reg m .rdi; let g := reg m .rsi; let col := reg m .rdx; let out := reg m .rcx
  StackOk m linearTransposeStack ∧ RhoAt m ∧ ws.size = keccakBits ∧
    NativeRustcVm.EWsAt m.dmem w ws.toList ∧
    Areas m linearTransposeStack [⟨g, weightsBytes⟩, ⟨col, 5120⟩, ⟨out, weightsBytes⟩]
      [⟨w, weightsBytes⟩, rhoRegion]

/-- `linear_transpose`'s postcondition. -/
def LinearTransposePost (ws : Array EW) (m m' : MachineData) : Prop :=
  let g := reg m .rsi; let col := reg m .rdx; let out := reg m .rcx
  NativeRustcVm.EWsAt m'.dmem out (keccakLinearTranspose ws).toList ∧
    Writes m m' linearTransposeStack [⟨g, weightsBytes⟩, ⟨col, 5120⟩, ⟨out, weightsBytes⟩] ∧
    Saved m m'

/-! ## `instance_weights` -/

/-- `instance_weights`'s precondition: the result's `Buf<EW, 16>` (264 bytes) at RDI. -/
def InstanceWeightsPre (m : MachineData) : Prop :=
  StackOk m instanceWeightsStack ∧ Areas m instanceWeightsStack [⟨reg m .rdi, 264⟩] [] ∧
    GotAt m instanceWeightsStack [(reg m .rdi, 264)] ["memcpy"]

/-- `instance_weights`'s postcondition. -/
def InstanceWeightsPost (m m' : MachineData) : Prop :=
  NativeRustcVm.BufEWAt m'.dmem (reg m .rdi) 16
      (keccakInstanceWeights (ewArg (reg m .rsi) (reg m .rdx))).toList ∧
    Writes m m' instanceWeightsStack [⟨reg m .rdi, 264⟩] ∧ Saved m m'

/-! ## `slot_weights` -/

/-- `slot_weights`'s rows: the stack argument. -/
def slotRows (m : MachineData) : BitVec 64 := stackArg m 0

/-- `slot_weights`'s precondition: the claim `c`'s point at RSI (RDX elements) and bit weights at
RCX; `first` (R8) and `count` (R9) with `1 ≤ count`, `first + count ≤ 2`; the rows at the stack
argument written. -/
def SlotWeightsPre (c : KeccakClaimW) (m : MachineData) : Prop :=
  let pt := reg m .rsi; let w := reg m .rcx; let rows := slotRows m
  StackOk m slotWeightsStack ∧ ArgsOk m 1 ∧ c.point.size = (reg m .rdx).toNat ∧
    NativeRustcVm.EWsAt m.dmem pt c.point.toList ∧ WeightsAt m.dmem w c ∧
    SegmentsFit (reg m .rdi).toNat c ∧ 1 ≤ (reg m .r9).toNat ∧
    (reg m .r8).toNat + (reg m .r9).toNat ≤ keccakSegments ∧
    Areas m slotWeightsStack [⟨rows, rowsBytes⟩]
      [ewsRegion pt c.point.size, ⟨w, weightsBytes⟩, argsRegion m 1]

/-- `slot_weights`'s postcondition. -/
def SlotWeightsPost (c : KeccakClaimW) (m m' : MachineData) : Prop :=
  let rows := slotRows m
  OkAl m' true ∧
    NativeRustcVm.EWsAt m'.dmem rows
      (rowsFlat (keccakSlotWeights (reg m .rdi).toNat c (reg m .r8).toNat (reg m .r9).toNat)) ∧
    Writes m m' slotWeightsStack [⟨rows, rowsBytes⟩] ∧ Saved m m'

/-! ## `keccak_open` -/

/-- `keccak_open`'s `first`: stack argument `0`. -/
def openFirst (m : MachineData) : BitVec 64 := stackArg m 0
/-- `keccak_open`'s `count`: stack argument `1`. -/
def openCount (m : MachineData) : BitVec 64 := stackArg m 1
/-- `keccak_open`'s value: stack arguments `2`, `3`. -/
def openValue (m : MachineData) : EW := ewArg (stackArg m 2) (stackArg m 3)
/-- The slot point's address: stack argument `4`. -/
def openSlot (m : MachineData) : BitVec 64 := stackArg m 4
/-- The rows' address: stack argument `5`. -/
def openRows (m : MachineData) : BitVec 64 := stackArg m 5

/-- `keccak_open`'s precondition: the `TState` at RSI, the claim `c`'s point (RCX, R8) and bit
weights (R9), `first` and `count` as `slot_weights` takes them; the output (RDI), the slot point
(6 elements) and the rows written. -/
def KeccakOpenPre (a : DecArea) (s : TState) (c : KeccakClaimW) (m : MachineData) : Prop :=
  let out := reg m .rdi; let t := reg m .rsi; let pt := reg m .rcx; let w := reg m .r9
  StackOk m keccakOpenStack ∧ ArgsOk m 6 ∧ RcAt m keccakOpenStack ∧ TStateAt m.dmem t a s ∧
    c.point.size = (reg m .r8).toNat ∧ NativeRustcVm.EWsAt m.dmem pt c.point.toList ∧
    WeightsAt m.dmem w c ∧ SegmentsFit (reg m .rdx).toNat c ∧ 1 ≤ (openCount m).toNat ∧
    (openFirst m).toNat + (openCount m).toNat ≤ keccakSegments ∧
    Areas m keccakOpenStack
      [⟨out, 24⟩, ⟨t, tstateBytes⟩, ewsRegion (openSlot m) qkeccakSlotBits, ⟨openRows m, rowsBytes⟩]
      [a.region, ewsRegion pt c.point.size, ⟨w, weightsBytes⟩, rcRegion, argsRegion m 6] ∧
    GotAt m keccakOpenStack
      [(out, 24), (t, tstateBytes), (openSlot m, 16 * qkeccakSlotBits), (openRows m, rowsBytes),
        (a.region.addr, a.region.size), (pt, 16 * c.point.size), (w, weightsBytes),
        (rcAddr, 192), (rspOf m + 8#64, 48)] ["memcpy"]

/-- `keccak_open`'s postcondition. -/
def KeccakOpenPost (a : DecArea) (s : TState) (c : KeccakClaimW) (m m' : MachineData) : Prop :=
  let out := reg m .rdi; let t := reg m .rsi
  let r := (keccakOpen (reg m .rdx).toNat c (openFirst m).toNat (openCount m).toNat
    (openValue m)).run s
  OptEWAt m'.dmem out (r.map (·.1.2.2)) ∧
    (∀ sl ws v s', r = some ((sl, ws, v), s') →
      NativeRustcVm.EWsAt m'.dmem (openSlot m) sl.toList ∧
        NativeRustcVm.EWsAt m'.dmem (openRows m) ws.toList ∧ TStateAt m'.dmem t a s') ∧
    Writes m m' keccakOpenStack
      [⟨out, 24⟩, ⟨t, tstateBytes⟩, ewsRegion (openSlot m) qkeccakSlotBits, ⟨openRows m, rowsBytes⟩] ∧
    Saved m m'

/-! ## `first_claim` -/

/-- `first_claim`'s committed value: stack arguments `0`, `1`. -/
def firstCommitted (m : MachineData) : EW := ewArg (stackArg m 0) (stackArg m 1)
/-- `first_claim`'s bit weights' address: stack argument `2`. -/
def firstWeights (m : MachineData) : BitVec 64 := stackArg m 2

/-- `first_claim`'s precondition: `inst` at RSI (RDX elements, at most 30), the segment (RCX, one
element), the lane point (R8, five), the output lanes (R9, 25); the result (RDI, 776 bytes) and
the bit weights written. -/
def FirstClaimPre (inst segment lanePoint output : Array EW) (m : MachineData) : Prop :=
  let out := reg m .rdi; let ip := reg m .rsi
  StackOk m firstClaimStack ∧ ArgsOk m 3 ∧ inst.size = (reg m .rdx).toNat ∧ inst.size ≤ 30 ∧
    NativeRustcVm.EWsAt m.dmem ip inst.toList ∧
    segment.size = keccakSegmentBits ∧ NativeRustcVm.EWsAt m.dmem (reg m .rcx) segment.toList ∧
    lanePoint.size = keccakLaneBits ∧ NativeRustcVm.EWsAt m.dmem (reg m .r8) lanePoint.toList ∧
    output.size = 25 ∧ NativeRustcVm.EWsAt m.dmem (reg m .r9) output.toList ∧
    Areas m firstClaimStack [⟨out, 8 + claimBytes⟩, ⟨firstWeights m, weightsBytes⟩]
      [ewsRegion ip inst.size, ewsRegion (reg m .rcx) 1, ewsRegion (reg m .r8) 5,
        ewsRegion (reg m .r9) 25, argsRegion m 3] ∧
    GotAt m firstClaimStack
      [(out, 8 + claimBytes), (firstWeights m, weightsBytes), (ip, 16 * inst.size),
        (reg m .rcx, 16), (reg m .r8, 80), (reg m .r9, 400), (rspOf m + 8#64, 24)] ["memcpy"]

/-- `first_claim`'s postcondition. -/
def FirstClaimPost (inst segment lanePoint output : Array EW) (m m' : MachineData) : Prop :=
  let out := reg m .rdi
  let c := keccakFirstClaim inst segment lanePoint output (firstCommitted m)
  NativeRustcVm.WordAt m'.dmem out 1 ∧ ClaimAt m'.dmem (off out 8) c ∧
    WeightsAt m'.dmem (firstWeights m) c ∧
    Writes m m' firstClaimStack [⟨out, 8 + claimBytes⟩, ⟨firstWeights m, weightsBytes⟩] ∧
    Saved m m'

/-! ## `verify_layer` -/

/-- The part of the scratch `verify_layer` writes: the running claim's bit weights, the layer's
weights, `g`, the columns, the local equality kernel. -/
def layerRegion (scratch : BitVec 64) : Region := ⟨off scratch weightsOff, rowsOff - weightsOff⟩

/-- `verify_layer`'s precondition: the `TState` at RDI, `logSteps` (RSI), `step < 12` (RDX), the
claim `c` at RCX, its bit weights at the scratch's (R8) `weights`. -/
def VerifyLayerPre (a : DecArea) (s : TState) (c : KeccakClaimW) (m : MachineData) : Prop :=
  let t := reg m .rdi; let cp := reg m .rcx; let sc := reg m .r8
  StackOk m verifyLayerStack ∧ RcAt m verifyLayerStack ∧ ProjectAt m ∧ RhoAt m ∧
    TStateAt m.dmem t a s ∧ ClaimAt m.dmem cp c ∧ WeightsAt m.dmem (off sc weightsOff) c ∧
    (reg m .rdx).toNat < keccakDepth ∧ SegmentsFit (reg m .rsi).toNat c ∧
    Areas m verifyLayerStack [⟨t, tstateBytes⟩, ⟨cp, claimBytes⟩, ⟨sc, scratchBytes⟩]
      [a.region, rcRegion, projectRegion, rhoRegion] ∧
    GotAt m verifyLayerStack
      [(t, tstateBytes), (cp, claimBytes), (sc, scratchBytes), (a.region.addr, a.region.size),
        (rcAddr, 192), (projectAddr, 128), (rhoAddr, 100)] ["memcpy"]

/-- `verify_layer`'s postcondition. -/
def VerifyLayerPost (a : DecArea) (s : TState) (c : KeccakClaimW) (m m' : MachineData) : Prop :=
  let t := reg m .rdi; let cp := reg m .rcx; let sc := reg m .r8
  let r := (verifyKeccakLayer (reg m .rsi).toNat (reg m .rdx).toNat c).run s
  OkAl m' r.isSome ∧
    (∀ c' s', r = some (c', s') → TStateAt m'.dmem t a s' ∧ ClaimAt m'.dmem cp c' ∧
      WeightsAt m'.dmem (off sc weightsOff) c') ∧
    Writes m m' verifyLayerStack [⟨t, tstateBytes⟩, ⟨cp, claimBytes⟩, layerRegion sc] ∧ Saved m m'

/-! ## `verify_keccak` -/

/-- `verify_keccak`'s column claims: stack argument `0`. -/
def keccakClaims (m : MachineData) : BitVec 64 := stackArg m 0
/-- `verify_keccak`'s `KeccakOutW`: stack argument `1`. -/
def keccakOutArg (m : MachineData) : BitVec 64 := stackArg m 1

/-- `verify_keccak`'s precondition: the `TState` at RDI, `logSteps` (RSI) at most 30, `inst` at RDX
(RCX = `logSteps` elements), the 25 output lanes at R8; the scratch (R9), the column claims `cs`
(stack argument `0`, one short of full at most) and `KeccakOutW` (stack argument `1`) written. -/
def VerifyKeccakPre (a : DecArea) (s : TState) (cs : Array ColumnClaimW) (inst output : Array EW)
    (m : MachineData) : Prop :=
  let t := reg m .rdi; let ip := reg m .rdx; let op := reg m .r8
  let sc := reg m .r9; let cl := keccakClaims m; let out := keccakOutArg m
  StackOk m verifyKeccakStack ∧ ArgsOk m 2 ∧ RcAt m verifyKeccakStack ∧ ProjectAt m ∧ RhoAt m ∧
    TStateAt m.dmem t a s ∧ NativeRustcVm.Layout.ClaimsWAt m.dmem cl cs ∧
    cs.size < NativeRustcVm.Layout.claimCap ∧
    inst.size = (reg m .rcx).toNat ∧ inst.size = (reg m .rsi).toNat ∧ inst.size ≤ 30 ∧
    NativeRustcVm.EWsAt m.dmem ip inst.toList ∧
    output.size = 25 ∧ NativeRustcVm.EWsAt m.dmem op output.toList ∧
    Areas m verifyKeccakStack
      [⟨t, tstateBytes⟩, ⟨sc, scratchBytes⟩, ⟨cl, NativeRustcVm.Layout.claimsBytes⟩, ⟨out, outBytes⟩]
      [a.region, ewsRegion ip inst.size, ewsRegion op 25, rcRegion, projectRegion, rhoRegion,
        argsRegion m 2] ∧
    GotAt m verifyKeccakStack
      [(t, tstateBytes), (sc, scratchBytes), (cl, NativeRustcVm.Layout.claimsBytes), (out, outBytes),
        (a.region.addr, a.region.size), (ip, 16 * inst.size), (op, 400),
        (rcAddr, 192), (projectAddr, 128), (rhoAddr, 100), (rspOf m + 8#64, 16)] ["memcpy"]

/-- `verify_keccak`'s postcondition. -/
def VerifyKeccakPost (a : DecArea) (s : TState) (cs : Array ColumnClaimW) (inst output : Array EW)
    (m m' : MachineData) : Prop :=
  let t := reg m .rdi; let sc := reg m .r9; let cl := keccakClaims m; let out := keccakOutArg m
  let r := (verifyKeccak (reg m .rsi).toNat inst output).run s
  OkAl m' r.isSome ∧
    (∀ outs pt sl s', r = some ((outs, pt, sl), s') → TStateAt m'.dmem t a s' ∧
      NativeRustcVm.Layout.ClaimsWAt m'.dmem cl (cs ++ outs) ∧ KeccakOutAt m'.dmem out pt sl) ∧
    Writes m m' verifyKeccakStack
      [⟨t, tstateBytes⟩, ⟨sc, scratchBytes⟩, ⟨cl, NativeRustcVm.Layout.claimsBytes⟩, ⟨out, outBytes⟩] ∧
    Saved m m'

/-! ## `keccak_phase` -/

/-- `keccak_phase`'s precondition: the `TState` at RDI, `logSteps` (RSI) `layout`'s log-height of
`KECCAK`, the tables' evaluations `evals` at RDX, `KECCAK`'s point of `logSteps` coordinates; the
scratch (RCX), the column claims `cs` (R8) and `KeccakOutW` (R9) written. -/
def KeccakPhasePre (a : DecArea) (s : TState) (cs : Array ColumnClaimW) (layout : LayoutW)
    (evals : Array (Array EW × Array EW)) (m : MachineData) : Prop :=
  let t := reg m .rdi; let ev := reg m .rdx; let sc := reg m .rcx
  let cl := reg m .r8; let out := reg m .r9
  StackOk m keccakPhaseStack ∧ RcAt m keccakPhaseStack ∧ ProjectAt m ∧ RhoAt m ∧
    TStateAt m.dmem t a s ∧ NativeRustcVm.Layout.ClaimsWAt m.dmem cl cs ∧
    cs.size < NativeRustcVm.Layout.claimCap ∧
    NativeRustcVm.Tables.TableEvalsAt m.dmem ev evals ∧
    (reg m .rsi).toNat = layout.tableLogHeights.getD opKeccak 0 ∧
    (evals.getD opKeccak (#[], #[])).1.size = (reg m .rsi).toNat ∧
    keccakOut ≤ (evals.getD opKeccak (#[], #[])).2.size ∧
    Areas m keccakPhaseStack
      [⟨t, tstateBytes⟩, ⟨sc, scratchBytes⟩, ⟨cl, NativeRustcVm.Layout.claimsBytes⟩, ⟨out, outBytes⟩]
      [a.region, ⟨ev, NativeRustcVm.Tables.tableEvalsBytes⟩, rcRegion, projectRegion, rhoRegion] ∧
    GotAt m keccakPhaseStack
      [(t, tstateBytes), (sc, scratchBytes), (cl, NativeRustcVm.Layout.claimsBytes), (out, outBytes),
        (a.region.addr, a.region.size), (ev, NativeRustcVm.Tables.tableEvalsBytes),
        (rcAddr, 192), (projectAddr, 128), (rhoAddr, 100)] ["memcpy"]

/-- `keccak_phase`'s postcondition. -/
def KeccakPhasePost (a : DecArea) (s : TState) (cs : Array ColumnClaimW) (layout : LayoutW)
    (evals : Array (Array EW × Array EW)) (m m' : MachineData) : Prop :=
  let t := reg m .rdi; let sc := reg m .rcx; let cl := reg m .r8; let out := reg m .r9
  let r := (keccakPhase layout evals).run s
  OkAl m' r.isSome ∧
    (∀ outs pt sl s', r = some ((outs, pt, sl), s') → TStateAt m'.dmem t a s' ∧
      NativeRustcVm.Layout.ClaimsWAt m'.dmem cl (cs ++ outs) ∧ KeccakOutAt m'.dmem out pt sl) ∧
    Writes m m' keccakPhaseStack
      [⟨t, tstateBytes⟩, ⟨sc, scratchBytes⟩, ⟨cl, NativeRustcVm.Layout.claimsBytes⟩, ⟨out, outBytes⟩] ∧
    Saved m m'

end

end

end NativeRustcVmX64
