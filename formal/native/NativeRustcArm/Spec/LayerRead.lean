module

public import NativeRustcArm.Spec.Keccak
public import NativeRustc.Xmss.Model

/-!
# The contract of `LayerSignature::read`

`read(out, rest)` (X0, X1) reads a layer from the slice descriptor at `rest`: its
first word is the data pointer and its second word the remaining byte count.
It writes the parsed layer in rustc's layout, advances the pointer by 1200,
subtracts 1200 from the count, and preserves memory outside the output,
descriptor and stack frame. The input prefix is preserved.
-/

namespace NativeRustcArm

open NativeRustc

@[expose] public section


/-- The reader's stack frame, including its saved registers. -/
def layerReadStack : Nat := 80 + 1856

/-- The data pointer in the slice descriptor. -/
def LayerReadPre.data (m : MachineData) : BitVec 64 :=
  BitVec.ofNat 64 (leNat (bytesOf m.dmem m.regs.X1.toBitVec 8))

/-- The remaining byte count in the slice descriptor. -/
def LayerReadPre.remaining (m : MachineData) : Nat :=
  (BitVec.ofNat 64 (leNat (bytesOf m.dmem (m.regs.X1.toBitVec + 8) 8))).toNat

/-- Only the layer's prefix is read. -/
def LayerReadPre.bytes (m : MachineData) : List UInt8 :=
  bytesOf m.dmem (LayerReadPre.data m) 1200

/-- A non-wrapping mapped buffer disjoint from the reader's frame. -/
def LayerReadPre.Buf (m : MachineData) (a : BitVec 64) (n : Nat) : Prop :=
  Mapped m.dmem a n ∧ NoWrap a n ∧ Apart a n (stackBelow m layerReadStack) layerReadStack

/-- The reader requires one complete layer and a disjoint mutable descriptor. -/
def LayerReadPre (m : MachineData) : Prop :=
  let o := m.regs.X0.toBitVec; let c := m.regs.X1.toBitVec; let b := LayerReadPre.data m
  StackOk m layerReadStack ∧ 1200 ≤ LayerReadPre.remaining m ∧
    LayerReadPre.Buf m o 1200 ∧ LayerReadPre.Buf m c 16 ∧ LayerReadPre.Buf m b 1200 ∧
    Apart o 1200 c 16 ∧ Apart o 1200 b 1200 ∧ Apart c 16 b 1200

/-- The parsed layer, updated slice descriptor, and preserved frame. -/
def LayerReadPost (m m' : MachineData) : Prop :=
  let o := m.regs.X0.toBitVec; let c := m.regs.X1.toBitVec
  BytesAt m'.dmem o (Xmss.takeLayer (LayerReadPre.bytes m) 0).1.memBytes ∧
    BytesAt m'.dmem c
      (LeanVM.Protocol.KeccakHash.wordBytes (UInt64.ofBitVec (LayerReadPre.data m + 1200))) ∧
    BytesAt m'.dmem (c + 8)
      (LeanVM.Protocol.KeccakHash.wordBytes (LayerReadPre.remaining m - 1200).toUInt64) ∧
    SameOutside m.dmem m'.dmem (fun p ↦ InRange o 1200 p ∨ InRange c 16 p ∨
      InRange (stackBelow m layerReadStack) layerReadStack p) ∧ Saved m m'

end

end NativeRustcArm
