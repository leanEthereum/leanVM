module

public import NativeRustcX64.Spec.Keccak
public import NativeRustcX64.Spec.Got
public import NativeRustc.Xmss.Model

/-!
# The contract of `LayerSignature::read`

The System V ABI passes the output in RDI and a mutable slice descriptor in RSI. The descriptor
contains the input pointer and its remaining length. Reading a layer consumes 1200 bytes,
updates both descriptor words, and writes the path, chain values and randomizer in rustc's
1200-byte layout. Only the output, descriptor and stack may change.
-/

namespace NativeRustcX64

open NativeRustc

@[expose] public section


/-- Six saved registers, the frame, and the return address of `memcpy`. -/
def layerReadStack : Nat := 48 + 1880 + 8

/-- The address of the first unconsumed input byte. -/
def LayerReadPre.input (m : MachineData) : BitVec 64 :=
  BitVec.ofNat 64 (leNat (bytesOf m.dmem (reg m .rsi) 8))

/-- The number of unconsumed input bytes. -/
def LayerReadPre.remaining (m : MachineData) : Nat :=
  leNat (bytesOf m.dmem (reg m .rsi + 8#64) 8)

/-- The layer's wire bytes. -/
def LayerReadPre.bytes (m : MachineData) : List UInt8 :=
  bytesOf m.dmem (LayerReadPre.input m) 1200

/-- A mapped, nonwrapping buffer disjoint from the stack and return address. -/
def LayerReadPre.Buf (m : MachineData) (a : BitVec 64) (n : Nat) : Prop :=
  Mapped m.dmem a n ∧ NoWrap a n ∧ Apart a n (stackBelow m layerReadStack) (layerReadStack + 8)

/-- The slice has enough bytes for one layer; the three buffers and GOT slot are disjoint. -/
def LayerReadPre [Labels] (m : MachineData) : Prop :=
  let o := reg m .rdi; let c := reg m .rsi; let b := LayerReadPre.input m
  StackOk m layerReadStack ∧ 1200 ≤ LayerReadPre.remaining m ∧
    LayerReadPre.remaining m < 2 ^ 64 ∧
    LayerReadPre.Buf m o 1200 ∧ LayerReadPre.Buf m c 16 ∧ LayerReadPre.Buf m b 1200 ∧
    Apart o 1200 c 16 ∧ Apart o 1200 b 1200 ∧ Apart c 16 b 1200 ∧
    GotAt m layerReadStack [(o, 1200), (c, 16), (b, 1200)] ["memcpy"]

/-- The parsed layer, advanced slice descriptor, and frame condition. -/
def LayerReadPost (m m' : MachineData) : Prop :=
  let o := reg m .rdi; let c := reg m .rsi
  BytesAt m'.dmem o (Xmss.takeLayer (LayerReadPre.bytes m) 0).1.memBytes ∧
    BytesAt m'.dmem c
      (LeanVM.Protocol.KeccakHash.wordBytes
        (UInt64.ofBitVec (LayerReadPre.input m + 1200#64))) ∧
    BytesAt m'.dmem (c + 8#64)
      (LeanVM.Protocol.KeccakHash.wordBytes (LayerReadPre.remaining m - 1200).toUInt64) ∧
    SameOutside m.dmem m'.dmem (fun p ↦ InRange o 1200 p ∨ InRange c 16 p ∨
      InRange (stackBelow m layerReadStack) layerReadStack p) ∧ Saved m m'

end

end NativeRustcX64
