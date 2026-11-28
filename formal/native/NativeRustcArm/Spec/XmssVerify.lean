module

public import NativeRustcArm.Spec.WotsLeaf
public import NativeRustcArm.Spec.LayerRead

/-!
# The contract of `xmss_verify`

`xmss_verify(ctx)` (X0, `rustc/xmss.rs`): the context's 309 input words `w` from byte 1024, each
8 little-endian bytes. It returns `1` in X0 if `Xmss.xmssVerify w` (`LeanXmss.verifyWithKeccak` of
the key, message and signature the words encode, `Xmss.verify_eq`), else `0`, with the callee-saved
registers and SP kept, and changes no byte outside its stack (`xmssVerifyStack` bytes below SP: its
frame of `96 + 4096 + 1680` and `wots_leaf`'s, the deepest of its callees'). It reads the round
constants (`RcAt`).
-/

namespace NativeRustcArm

open NativeRustc

@[expose] public section

/-- The number of input words. -/
def xmssInputWords : Nat := 309

/-- `xmss_verify`'s frame. -/
def xmssVerifyFrame : Nat := 96 + 4096 + 1680

/-- The stack `xmss_verify` uses: its frame and `wots_leaf`'s, the deepest callee's. -/
def xmssVerifyStack : Nat := xmssVerifyFrame + wotsLeafStack

/-- The input words' address: byte 1024 of the context. -/
def xmssInput (m : MachineData) : BitVec 64 := m.regs.X0.toBitVec + BitVec.ofNat 64 1024

section
variable [Labels]

/-- `xmss_verify`'s precondition on the input words `w`. -/
def XmssVerifyPre (w : Nat → UInt64) (m : MachineData) : Prop :=
  StackOk m xmssVerifyStack ∧ RcAt m xmssVerifyStack ∧
    (∀ i < xmssInputWords, BytesAt m.dmem (xmssInput m + BitVec.ofNat 64 (8 * i))
      (LeanVM.Protocol.KeccakHash.wordBytes (w i))) ∧
    NoWrap (xmssInput m) (8 * xmssInputWords) ∧
    Apart (xmssInput m) (8 * xmssInputWords) (stackBelow m xmssVerifyStack) xmssVerifyStack

/-- `xmss_verify`'s postcondition on the input words `w`. -/
def XmssVerifyPost (w : Nat → UInt64) (m m' : MachineData) : Prop :=
  m'.regs.X0 = (if Xmss.xmssVerify w then 1 else 0) ∧
    SameOutside m.dmem m'.dmem (InRange (stackBelow m xmssVerifyStack) xmssVerifyStack) ∧ Saved m m'

end

end

end NativeRustcArm
