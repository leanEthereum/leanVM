module

public import NativeRustcX64.Spec.WotsLeaf
public import NativeRustcX64.Spec.LayerRead

/-!
# The contract of `xmss_verify` (x86-64)

`xmss_verify(ctx)` (RDI, `rustc/xmss.rs`): the context's 309 input words `w` from byte 1024, each
8 little-endian bytes. It returns `1` in RAX if `Xmss.xmssVerify w` (`LeanXmss.verifyWithKeccak` of
the key, message and signature the words encode, `Xmss.verify_eq`), else `0`, with the callee-saved
registers kept (and RSP 8 above, `Spec`), and changes no byte outside its stack
(`xmssVerifyStack` bytes below RSP: its pushes and frame of `48 + 5736`, the two stack arguments
and the return address of its call of `wots_leaf`, and `wots_leaf`'s stack, the deepest of its
callees'). It reads the round constants (`RcAt`) and the `memcpy` and `memset` GOT slots,
whose eight-byte label pointers must occupy nonwrapping, mutually disjoint slots apart from
the stack, return address and input words (`GotAt`).
-/

namespace NativeRustcX64

open NativeRustc

@[expose] public section

/-- The number of input words. -/
def xmssInputWords : Nat := 309

/-- `xmss_verify`'s pushes and frame. -/
def xmssVerifyFrame : Nat := 48 + 5736

/-- The stack `xmss_verify` uses: its frame, `wots_leaf`'s two stack arguments and return address,
and `wots_leaf`'s stack, the deepest callee's. -/
def xmssVerifyStack : Nat := xmssVerifyFrame + 24 + wotsLeafStack

/-- The input words' address: byte 1024 of the context. -/
def xmssInput (m : MachineData) : BitVec 64 := reg m .rdi + BitVec.ofNat 64 1024

section
variable [Labels]

/-- `xmss_verify`'s precondition on the input words `w`. -/
def XmssVerifyPre (w : Nat → UInt64) (m : MachineData) : Prop :=
  StackOk m xmssVerifyStack ∧ RcAt m xmssVerifyStack ∧
    (∀ i < xmssInputWords, BytesAt m.dmem (xmssInput m + BitVec.ofNat 64 (8 * i))
      (LeanVM.Protocol.KeccakHash.wordBytes (w i))) ∧
    NoWrap (xmssInput m) (8 * xmssInputWords) ∧
    Apart (xmssInput m) (8 * xmssInputWords) (stackBelow m xmssVerifyStack) (xmssVerifyStack + 8) ∧
    GotAt m xmssVerifyStack [(xmssInput m, 8 * xmssInputWords)] ["memcpy", "memset"]

/-- `xmss_verify`'s postcondition on the input words `w`. -/
def XmssVerifyPost (w : Nat → UInt64) (m m' : MachineData) : Prop :=
  reg m' .rax = (if Xmss.xmssVerify w then 1 else 0) ∧
    SameOutside m.dmem m'.dmem (InRange (stackBelow m xmssVerifyStack) xmssVerifyStack) ∧
    Saved m m'

end

end

end NativeRustcX64
