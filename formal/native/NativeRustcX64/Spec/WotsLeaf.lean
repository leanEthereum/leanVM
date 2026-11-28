module

public import NativeRustcX64.Code.Common.Finalize.Names
public import NativeRustcX64.Code.Common.KeccakF.Names
public import NativeRustcX64.Code.Common.Memcpy.Names
public import NativeRustcX64.Code.Common.Memset.Names
public import NativeRustcX64.Code.Common.Update.Names

public import NativeRustcX64.Spec.Keccak
public import NativeRustcX64.Spec.Got
public import NativeRustc.Xmss.Model

/-!
# The contract of `lean_xmss::wots::wots_leaf`

`wots_leaf(out, pp, layer, e, message, message_len, randomizer, values)`: `out` in RDI, `pp` in
RSI, the layer in RDX, the key index in ECX, `message` in R8, `message_len` in R9, and the
pointers `randomizer` and `values` on the stack, at RSP + 8 and RSP + 16 (above the return
address). The public parameter's 16 bytes at `pp`, `message_len` bytes of the message at
`message`, the randomizer's 16 bytes at `randomizer`, the 58 chain values' 16 bytes each at
`values`. It writes `Xmss.wotsLeaf` of them at `out` in rustc's layout of
`Option<([u8; 58], [u8; 16])>`, the tag of `Some` being 1 (`WotsLeafOut1`), and changes no byte outside the 75 at `out`
and its stack (`wotsLeafStack` bytes below RSP: its pushes and frame of `48 + 2712`, the return
address of a call and `Hasher::finalize`'s stack, the deepest of its callees'). The inputs may
overlap `out`: it writes `out` after its last read.
-/

namespace NativeRustcX64

open NativeRustc

@[expose] public section

/-- The stack `wots_leaf` uses: its six pushes, its frame, a callee's return address and
`Hasher::finalize`'s stack, the deepest callee's. -/
def wotsLeafStack : Nat := 48 + 2712 + 8 + finalizeStack

/-- The 8 bytes of `d` at `a` as a pointer. -/
def ptrAt (d : DataMem) (a : BitVec 64) : BitVec 64 :=
  BitVec.ofInt 64 ((Mem.loadInt d a 8).getD 0)

/-- The randomizer's address, the stack argument at RSP + 8. -/
def WotsLeafPre.rndPtr (m : MachineData) : BitVec 64 := ptrAt m.dmem (rspOf m + 8#64)

/-- The chain values' address, the stack argument at RSP + 16. -/
def WotsLeafPre.valuesPtr (m : MachineData) : BitVec 64 := ptrAt m.dmem (rspOf m + 16#64)

/-- The public parameter `wots_leaf` reads. -/
def WotsLeafPre.pp (m : MachineData) : List UInt8 := bytesOf m.dmem (reg m .rsi) 16

/-- The message `wots_leaf` reads. -/
def WotsLeafPre.message (m : MachineData) : List UInt8 :=
  bytesOf m.dmem (reg m .r8) (reg m .r9).toNat

/-- The randomizer `wots_leaf` reads. -/
def WotsLeafPre.randomizer (m : MachineData) : List UInt8 :=
  bytesOf m.dmem (WotsLeafPre.rndPtr m) 16

/-- The 58 chain values `wots_leaf` reads. -/
def WotsLeafPre.values (m : MachineData) : List (List UInt8) :=
  (List.range 58).map fun i ↦
    bytesOf m.dmem (WotsLeafPre.valuesPtr m + BitVec.ofNat 64 (16 * i)) 16

/-- The layer. -/
def WotsLeafPre.layer (m : MachineData) : Nat := (reg m .rdx).toNat

/-- The key index, ECX. -/
def WotsLeafPre.e (m : MachineData) : UInt32 := UInt32.ofBitVec ((reg m .rcx).setWidth 32)

/-- An input of `n` bytes from `a`: data memory, not wrapping around, apart from the stack, the
return address and the stack arguments. -/
def WotsLeafPre.Input (m : MachineData) (a : BitVec 64) (n : Nat) : Prop :=
  Mapped m.dmem a n ∧ NoWrap a n ∧ Apart a n (stackBelow m wotsLeafStack) (wotsLeafStack + 24)

section
variable [Labels]

/-- `wots_leaf`'s precondition: the stack, the round constants, the stack arguments' 16 bytes
mapped, not wrapping with the return address below them, and the inputs. The actual `memcpy`
and `memset` GOT pointers occupy nonwrapping, mutually disjoint slots, apart from the stack,
return address, stack arguments, output, public parameters, message, randomizer, and values. -/
def WotsLeafPre (m : MachineData) : Prop :=
  let o := reg m .rdi
  StackOk m wotsLeafStack ∧ RcAt m wotsLeafStack ∧
    Mapped m.dmem (rspOf m + 8#64) 16 ∧ NoWrap (rspOf m) 24 ∧
    WotsLeafPre.Input m o 75 ∧
    WotsLeafPre.Input m (reg m .rsi) 16 ∧
    WotsLeafPre.Input m (reg m .r8) (reg m .r9).toNat ∧
    WotsLeafPre.Input m (WotsLeafPre.rndPtr m) 16 ∧
    WotsLeafPre.Input m (WotsLeafPre.valuesPtr m) (16 * 58) ∧
    GotAt m wotsLeafStack
      [(o, 75), (reg m .rsi, 16), (reg m .r8, (reg m .r9).toNat),
        (WotsLeafPre.rndPtr m, 16), (WotsLeafPre.valuesPtr m, 16 * 58),
        (rspOf m + 8#64, 16)] ["memcpy", "memset"]

/-- The 75 bytes at `out` as x86 `wots_leaf` writes them: `None` a tag `0`, `Some (x, leaf)` the
tag `1`, the codeword's 58 digits and the leaf's 16 bytes. -/
def WotsLeafOut1 (out : List UInt8) : Option (List UInt8 × List UInt8) → Prop
  | none => out.head? = some 0
  | some (x, leaf) => out.take 75 = 1 :: (x ++ leaf)

/-- `wots_leaf`'s postcondition. -/
def WotsLeafPost (m m' : MachineData) : Prop :=
  let o := reg m .rdi
  WotsLeafOut1 (bytesOf m'.dmem o 75)
      (Xmss.wotsLeaf (WotsLeafPre.pp m) (WotsLeafPre.layer m) (WotsLeafPre.e m)
        (WotsLeafPre.message m) (WotsLeafPre.randomizer m) (WotsLeafPre.values m)) ∧
    SameOutside m.dmem m'.dmem (fun p ↦ InRange o 75 p ∨
      InRange (stackBelow m wotsLeafStack) wotsLeafStack p) ∧ Saved m m'

end


/-- **The contracts of `wots_leaf`'s callees**: `memcpy`, `memset`, `Hasher::update`,
`Hasher::finalize`, `keccak_f`. -/
def WotsLeafCallees [Host] : Prop :=
  Spec (label NativeRustcX64.Common.Memcpy.entryLabel) MemcpyPre MemcpyPost ∧ Spec (label NativeRustcX64.Common.Memset.entryLabel) MemsetPre MemsetPost ∧
    Spec (label NativeRustcX64.Common.Update.entryLabel) UpdatePre UpdatePost ∧
    Spec (label NativeRustcX64.Common.Finalize.entryLabel) FinalizePre FinalizePost ∧
    Spec (label NativeRustcX64.Common.KeccakF.entryLabel) KeccakFPre KeccakFPost

end

end NativeRustcX64
