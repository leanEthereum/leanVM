module

public import NativeRustcArm.Spec.Keccak
public import NativeRustc.Xmss.Model

/-!
# The contract of `lean_xmss::wots::wots_leaf`

`wots_leaf(out, pp, layer, e, message, message_len, randomizer, values)` (X0 to X7): the public
parameter's 16 bytes at `pp`, the layer in X2, the key index in W3, `message_len` bytes of the
message at `message`, the randomizer's 16 bytes at `randomizer`, the 58 chain values' 16 bytes each
at `values`. It writes `Xmss.wotsLeaf` of them at `out` in rustc's layout of
`Option<([u8; 58], [u8; 16])>` (`Xmss.WotsLeafOut`), and changes no byte outside the 75 at `out`
and its stack (`wotsLeafStack` bytes below SP: its frame of `96 + 2656` and `Hasher::finalize`'s,
the deepest of its callees'). The inputs may overlap `out`: it writes `out` after its last read.
-/

namespace NativeRustcArm

open NativeRustc

@[expose] public section

/-- The stack `wots_leaf` uses: its frame and `Hasher::finalize`'s, the deepest callee's. -/
def wotsLeafStack : Nat := 96 + 2656 + finalizeStack

/-- The public parameter `wots_leaf` reads. -/
def WotsLeafPre.pp (m : MachineData) : List UInt8 := bytesOf m.dmem m.regs.X1.toBitVec 16

/-- The message `wots_leaf` reads. -/
def WotsLeafPre.message (m : MachineData) : List UInt8 :=
  bytesOf m.dmem m.regs.X4.toBitVec m.regs.X5.toNat

/-- The randomizer `wots_leaf` reads. -/
def WotsLeafPre.randomizer (m : MachineData) : List UInt8 := bytesOf m.dmem m.regs.X6.toBitVec 16

/-- The 58 chain values `wots_leaf` reads. -/
def WotsLeafPre.values (m : MachineData) : List (List UInt8) :=
  (List.range 58).map fun i ↦ bytesOf m.dmem (m.regs.X7.toBitVec + BitVec.ofNat 64 (16 * i)) 16

/-- An input of `n` bytes from `a`: data memory, not wrapping around, apart from the stack. -/
def WotsLeafPre.Input (m : MachineData) (a : BitVec 64) (n : Nat) : Prop :=
  Mapped m.dmem a n ∧ NoWrap a n ∧ Apart a n (stackBelow m wotsLeafStack) wotsLeafStack

section
variable [Labels]

/-- `wots_leaf`'s precondition. -/
def WotsLeafPre (m : MachineData) : Prop :=
  let o := m.regs.X0.toBitVec
  StackOk m wotsLeafStack ∧ RcAt m wotsLeafStack ∧
    WotsLeafPre.Input m o 75 ∧
    WotsLeafPre.Input m m.regs.X1.toBitVec 16 ∧
    WotsLeafPre.Input m m.regs.X4.toBitVec m.regs.X5.toNat ∧
    WotsLeafPre.Input m m.regs.X6.toBitVec 16 ∧
    WotsLeafPre.Input m m.regs.X7.toBitVec (16 * 58)

/-- `wots_leaf`'s postcondition. -/
def WotsLeafPost (m m' : MachineData) : Prop :=
  let o := m.regs.X0.toBitVec
  Xmss.WotsLeafOut (bytesOf m'.dmem o 75)
      (Xmss.wotsLeaf (WotsLeafPre.pp m) m.regs.X2.toNat m.regs.X3.toUInt32
        (WotsLeafPre.message m) (WotsLeafPre.randomizer m) (WotsLeafPre.values m)) ∧
    SameOutside m.dmem m'.dmem (fun p ↦ InRange o 75 p ∨
      InRange (stackBelow m wotsLeafStack) wotsLeafStack p) ∧ Saved m m'

end

end

end NativeRustcArm
