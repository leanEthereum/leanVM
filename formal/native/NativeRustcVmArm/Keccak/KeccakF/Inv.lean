module

public import NativeRustcVmArm.Keccak.Common

/-!
# `keccak_f`'s loop invariant

At the head of the round loop `.LKeccakF_1` after `i` rounds, from the machine state `m0` at
`keccak_f`'s entry: SP is the frame's base (`frame`, 400 bytes below the entry's SP), the
counter X9 is `16 + 8 i`; the 25 lanes of the state after `i` rounds (`stAfter`) are in 20
registers (`laneRegs`) and 5 frame slots (`laneSlots`); the round constants are in the frame at
112; the frame slots `savedSlots` hold the entry's state pointer X0, its X29, X30 and its
callee-saved X19 to X28; memory outside the frame is the entry's, and every byte mapped at entry
is mapped (`At`).
-/

namespace NativeRustcVmArm.KeccakF

open NativeRustcArm NativeRustcArm.Sym NativeRustc NativeRustc.Keccak LeanVM.Semantics
open NativeRustcArm.KeccakF (WordAt)

@[expose] public section

/-- The frame's base: SP in the loop. -/
def frame (m0 : MachineData) : BitVec 64 := stackBelow m0 NativeRustcVmArm.keccakFStack

/-- The state after `i` rounds, from the 200 bytes at the entry's X0. -/
def stAfter (m0 : MachineData) (i : Nat) : KeccakState :=
  roundsTo (stateOf (bytesOf m0.dmem m0.regs.X0.toBitVec 200)) i

/-- The registers that hold lanes at the loop head, with the lanes' indices. -/
def laneRegs : List (XReg × Nat) :=
  [(.X27, 0), (.X11, 1), (.X18, 4), (.X5, 5), (.X12, 6), (.X16, 8), (.X10, 10), (.X0, 11),
    (.X17, 12), (.X6, 14), (.X25, 15), (.X2, 16), (.X1, 17), (.X4, 18), (.X22, 19), (.X3, 20),
    (.X21, 21), (.X7, 22), (.X26, 23), (.X23, 24)]

/-- The frame slots that hold lanes at the loop head, with the lanes' indices. -/
def laneSlots : List (Nat × Nat) := [(56, 7), (64, 9), (72, 3), (80, 13), (88, 2)]

/-- The frame slots that hold the entry's registers. -/
def savedSlots : List (Nat × XReg) :=
  [(16, .X0), (304, .X29), (312, .X30), (320, .X28), (328, .X27), (336, .X26), (344, .X25),
    (352, .X24), (360, .X23), (368, .X22), (376, .X21), (384, .X20), (392, .X19)]

/-- **The loop invariant** after `i` rounds, from the entry's state `m0`. -/
structure At (m0 : MachineData) (i : Nat) (m : MachineData) : Prop where
  sp : m.regs.SP.toBitVec = frame m0
  ctr : (m.regs.getXReg .X9).toBitVec = BitVec.ofNat 64 (16 + 8 * i)
  regs : AllOf (fun p : XReg × Nat =>
    (m.regs.getXReg p.1).toBitVec = (Keccak.lane (stAfter m0 i) p.2).toBitVec) laneRegs
  slots : AllOf (fun p : Nat × Nat => WordAt m.dmem (frame m0 + BitVec.ofNat 64 p.1)
    (Keccak.lane (stAfter m0 i) p.2).toBitVec) laneSlots
  saved : AllOf (fun p : Nat × XReg => WordAt m.dmem (frame m0 + BitVec.ofNat 64 p.1)
    (m0.regs.getXReg p.2).toBitVec) savedSlots
  rc : BytesAt m.dmem (frame m0 + BitVec.ofNat 64 112) rcBytes
  same : SameOutside m0.dmem m.dmem (InRange (frame m0) NativeRustcVmArm.keccakFStack)
  kept : Kept m0.dmem m.dmem

end

public section

theorem frame_toNat {m0 : MachineData} (h : StackOk m0 NativeRustcVmArm.keccakFStack) :
    (frame m0).toNat = m0.regs.SP.toNat - 400 := by
  have := h.2.1
  simp only [frame, stackBelow, NativeRustcVmArm.keccakFStack] at this ⊢
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp; omega)]
  simp

theorem frame_noWrap {m0 : MachineData} (h : StackOk m0 NativeRustcVmArm.keccakFStack) :
    NoWrap (frame m0) NativeRustcVmArm.keccakFStack := by
  have := m0.regs.SP.toBitVec.isLt
  simp only [NoWrap, frame_toNat h, NativeRustcVmArm.keccakFStack]
  simp only [UInt64.toNat_toBitVec] at this
  have := h.2.1
  simp only [NativeRustcVmArm.keccakFStack] at this
  omega

theorem frame_aligned {m0 : MachineData} (h : StackOk m0 NativeRustcVmArm.keccakFStack) :
    (frame m0).toNat % 16 = 0 := by
  rw [frame_toNat h]
  have := h.1
  have := h.2.1
  simp only [NativeRustcVmArm.keccakFStack] at this
  omega

theorem frame_add_toNat {m0 : MachineData} (h : StackOk m0 NativeRustcVmArm.keccakFStack)
    {o : Nat} (ho : o < 400) : (frame m0 + BitVec.ofNat 64 o).toNat = (frame m0).toNat + o := by
  have := frame_noWrap h
  unfold NoWrap NativeRustcVmArm.keccakFStack at this
  rw [toNat_add_ofNat _ _ (by omega)]

end

end NativeRustcVmArm.KeccakF
