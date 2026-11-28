module

public import NativeRustcVmX64.Keccak.Common

/-!
# `keccak_f`'s loop invariant (x86-64)

The frame: the 488 bytes from 480 below the entry's RSP (`frame`): `memcpy`'s return address
(offset 0), the 424 bytes of locals (8 to 431), the six pushed registers (RBX at 432, R12, R13,
R14, R15, RBP at 472) and the return address (480). In the loop RSP is `frame + 8`.

At the head of the round loop `NativeRustcVmX64.Vm.KeccakF.label_1` after `i` rounds (`At m0 i m`, from the machine
state `m0` at `keccak_f`'s entry): RSP is `frame + 8`; the counter RAX is `2 + i`; the state
pointer at 184 is the entry's RDI; the 25 lanes of the state after `i` rounds (`stAfter`) are in
11 registers (`laneRegs`) and 14 frame slots (`laneSlots`); the round constants are in the frame at
240; the pushed registers are the entry's (`savedSlots`); memory outside the frame's first 480
bytes is the entry's, and every byte mapped at entry is mapped.
-/

namespace NativeRustcVmX64.KeccakF

open NativeRustcX64 NativeRustcX64.Sym NativeRustc NativeRustc.Keccak LeanVM.Semantics
open NativeRustcX64.KeccakF (WordAt)

@[expose] public section

/-- The frame's base: 480 bytes below the entry's RSP. -/
def frame (m0 : MachineData) : BitVec 64 := stackBelow m0 NativeRustcVmX64.keccakFStack

/-- The state after `i` rounds, from the 200 bytes at the entry's RDI. -/
def stAfter (m0 : MachineData) (i : Nat) : KeccakState :=
  roundsTo (stateOf (bytesOf m0.dmem (m0.regs.get64 .rdi) 200)) i

/-- The registers that hold lanes at the loop head, with the lanes' indices. -/
def laneRegs : List (Reg64 × Nat) :=
  [(.r12, 3), (.r15, 6), (.r14, 7), (.r13, 8), (.r11, 11), (.rbp, 12), (.rdi, 13), (.r8, 15),
    (.rsi, 16), (.r9, 17), (.r10, 18)]

/-- The frame slots that hold lanes at the loop head, with the lanes' indices. -/
def laneSlots : List (Nat × Nat) :=
  [(40, 0), (112, 1), (104, 2), (120, 4), (56, 5), (48, 9), (32, 10), (8, 14), (16, 19),
    (96, 20), (72, 21), (88, 22), (80, 23), (24, 24)]

/-- The frame slots of the pushed registers. -/
def savedSlots : List (Nat × Reg64) :=
  [(432, .rbx), (440, .r12), (448, .r13), (456, .r14), (464, .r15), (472, .rbp)]

/-- **The loop invariant** after `i` rounds, from the entry's state `m0`. -/
structure At (m0 : MachineData) (i : Nat) (m : MachineData) : Prop where
  rsp : rspOf m = frame m0 + 8#64
  ctr : m.regs.get64 .rax = BitVec.ofNat 64 (2 + i)
  ptr : WordAt m.dmem (frame m0 + BitVec.ofNat 64 184) (m0.regs.get64 .rdi)
  regs : AllOf (fun p : Reg64 × Nat =>
    m.regs.get64 p.1 = (Keccak.lane (stAfter m0 i) p.2).toBitVec) laneRegs
  slots : AllOf (fun p : Nat × Nat => WordAt m.dmem (frame m0 + BitVec.ofNat 64 p.1)
    (Keccak.lane (stAfter m0 i) p.2).toBitVec) laneSlots
  saved : AllOf (fun p : Nat × Reg64 => WordAt m.dmem (frame m0 + BitVec.ofNat 64 p.1)
    (m0.regs.get64 p.2)) savedSlots
  rc : BytesAt m.dmem (frame m0 + BitVec.ofNat 64 240) rcBytes
  same : SameOutside m0.dmem m.dmem (InRange (frame m0) NativeRustcVmX64.keccakFStack)
  kept : Kept m0.dmem m.dmem

end

public section

theorem frame_toNat {m0 : MachineData} (h : StackOk m0 NativeRustcVmX64.keccakFStack) :
    (frame m0).toNat = (rspOf m0).toNat - 480 := by
  have := h.1
  simp only [frame, stackBelow, NativeRustcVmX64.keccakFStack] at this ⊢
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp; omega)]
  simp

/-- The frame and the return address do not wrap around. -/
theorem frame_noWrap {m0 : MachineData} (h : StackOk m0 NativeRustcVmX64.keccakFStack) :
    NoWrap (frame m0) (NativeRustcVmX64.keccakFStack + 8) := by
  have h1 := h.1
  have h2 := h.2.1
  simp only [NoWrap, frame_toNat h, NativeRustcVmX64.keccakFStack] at h1 ⊢
  omega

theorem frame_add (m0 : MachineData) : frame m0 + BitVec.ofNat 64 480 = rspOf m0 := by
  simp only [frame, stackBelow, NativeRustcVmX64.keccakFStack]
  exact BitVec.sub_add_cancel _ _

theorem frame_add_toNat {m0 : MachineData} (h : StackOk m0 NativeRustcVmX64.keccakFStack)
    {o : Nat} (ho : o < 488) : (frame m0 + BitVec.ofNat 64 o).toNat = (frame m0).toNat + o := by
  have := frame_noWrap h
  unfold NoWrap NativeRustcVmX64.keccakFStack at this
  rw [toNat_add_ofNat _ _ (by omega)]

end

end NativeRustcVmX64.KeccakF
