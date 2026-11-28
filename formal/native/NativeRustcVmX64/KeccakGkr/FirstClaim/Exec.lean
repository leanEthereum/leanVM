module

public import NativeRustcVmX64.Transcript.Frame
public import NativeRustcVmX64.Code.Vm.FirstClaim
public import NativeRustcVmX64.Code.Vm.BufEW30Extend.Names
public import NativeRustcVmX64.Code.Vm.Dot.Names
public import NativeRustcVmX64.Code.Vm.EWMul.Names
public import NativeRustcVmX64.Code.Vm.EqKernel.Names
public import NativeRustcVmX64.Code.Vm.FirstClaim.Names
public import NativeRustcVmX64.Code.Vm.Memcpy.Names
public meta import NativeRustcVmX64.Code.Vm.FirstClaim
public meta import NativeRustcVmX64.Transcript.Frame

/-!
# `first_claim`'s blocks, run by the symbolic executor (x86-64)

Region 0 the 1376-byte frame and the return address: RBP to RBX pushed at offsets `1368` to `1328`;
the locals from `8` (RSP's in the body): `inst`'s address at `16` and length at `24`, the segment
kernel (2 elements) at `32`, `mu`'s `Buf<EW, 16>` at `64`, the lanes' kernel (32 elements) at `328`,
the point's `Buf<EW, 30>` at `840`; a call's return address at `0`. Region 1 the three stack
argument words (`committed`, the weights' address), reached as the frame offsets `1384` to `1400`
(aliases). The bit weights' loop: `b3` from `lanesS` (the lane's byte offset bounded), `b4` from
`storeS` (region 1 the weight's element, `R14 + RBP - 8`). The result's stores (`b17`) from
`outS` (region 1 the result, R15).
-/

namespace NativeRustcVmX64.KeccakGkr.FirstClaim

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.FirstClaim NativeRustcVmX64.Transcript

@[expose] public section

/-- The frame's slots. -/
def slots : Slots :=
  [(1368, .rbp), (1360, .r15), (1352, .r14), (1344, .r13), (1336, .r12), (1328, .rbx)]

/-- The stack arguments' aliases. -/
def argAliases : List (Sym × Nat × Int) :=
  [(.ptr 0 1384, 1, 0), (.ptr 0 1392, 1, 8), (.ptr 0 1400, 1, 16)]

/-- A lane's byte offset in the lanes' kernel: `16 ((j / 64) % 32)`. -/
def laneS : Sym :=
  .bin .and .W32 (.bin .shr .W32 (.un .trunc .W32 (.reg .rcx)) (.lit 2)) (.lit 496)

def entryS : SState := init [1384, 24] [(.rsp, .ptr 0 1376)] [] [] argAliases
def callS : SState := init [1384, 24] [(.rsp, .ptr 0 8)] [] [] argAliases
def lanesS : SState := init [1384, 24] [(.rsp, .ptr 0 8)] [] [(laneS, 497)] argAliases
def storeS : SState :=
  init [1384, 16] [(.rsp, .ptr 0 8)] [] [] [(.bin .add .W64 (.reg .r14) (.reg .rbp), 1, 8)]
def outS : SState := init [1384, 776] [(.rsp, .ptr 0 8), (.r15, .ptr 1 0)]

/-- The first copy loads the loader's `memcpy` slot into the callee-saved R14. -/
def copyS : SState :=
  (init [1384, 24, 8] [(.rsp, .ptr 0 8)] [] []
    (argAliases ++ [(.gotSlot "memcpy", 2, 0)])).withKnownBytes 2 0 8 (.label "memcpy")

/-- The second copy calls the address retained in R14, without another slot read. -/
def copyRetS : SState :=
  init [1384, 24] [(.rsp, .ptr 0 8), (.r14, .label "memcpy")] [] [] argAliases


/-- Registers holding their atoms. -/
def atoms (S : SState) (rs : List Reg64) : Bool := rs.all fun r ↦ S.reg r == some (.reg r)

/-- Every write in region 0 between `lo` and `hi`. -/
def within (S : SState) (lo hi : Nat) : Bool :=
  S.mem.all fun w ↦ w.r == 0 && decide (lo ≤ w.off) && decide (w.off + w.n ≤ hi)

/-- The 8-byte words from `lo` to `hi` are zero. -/
def zeros (S : SState) (lo n : Nat) : Bool :=
  (List.range n).all fun q ↦ (List.range 8).all fun t ↦
    findWrite 0 (lo + 8 * q + t) S.mem == some (.lit 0, t)


/-- `b6`, `b10` test AL's bit 0; `b12`, `b14` AL. -/
def test1 : SBool := .cmp .eq .W8 (.bin .and .W8 (.reg .rax) (.lit 1)) (.lit 0)
def testA : SBool := .cmp .eq .W8 (.bin .and .W8 (.reg .rax) (.reg .rax)) (.lit 0)

end

set_option Elab.async false

sym_block e0 := exec b0 entryS
sym_block e1 := exec b1 callS
sym_block e2 := exec b2 callS
sym_block e3 := exec b3 lanesS
sym_block e4 := exec b4 storeS
sym_block e5 := exec b5 callS
sym_block e6 := exec b6 callS
sym_block e7 := exec b7 callS
sym_block e8 := exec b8 callS
sym_block e9 := exec b9 callS
sym_block e10 := exec b10 callS
sym_block e11 := exec b11 callS
sym_block e12 := exec b12 callS
sym_block e13 := exec b13 callS
sym_block e14 := exec b14 callS
sym_block e15 := exec b15 copyS
sym_block e16 := exec b16 copyRetS
sym_block e17 := exec b17 outS
sym_block e20 := exec b20 callS

public section

theorem ok_b0 : ProOk 1376 0 slots (after b0 entryS) = true ∧
    (∀ w ∈ (after b0 entryS).mem, w.r = 0 ∧ w.off + w.n ≤ 1376) ∧
    (∀ w ∈ (after b0 entryS).mem, w.off + w.n ≤ 8 ∨ (328 ≤ w.off ∧ w.off + w.n ≤ 840) ∨
      1328 ≤ w.off) ∧
    (after b0 entryS).reg .rdi = some (.reg .r8) ∧ (after b0 entryS).reg .rsi = some (.lit 5) ∧
    (after b0 entryS).reg .rdx = some (.ptr 0 328) ∧ (after b0 entryS).reg .rcx = some (.lit 32) ∧
    (after b0 entryS).reg .r13 = some (.reg .r9) ∧ (after b0 entryS).reg .r14 = some (.reg .rcx) ∧
    (after b0 entryS).reg .r15 = some (.reg .rdx) ∧ (after b0 entryS).reg .r12 = some (.reg .rsi) ∧
    (after b0 entryS).reg .rbx = some (.reg .rdi) := by
  rw [after_eq e0]; decide +kernel

theorem exit_b0 : exec b0 entryS = some (after b0 entryS,
    .call NativeRustcVmX64.Vm.EqKernel.entryLabel) := e0.trans (by rw [after_eq e0])

theorem ok_b1 : MidOk 1376 8 slots (after b1 callS) = true ∧ (after b1 callS).mem = [] ∧
    atoms (after b1 callS) [.rbx, .r12, .r13, .r14, .r15] = true := by
  rw [after_eq e1]; decide +kernel

theorem exit_b1 : exec b1 callS = some (after b1 callS,
    .cond (SBool.cmp .eq .W64 (.reg .rax) (.lit 1)).not NativeRustcVmX64.Vm.FirstClaim.label_8) :=
  e1.trans (by rw [after_eq e1])

theorem ok_b2 : MidOk 1376 8 slots (after b2 callS) = true ∧ within (after b2 callS) 16 32 = true ∧
    (∀ i < 8, findWrite 0 (16 + i) (after b2 callS).mem = some (.reg .r12, i)) ∧
    (∀ i < 8, findWrite 0 (24 + i) (after b2 callS).mem = some (.reg .r15, i)) ∧
    (after b2 callS).reg .r15 = some (.reg .rbx) ∧ (after b2 callS).reg .rbx = some (.reg .r14) ∧
    (after b2 callS).reg .r14 = some (.load 1 16 8) ∧ (after b2 callS).reg .rbp = some (.lit 8) ∧
    (after b2 callS).reg .rcx = some (.lit 0) ∧ atoms (after b2 callS) [.r13] = true := by
  rw [after_eq e2]; decide +kernel

theorem exit_b2 : exec b2 callS = some (after b2 callS, .fall) := e2.trans (by rw [after_eq e2])

theorem ok_b3 : MidOk 1376 0 slots (after b3 lanesS) = true ∧ within (after b3 lanesS) 0 8 = true ∧
    (after b3 lanesS).reg .rdi = some (.loadx 0 328 laneS 8) ∧
    (after b3 lanesS).reg .rsi = some (.loadx 0 336 laneS 8) ∧
    (after b3 lanesS).reg .rdx = some (.bin .shl .W64 (.lit 1) (.reg .rcx)) ∧
    (after b3 lanesS).reg .rcx = some (.lit 0) ∧
    (after b3 lanesS).reg .r12 = some (.bin .add .W64 (.reg .rcx) (.lit 1)) ∧
    atoms (after b3 lanesS) [.rbx, .rbp, .r13, .r14, .r15] = true := by
  rw [after_eq e3]; decide +kernel

theorem exit_b3 : exec b3 lanesS = some (after b3 lanesS,
    .call NativeRustcVmX64.Vm.EWMul.entryLabel) := e3.trans (by rw [after_eq e3])

theorem ok_b4 : MidOk 1376 8 slots (after b4 storeS) = true ∧
    (∀ w ∈ (after b4 storeS).mem, w.r = 1 ∧ 0 ≤ w.off ∧ w.off + w.n ≤ 16) ∧
    (∀ t < 8, findWrite 1 (0 + t) (after b4 storeS).mem = some (.reg .rax, t)) ∧
    (∀ t < 8, findWrite 1 (0 + 8 + t) (after b4 storeS).mem = some (.reg .rdx, t)) ∧
    (after b4 storeS).reg .rbp = some (.bin .add .W64 (.lit 16) (.reg .rbp)) ∧
    (after b4 storeS).reg .rcx = some (.reg .r12) ∧
    atoms (after b4 storeS) [.rbx, .r12, .r13, .r14, .r15] = true := by
  rw [after_eq e4]; decide +kernel

theorem exit_b4 : exec b4 storeS = some (after b4 storeS,
    .cond (SBool.cmp .eq .W64 (.bin .add .W64 (.lit 16) (.reg .rbp)) (.lit 25608)).not
      NativeRustcVmX64.Vm.FirstClaim.label_2) := e4.trans (by rw [after_eq e4])

theorem ok_b5 : MidOk 1376 0 slots (after b5 callS) = true ∧ within (after b5 callS) 0 64 = true ∧
    (∀ w ∈ (after b5 callS).mem, w.off + w.n ≤ 8 ∨ 32 ≤ w.off) ∧
    (after b5 callS).reg .rdi = some (.reg .rbx) ∧ (after b5 callS).reg .rsi = some (.lit 1) ∧
    (after b5 callS).reg .rdx = some (.ptr 0 32) ∧ (after b5 callS).reg .rcx = some (.lit 2) ∧
    (after b5 callS).reg .r12 = some (.reg .rbx) ∧
    atoms (after b5 callS) [.rbx, .r13, .r15] = true := by
  rw [after_eq e5]; decide +kernel

theorem exit_b5 : exec b5 callS = some (after b5 callS,
    .call NativeRustcVmX64.Vm.EqKernel.entryLabel) := e5.trans (by rw [after_eq e5])

/-- `b6`, `b10`, `b12`, `b14`: `None` tests, nothing else. -/
theorem ok_test : ∀ b ∈ [b6, b10, b12, b14], MidOk 1376 8 slots (after b callS) = true ∧
    (after b callS).mem = [] ∧
    atoms (after b callS) [.rdx, .rbx, .rbp, .r12, .r13, .r14, .r15] = true := by
  intro b hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl
  · rw [after_eq e6]; decide +kernel
  · rw [after_eq e10]; decide +kernel
  · rw [after_eq e12]; decide +kernel
  · rw [after_eq e14]; decide +kernel

theorem exit_b6 : exec b6 callS = some (after b6 callS, .cond test1 NativeRustcVmX64.Vm.FirstClaim.label_9) :=
  e6.trans (by rw [after_eq e6]; rfl)
theorem exit_b10 : exec b10 callS = some (after b10 callS, .cond test1 NativeRustcVmX64.Vm.FirstClaim.label_9) :=
  e10.trans (by rw [after_eq e10]; rfl)
theorem exit_b12 : exec b12 callS = some (after b12 callS, .cond testA NativeRustcVmX64.Vm.FirstClaim.label_9) :=
  e12.trans (by rw [after_eq e12]; rfl)
theorem exit_b14 : exec b14 callS = some (after b14 callS, .cond testA NativeRustcVmX64.Vm.FirstClaim.label_9) :=
  e14.trans (by rw [after_eq e14]; rfl)

theorem ok_b7 : MidOk 1376 0 slots (after b7 callS) = true ∧ within (after b7 callS) 0 8 = true ∧
    (after b7 callS).reg .rdi = some (.ptr 0 328) ∧ (after b7 callS).reg .rsi = some (.lit 25) ∧
    (after b7 callS).reg .rdx = some (.reg .r13) ∧ (after b7 callS).reg .rcx = some (.lit 25) ∧
    (after b7 callS).reg .rbp = some (.load 0 48 8) ∧ (after b7 callS).reg .r14 = some (.load 0 56 8) ∧
    atoms (after b7 callS) [.rbx, .r12, .r15] = true := by
  rw [after_eq e7]; decide +kernel

theorem exit_b7 : exec b7 callS = some (after b7 callS,
    .call NativeRustcVmX64.Vm.Dot.entryLabel) := e7.trans (by rw [after_eq e7])

theorem ok_b8 : MidOk 1376 0 slots (after b8 callS) = true ∧ within (after b8 callS) 0 8 = true ∧
    (after b8 callS).reg .rdi = some (.reg .rbp) ∧ (after b8 callS).reg .rsi = some (.reg .r14) ∧
    (after b8 callS).reg .rdx = some (.reg .rax) ∧ (after b8 callS).reg .rcx = some (.reg .rdx) ∧
    atoms (after b8 callS) [.rbx, .r12, .r15] = true := by
  rw [after_eq e8]; decide +kernel

theorem exit_b8 : exec b8 callS = some (after b8 callS,
    .call NativeRustcVmX64.Vm.EWMul.entryLabel) := e8.trans (by rw [after_eq e8])

theorem ok_b9 : MidOk 1376 0 slots (after b9 callS) = true ∧ within (after b9 callS) 0 328 = true ∧
    (∀ w ∈ (after b9 callS).mem, w.off + w.n ≤ 8 ∨ 64 ≤ w.off) ∧ zeros (after b9 callS) 64 33 = true ∧
    (after b9 callS).reg .rdi = some (.load 0 16 8) ∧
    (after b9 callS).reg .rsi =
      some (.ite (SBool.cmp .ult .W64 (.load 0 24 8) (.lit 4)) (.load 0 24 8) (.lit 4)) ∧
    (after b9 callS).reg .rdx = some (.ptr 0 72) ∧ (after b9 callS).reg .rcx = some (.lit 16) ∧
    (after b9 callS).reg .rbx = some (.load 0 24 8) ∧ (after b9 callS).reg .r14 = some (.load 0 16 8) ∧
    (after b9 callS).reg .r13 = some (.reg .rax) ∧ (after b9 callS).reg .rbp = some (.reg .rdx) ∧
    atoms (after b9 callS) [.r12, .r15] = true := by
  rw [after_eq e9]; decide +kernel

theorem exit_b9 : exec b9 callS = some (after b9 callS,
    .call NativeRustcVmX64.Vm.EqKernel.entryLabel) := e9.trans (by rw [after_eq e9])

theorem ok_b11 : MidOk 1376 0 slots (after b11 callS) = true ∧ within (after b11 callS) 0 1328 = true ∧
    (∀ w ∈ (after b11 callS).mem, w.off + w.n ≤ 8 ∨ (64 ≤ w.off ∧ w.off + w.n ≤ 72) ∨ 840 ≤ w.off) ∧
    zeros (after b11 callS) 840 61 = true ∧
    (∀ i < 8, findWrite 0 (64 + i) (after b11 callS).mem = some (.reg .rdx, i)) ∧
    (after b11 callS).reg .rdi = some (.ptr 0 840) ∧
    (after b11 callS).reg .rsi = some (.ite (SBool.cmp .ult .W64 (.reg .rbx) (.lit 4)).not
      (.bin .add .W64 (.lit 64) (.reg .r14)) (.lit 8)) ∧
    (after b11 callS).reg .rdx = some (.ite (SBool.cmp .ult .W64 (.reg .rbx) (.lit 4)).not
      (.bin .sub .W64 (.reg .rbx) (.lit 4)) (.lit 0)) ∧
    atoms (after b11 callS) [.rbp, .r12, .r13, .r15] = true := by
  rw [after_eq e11]; decide +kernel

theorem exit_b11 : exec b11 callS = some (after b11 callS, .call
    NativeRustcVmX64.Vm.BufEW30Extend.entryLabel) :=
  e11.trans (by rw [after_eq e11])

theorem ok_b13 : MidOk 1376 0 slots (after b13 callS) = true ∧ within (after b13 callS) 0 8 = true ∧
    (after b13 callS).reg .rdi = some (.ptr 0 840) ∧ (after b13 callS).reg .rsi = some (.reg .r12) ∧
    (after b13 callS).reg .rdx = some (.lit 1) ∧
    atoms (after b13 callS) [.rbp, .r12, .r13, .r15] = true := by
  rw [after_eq e13]; decide +kernel

theorem exit_b13 : exec b13 callS = some (after b13 callS, .call
    NativeRustcVmX64.Vm.BufEW30Extend.entryLabel) :=
  e13.trans (by rw [after_eq e13])

theorem ok_b15 : MidOk 1376 0 slots (after b15 copyS) = true ∧ within (after b15 copyS) 0 8 = true ∧
    (after b15 copyS).reg .rdi = some (.bin .add .W64 (.reg .r15) (.lit 24)) ∧
    (after b15 copyS).reg .rsi = some (.ptr 0 64) ∧ (after b15 copyS).reg .rdx = some (.lit 264) ∧
    (after b15 copyS).reg .r13 = some (.bin .xor .W64 (.reg .r13) (.load 1 0 8)) ∧
    (after b15 copyS).reg .rbp = some (.bin .xor .W64 (.reg .rbp) (.load 1 8 8)) ∧
    atoms (after b15 copyS) [.r15] = true ∧
    (after b15 copyS).reg .r14 = some (.label "memcpy") := by
  rw [after_eq e15]; decide +kernel

theorem exit_b15 : exec b15 copyS = some (after b15 copyS, .call NativeRustcVmX64.Vm.Memcpy.entryLabel) :=
  e15.trans (by rw [after_eq e15])

theorem ok_b16 : MidOk 1376 0 slots (after b16 copyRetS) = true ∧ within (after b16 copyRetS) 0 8 = true ∧
    (after b16 copyRetS).reg .rdi = some (.bin .add .W64 (.reg .r15) (.lit 288)) ∧
    (after b16 copyRetS).reg .rsi = some (.ptr 0 840) ∧ (after b16 copyRetS).reg .rdx = some (.lit 488) ∧
    atoms (after b16 copyRetS) [.rbp, .r13, .r15] = true := by
  rw [after_eq e16]; decide +kernel

theorem exit_b16 : exec b16 copyRetS = some (after b16 copyRetS, .call NativeRustcVmX64.Vm.Memcpy.entryLabel) :=
  e16.trans (by rw [after_eq e16])

theorem ok_b17 : MidOk 1376 8 slots (after b17 outS) = true ∧
    (∀ w ∈ (after b17 outS).mem, w.r = 1 ∧ 0 ≤ w.off ∧ w.off + w.n ≤ 24) ∧
    (∀ t < 8, findWrite 1 (0 + t) (after b17 outS).mem = some (.lit 1, t)) ∧
    (∀ t < 8, findWrite 1 (8 + t) (after b17 outS).mem = some (.reg .r13, t)) ∧
    (∀ t < 8, findWrite 1 (16 + t) (after b17 outS).mem = some (.reg .rbp, t)) := by
  rw [after_eq e17]; decide +kernel

theorem exit_b17 : exec b17 outS = some (after b17 outS, .jump NativeRustcVmX64.Vm.FirstClaim.label_10) :=
  e17.trans (by rw [after_eq e17])

theorem ok_b20 : EpiOk 1376 slots (after b20 callS) = true ∧ (after b20 callS).mem = [] := by
  rw [after_eq e20]; decide +kernel

theorem exit_b20 : exec b20 callS = some (after b20 callS, .ret (.load 0 1376 8)) :=
  e20.trans (by rw [after_eq e20])

end

end NativeRustcVmX64.KeccakGkr.FirstClaim
