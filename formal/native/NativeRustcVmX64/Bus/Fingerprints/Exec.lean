module

public import NativeRustcVmX64.Bus.Facts
public import NativeRustcVmX64.Code.Vm.Fingerprints
public meta import NativeRustcVmX64.Code.Vm.Fingerprints
public meta import NativeRustcVmX64.Transcript.Frame

/-!
# `fingerprints`' blocks, run by the symbolic executor (x86-64)

Region 0 the 256-byte frame (RBP, R15, R14, R13, R12, RBX pushed at offsets `248` to `208`, R9 kept
at `24`, the first dot product's limb `0` at `16`, the three arrays `dot` reads at `32`, `128`,
`80`, a callee's return address at `0`) and the return address. Region 1 the 8 argument words on
the stack above it (`argAliases`: the frame offset `264 + 8 i` is region 1's `8 i`), or the
`memory` slice (`memS`, for the first four instructions of `b3`), or the output (`outS`, for
`b7`'s writes and epilogue).
-/

namespace NativeRustcVmX64.Bus.Fingerprints

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.Fingerprints
open NativeRustcVmX64.Transcript NativeRustcVmX64.Bus

@[expose] public section

/-- The frame's slots. -/
def slots : Slots := [(248, .rbp), (240, .r15), (232, .r14), (224, .r13), (216, .r12), (208, .rbx)]

/-- The stack arguments' aliases: the frame offset `264 + 8 i` is region 1's `8 i`. -/
def argAliases : List (Sym × Nat × Int) :=
  [(.ptr 0 264, 1, 0), (.ptr 0 272, 1, 8), (.ptr 0 280, 1, 16), (.ptr 0 288, 1, 24),
    (.ptr 0 296, 1, 32), (.ptr 0 304, 1, 40), (.ptr 0 312, 1, 48), (.ptr 0 320, 1, 56)]

def entryS : SState := init [264, 64] [(.rsp, .ptr 0 256)] [] [] argAliases
def midS : SState := init [264, 64] [(.rsp, .ptr 0 8)] [] [] argAliases
def memS : SState := init [264, 32] [(.rsp, .ptr 0 8), (.r12, .ptr 1 0)]
def outS : SState := init [264, 48] [(.rsp, .ptr 0 8), (.rbx, .ptr 1 0)]

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 midS
sym_block run_b2 := exec b2 midS
sym_block run_b3a := exec (b3.take 4) memS
sym_block run_b3b := exec (b3.drop 4) midS
sym_block run_b4 := exec b4 midS
sym_block run_b5 := exec b5 midS
sym_block run_b6 := exec b6 midS
sym_block run_b7a := exec (b7.take 2) midS
sym_block run_b7b := exec (b7.drop 2) outS

public theorem ok_b0 : ProOk 256 0 slots (after b0 entryS) = true ∧
    (∀ w ∈ (after b0 entryS).mem, w.r = 0) ∧ Wrote 0 [(24, .reg .r9)] (after b0 entryS) ∧
    (after b0 entryS).reg .rbx = some (.reg .rdi) ∧ (after b0 entryS).reg .r14 = some (.reg .rsi) ∧
    (after b0 entryS).reg .r12 = some (.reg .rdx) ∧ (after b0 entryS).reg .r13 = some (.reg .rcx) ∧
    (after b0 entryS).reg .r15 = some (.reg .r8) ∧ (after b0 entryS).reg .rbp = some (.load 1 24 8) ∧
    (after b0 entryS).reg .rdi = some (.lit 0) := by
  decide +kernel

public theorem ok_b1 : MidOk 256 0 slots (after b1 midS) = true ∧
    (∀ w ∈ (after b1 midS).mem, w.r = 0) ∧
    Wrote 0 [(32, .lit 1), (40, .lit 0), (48, .reg .rbp), (56, .lit 0), (64, .reg .rax),
      (72, .lit 0)] (after b1 midS) ∧
    (∀ w ∈ (after b1 midS).mem, w.off + w.n ≤ 8 ∨ 32 ≤ w.off ∧ w.off + w.n ≤ 80) ∧
    Keeps [.rbx, .rbp, .r12, .r13, .r14, .r15] (after b1 midS) ∧
    (after b1 midS).reg .rdi = some (.reg .r14) ∧ (after b1 midS).reg .rsi = some (.lit 3) ∧
    (after b1 midS).reg .rdx = some (.ptr 0 32) ∧ (after b1 midS).reg .rcx = some (.lit 3) := by
  decide +kernel

public theorem ok_b2 : MidOk 256 0 slots (after b2 midS) = true ∧
    (∀ w ∈ (after b2 midS).mem, w.r = 0) ∧ Wrote 0 [(16, .reg .rax)] (after b2 midS) ∧
    (∀ w ∈ (after b2 midS).mem, w.off + w.n ≤ 8 ∨ 16 ≤ w.off ∧ w.off + w.n ≤ 24) ∧
    Keeps [.rbx, .r12, .r13, .r14, .r15] (after b2 midS) ∧
    (after b2 midS).reg .rbp = some (.reg .rdx) ∧
    (after b2 midS).reg .rdi = some (.reg .r13) ∧ (after b2 midS).reg .rsi = some (.reg .r15) := by
  decide +kernel

public theorem ok_b3a : MidOk 256 8 slots (after (b3.take 4) memS) = true ∧
    (after (b3.take 4) memS).mem = [] ∧
    Keeps [.rbx, .rbp, .r13, .r14, .r15, .rax, .rdx] (after (b3.take 4) memS) ∧
    (after (b3.take 4) memS).reg .rcx = some (.load 1 0 8) ∧
    (after (b3.take 4) memS).reg .rsi = some (.load 1 8 8) ∧
    (after (b3.take 4) memS).reg .rdi = some (.load 1 16 8) ∧
    (after (b3.take 4) memS).reg .r8 = some (.load 1 24 8) := by
  decide +kernel

public theorem ok_b3b : MidOk 256 0 slots (after (b3.drop 4) midS) = true ∧
    (∀ w ∈ (after (b3.drop 4) midS).mem, w.r = 0) ∧
    Wrote 0 [(128, .lit 2), (136, .lit 0), (144, .reg .rax), (152, .reg .rdx),
      (160, .load 1 32 8), (168, .load 1 40 8), (176, .reg .rcx), (184, .reg .rsi),
      (192, .reg .rdi), (200, .reg .r8)] (after (b3.drop 4) midS) ∧
    (∀ w ∈ (after (b3.drop 4) midS).mem, w.off + w.n ≤ 8 ∨ 128 ≤ w.off ∧ w.off + w.n ≤ 208) ∧
    Keeps [.rbx, .rbp, .r12, .r13, .r14, .r15] (after (b3.drop 4) midS) ∧
    (after (b3.drop 4) midS).reg .rdi = some (.reg .r14) ∧
    (after (b3.drop 4) midS).reg .rsi = some (.lit 5) ∧
    (after (b3.drop 4) midS).reg .rdx = some (.ptr 0 128) ∧
    (after (b3.drop 4) midS).reg .rcx = some (.lit 5) := by
  decide +kernel

public theorem ok_b4 : MidOk 256 0 slots (after b4 midS) = true ∧
    (∀ w ∈ (after b4 midS).mem, w.r = 0 ∧ w.off + w.n ≤ 8) ∧
    Keeps [.rbx, .rbp, .r13, .r14] (after b4 midS) ∧
    (after b4 midS).reg .r15 = some (.reg .rax) ∧ (after b4 midS).reg .r12 = some (.reg .rdx) ∧
    (after b4 midS).reg .rdi = some (.lit 2) := by
  decide +kernel

public theorem ok_b5 : MidOk 256 0 slots (after b5 midS) = true ∧
    (∀ w ∈ (after b5 midS).mem, w.r = 0 ∧ w.off + w.n ≤ 8) ∧
    Keeps [.rbx, .rbp, .r12, .r14, .r15] (after b5 midS) ∧
    (after b5 midS).reg .r13 = some (.reg .rax) ∧
    (after b5 midS).reg .rdi = some (.load 0 24 8) ∧
    (after b5 midS).reg .rsi = some (.load 1 0 8) := by
  decide +kernel

public theorem ok_b6 : MidOk 256 0 slots (after b6 midS) = true ∧
    (∀ w ∈ (after b6 midS).mem, w.r = 0) ∧
    Wrote 0 [(80, .reg .r13), (88, .lit 0), (96, .reg .rax), (104, .reg .rdx),
      (112, .load 1 48 8), (120, .load 1 56 8)] (after b6 midS) ∧
    (∀ w ∈ (after b6 midS).mem, w.off + w.n ≤ 8 ∨ 80 ≤ w.off ∧ w.off + w.n ≤ 128) ∧
    Keeps [.rbx, .rbp, .r12, .r13, .r14, .r15] (after b6 midS) ∧
    (after b6 midS).reg .rdi = some (.reg .r14) ∧ (after b6 midS).reg .rsi = some (.lit 3) ∧
    (after b6 midS).reg .rdx = some (.ptr 0 80) ∧ (after b6 midS).reg .rcx = some (.lit 3) := by
  decide +kernel

public theorem ok_b7a : MidOk 256 8 slots (after (b7.take 2) midS) = true ∧
    (after (b7.take 2) midS).mem = [] ∧
    Keeps [.rbx, .rbp, .r12, .r13, .r14, .r15] (after (b7.take 2) midS) ∧
    (after (b7.take 2) midS).reg .rax = some (.bin .xor .W64 (.reg .rax) (.load 1 8 8)) ∧
    (after (b7.take 2) midS).reg .rdx = some (.bin .xor .W64 (.reg .rdx) (.load 1 16 8)) := by
  decide +kernel

public theorem ok_b7b : EpiOk 256 slots (after (b7.drop 2) outS) = true ∧
    (∀ w ∈ (after (b7.drop 2) outS).mem, w.r = 1 ∧ w.off + w.n ≤ 48) ∧
    Wrote 1 [(0, .load 0 16 8), (8, .reg .rbp), (16, .reg .r15), (24, .reg .r12),
      (32, .reg .rax), (40, .reg .rdx)] (after (b7.drop 2) outS) := by
  decide +kernel

end NativeRustcVmX64.Bus.Fingerprints
