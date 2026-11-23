module

public import NativeRustcVmX64.Whir.Common
public import NativeRustcVmX64.Whir.SampleQueries.Exec
public import NativeRustcVmX64.Code.Vm.FoldRound
public meta import NativeRustcVmX64.Code.Vm.FoldRound
public meta import NativeRustcVmX64.Whir.Common
public meta import NativeRustcVmX64.Whir.SampleQueries.Exec

/-!
# `fold_round`'s blocks, run by the symbolic executor (x86-64)

Region 0 is the 176-byte frame (RBP to RBX pushed at offsets `168` to `128`, the locals at `8` to
`128`, a callee's return address at `0`) and the return address at `176`.
- `entryS` at the entry: the prologue and the first `read_scalar` call (`b0`);
- `midS` (RSP at offset `8`): the frame only, every block but the state's and the output's;
- `stS` (`b12`, `b18`): region 1 the state's claim and `α`s' count (24 bytes at R14);
- `pushS` (`b19`): region 1 as `stS`, region 2 the new `α`'s slot (R14 + 16 RAX + 24), region 3 the
  output's 40 bytes at RBX;
- `tagS` (`b21`): region 1 the output's tag at RBX.

Each block's facts (`ok_b<k>`): its frame checks, its writes (`wr0`, `wrR`, `wrote`), the frame
words it misses (`missL`), its registers.
-/

namespace NativeRustcVmX64.Whir.FoldRound

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.FoldRound
open NativeRustcVmX64.Transcript (Slots ProOk MidOk EpiOk)
open NativeRustcVmX64.Whir.SampleQueries (wr0 miss wrote kept)

@[expose] public section

/-- The frame's slots. -/
def slots : Slots := [(168, .rbp), (160, .r15), (152, .r14), (144, .r13), (136, .r12), (128, .rbx)]

def entryS : SState := init [184] [(.rsp, .ptr 0 176)]
def midS : SState := init [184] [(.rsp, .ptr 0 8)]
def stS : SState := init [184, 24] [(.rsp, .ptr 0 8), (.r14, .ptr 1 0)]
/-- The new `α`'s slot address. -/
def slotA : Sym := .bin .add .W64 (.reg .r14) (.bin .shl .W64 (.reg .rax) (.lit 4))
def pushS : SState := init [184, 24, 16, 40] [(.rsp, .ptr 0 8), (.rbx, .ptr 3 0)]
  (aliases := [(.reg .r14, 1, 0), (slotA, 2, -24)])
def tagS : SState := init [184, 8] [(.rsp, .ptr 0 8), (.rbx, .ptr 1 0)]

/-- Every write in region `r` below `L`. -/
def wrR (S : SState) (r L : Nat) : Bool := S.mem.all fun w ↦ w.r == r && decide (w.off + w.n ≤ L)
/-- No write over the frame's words at `os`. -/
def missL (S : SState) (os : List Nat) : Bool := os.all (miss S)
/-- Registers kept from the start state `S0`. -/
def keptI (S0 S : SState) (rs : List Reg64) : Bool :=
  rs.all fun r ↦ (S0.reg r).isSome && S.reg r == S0.reg r
/-- The callee-saved registers. -/
def cs : List Reg64 := [.rbx, .rbp, .r12, .r13, .r14, .r15]

/-- `b18`'s claim, low limb. -/
def claim0S : Sym := .bin .xor .W64 (.bin .xor .W64 (.reg .rax) (.reg .r12))
  (.bin .xor .W64 (.bin .xor .W64 (.reg .r15) (.load 0 88 8)) (.load 0 96 8))
/-- `b18`'s claim, high limb. -/
def claim1S : Sym := .bin .xor .W64 (.bin .xor .W64 (.reg .rdx) (.reg .rbp))
  (.bin .xor .W64 (.bin .xor .W64 (.reg .r13) (.load 0 64 8)) (.load 0 104 8))

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 midS
sym_block run_b2 := exec b2 midS
sym_block run_b3 := exec b3 midS
sym_block run_b4 := exec b4 midS
sym_block run_b5 := exec b5 midS
sym_block run_b6 := exec b6 midS
sym_block run_b7 := exec b7 midS
sym_block run_b8 := exec b8 midS
sym_block run_b9 := exec b9 midS
sym_block run_b10 := exec b10 midS
sym_block run_b11 := exec b11 midS
sym_block run_b12 := exec b12 stS
sym_block run_b13 := exec b13 midS
sym_block run_b14 := exec b14 midS
sym_block run_b15 := exec b15 midS
sym_block run_b16 := exec b16 midS
sym_block run_b17 := exec b17 midS
sym_block run_b18 := exec b18 stS
sym_block run_b19 := exec b19 pushS
sym_block run_b20 := exec b20 midS
sym_block run_b21 := exec b21 tagS

/-! ## The prologue and the reads -/

public theorem ok_b0 : ProOk 176 0 slots (after b0 entryS) = true ∧ wr0 (after b0 entryS) 176 = true ∧
    (after b0 entryS).reg .rdi = some (.ptr 0 8) ∧ (after b0 entryS).reg .rsi = some (.reg .rsi) ∧
    (after b0 entryS).reg .r13 = some (.reg .rsi) ∧ (after b0 entryS).reg .r14 = some (.reg .rdx) ∧
    (after b0 entryS).reg .rbx = some (.reg .rdi) := by decide +kernel
public theorem ok_b1 : MidOk 176 8 slots (after b1 midS) = true ∧ (after b1 midS).mem = [] ∧
    kept (after b1 midS) cs = true := by decide +kernel
public theorem ok_b2 : MidOk 176 0 slots (after b2 midS) = true ∧ wr0 (after b2 midS) 8 = true ∧
    (after b2 midS).reg .r12 = some (.load 0 16 8) ∧ (after b2 midS).reg .rbp = some (.load 0 24 8) ∧
    (after b2 midS).reg .rdi = some (.ptr 0 8) ∧ (after b2 midS).reg .rsi = some (.reg .r13) ∧
    kept (after b2 midS) [.rbx, .r13, .r14] = true := by decide +kernel
public theorem ok_b3 : MidOk 176 8 slots (after b3 midS) = true ∧ (after b3 midS).mem = [] ∧
    kept (after b3 midS) cs = true := by decide +kernel
public theorem ok_b4 : MidOk 176 0 slots (after b4 midS) = true ∧ wr0 (after b4 midS) 72 = true ∧
    wrote (after b4 midS) 0 64 (.load 0 24 8) = true ∧ (after b4 midS).reg .r15 = some (.load 0 16 8) ∧
    (after b4 midS).reg .rdi = some (.ptr 0 8) ∧ (after b4 midS).reg .rsi = some (.reg .r13) ∧
    kept (after b4 midS) [.rbx, .rbp, .r12, .r13, .r14] = true := by decide +kernel
public theorem ok_b5 : MidOk 176 8 slots (after b5 midS) = true ∧ (after b5 midS).mem = [] ∧
    kept (after b5 midS) cs = true := by decide +kernel
public theorem ok_b6 : MidOk 176 0 slots (after b6 midS) = true ∧ wr0 (after b6 midS) 88 = true ∧
    wrote (after b6 midS) 0 72 (.load 0 16 8) = true ∧ wrote (after b6 midS) 0 80 (.load 0 24 8) = true ∧
    missL (after b6 midS) [64] = true ∧
    (after b6 midS).reg .rdi = some (.ptr 0 8) ∧ (after b6 midS).reg .rsi = some (.reg .r13) ∧
    kept (after b6 midS) cs = true := by decide +kernel
public theorem ok_b7 : MidOk 176 8 slots (after b7 midS) = true ∧ (after b7 midS).mem = [] ∧
    kept (after b7 midS) cs = true := by decide +kernel
public theorem ok_b8 : MidOk 176 0 slots (after b8 midS) = true ∧ wr0 (after b8 midS) 128 = true ∧
    wrote (after b8 midS) 0 120 (.load 0 16 8) = true ∧ wrote (after b8 midS) 0 112 (.load 0 24 8) = true ∧
    missL (after b8 midS) [64, 72, 80] = true ∧
    (after b8 midS).reg .rdi = some (.reg .r13) ∧ (after b8 midS).reg .rsi = some (.lit 7) ∧
    kept (after b8 midS) cs = true := by decide +kernel
public theorem ok_b9 : MidOk 176 8 slots (after b9 midS) = true ∧ (after b9 midS).mem = [] ∧
    kept (after b9 midS) cs = true := by decide +kernel

/-! ## The squeezes and the products -/

public theorem ok_b10 : MidOk 176 0 slots (after b10 midS) = true ∧ wr0 (after b10 midS) 8 = true ∧
    (after b10 midS).reg .rdi = some (.reg .r13) ∧ kept (after b10 midS) cs = true := by decide +kernel
public theorem ok_b11 : MidOk 176 0 slots (after b11 midS) = true ∧ wr0 (after b11 midS) 64 = true ∧
    wrote (after b11 midS) 0 56 (.reg .rax) = true ∧ wrote (after b11 midS) 0 32 (.reg .rdx) = true ∧
    missL (after b11 midS) [64, 72, 80, 120, 112] = true ∧
    (after b11 midS).reg .rdi = some (.reg .r13) ∧ kept (after b11 midS) cs = true := by decide +kernel
public theorem ok_b12 : MidOk 176 0 slots (after b12 stS) = true ∧ wr0 (after b12 stS) 56 = true ∧
    wrote (after b12 stS) 0 48 (.reg .rax) = true ∧ wrote (after b12 stS) 0 40 (.reg .rdx) = true ∧
    missL (after b12 stS) [64, 72, 80, 120, 112, 56, 32] = true ∧
    (after b12 stS).reg .rdi = some (.load 0 56 8) ∧ (after b12 stS).reg .rsi = some (.load 0 32 8) ∧
    (after b12 stS).reg .rdx = some (.bin .xor .W64 (.load 1 0 8) (.reg .r12)) ∧
    (after b12 stS).reg .rcx = some (.bin .xor .W64 (.load 1 8 8) (.reg .rbp)) ∧
    (after b12 stS).reg .r13 = some (.load 0 56 8) ∧
    keptI stS (after b12 stS) [.rbx, .rbp, .r12, .r14, .r15] = true := by decide +kernel
public theorem ok_b13 : MidOk 176 0 slots (after b13 midS) = true ∧ wr0 (after b13 midS) 112 = true ∧
    wrote (after b13 midS) 0 96 (.reg .rax) = true ∧ wrote (after b13 midS) 0 104 (.reg .rdx) = true ∧
    missL (after b13 midS) [64, 72, 80, 120, 112, 56, 32, 48, 40] = true ∧
    (after b13 midS).reg .rdi = some (.reg .r13) ∧ (after b13 midS).reg .rsi = some (.load 0 32 8) ∧
    (after b13 midS).reg .rdx = some (.reg .r13) ∧ (after b13 midS).reg .rcx = some (.load 0 32 8) ∧
    kept (after b13 midS) cs = true := by decide +kernel
public theorem ok_b14 : MidOk 176 0 slots (after b14 midS) = true ∧ wr0 (after b14 midS) 8 = true ∧
    (after b14 midS).reg .rdi = some (.reg .rax) ∧ (after b14 midS).reg .rsi = some (.reg .rdx) ∧
    (after b14 midS).reg .rdx = some (.reg .r15) ∧ (after b14 midS).reg .rcx = some (.load 0 64 8) ∧
    kept (after b14 midS) cs = true := by decide +kernel
public theorem ok_b15 : MidOk 176 0 slots (after b15 midS) = true ∧ wr0 (after b15 midS) 96 = true ∧
    wrote (after b15 midS) 0 88 (.reg .rax) = true ∧ wrote (after b15 midS) 0 64 (.reg .rdx) = true ∧
    missL (after b15 midS) [72, 80, 120, 112, 56, 32, 48, 40, 96, 104] = true ∧
    (after b15 midS).reg .rdi = some (.load 0 48 8) ∧ (after b15 midS).reg .rsi = some (.load 0 40 8) ∧
    (after b15 midS).reg .rdx = some (.load 0 72 8) ∧ (after b15 midS).reg .rcx = some (.load 0 80 8) ∧
    kept (after b15 midS) cs = true := by decide +kernel
public theorem ok_b16 : MidOk 176 0 slots (after b16 midS) = true ∧ wr0 (after b16 midS) 8 = true ∧
    (after b16 midS).reg .r15 = some (.reg .rax) ∧ (after b16 midS).reg .r13 = some (.reg .rdx) ∧
    (after b16 midS).reg .rdi = some (.load 0 56 8) ∧ (after b16 midS).reg .rsi = some (.load 0 32 8) ∧
    (after b16 midS).reg .rdx = some (.load 0 48 8) ∧ (after b16 midS).reg .rcx = some (.load 0 40 8) ∧
    kept (after b16 midS) [.rbx, .rbp, .r12, .r14] = true := by decide +kernel
public theorem ok_b17 : MidOk 176 0 slots (after b17 midS) = true ∧ wr0 (after b17 midS) 8 = true ∧
    (after b17 midS).reg .rdi = some (.reg .rax) ∧ (after b17 midS).reg .rsi = some (.reg .rdx) ∧
    (after b17 midS).reg .rdx = some (.bin .xor .W64 (.load 0 120 8) (.load 0 72 8)) ∧
    (after b17 midS).reg .rcx = some (.bin .xor .W64 (.load 0 112 8) (.load 0 80 8)) ∧
    kept (after b17 midS) cs = true := by decide +kernel

/-! ## The claim, the push, the output -/

public theorem ok_b18 : MidOk 176 8 slots (after b18 stS) = true ∧ wrR (after b18 stS) 1 16 = true ∧
    wrote (after b18 stS) 1 0 claim0S = true ∧ wrote (after b18 stS) 1 8 claim1S = true ∧
    (after b18 stS).reg .rax = some (.load 1 16 8) ∧
    keptI stS (after b18 stS) [.rbx, .rbp, .r12, .r14] = true := by
  decide +kernel
public theorem ok_b19 : MidOk 176 8 slots (after b19 pushS) = true ∧
    wrote (after b19 pushS) 2 0 (.load 0 56 8) = true ∧ wrote (after b19 pushS) 2 8 (.load 0 32 8) = true ∧
    wrote (after b19 pushS) 1 16 (.bin .add .W64 (.reg .rax) (.lit 1)) = true ∧
    wrote (after b19 pushS) 3 8 (.load 0 56 8) = true ∧ wrote (after b19 pushS) 3 16 (.load 0 32 8) = true ∧
    wrote (after b19 pushS) 3 24 (.load 0 48 8) = true ∧ wrote (after b19 pushS) 3 32 (.load 0 40 8) = true ∧
    (∀ w ∈ (after b19 pushS).mem, (w.r = 1 ∧ 16 ≤ w.off ∧ w.off + w.n ≤ 24) ∨
      (w.r = 2 ∧ w.off + w.n ≤ 16) ∨ (w.r = 3 ∧ 8 ≤ w.off ∧ w.off + w.n ≤ 40)) ∧
    (after b19 pushS).reg .rax = some (.lit 1) ∧ keptI pushS (after b19 pushS) cs = true := by
  decide +kernel
public theorem ok_b20 : MidOk 176 8 slots (after b20 midS) = true ∧ (after b20 midS).mem = [] ∧
    (after b20 midS).reg .rax = some (.lit 0) ∧ kept (after b20 midS) cs = true := by decide +kernel
public theorem ok_b21 : EpiOk 176 slots (after b21 tagS) = true ∧ wrR (after b21 tagS) 1 8 = true ∧
    wrote (after b21 tagS) 1 0 (.reg .rax) = true := by decide +kernel

end NativeRustcVmX64.Whir.FoldRound
