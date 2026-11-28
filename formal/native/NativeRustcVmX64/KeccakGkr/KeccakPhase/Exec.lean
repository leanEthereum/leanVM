module

public import NativeRustcVmX64.Sumcheck.Common
public import NativeRustcVmX64.Code.Vm.KeccakPhase
public import NativeRustcVmX64.Code.Vm.KeccakPhase.Names
public import NativeRustcVmX64.Code.Vm.Memcpy.Names
public import NativeRustcVmX64.Code.Vm.VerifyKeccak.Names
public meta import NativeRustcVmX64.Code.Vm.KeccakPhase
public meta import NativeRustcVmX64.Sumcheck.Common

/-!
# `keccak_phase`'s blocks, run by the symbolic executor (x86-64)

Region 0 is the 480-byte frame below the entry's RSP and the return address (`F = 480`): the six
pushed registers from `432`, RSP at offset `24` in the body; the output lanes at `32` (`400`
bytes); `verify_keccak`'s two stack arguments at `8`, `16`, its return address at `0`. Region 1
is the tables' evaluations (RDX at the entry, RBX from `b1`); `KECCAK`'s entry at `9840`: its
point's count at `9840`, its values' count at `10328`.

- `entryS` at the entry (`b0`: the prologue, the lanes zeroed, the values' bounds; then `b1`,
  `memcpy`'s arguments);
- `retS` after `memcpy` (`b2`: `verify_keccak`'s arguments and call);
- `vkS` after `verify_keccak` (`b3`, `b4`: the epilogue).
-/

namespace NativeRustcVmX64.KeccakGkr.KeccakPhase

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.KeccakPhase NativeRustcVmX64.Transcript
open NativeRustcVmX64.Sumcheck

@[expose] public section

/-- The frame's slots: the pushed registers. -/
def slots : Slots := [(472, .rbp), (464, .r15), (456, .r14), (448, .r13), (440, .r12), (432, .rbx)]

/-- At the entry: the frame, the evaluations, and the ordinary `memcpy` GOT slot. -/
def entryS : SState :=
  (init [488, 11808, 8] [(.rsp, .ptr 0 480), (.rdx, .ptr 1 0)]
    (aliases := [(.gotSlot "memcpy", 2, 0)])).withKnownBytes 2 0 8 (.label "memcpy")

/-- After `memcpy`: the frame, the evaluations (RBX). -/
def retS : SState := init [488, 11808] [(.rsp, .ptr 0 24), (.rbx, .ptr 1 0)]

/-- After `verify_keccak`: the frame. -/
def vkS : SState := init [488] [(.rsp, .ptr 0 8)]

/-- The values' count. -/
def lenS : Sym := .load 1 10328 8
/-- The values' slice's length: the count if at most the capacity, else `0`. -/
def bxS : Sym := .ite (.cmp .ult .W64 lenS (.lit 93)) lenS (.lit 0)
/-- The slice's length past `KECCAK_OUT`, saturating. -/
def subS : Sym := .ite (.cmp .ult .W64 bxS (.lit 40)) (.lit 0) (.bin .sub .W64 bxS (.lit 40))
/-- The lanes present: at most 25. -/
def r15S : Sym := .ite (.cmp .ult .W64 subS (.lit 25)) subS (.lit 25)
/-- `KECCAK_OUT` plus the lanes present. -/
def r10S : Sym :=
  .ite (.cmp .ult .W64 subS (.lit 25)) (.bin .add .W64 subS (.lit 40))
    (.bin .add .W64 (.lit 25) (.lit 40))
/-- `b0`'s exit: the lanes past the slice. -/
def c0 : SBool := .and (.not (.cmp .ult .W64 r10S bxS)) (.not (.cmp .eq .W64 r10S bxS))
/-- `memcpy`'s source: the values' lane `KECCAK_OUT`. -/
def srcS : Sym :=
  .bin .add .W64 (.lit 640) (.ite (.not (.cmp .ult .W64 lenS (.lit 93))) (.lit 8) (.ptr 1 10336))
/-- `memcpy`'s byte count. -/
def nS : Sym := .bin .shl .W64 r15S (.lit 4)
/-- The point's count. -/
def ptS : Sym := .load 1 9840 8
/-- The point's slice's address. -/
def instS : Sym := .ite (.not (.cmp .ult .W64 ptS (.lit 31))) (.lit 8) (.ptr 1 9848)
/-- The point's slice's length. -/
def nInstS : Sym := .ite (.cmp .ult .W64 ptS (.lit 31)) ptS (.lit 0)

/-- The state at `memcpy`. -/
abbrev s1 : SState := after b1 (after b0 entryS)
/-- The state at `verify_keccak`. -/
abbrev s2 : SState := after b2 retS
/-- The state at the return. -/
abbrev s4 : SState := after b4 (after b3 vkS)

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 (after b0 entryS)
sym_block run_b2 := exec b2 retS
sym_block run_b3 := exec b3 vkS
sym_block run_b4 := exec b4 (after b3 vkS)

end NativeRustcVmX64.KeccakGkr.KeccakPhase

namespace NativeRustcVmX64.KeccakGkr.KeccakPhase

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.KeccakPhase NativeRustcVmX64.Transcript

public section

theorem exit_b0 : exec b0 entryS = some (after b0 entryS, .cond c0 NativeRustcVmX64.Vm.KeccakPhase.label_2) :=
  run_b0.trans (by rw [after_eq run_b0]; rfl)

theorem exit_b1 : exec b1 (after b0 entryS) = some (s1, .call NativeRustcVmX64.Vm.Memcpy.entryLabel) :=
  run_b1.trans (by rw [show s1 = after b1 (after b0 entryS) from rfl, after_eq run_b1])

theorem exit_b2 :
    exec b2 retS = some (s2, .call NativeRustcVmX64.Vm.VerifyKeccak.entryLabel) :=
  run_b2.trans (by rw [show s2 = after b2 retS from rfl, after_eq run_b2])

theorem exit_b3 : exec b3 vkS = some (after b3 vkS, .fall) :=
  run_b3.trans (by rw [after_eq run_b3])

theorem exit_b4 : exec b4 (after b3 vkS) = some (s4, .ret (.load 0 480 8)) :=
  run_b4.trans (by rw [show s4 = after b4 (after b3 vkS) from rfl, after_eq run_b4])

theorem ok_s1 : s1.reg .rsp = some (.ptr 0 16) ∧ s1.reg .rdi = some (.ptr 0 32) ∧
    s1.reg .rsi = some srcS ∧ s1.reg .rdx = some nS ∧ s1.reg .rbx = some (.ptr 1 0) ∧
    s1.reg .rbp = some (.reg .rsi) ∧ s1.reg .r12 = some (.reg .r9) ∧
    s1.reg .r13 = some (.reg .rdi) ∧ s1.reg .r14 = some (.reg .rcx) ∧
    s1.reg .r15 = some (.reg .r8) ∧
    (∀ p ∈ slots, ∀ t < 8, findWrite 0 (p.1 + t) s1.mem = some (.reg p.2, t)) ∧
    (∀ i < 400, findWrite 0 (32 + i) s1.mem = some (.lit 0, i % 8)) ∧
    (∀ w ∈ s1.mem, w.r = 0 ∧ 16 ≤ w.off ∧ w.off + w.n ≤ 480) := by
  decide +kernel

theorem ok_b0 : (after b0 entryS).reg .rdx = some (.ptr 1 0) := by decide +kernel

theorem ok_s2 : s2.reg .rsp = some (.ptr 0 0) ∧ s2.reg .rdi = some (.reg .r13) ∧
    s2.reg .rsi = some (.reg .rbp) ∧ s2.reg .rdx = some instS ∧ s2.reg .rcx = some nInstS ∧
    s2.reg .r8 = some (.ptr 0 32) ∧ s2.reg .r9 = some (.reg .r14) ∧
    (∀ t < 8, findWrite 0 (8 + t) s2.mem = some (.reg .r15, t)) ∧
    (∀ t < 8, findWrite 0 (16 + t) s2.mem = some (.reg .r12, t)) ∧
    (∀ w ∈ s2.mem, w.r = 0 ∧ w.off + w.n ≤ 24) := by
  decide +kernel

theorem ok_b3 : (after b3 vkS).reg .rsp = some (.ptr 0 24) ∧ (after b3 vkS).mem = [] := by
  decide +kernel

theorem ok_s4 : (∀ p ∈ slots, s4.reg p.2 = some (.load 0 p.1 8)) ∧
    s4.reg .rsp = some (.ptr 0 488) ∧ s4.reg .rax = some (.reg .rax) ∧ s4.mem = [] := by
  decide +kernel

end

end NativeRustcVmX64.KeccakGkr.KeccakPhase
