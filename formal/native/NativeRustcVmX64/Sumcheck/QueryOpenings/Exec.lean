module

public import NativeRustcVmX64.Sumcheck.OpenPhase.Common
public import NativeRustcVmX64.Code.Vm.TStateQueryOpenings
public import NativeRustcVmX64.Code.Vm.DecodedPhase.Names
public import NativeRustcVmX64.Code.Vm.OpenPhase.Names
public import NativeRustcVmX64.Code.Vm.TStateQueryOpenings.Names
public meta import NativeRustcVmX64.Code.Vm.TStateQueryOpenings
public meta import NativeRustcVmX64.Sumcheck.OpenPhase.Common

/-!
# `TState::query_openings`'s blocks, run by the symbolic executor (x86-64)

Region 0 is the 96-byte frame below the entry's RSP and the return address (`Frame`, `F = 96`:
RSP at offset `8` in the body, a callee's return address at `0`): `open_phase`'s stack argument
(the phase's address) at `8`, its output (`Option<Rows>`, 32 bytes) at `16`, the six pushed
registers from `48`.

- `entryS` at the entry (`b0`: the prologue, the roots' count against `9` and `i`; then `b1`,
  `call phase`): region 1 the `TState` (RSI);
- `retS` after a call: `b2` (the phase's address against `0`) and `b4` (`open_phase`'s result
  against `None`);
- `openS` at `b3` (`call open_phase`): region 1 the `TState` from root `i` on (`t + 48 i`,
  `rootSym`);
- `okS` at `b5` (the rows copied, the phase advanced, then `b7`, the epilogue): region 1 the
  output (R14), region 2 the `TState` (RBX);
- `failS` at `b6` (`None`, then `b7`): region 1 the output (R14).
-/

namespace NativeRustcVmX64.Sumcheck.QueryOpenings

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.TStateQueryOpenings
open NativeRustcVmX64.Transcript NativeRustcVmX64.Sumcheck

@[expose] public section

/-- The frame's slots: the pushed registers. -/
def slots : Slots := [(88, .rbp), (80, .r15), (72, .r14), (64, .r13), (56, .r12), (48, .rbx)]

/-- Root `i`'s address minus `368`, as `b3` computes it: `RBX + ((RBP + 2 * RBP) << 4)`. -/
def rootSym : Sym :=
  .bin .add .W64 (.reg .rbx)
    (.bin .shl .W64 (.bin .add .W64 (.reg .rbp) (.bin .mul .W64 (.reg .rbp) (.lit 2))) (.lit 4))

/-- The roots' count. -/
abbrev cntSym : Sym := .load 1 752 8

/-- `setae` of a comparison: `1` or `0`. -/
abbrev setae (a b : Sym) : Sym := .ite (.not (.cmp .ult .W64 a b)) (.lit 1) (.lit 0)

/-- `b0`'s exit: `i ≥ count` or `count ≥ 9`. -/
def c0 : SBool :=
  .not (.cmp .eq .W8 (.bin .or .W8 (.bin .merge .W8 cntSym (setae (.reg .rdx) cntSym))
    (.bin .merge .W8 (.reg .rcx) (setae cntSym (.lit 9)))) (.lit 0))

/-- `b2`'s exit: no such phase. -/
def c2 : SBool := .cmp .eq .W64 (.bin .and .W64 (.reg .rax) (.reg .rax)) (.lit 0)

/-- `b4`'s exit: `open_phase`'s `None`. -/
def c4 : SBool := .cmp .eq .W64 (.load 0 16 8) (.lit 0)

def entryS : SState := init [104, 760] [(.rsp, .ptr 0 96), (.rsi, .ptr 1 0)]
def retS : SState := init [104] [(.rsp, .ptr 0 8)]
def openS : SState := init [104, 416] [(.rsp, .ptr 0 8)] (aliases := [(rootSym, (1, 0))])
def okS : SState := init [104, 32, 760] [(.rsp, .ptr 0 8), (.r14, .ptr 1 0), (.rbx, .ptr 2 0)]
def failS : SState := init [104, 32] [(.rsp, .ptr 0 8), (.r14, .ptr 1 0)]

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 (after b0 entryS)
sym_block run_b2 := exec b2 retS
sym_block run_b3 := exec b3 openS
sym_block run_b4 := exec b4 retS
sym_block run_b5 := exec b5 okS
sym_block run_b7o := exec b7 (after b5 okS)
sym_block run_b6 := exec b6 failS
sym_block run_b7f := exec b7 (after b6 failS)

public theorem exit_b0 :
    exec b0 entryS = some (after b0 entryS, .cond c0 NativeRustcVmX64.Vm.TStateQueryOpenings.label_4) :=
  run_b0.trans (by rw [after_eq run_b0]; rfl)
public theorem ok_b0 : ProOk 96 8 slots (after b0 entryS) = true ∧
    (∀ w ∈ (after b0 entryS).mem, w.r = 0 ∧ w.off + w.n ≤ 96) ∧
    (after b0 entryS).reg .r14 = some (.reg .rdi) := by
  decide +kernel
public theorem exit_b1 : exec b1 (after b0 entryS) = some (after b1 (after b0 entryS),
    .call NativeRustcVmX64.Vm.DecodedPhase.entryLabel) :=
  run_b1.trans (by rw [after_eq run_b1])
public theorem ok_b1 : ProOk 96 0 slots (after b1 (after b0 entryS)) = true ∧
    (∀ w ∈ (after b1 (after b0 entryS)).mem, w.r = 0 ∧ w.off + w.n ≤ 96) ∧
    (after b1 (after b0 entryS)).reg .rdi = some (.ptr 1 328) ∧
    (after b1 (after b0 entryS)).reg .rsi = some (.load 1 360 8) ∧
    (after b1 (after b0 entryS)).reg .r15 = some (.load 1 360 8) ∧
    (after b1 (after b0 entryS)).reg .rbx = some (.ptr 1 0) ∧
    (after b1 (after b0 entryS)).reg .rbp = some (.reg .rdx) ∧
    (after b1 (after b0 entryS)).reg .r12 = some (.reg .r8) ∧
    (after b1 (after b0 entryS)).reg .r13 = some (.reg .rcx) ∧
    (after b1 (after b0 entryS)).reg .r14 = some (.reg .rdi) := by
  decide +kernel
public theorem exit_b2 : exec b2 retS = some (after b2 retS, .cond c2 NativeRustcVmX64.Vm.TStateQueryOpenings.label_4) :=
  run_b2.trans (by rw [after_eq run_b2]; rfl)
public theorem ok_b2 : MidOk 96 8 slots (after b2 retS) = true ∧ (after b2 retS).mem = [] ∧
    KeepAll (after b2 retS) = true := by
  decide +kernel
public theorem exit_b3 : exec b3 openS = some (after b3 openS,
    .call NativeRustcVmX64.Vm.OpenPhase.entryLabel) :=
  run_b3.trans (by rw [after_eq run_b3])
public theorem ok_b3 : MidOk 96 0 slots (after b3 openS) = true ∧
    (∀ w ∈ (after b3 openS).mem, w.r = 0 ∧ w.off + w.n ≤ 16) ∧
    WordW 0 8 (.reg .rax) (after b3 openS) ∧
    (after b3 openS).reg .rdi = some (.ptr 0 16) ∧
    (after b3 openS).reg .rsi = some (.bin .add .W64 (.lit 368) rootSym) ∧
    (after b3 openS).reg .rdx = some (.load 1 400 8) ∧
    (after b3 openS).reg .rcx = some (.load 1 408 8) ∧
    (after b3 openS).reg .r8 = some (.reg .r13) ∧ (after b3 openS).reg .r9 = some (.reg .r12) ∧
    KeepBut [.rcx, .rdx, .rsi, .rdi, .r8, .r9] (after b3 openS) = true := by
  decide +kernel
public theorem exit_b4 : exec b4 retS = some (after b4 retS, .cond c4 NativeRustcVmX64.Vm.TStateQueryOpenings.label_4) :=
  run_b4.trans (by rw [after_eq run_b4]; rfl)
public theorem ok_b4 : MidOk 96 8 slots (after b4 retS) = true ∧ (after b4 retS).mem = [] ∧
    KeepAll (after b4 retS) = true := by
  decide +kernel
public theorem exit_b5 :
    exec b5 okS = some (after b5 okS, .jump NativeRustcVmX64.Vm.TStateQueryOpenings.label_5) :=
  run_b5.trans (by rw [after_eq run_b5])
public theorem exit_b7o :
    exec b7 (after b5 okS) = some (after b7 (after b5 okS), .ret (.load 0 96 8)) :=
  run_b7o.trans (by rw [after_eq run_b7o])
public theorem ok_ok : EpiOk 96 slots (after b7 (after b5 okS)) = true ∧
    WordW 1 0 (.load 0 16 8) (after b7 (after b5 okS)) ∧
    WordW 1 8 (.load 0 24 8) (after b7 (after b5 okS)) ∧
    WordW 1 16 (.load 0 32 8) (after b7 (after b5 okS)) ∧
    WordW 1 24 (.load 0 40 8) (after b7 (after b5 okS)) ∧
    WordW 2 360 (.bin .add .W64 (.reg .r15) (.lit 1)) (after b7 (after b5 okS)) ∧
    (∀ w ∈ (after b7 (after b5 okS)).mem, (w.r = 1 ∧ w.off + w.n ≤ 32) ∨
      (w.r = 2 ∧ 360 ≤ w.off ∧ w.off + w.n ≤ 368)) := by
  decide +kernel
public theorem exit_b6 : exec b6 failS = some (after b6 failS, .fall) :=
  run_b6.trans (by rw [after_eq run_b6])
public theorem exit_b7f :
    exec b7 (after b6 failS) = some (after b7 (after b6 failS), .ret (.load 0 96 8)) :=
  run_b7f.trans (by rw [after_eq run_b7f])
public theorem ok_fail : EpiOk 96 slots (after b7 (after b6 failS)) = true ∧
    WordW 1 0 (.lit 0) (after b7 (after b6 failS)) ∧
    (∀ w ∈ (after b7 (after b6 failS)).mem, w.r = 1 ∧ 0 ≤ w.off ∧ w.off + w.n ≤ 32) := by
  decide +kernel

end NativeRustcVmX64.Sumcheck.QueryOpenings
