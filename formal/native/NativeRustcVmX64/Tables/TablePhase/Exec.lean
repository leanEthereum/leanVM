module

public import NativeRustcVmX64.Tables.ColumnClaims.Exec
public import NativeRustcVmX64.Transcript.Frame
public import NativeRustcVmX64.Code.Vm.TablePhase
public meta import NativeRustcVmX64.Code.Vm.TablePhase
public meta import NativeRustcVmX64.Tables.ColumnClaims.Exec
public meta import NativeRustcVmX64.Transcript.Frame

/-!
# `table_phase`'s blocks, run by the symbolic executor (x86-64)

Region 0 is the frame (`Transcript.Frame`, `F = 160`): the six pushes at `112` to `160`, the locals
from `24` (RSP after the prologue), the five powers at `32`, the two words pushed for
`table_sumcheck` at `8` and `16`, its return address at `0`, the other callees' at `16`, the entry's
return address at `160`. `entryS` at the entry (`b0`), `mS` after a call (RSP at `24`: `b1` to `b6`,
`b8`), `s8` after `table_sumcheck` (`b7`).
-/

namespace NativeRustcVmX64.Tables.TablePhase

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.TablePhase NativeRustcVmX64.Transcript

open NativeRustcVmX64.Tables.ColumnClaims (RegsAre)

@[expose] public section

/-- RSP at the frame's offset `o`. -/
def stO (o : Nat) : SState := init [168] [(.rsp, .ptr 0 (o : Int))]
/-- At the entry. -/
abbrev entryS : SState := stO 160
/-- After a call returned, RSP at `24`. -/
abbrev mS : SState := stO 24
/-- After `table_sumcheck` returned, RSP at `8`. -/
abbrev s8 : SState := stO 8

/-- The pushed registers' slots. -/
def slots : Slots := [(152, .rbp), (144, .r15), (136, .r14), (128, .r13), (120, .r12), (112, .rbx)]

/-- Every write in region 0. -/
def In0 (S : SState) : Prop := ∀ w ∈ S.mem, w.r = 0

instance (S : SState) : Decidable (In0 S) := by unfold In0; infer_instance

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 mS
sym_block run_b2 := exec b2 mS
sym_block run_b3 := exec b3 mS
sym_block run_b4 := exec b4 mS
sym_block run_b5 := exec b5 mS
sym_block run_b6 := exec b6 mS
sym_block run_b7 := exec b7 s8
sym_block run_b8 := exec b8 mS

public theorem ok_b0 : ProOk 160 16 slots (after b0 entryS) = true ∧ In0 (after b0 entryS) ∧
    RegsAre (after b0 entryS) [(.rbx, .reg .rcx), (.r14, .reg .rdx), (.r15, .reg .rsi),
      (.r12, .reg .rdi), (.rdi, .lit 3)] := by
  decide +kernel

public theorem ok_b1 : MidOk 160 16 slots (after b1 mS) = true ∧ In0 (after b1 mS) ∧
    RegsAre (after b1 mS) [(.rdi, .reg .r12), (.rbp, .lit 0), (.rsi, .un .trunc .W32 (.ite
      (.cmp .ult .W32 (.reg .rax) (.lit 3)) (.lit 0) (.bin .sub .W32 (.reg .rax) (.lit 3)))),
      (.rbx, .reg .rbx), (.r12, .reg .r12), (.r14, .reg .r14), (.r15, .reg .r15)] := by
  decide +kernel

public theorem ok_b2 : MidOk 160 24 slots (after b2 mS) = true ∧ (after b2 mS).mem = [] ∧
    RegsAre (after b2 mS) [(.rbp, .reg .rbp), (.rbx, .reg .rbx), (.r12, .reg .r12), (.r14, .reg .r14), (.r15, .reg .r15)] := by
  decide +kernel

public theorem ok_b3 : MidOk 160 16 slots (after b3 mS) = true ∧ In0 (after b3 mS) ∧
    RegsAre (after b3 mS) [(.rdi, .reg .r12), (.rbp, .reg .rbp), (.rbx, .reg .rbx), (.r12, .reg .r12), (.r14, .reg .r14), (.r15, .reg .r15)] := by
  decide +kernel

public theorem ok_b4 : MidOk 160 16 slots (after b4 mS) = true ∧ In0 (after b4 mS) ∧
    (∀ w ∈ (after b4 mS).mem, w.off + w.n ≤ 24 ∨ (32 ≤ w.off ∧ w.off + w.n ≤ 112)) ∧
    RegsAre (after b4 mS) [(.r13, .ptr 0 64), (.rbp, .ptr 0 32), (.rcx, .lit 5), (.rdi, .reg .rax),
      (.rsi, .reg .rdx), (.rdx, .ptr 0 32),
      (.rbx, .reg .rbx), (.r12, .reg .r12), (.r14, .reg .r14), (.r15, .reg .r15)] := by
  decide +kernel

public theorem ok_b5 : MidOk 160 16 slots (after b5 mS) = true ∧ In0 (after b5 mS) ∧
    (∀ w ∈ (after b5 mS).mem, w.off + w.n ≤ 24) ∧
    RegsAre (after b5 mS) [(.rdx, .bin .add .W64 (.reg .r14) (.lit 107720)), (.rsi, .lit 3),
      (.rcx, .lit 3), (.rdi, .reg .r13), (.rbp, .reg .rbp), (.r13, .reg .r13),
      (.rbx, .reg .rbx), (.r12, .reg .r12), (.r14, .reg .r14), (.r15, .reg .r15)] := by
  decide +kernel

public theorem ok_b6 : MidOk 160 0 slots (after b6 mS) = true ∧ In0 (after b6 mS) ∧
    (∀ w ∈ (after b6 mS).mem, w.off + w.n ≤ 24) ∧
    RegsAre (after b6 mS) [(.rdi, .reg .r12), (.rsi, .bin .add .W64 (.lit 24) (.reg .r15)),
      (.rdx, .reg .r14), (.rcx, .reg .rbp), (.r8, .reg .r13), (.r9, .reg .rax)] ∧
    (∀ t < 8, findWrite 0 (8 + t) (after b6 mS).mem = some (.reg .rdx, t)) ∧
    (∀ t < 8, findWrite 0 (16 + t) (after b6 mS).mem = some (.reg .rbx, t)) := by
  decide +kernel

public theorem ok_b7 : MidOk 160 24 slots (after b7 s8) = true ∧ (after b7 s8).mem = [] ∧
    RegsAre (after b7 s8) [(.rbp, .un .trunc .W32 (.reg .rax))] := by
  decide +kernel

public theorem ok_b8 : EpiOk 160 slots (after b8 mS) = true ∧ (after b8 mS).mem = [] ∧
    RegsAre (after b8 mS) [(.rax, .un .trunc .W32 (.reg .rbp))] := by
  decide +kernel

end NativeRustcVmX64.Tables.TablePhase
