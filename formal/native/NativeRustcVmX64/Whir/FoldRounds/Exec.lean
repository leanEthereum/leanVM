module

public import NativeRustcVmX64.Whir.Common
public import NativeRustcVmX64.Whir.SampleQueries.Exec
public import NativeRustcVmX64.Code.Vm.FoldRounds
public meta import NativeRustcVmX64.Code.Vm.FoldRounds
public meta import NativeRustcVmX64.Whir.Common
public meta import NativeRustcVmX64.Whir.SampleQueries.Exec

/-!
# `fold_rounds`' blocks, run by the symbolic executor (x86-64)

Region 0 is the 160-byte frame (RBP, R15, R14, R13, R12, RBX pushed at offsets `152` to `112`,
`fold_round`'s output at `40`, a copy of its `α`, `β` at `8`, a callee's return address at `0`)
and the return address at `160`. rustc unrolled the (at most `6`) rounds.
- `entryS` at the entry, region 1 the buffer's count word at RCX: the prologue `b0` (the count
  cleared, BL `1`); `n = 0` returns (`b21`, `ok_b21z`), else `b1` calls `fold_round` (`ok_b1`);
- `midS` (RSP at offset `8`), the frame only: each round's tag test (`b2`, `b5`, `b8`, `b11`,
  `b14`, `b17`; `TagOk`), each next round's call (`b4`, `b7`, `b10`, `b13`, `b16`; `CallOk`), the
  rejection `b20` (EBX cleared) and the return `b21` (AL the low byte of EBX);
- `store0S`, `storeS` (round `1`; rounds `2` to `6`, RBP the output's `α`): region 1 the buffer;
  each round's store (`b3`, `b6`, `b9`, `b12`, `b15`, `b18`; `StoreOk`): its `α`, `β` pushed,
  the count, then `n` compared with the rounds done.
`b19`, a seventh round, is never reached (`n ≤ 6`).
-/

namespace NativeRustcVmX64.Whir.FoldRounds

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.FoldRounds
open NativeRustcVmX64.Transcript (Slots ProOk MidOk EpiOk writesIn)
open NativeRustcVmX64.Whir.SampleQueries (wr0 miss wrote kept)

@[expose] public section

/-- The frame's slots. -/
def slots : Slots := [(152, .rbp), (144, .r15), (136, .r14), (128, .r13), (120, .r12), (112, .rbx)]

/-- At the entry: the frame, the buffer's count word at RCX. -/
def entryS : SState := init [168, 8] [(.rsp, .ptr 0 160), (.rcx, .ptr 1 0)]
/-- After the prologue. -/
def S0 : SState := after b0 entryS
/-- RSP at offset `8`: the frame only. -/
def midS : SState := init [168] [(.rsp, .ptr 0 8)]
/-- The first round's store: region 1 the buffer at R12. -/
def store0S : SState := init [168, 200] [(.rsp, .ptr 0 8), (.r12, .ptr 1 0)]
/-- A later round's store: region 1 the buffer at R12, RBP the output's `α`. -/
def storeS : SState := init [168, 200] [(.rsp, .ptr 0 8), (.r12, .ptr 1 0), (.rbp, .ptr 0 48)]

/-- The callee-saved registers. -/
def cs : List Reg64 := [.rbx, .rbp, .r12, .r13, .r14, .r15]

/-- Every write in the frame or the count word. -/
def entryW (S : SState) : Bool :=
  S.mem.all fun w ↦ (w.r == 0 && decide (w.off + w.n ≤ 160)) || (w.r == 1 && decide (w.off + w.n ≤ 8))

/-- Every write of round `i`'s store: the count, the round's item, the frame's copy. -/
def storeW (S : SState) (i : Nat) : Bool :=
  S.mem.all fun w ↦ (w.r == 1 && decide (w.off + w.n ≤ 8)) ||
    (w.r == 1 && decide (8 + 32 * i ≤ w.off) && decide (w.off + w.n ≤ 40 + 32 * i)) ||
    (w.r == 0 && decide (8 ≤ w.off) && decide (w.off + w.n ≤ 40))

/-- A round's tag test: no write, the registers kept. -/
def TagOk (S : SState) : Prop := MidOk 160 8 slots S = true ∧ S.mem = [] ∧ kept S cs = true

/-- A round's call: `fold_round(rsp + 32, t, s)`. -/
def CallOk (S : SState) : Prop :=
  MidOk 160 0 slots S = true ∧ wr0 S 8 = true ∧ S.reg .rdi = some (.ptr 0 40) ∧
    S.reg .rsi = some (.reg .r15) ∧ S.reg .rdx = some (.reg .r14) ∧ kept S cs = true

/-- Round `i`'s store (from `0`): the output's `α`, `β` into the buffer's item `i`, the count
`i + 1`. -/
def StoreOk (i : Nat) (S : SState) : Prop :=
  MidOk 160 8 slots S = true ∧ wrote S 1 0 (.lit (i + 1)) = true ∧
    wrote S 1 (8 + 32 * i) (.load 0 48 8) = true ∧ wrote S 1 (16 + 32 * i) (.load 0 56 8) = true ∧
    wrote S 1 (24 + 32 * i) (.load 0 64 8) = true ∧ wrote S 1 (32 + 32 * i) (.load 0 72 8) = true ∧
    storeW S i = true ∧ S.reg .r12 = some (.ptr 1 0) ∧ S.reg .rbp = some (.ptr 0 48) ∧
    kept S [.rbx, .r13, .r14, .r15] = true

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b21z := exec b21 S0
sym_block run_b1 := exec b1 S0
sym_block run_b2 := exec b2 midS
sym_block run_b3 := exec b3 store0S
sym_block run_b4 := exec b4 midS
sym_block run_b5 := exec b5 midS
sym_block run_b6 := exec b6 storeS
sym_block run_b7 := exec b7 midS
sym_block run_b8 := exec b8 midS
sym_block run_b9 := exec b9 storeS
sym_block run_b10 := exec b10 midS
sym_block run_b11 := exec b11 midS
sym_block run_b12 := exec b12 storeS
sym_block run_b13 := exec b13 midS
sym_block run_b14 := exec b14 midS
sym_block run_b15 := exec b15 storeS
sym_block run_b16 := exec b16 midS
sym_block run_b17 := exec b17 midS
sym_block run_b18 := exec b18 storeS
sym_block run_b20 := exec b20 midS
sym_block run_b21 := exec b21 midS

/-! ## The entry -/

public theorem ok_b21z : EpiOk 160 [] (after b21 S0) = true ∧ entryW (after b21 S0) = true ∧
    wrote (after b21 S0) 1 0 (.lit 0) = true ∧
    (after b21 S0).reg .rax = some (.un .trunc .W32 (.bin .merge .W8 (.reg .rbx) (.lit 1))) := by
  decide +kernel
public theorem ok_b1 : ProOk 160 0 slots (after b1 S0) = true ∧ entryW (after b1 S0) = true ∧
    wrote (after b1 S0) 1 0 (.lit 0) = true ∧ (after b1 S0).reg .rdi = some (.ptr 0 40) ∧
    (after b1 S0).reg .rsi = some (.reg .rdi) ∧ (after b1 S0).reg .rdx = some (.reg .rdx) ∧
    (after b1 S0).reg .r12 = some (.ptr 1 0) ∧ (after b1 S0).reg .r13 = some (.reg .rsi) ∧
    (after b1 S0).reg .r14 = some (.reg .rdx) ∧ (after b1 S0).reg .r15 = some (.reg .rdi) ∧
    (after b1 S0).reg .rbx = some (.bin .merge .W8 (.reg .rbx) (.lit 1)) := by
  decide +kernel

/-! ## The rounds -/

public theorem ok_b2 : TagOk (after b2 midS) := by unfold TagOk; decide +kernel
public theorem ok_b5 : TagOk (after b5 midS) := by unfold TagOk; decide +kernel
public theorem ok_b8 : TagOk (after b8 midS) := by unfold TagOk; decide +kernel
public theorem ok_b11 : TagOk (after b11 midS) := by unfold TagOk; decide +kernel
public theorem ok_b14 : TagOk (after b14 midS) := by unfold TagOk; decide +kernel
public theorem ok_b17 : TagOk (after b17 midS) := by unfold TagOk; decide +kernel
public theorem ok_b4 : CallOk (after b4 midS) := by unfold CallOk; decide +kernel
public theorem ok_b7 : CallOk (after b7 midS) := by unfold CallOk; decide +kernel
public theorem ok_b10 : CallOk (after b10 midS) := by unfold CallOk; decide +kernel
public theorem ok_b13 : CallOk (after b13 midS) := by unfold CallOk; decide +kernel
public theorem ok_b16 : CallOk (after b16 midS) := by unfold CallOk; decide +kernel
public theorem ok_b3 : StoreOk 0 (after b3 store0S) := by unfold StoreOk; decide +kernel
public theorem ok_b6 : StoreOk 1 (after b6 storeS) := by unfold StoreOk; decide +kernel
public theorem ok_b9 : StoreOk 2 (after b9 storeS) := by unfold StoreOk; decide +kernel
public theorem ok_b12 : StoreOk 3 (after b12 storeS) := by unfold StoreOk; decide +kernel
public theorem ok_b15 : StoreOk 4 (after b15 storeS) := by unfold StoreOk; decide +kernel
public theorem ok_b18 : StoreOk 5 (after b18 storeS) := by unfold StoreOk; decide +kernel

/-! ## The exits -/

public theorem ok_b20 : MidOk 160 8 slots (after b20 midS) = true ∧ (after b20 midS).mem = [] ∧
    (after b20 midS).reg .rbx = some (.lit 0) := by decide +kernel
public theorem ok_b21 : EpiOk 160 slots (after b21 midS) = true ∧ (after b21 midS).mem = [] ∧
    (after b21 midS).reg .rax = some (.un .trunc .W32 (.reg .rbx)) := by decide +kernel

end NativeRustcVmX64.Whir.FoldRounds
