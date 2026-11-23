module

public import NativeRustcVmX64.Transcript.Frame
public import NativeRustcVmX64.Code.Vm.RingClaimWeight
public import NativeRustcVmX64.Code.Vm.RingClaimWeight.Names
public meta import NativeRustcVmX64.Code.Vm.RingClaimWeight
public meta import NativeRustcVmX64.Transcript.Frame

/-!
# `ring_claim_weight`'s blocks, run by the symbolic executor (x86-64)

Region 0 the 96-byte frame (RBP, R15, R14, R13, R12, RBX pushed at offsets `88` to `48`,
`ring_weight`'s `Option<EW>` at `24`, the coefficients' pointer spilled at `16`, a callee's return
address at `0`) and the return address, region 1 the two argument words `x` above it (reached as
`96(%rsp)`, `104(%rsp)`: the frame offsets `104`, `112` are aliases of region 1's), region 2 the
`Option<EW>` output. From `entryS`: `b0` (the prologue, `eq_above`'s arguments, `call
eq_eval_fn`); from `midS` (RSP at offset `8`, the output in RBX, `x` reached as above): `b1`
(`call ring_weight` into the frame); `b2` (its tag); `b3` (`call EW::mul`); `b4`, `b6` (the product
and the tag `1` stored, the epilogue).
-/

namespace NativeRustcVmX64.Ring.Claim

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.RingClaimWeight NativeRustcVmX64.Transcript

@[expose] public section

/-- The frame's slots. -/
def slots : Slots :=
  [(88, .rbp), (80, .r15), (72, .r14), (64, .r13), (56, .r12), (48, .rbx)]

/-- `x`'s words: the frame offsets `104`, `112`. -/
def xAliases : List (Sym × Nat × Int) := [(.ptr 0 104, 1, 0), (.ptr 0 112, 1, 8)]

/-- At the entry. -/
def entryS : SState :=
  init [104, 16, 24] [(.rsp, .ptr 0 96), (.rdi, .ptr 2 0)] [] [] xAliases

/-- After a call: RSP at offset `8`, the output in RBX. -/
def midS : SState := init [104, 16, 24] [(.rsp, .ptr 0 8), (.rbx, .ptr 2 0)] [] [] xAliases

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 midS
sym_block run_b2 := exec b2 midS
sym_block run_b3 := exec b3 (after b2 midS)
sym_block run_b4 := exec b4 midS
sym_block run_b6 := exec b6 (after b4 midS)

/-! ## What the blocks do -/

/-- `eq_above`'s length: `|x| - vc`, saturating. -/
@[expose] public def satS : Sym :=
  .ite (.cmp .ult .W64 (.load 1 8 8) (.reg .rsi)) (.lit 0) (.bin .sub .W64 (.load 1 8 8) (.reg .rsi))

/-- `eq_above`'s selector: `index >> vc`, `0` when `vc ≥ 64`. -/
@[expose] public def shrS : Sym :=
  .ite (.cmp .ult .W64 (.reg .rsi) (.lit 64)) (.bin .shr .W64 (.reg .rdx) (.reg .rsi)) (.lit 0)

/-- `x`'s rest from `vc`: its address, `8` (dangling) when `vc > |x|`. -/
@[expose] public def aboveS : Sym :=
  .ite ((SBool.cmp .ult .W64 (.reg .rsi) (.load 1 8 8)).or (.cmp .eq .W64 (.reg .rsi) (.load 1 8 8)))
    (.bin .add .W64 (.load 1 0 8) (.bin .shl .W64 (.reg .rsi) (.lit 4))) (.lit 8)

/-- `min(vc, |x|)`. -/
@[expose] public def minS : Sym :=
  .ite (.cmp .ult .W64 (.reg .rsi) (.load 1 8 8)) (.reg .rsi) (.load 1 8 8)

public theorem ok_b0 : ProOk 96 0 slots (after b0 entryS) = true ∧
    (∀ w ∈ (after b0 entryS).mem, w.r = 0 ∧ w.off + w.n ≤ 96) ∧
    (after b0 entryS).reg .rdi = some satS ∧ (after b0 entryS).reg .rcx = some satS ∧
    (after b0 entryS).reg .rsi = some shrS ∧ (after b0 entryS).reg .rdx = some aboveS ∧
    (after b0 entryS).reg .rbx = some (.ptr 2 0) ∧ (after b0 entryS).reg .rbp = some minS ∧
    (after b0 entryS).reg .r12 = some (.reg .rcx) ∧ (after b0 entryS).reg .r15 = some (.reg .r8) ∧
    (∀ t < 8, findWrite 0 (16 + t) (after b0 entryS).mem = some (.reg .r9, t)) := by
  decide +kernel

public theorem ok_b1 : MidOk 96 0 slots (after b1 midS) = true ∧
    (∀ w ∈ (after b1 midS).mem, w.r = 0 ∧ w.off + w.n ≤ 8) ∧
    (after b1 midS).reg .rdi = some (.ptr 0 24) ∧ (after b1 midS).reg .rsi = some (.reg .r12) ∧
    (after b1 midS).reg .rdx = some (.reg .r15) ∧ (after b1 midS).reg .rcx = some (.load 1 0 8) ∧
    (after b1 midS).reg .r8 = some (.reg .rbp) ∧ (after b1 midS).reg .r9 = some (.load 0 16 8) ∧
    (after b1 midS).reg .r13 = some (.reg .rax) ∧ (after b1 midS).reg .r14 = some (.reg .rdx) ∧
    (after b1 midS).reg .rbx = some (.ptr 2 0) := by
  decide +kernel

public theorem exit_b2 : exec b2 midS = some (after b2 midS,
    .cond (SBool.cmp .eq .W32 (.load 0 24 4) (.lit 1)).not NativeRustcVmX64.Vm.RingClaimWeight.label_2) :=
  run_b2.trans (by rw [after_eq run_b2])

public theorem ok_b3 : MidOk 96 0 slots (after b3 (after b2 midS)) = true ∧
    (∀ w ∈ (after b3 (after b2 midS)).mem, w.r = 0 ∧ w.off + w.n ≤ 8) ∧
    (after b3 (after b2 midS)).reg .rdi = some (.reg .r13) ∧
    (after b3 (after b2 midS)).reg .rsi = some (.reg .r14) ∧
    (after b3 (after b2 midS)).reg .rdx = some (.load 0 32 8) ∧
    (after b3 (after b2 midS)).reg .rcx = some (.load 0 40 8) ∧
    (after b3 (after b2 midS)).reg .rbx = some (.ptr 2 0) := by
  decide +kernel

/-- The product and the tag `1` stored, the epilogue. -/
public theorem ok_s : EpiOk 96 slots (after b6 (after b4 midS)) = true ∧
    (∀ t < 8, findWrite 2 t (after b6 (after b4 midS)).mem = some (.lit 1, t)) ∧
    (∀ t < 8, findWrite 2 (8 + t) (after b6 (after b4 midS)).mem = some (.reg .rax, t)) ∧
    (∀ t < 8, findWrite 2 (16 + t) (after b6 (after b4 midS)).mem = some (.reg .rdx, t)) ∧
    (∀ w ∈ (after b6 (after b4 midS)).mem, w.r = 2 ∧ 0 ≤ w.off ∧ w.off + w.n ≤ 24) := by
  decide +kernel

end NativeRustcVmX64.Ring.Claim
