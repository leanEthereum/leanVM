module

public import NativeRustcVmX64.Sumcheck.Common
public import NativeRustcVmX64.Bus.Facts
public import NativeRustcVmX64.Code.Vm.VerifyBusBalance
public import NativeRustcVmX64.Code.Vm.AccumulateSide.Names
public import NativeRustcVmX64.Code.Vm.BitLength.Names
public import NativeRustcVmX64.Code.Vm.BufEW63Extend.Names
public import NativeRustcVmX64.Code.Vm.BusLayout.Names
public import NativeRustcVmX64.Code.Vm.BytecodeShare.Names
public import NativeRustcVmX64.Code.Vm.ComputedBytecodeValue.Names
public import NativeRustcVmX64.Code.Vm.Kpow.Names
public import NativeRustcVmX64.Code.Vm.Memcpy.Names
public import NativeRustcVmX64.Code.Vm.Names
public import NativeRustcVmX64.Code.Vm.PushClaim.Names
public import NativeRustcVmX64.Code.Vm.SpongeWSqueeze.Names
public import NativeRustcVmX64.Code.Vm.TStateGrind.Names
public import NativeRustcVmX64.Code.Vm.TStateReadScalar.Names
public import NativeRustcVmX64.Code.Vm.TStateReadScalars.Names
public import NativeRustcVmX64.Code.Vm.TStateSampleChallenges.Names
public import NativeRustcVmX64.Code.Vm.VerifyBusBalance.Names
public import NativeRustcVmX64.Code.Vm.VerifyBusBalanceClosure0.Names
public import NativeRustcVmX64.Code.Vm.VerifyGkrGrandProducts.Names
public meta import NativeRustcVmX64.Code.Vm.VerifyBusBalance
public meta import NativeRustcVmX64.Sumcheck.Common

/-!
# `verify_bus_balance`'s blocks, run by the symbolic executor (x86-64)

Region 0 is the 5520-byte frame below the entry's RSP and the return address (`F = 5520`): RBP,
R15, R14, R13, R12, RBX pushed at `5512` to `5472`; RSP at `104` in the body, a callee's return
address at `96` (`80` for the closure, `0` for `accumulate_side`, below their stack arguments).
The locals (frame offsets): the bus's address at `112`, the bytecode's at `128`, `136`, the point's
address and length at `104`, `120`, the counts at `144` to `168`, the β at `176`, `184`, the sides'
totals at `192`, `624`, the framework sizes at `328`, the memory's scalars at `216`, the share at
`352`, the closure's environment at `248`, the weights at `368`, callees' outputs at `248`,
`672`, the `GkrStateW` at `1744`, the three side layouts at `2808`, `3696`, `4584`.

- `eS`: the entry, region 1 the layout's first 16 bytes (RSI);
- `fS o`: RSP at `o` (`104` the body, `88` after a closure's call, `8` after `accumulate_side`'s);
- `cS`: region 1 the claims' length word (R15), `b27`;
- `bS`: region 1 the bus, its address the word at `112` (`b44`, `b53`, `b55`);
- `lS B`: the zeroing loops' heads, RAX `8 * v` with `v < B` (`b16`, `b36`, `b37`).
-/

namespace NativeRustcVmX64.Bus.VerifyBusBalance

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.VerifyBusBalance
open NativeRustcVmX64.Transcript NativeRustcVmX64.Sumcheck NativeRustcVmX64.Bus

@[expose] public section

/-- The frame's slots. -/
def slots : Slots :=
  [(5512, .rbp), (5504, .r15), (5496, .r14), (5488, .r13), (5480, .r12), (5472, .rbx)]

/-- The callee-saved registers. -/
def cs : List Reg64 := [.rbx, .rbp, .r12, .r13, .r14, .r15]

/-- Every register but RSP. -/
def nsp : List Reg64 :=
  [.rax, .rbx, .rcx, .rdx, .rsi, .rdi, .rbp, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15]

def l6 : Label := NativeRustcVmX64.Vm.Symbols.rodata6Label
def l7 : Label := NativeRustcVmX64.Vm.Symbols.rodata7Label
def l8 : Label := NativeRustcVmX64.Vm.Symbols.rodata8Label
def l9 : Label := NativeRustcVmX64.Vm.Symbols.rodata9Label
/-- The failure's label. -/
def lF : Label := NativeRustcVmX64.Vm.VerifyBusBalance.label_27

def eS : SState := init [5528, 16] [(.rsp, .ptr 0 5520), (.rsi, .ptr 1 0)]
def fS (o : Nat) : SState := init [5528] [(.rsp, .ptr 0 (o : Int))]
/-- The frame and loader slot for a raw indirect copy. -/
def copyS : SState :=
  (init [5528, 8] [(.rsp, .ptr 0 104)] [] [] [(.gotSlot "memcpy", 1, 0)]).withKnownBytes
    1 0 8 (.label "memcpy")
def cS : SState := init [5528, 8] [(.rsp, .ptr 0 104), (.r15, .ptr 1 0)]
def bS : SState := init [5528, 107768] [(.rsp, .ptr 0 104)] (aliases := [(.load 0 112 8, 1, 0)])
def lS (B : Nat) : SState :=
  init [5528] [(.rsp, .ptr 0 104), (.rax, .bin .mul .W64 (.var 0) (.lit 8))]
    (bounds := [(.var 0, B)])

/-- A block in the body, RSP at `o` at its end. -/
abbrev Mid (o : Nat) (S : SState) : Prop := MidOk 5520 o slots S = true

/-- Every write of region `0` between `lo` and `hi`. -/
def W0 (lo hi : Nat) (S : SState) : Prop := ∀ w ∈ S.mem, w.r = 0 ∧ lo ≤ w.off ∧ w.off + w.n ≤ hi

instance (lo hi : Nat) (S : SState) : Decidable (W0 lo hi S) := by unfold W0; infer_instance

/-- Every write of region `0` between `lo` and `hi` or of region `1` between `lo1` and `hi1`. -/
def W01 (lo hi lo1 hi1 : Nat) (S : SState) : Prop :=
  ∀ w ∈ S.mem, (w.r = 0 ∧ lo ≤ w.off ∧ w.off + w.n ≤ hi) ∨
    (w.r = 1 ∧ lo1 ≤ w.off ∧ w.off + w.n ≤ hi1)

instance (lo hi lo1 hi1 : Nat) (S : SState) : Decidable (W01 lo hi lo1 hi1 S) := by
  unfold W01; infer_instance

/-- A test: nothing written, every register but RSP kept, RSP at `104`. -/
def TestOk (S : SState) : Prop := Mid 104 S ∧ S.mem = [] ∧ Keeps nsp S

instance (S : SState) : Decidable (TestOk S) := by unfold TestOk; infer_instance

/-- The point's length as `b21` reads it. -/
def lenS : Sym := .ite (.cmp .ult .W64 (.load 0 1792 8) (.lit 64)) (.load 0 1792 8) (.lit 0)

/-- The tag word `0` of the output at `o` is `1` (`cmpl $1`). -/
def tag32 (o : Nat) : SBool := .not (.cmp .eq .W32 (.load 0 o 4) (.lit 1))
/-- The tag byte of the output at `o` is `0` (`cmpb $0`). -/
def tag8 (o : Nat) : SBool := .cmp .eq .W8 (.load 0 o 1) (.lit 0)
/-- AL is `0` (`testb %al, %al`). -/
def alZ : SBool := .cmp .eq .W8 (.bin .and .W8 (.reg .rax) (.reg .rax)) (.lit 0)

end

set_option Elab.async false

sym_block run_b0 := exec b0 eS
sym_block run_b1 := exec b1 (fS 104)
sym_block run_b2 := exec b2 copyS
sym_block run_b3 := exec b3 (fS 104)
sym_block run_b4 := exec b4 (fS 104)
sym_block run_b5 := exec b5 copyS
sym_block run_b6 := exec b6 (fS 104)
sym_block run_b7 := exec b7 (fS 104)
sym_block run_b8 := exec b8 copyS
sym_block run_b9 := exec b9 (fS 104)
sym_block run_b10 := exec b10 (fS 104)
sym_block run_b11 := exec b11 (fS 104)
sym_block run_b12 := exec b12 (fS 104)
sym_block run_b13 := exec b13 (fS 104)
sym_block run_b14 := exec b14 (fS 104)
sym_block run_b15 := exec b15 (fS 104)
sym_block run_b16 := exec b16 (lS 132)
sym_block run_b17 := exec b17 copyS
sym_block run_b18 := exec b18 (fS 104)
sym_block run_b19 := exec b19 (fS 104)
sym_block run_b20 := exec b20 (fS 104)
sym_block run_b21 := exec b21 (fS 104)
sym_block run_b22 := exec b22 (fS 104)
sym_block run_b23 := exec b23 (fS 104)
sym_block run_b24 := exec b24 (fS 104)
sym_block run_b25 := exec b25 (fS 104)
sym_block run_b26 := exec b26 (fS 104)
sym_block run_b27 := exec b27 cS
sym_block run_b28 := exec b28 (fS 104)
sym_block run_b29 := exec b29 (fS 104)
sym_block run_b30 := exec b30 (fS 104)
sym_block run_b31 := exec b31 (fS 104)
sym_block run_b32 := exec b32 (fS 104)
sym_block run_b33 := exec b33 (fS 104)
sym_block run_b34 := exec b34 (fS 104)
sym_block run_b35 := exec b35 (fS 104)
sym_block run_b36 := exec b36 (lS 136)
sym_block run_b37 := exec b37 (lS 128)
sym_block run_b38 := exec b38 (fS 104)
sym_block run_b39 := exec b39 (fS 104)
sym_block run_b40 := exec b40 (fS 104)
sym_block run_b41 := exec b41 (fS 104)
sym_block run_b42 := exec b42 (fS 104)
sym_block run_b43 := exec b43 (fS 104)
sym_block run_b44 := exec b44 bS
sym_block run_b45 := exec b45 (fS 104)
sym_block run_b46 := exec b46 (fS 88)
sym_block run_b47 := exec b47 (fS 8)
sym_block run_b48 := exec b48 (fS 104)
sym_block run_b49 := exec b49 (fS 88)
sym_block run_b50 := exec b50 (fS 8)
sym_block run_b51 := exec b51 (fS 104)
sym_block run_b52 := exec b52 (fS 8)
sym_block run_b53 := exec b53 bS
sym_block run_b54 := exec b54 (fS 104)
sym_block run_b55 := exec b55 bS
sym_block run_b56 := exec b56 (fS 104)
sym_block run_b57 := exec b57 (fS 104)

end NativeRustcVmX64.Bus.VerifyBusBalance

namespace NativeRustcVmX64.Bus.VerifyBusBalance

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.VerifyBusBalance
open NativeRustcVmX64.Transcript NativeRustcVmX64.Sumcheck NativeRustcVmX64.Bus

set_option Elab.async false

/-! ## The layouts (`b0` to `b8`) -/

public theorem exit_b0 : exec b0 eS =
    some (after b0 eS, .call NativeRustcVmX64.Vm.BusLayout.entryLabel) :=
  run_b0.trans (by rw [after_eq run_b0])
public theorem ok_b0 : ProOk 5520 96 slots (after b0 eS) = true ∧ W0 96 5520 (after b0 eS) ∧
    Wrote 0 [(128, .reg .rdx), (136, .reg .rcx), (328, .lit 0), (336, .load 1 0 8),
      (344, .load 1 8 8)] (after b0 eS) ∧
    (after b0 eS).reg .rbx = some (.reg .rdi) ∧ (after b0 eS).reg .rcx = some (.label l6) ∧
    (after b0 eS).reg .rdx = some (.lit 3) ∧ (after b0 eS).reg .rsi = some (.ptr 0 328) ∧
    (after b0 eS).reg .rdi = some (.ptr 0 672) ∧ (after b0 eS).reg .rbp = some (.load 1 0 8) ∧
    (after b0 eS).reg .r8 = some (.lit 51) ∧ (after b0 eS).reg .r9 = some (.ptr 1 0) ∧
    (after b0 eS).reg .r12 = some (.reg .r8) ∧ (after b0 eS).reg .r13 = some (.load 1 8 8) ∧
    (after b0 eS).reg .r14 = some (.ptr 1 0) ∧ (after b0 eS).reg .r15 = some (.reg .r9) := by
  decide +kernel

public theorem exit_b1 : exec b1 (fS 104) = some (after b1 (fS 104), .cond (tag32 672) lF) :=
  run_b1.trans (by rw [after_eq run_b1]; rfl)
public theorem ok_b1 : TestOk (after b1 (fS 104)) := by decide +kernel

public theorem exit_b2 : exec b2 copyS = some (after b2 copyS, .call NativeRustcVmX64.Vm.Memcpy.entryLabel) :=
  run_b2.trans (by rw [after_eq run_b2])
public theorem ok_b2 : Mid 96 (after b2 copyS) ∧ W0 96 120 (after b2 copyS) ∧
    Wrote 0 [(112, .reg .r12)] (after b2 copyS) ∧
    (after b2 copyS).reg .rdi = some (.ptr 0 2816) ∧
    (after b2 copyS).reg .rsi = some (.ptr 0 688) ∧
    (after b2 copyS).reg .rdx = some (.lit 880) ∧
    (after b2 copyS).reg .r12 = some (.load 0 680 8) ∧
    Keeps [.rbx, .rbp, .r13, .r14, .r15] (after b2 copyS) := by
  decide +kernel

public theorem exit_b3 : exec b3 (fS 104) =
    some (after b3 (fS 104), .call NativeRustcVmX64.Vm.BusLayout.entryLabel) :=
  run_b3.trans (by rw [after_eq run_b3])
public theorem ok_b3 : Mid 96 (after b3 (fS 104)) ∧ W0 96 2816 (after b3 (fS 104)) ∧
    Wrote 0 [(2808, .reg .r12)] (after b3 (fS 104)) ∧
    (after b3 (fS 104)).reg .rcx = some (.label l7) ∧
    (after b3 (fS 104)).reg .rdx = some (.lit 3) ∧
    (after b3 (fS 104)).reg .rsi = some (.ptr 0 328) ∧
    (after b3 (fS 104)).reg .rdi = some (.ptr 0 672) ∧
    (after b3 (fS 104)).reg .r8 = some (.lit 51) ∧
    (after b3 (fS 104)).reg .r9 = some (.reg .r14) ∧ Keeps cs (after b3 (fS 104)) := by
  decide +kernel

public theorem exit_b4 : exec b4 (fS 104) = some (after b4 (fS 104), .cond (tag8 672) lF) :=
  run_b4.trans (by rw [after_eq run_b4]; rfl)
public theorem ok_b4 : TestOk (after b4 (fS 104)) := by decide +kernel

public theorem exit_b5 : exec b5 copyS = some (after b5 copyS, .call NativeRustcVmX64.Vm.Memcpy.entryLabel) :=
  run_b5.trans (by rw [after_eq run_b5])
public theorem ok_b5 : Mid 96 (after b5 copyS) ∧ W0 96 104 (after b5 copyS) ∧
    (after b5 copyS).reg .rdi = some (.ptr 0 3696) ∧
    (after b5 copyS).reg .rsi = some (.ptr 0 680) ∧
    (after b5 copyS).reg .rdx = some (.lit 888) ∧ Keeps cs (after b5 copyS) := by
  decide +kernel

public theorem exit_b6 : exec b6 (fS 104) =
    some (after b6 (fS 104), .call NativeRustcVmX64.Vm.BusLayout.entryLabel) :=
  run_b6.trans (by rw [after_eq run_b6])
public theorem ok_b6 : Mid 96 (after b6 (fS 104)) ∧ W0 96 104 (after b6 (fS 104)) ∧
    (after b6 (fS 104)).reg .rcx = some (.label l8) ∧
    (after b6 (fS 104)).reg .rdx = some (.lit 0) ∧
    (after b6 (fS 104)).reg .rsi = some (.lit 8) ∧
    (after b6 (fS 104)).reg .rdi = some (.ptr 0 672) ∧
    (after b6 (fS 104)).reg .r8 = some (.lit 45) ∧
    (after b6 (fS 104)).reg .r9 = some (.reg .r14) ∧ Keeps cs (after b6 (fS 104)) := by
  decide +kernel

public theorem exit_b7 : exec b7 (fS 104) = some (after b7 (fS 104), .cond (tag8 672) lF) :=
  run_b7.trans (by rw [after_eq run_b7]; rfl)
public theorem ok_b7 : TestOk (after b7 (fS 104)) := by decide +kernel

public theorem exit_b8 : exec b8 copyS = some (after b8 copyS, .call NativeRustcVmX64.Vm.Memcpy.entryLabel) :=
  run_b8.trans (by rw [after_eq run_b8])
public theorem ok_b8 : Mid 96 (after b8 copyS) ∧ W0 96 104 (after b8 copyS) ∧
    (after b8 copyS).reg .rdi = some (.ptr 0 4584) ∧
    (after b8 copyS).reg .rsi = some (.ptr 0 680) ∧
    (after b8 copyS).reg .rdx = some (.lit 888) ∧ Keeps cs (after b8 copyS) := by
  decide +kernel

/-! ## The grind, the challenges, the GKR walk (`b9` to `b20`) -/

public theorem exit_b9 : exec b9 (fS 104) = some (after b9 (fS 104),
    .cond (.not (.cmp .ult .W64 (.reg .r12) (.lit 64))) lF) :=
  run_b9.trans (by rw [after_eq run_b9]; rfl)
public theorem ok_b9 : TestOk (after b9 (fS 104)) := by decide +kernel

public theorem exit_b10 : exec b10 (fS 104) =
    some (after b10 (fS 104), .call NativeRustcVmX64.Vm.BitLength.entryLabel) :=
  run_b10.trans (by rw [after_eq run_b10])
public theorem ok_b10 : Mid 96 (after b10 (fS 104)) ∧ W0 96 104 (after b10 (fS 104)) ∧
    (after b10 (fS 104)).reg .rdi = some (.un .not .W64 (.bin .shl .W64
      (.lit 18446744073709551615) (.un .trunc .W32 (.reg .r12)))) ∧
    Keeps cs (after b10 (fS 104)) := by
  decide +kernel

public theorem exit_b11 : exec b11 (fS 104) = some (after b11 (fS 104),
    .call NativeRustcVmX64.Vm.TStateGrind.entryLabel) :=
  run_b11.trans (by rw [after_eq run_b11])
public theorem ok_b11 : Mid 96 (after b11 (fS 104)) ∧ W0 96 104 (after b11 (fS 104)) ∧
    (after b11 (fS 104)).reg .rsi = some (.ite (.not (.cmp .ult .W32 (.reg .rax) (.lit 3)))
      (.bin .sub .W32 (.reg .rax) (.lit 3)) (.lit 0)) ∧
    (after b11 (fS 104)).reg .rdi = some (.reg .rbx) ∧ Keeps cs (after b11 (fS 104)) := by
  decide +kernel

public theorem exit_b12 : exec b12 (fS 104) = some (after b12 (fS 104), .cond alZ lF) :=
  run_b12.trans (by rw [after_eq run_b12]; rfl)
public theorem ok_b12 : TestOk (after b12 (fS 104)) := by decide +kernel

public theorem exit_b13 : exec b13 (fS 104) = some (after b13 (fS 104),
    .call NativeRustcVmX64.Vm.TStateSampleChallenges.entryLabel) :=
  run_b13.trans (by rw [after_eq run_b13])
public theorem ok_b13 : Mid 96 (after b13 (fS 104)) ∧ W0 96 624 (after b13 (fS 104)) ∧
    (after b13 (fS 104)).reg .rdi = some (.reg .rbx) ∧
    (after b13 (fS 104)).reg .rsi = some (.ptr 0 368) ∧
    (after b13 (fS 104)).reg .rdx = some (.lit 16) ∧ Keeps cs (after b13 (fS 104)) := by
  decide +kernel

public theorem exit_b14 : exec b14 (fS 104) = some (after b14 (fS 104),
    .call NativeRustcVmX64.Vm.SpongeWSqueeze.entryLabel) :=
  run_b14.trans (by rw [after_eq run_b14])
public theorem ok_b14 : Mid 96 (after b14 (fS 104)) ∧ W0 96 104 (after b14 (fS 104)) ∧
    (after b14 (fS 104)).reg .rdi = some (.reg .rbx) ∧ Keeps cs (after b14 (fS 104)) := by
  decide +kernel

public theorem exit_b15 : exec b15 (fS 104) = some (after b15 (fS 104), .fall) :=
  run_b15.trans (by rw [after_eq run_b15])
public theorem ok_b15 : Mid 104 (after b15 (fS 104)) ∧ W0 176 192 (after b15 (fS 104)) ∧
    Wrote 0 [(176, .reg .rdx), (184, .reg .rax)] (after b15 (fS 104)) ∧
    (after b15 (fS 104)).reg .rax = some (.lit 40) ∧ Keeps cs (after b15 (fS 104)) := by
  decide +kernel

public theorem exit_b16 : exec b16 (lS 132) = some (after b16 (lS 132),
    .cond (.not (.cmp .eq .W64 (.bin .add .W64 (.lit 48) (.bin .mul .W64 (.var 0) (.lit 8)))
      (.lit 1048))) NativeRustcVmX64.Vm.VerifyBusBalance.label_6) :=
  run_b16.trans (by rw [after_eq run_b16])
public theorem ok_b16 : Mid 104 (after b16 (lS 132)) ∧ W0 632 1728 (after b16 (lS 132)) ∧
    (after b16 (lS 132)).reg .rax =
      some (.bin .add .W64 (.lit 48) (.bin .mul .W64 (.var 0) (.lit 8))) ∧
    Keeps cs (after b16 (lS 132)) := by
  decide +kernel

public theorem exit_b17 : exec b17 copyS = some (after b17 copyS, .call NativeRustcVmX64.Vm.Memcpy.entryLabel) :=
  run_b17.trans (by rw [after_eq run_b17])
public theorem ok_b17 : Mid 96 (after b17 copyS) ∧ W0 96 104 (after b17 copyS) ∧
    (after b17 copyS).reg .rdi = some (.ptr 0 1800) ∧
    (after b17 copyS).reg .rsi = some (.ptr 0 672) ∧
    (after b17 copyS).reg .rdx = some (.lit 1008) ∧ Keeps cs (after b17 copyS) := by
  decide +kernel

public theorem exit_b18 : exec b18 (fS 104) = some (after b18 (fS 104),
    .call NativeRustcVmX64.Vm.VerifyGkrGrandProducts.entryLabel) :=
  run_b18.trans (by rw [after_eq run_b18])
public theorem ok_b18 : Mid 96 (after b18 (fS 104)) ∧ W0 96 1800 (after b18 (fS 104)) ∧
    (after b18 (fS 104)).reg .rdi = some (.ptr 0 672) ∧
    (after b18 (fS 104)).reg .rsi = some (.reg .rbx) ∧
    (after b18 (fS 104)).reg .rdx = some (.reg .r12) ∧
    (after b18 (fS 104)).reg .rcx = some (.ptr 0 1744) ∧ Keeps cs (after b18 (fS 104)) := by
  decide +kernel

public theorem exit_b19 : exec b19 (fS 104) = some (after b19 (fS 104), .cond (tag32 672) lF) :=
  run_b19.trans (by rw [after_eq run_b19]; rfl)
public theorem ok_b19 : TestOk (after b19 (fS 104)) := by decide +kernel

public theorem exit_b20 : exec b20 (fS 104) = some (after b20 (fS 104),
    .cond (.cmp .eq .W64 (.bin .or .W64 (.load 0 688 8) (.load 0 680 8)) (.lit 0)) lF) :=
  run_b20.trans (by rw [after_eq run_b20]; rfl)
public theorem ok_b20 : Mid 104 (after b20 (fS 104)) ∧ (after b20 (fS 104)).mem = [] ∧
    Keeps cs (after b20 (fS 104)) := by
  decide +kernel

/-! ## The scalars (`b21` to `b26`) -/

public theorem exit_b21 : exec b21 (fS 104) = some (after b21 (fS 104),
    .call NativeRustcVmX64.Vm.TStateReadScalars.entryLabel) :=
  run_b21.trans (by rw [after_eq run_b21])
public theorem ok_b21 : Mid 96 (after b21 (fS 104)) ∧ W0 96 248 (after b21 (fS 104)) ∧
    Wrote 0 [(104, .ite (.cmp .ult .W64 (.load 0 1792 8) (.lit 64)) (.ptr 0 1800) (.lit 8)),
      (120, lenS)] (after b21 (fS 104)) ∧
    (after b21 (fS 104)).reg .rdi = some (.reg .rbx) ∧
    (after b21 (fS 104)).reg .rsi = some (.ptr 0 216) ∧
    (after b21 (fS 104)).reg .rdx = some (.lit 2) ∧
    (after b21 (fS 104)).reg .rbp =
      some (.ite (.not (.cmp .ult .W64 (.reg .rbp) lenS)) lenS (.reg .rbp)) ∧
    (after b21 (fS 104)).reg .r12 = some (.ite (.cmp .ult .W64 (.reg .r13) lenS) (.reg .r13) lenS) ∧
    Keeps [.rbx, .r13, .r14, .r15] (after b21 (fS 104)) := by
  decide +kernel

public theorem exit_b22 : exec b22 (fS 104) = some (after b22 (fS 104), .cond alZ lF) :=
  run_b22.trans (by rw [after_eq run_b22]; rfl)
public theorem ok_b22 : TestOk (after b22 (fS 104)) := by decide +kernel

public theorem exit_b23 : exec b23 (fS 104) = some (after b23 (fS 104),
    .call NativeRustcVmX64.Vm.TStateReadScalar.entryLabel) :=
  run_b23.trans (by rw [after_eq run_b23])
public theorem ok_b23 : Mid 96 (after b23 (fS 104)) ∧ W0 96 104 (after b23 (fS 104)) ∧
    (after b23 (fS 104)).reg .rdi = some (.ptr 0 672) ∧
    (after b23 (fS 104)).reg .rsi = some (.reg .rbx) ∧ Keeps cs (after b23 (fS 104)) := by
  decide +kernel

public theorem exit_b24 : exec b24 (fS 104) = some (after b24 (fS 104), .cond (tag8 672) lF) :=
  run_b24.trans (by rw [after_eq run_b24]; rfl)
public theorem ok_b24 : TestOk (after b24 (fS 104)) := by decide +kernel

public theorem exit_b25 : exec b25 (fS 104) = some (after b25 (fS 104),
    .call NativeRustcVmX64.Vm.TStateReadScalar.entryLabel) :=
  run_b25.trans (by rw [after_eq run_b25])
public theorem ok_b25 : Mid 96 (after b25 (fS 104)) ∧ W0 96 176 (after b25 (fS 104)) ∧
    Wrote 0 [(160, .load 0 688 8), (168, .load 0 680 8)] (after b25 (fS 104)) ∧
    (after b25 (fS 104)).reg .rdi = some (.ptr 0 672) ∧
    (after b25 (fS 104)).reg .rsi = some (.reg .rbx) ∧ Keeps cs (after b25 (fS 104)) := by
  decide +kernel

public theorem exit_b26 : exec b26 (fS 104) = some (after b26 (fS 104), .cond (tag8 672) lF) :=
  run_b26.trans (by rw [after_eq run_b26]; rfl)
public theorem ok_b26 : TestOk (after b26 (fS 104)) := by decide +kernel

/-! ## The claims (`b27` to `b34`) -/

public theorem exit_b27 : exec b27 cS =
    some (after b27 cS, .call NativeRustcVmX64.Vm.PushClaim.entryLabel) :=
  run_b27.trans (by rw [after_eq run_b27])
public theorem ok_b27 : Mid 96 (after b27 cS) ∧ W01 96 160 0 8 (after b27 cS) ∧
    Wrote 0 [(144, .load 0 688 8), (152, .load 0 680 8)] (after b27 cS) ∧
    Wrote 1 [(0, .lit 0)] (after b27 cS) ∧
    (after b27 cS).reg .rdi = some (.ptr 1 0) ∧ (after b27 cS).reg .rsi = some (.lit 0) ∧
    (after b27 cS).reg .rdx = some (.load 0 104 8) ∧ (after b27 cS).reg .rcx = some (.reg .rbp) ∧
    (after b27 cS).reg .r8 = some (.load 0 216 8) ∧ (after b27 cS).reg .r9 = some (.load 0 224 8) ∧
    (after b27 cS).reg .r15 = some (.ptr 1 0) ∧ Keeps [.rbx, .rbp, .r12, .r13, .r14] (after b27 cS) := by
  decide +kernel

public theorem exit_b28 : exec b28 (fS 104) = some (after b28 (fS 104), .cond alZ lF) :=
  run_b28.trans (by rw [after_eq run_b28]; rfl)
public theorem ok_b28 : TestOk (after b28 (fS 104)) := by decide +kernel

public theorem exit_b29 : exec b29 (fS 104) =
    some (after b29 (fS 104), .call NativeRustcVmX64.Vm.PushClaim.entryLabel) :=
  run_b29.trans (by rw [after_eq run_b29])
public theorem ok_b29 : Mid 96 (after b29 (fS 104)) ∧ W0 96 104 (after b29 (fS 104)) ∧
    (after b29 (fS 104)).reg .rdi = some (.reg .r15) ∧
    (after b29 (fS 104)).reg .rsi = some (.lit 1) ∧
    (after b29 (fS 104)).reg .rdx = some (.load 0 104 8) ∧
    (after b29 (fS 104)).reg .rcx = some (.reg .rbp) ∧
    (after b29 (fS 104)).reg .r8 = some (.load 0 232 8) ∧
    (after b29 (fS 104)).reg .r9 = some (.load 0 240 8) ∧ Keeps cs (after b29 (fS 104)) := by
  decide +kernel

public theorem exit_b30 : exec b30 (fS 104) = some (after b30 (fS 104), .cond alZ lF) :=
  run_b30.trans (by rw [after_eq run_b30]; rfl)
public theorem ok_b30 : TestOk (after b30 (fS 104)) := by decide +kernel

public theorem exit_b31 : exec b31 (fS 104) =
    some (after b31 (fS 104), .call NativeRustcVmX64.Vm.PushClaim.entryLabel) :=
  run_b31.trans (by rw [after_eq run_b31])
public theorem ok_b31 : Mid 96 (after b31 (fS 104)) ∧ W0 96 104 (after b31 (fS 104)) ∧
    (after b31 (fS 104)).reg .rdi = some (.reg .r15) ∧
    (after b31 (fS 104)).reg .rsi = some (.lit 2) ∧
    (after b31 (fS 104)).reg .rdx = some (.load 0 104 8) ∧
    (after b31 (fS 104)).reg .rcx = some (.reg .rbp) ∧
    (after b31 (fS 104)).reg .r8 = some (.load 0 168 8) ∧
    (after b31 (fS 104)).reg .r9 = some (.load 0 160 8) ∧ Keeps cs (after b31 (fS 104)) := by
  decide +kernel

public theorem exit_b32 : exec b32 (fS 104) = some (after b32 (fS 104), .cond alZ lF) :=
  run_b32.trans (by rw [after_eq run_b32]; rfl)
public theorem ok_b32 : TestOk (after b32 (fS 104)) := by decide +kernel

public theorem exit_b33 : exec b33 (fS 104) =
    some (after b33 (fS 104), .call NativeRustcVmX64.Vm.PushClaim.entryLabel) :=
  run_b33.trans (by rw [after_eq run_b33])
public theorem ok_b33 : Mid 96 (after b33 (fS 104)) ∧ W0 96 104 (after b33 (fS 104)) ∧
    (after b33 (fS 104)).reg .rdi = some (.reg .r15) ∧
    (after b33 (fS 104)).reg .rsi = some (.lit 3) ∧
    (after b33 (fS 104)).reg .rdx = some (.load 0 104 8) ∧
    (after b33 (fS 104)).reg .rcx = some (.reg .r12) ∧
    (after b33 (fS 104)).reg .r8 = some (.load 0 152 8) ∧
    (after b33 (fS 104)).reg .r9 = some (.load 0 144 8) ∧ Keeps cs (after b33 (fS 104)) := by
  decide +kernel

public theorem exit_b34 : exec b34 (fS 104) = some (after b34 (fS 104), .cond alZ lF) :=
  run_b34.trans (by rw [after_eq run_b34]; rfl)
public theorem ok_b34 : TestOk (after b34 (fS 104)) := by decide +kernel

/-! ## The share, the bytecode's value (`b35` to `b42`) -/

public theorem exit_b35 : exec b35 (fS 104) = some (after b35 (fS 104), .fall) :=
  run_b35.trans (by rw [after_eq run_b35])
public theorem ok_b35 : Mid 104 (after b35 (fS 104)) ∧ (after b35 (fS 104)).mem = [] ∧
    (after b35 (fS 104)).reg .rax = some (.lit 56) ∧ Keeps cs (after b35 (fS 104)) := by
  decide +kernel

public theorem exit_b36 : exec b36 (lS 136) = some (after b36 (lS 136),
    .cond (.cmp .eq .W64 (.bin .mul .W64 (.var 0) (.lit 8)) (.lit 1080))
      NativeRustcVmX64.Vm.VerifyBusBalance.label_19) :=
  run_b36.trans (by rw [after_eq run_b36])
public theorem ok_b36 : Mid 104 (after b36 (lS 136)) ∧ W0 616 1744 (after b36 (lS 136)) ∧
    Wrote 0 [(616, .ite (.cmp .eq .W64 (.var 0) (.lit 0)) (.lit 0) (.load 0 616 8))]
      (after b36 (lS 136)) ∧
    (∀ w ∈ (after b36 (lS 136)).mem, w.off < 624 → w.off = 616 ∧ w.n = 8) ∧
    (after b36 (lS 136)).reg .rax = some (.bin .mul .W64 (.var 0) (.lit 8)) ∧
    Keeps cs (after b36 (lS 136)) := by
  decide +kernel

public theorem exit_b37 : exec b37 (lS 128) =
    some (after b37 (lS 128), .jump NativeRustcVmX64.Vm.VerifyBusBalance.label_17) :=
  run_b37.trans (by rw [after_eq run_b37])
public theorem ok_b37 : Mid 104 (after b37 (lS 128)) ∧ W0 664 1696 (after b37 (lS 128)) ∧
    (after b37 (lS 128)).reg .rax =
      some (.bin .add .W64 (.lit 64) (.bin .mul .W64 (.var 0) (.lit 8))) ∧
    Keeps cs (after b37 (lS 128)) := by
  decide +kernel

public theorem exit_b38 : exec b38 (fS 104) = some (after b38 (fS 104),
    .call NativeRustcVmX64.Vm.BytecodeShare.entryLabel) :=
  run_b38.trans (by rw [after_eq run_b38])
public theorem ok_b38 : Mid 96 (after b38 (fS 104)) ∧ W0 96 104 (after b38 (fS 104)) ∧
    (after b38 (fS 104)).reg .rdi = some (.ptr 0 248) ∧
    (after b38 (fS 104)).reg .rsi = some (.reg .rbx) ∧
    (after b38 (fS 104)).reg .rdx = some (.ptr 0 368) ∧
    (after b38 (fS 104)).reg .rcx = some (.load 0 104 8) ∧
    (after b38 (fS 104)).reg .r8 = some (.reg .r12) ∧
    (after b38 (fS 104)).reg .r9 = some (.ptr 0 672) ∧
    (after b38 (fS 104)).reg .r15 = some (.ptr 0 368) ∧
    Keeps [.rbx, .rbp, .r12, .r13, .r14] (after b38 (fS 104)) := by
  decide +kernel

public theorem exit_b39 : exec b39 (fS 104) = some (after b39 (fS 104), .cond (tag32 248) lF) :=
  run_b39.trans (by rw [after_eq run_b39]; rfl)
public theorem ok_b39 : TestOk (after b39 (fS 104)) := by decide +kernel

public theorem exit_b40 : exec b40 (fS 104) = some (after b40 (fS 104),
    .cond (.not (.cmp .ult .W64 (.load 0 272 8) (.lit 68))) lF) :=
  run_b40.trans (by rw [after_eq run_b40]; rfl)
public theorem ok_b40 : Mid 104 (after b40 (fS 104)) ∧ W0 352 368 (after b40 (fS 104)) ∧
    Wrote 0 [(352, .load 0 256 8), (360, .load 0 264 8)] (after b40 (fS 104)) ∧
    (after b40 (fS 104)).reg .rcx = some (.load 0 272 8) ∧
    (after b40 (fS 104)).reg .r8 = some (.load 0 280 8) ∧
    (after b40 (fS 104)).reg .r9 = some (.load 0 288 8) ∧ Keeps cs (after b40 (fS 104)) := by
  decide +kernel

public theorem exit_b41 : exec b41 (fS 104) = some (after b41 (fS 104),
    .call NativeRustcVmX64.Vm.ComputedBytecodeValue.entryLabel) :=
  run_b41.trans (by rw [after_eq run_b41])
public theorem ok_b41 : Mid 96 (after b41 (fS 104)) ∧ W0 96 104 (after b41 (fS 104)) ∧
    (after b41 (fS 104)).reg .rdi = some (.load 0 128 8) ∧
    (after b41 (fS 104)).reg .rsi = some (.load 0 136 8) ∧
    (after b41 (fS 104)).reg .rdx = some (.ptr 0 672) ∧
    Keeps [.rcx, .r8, .r9, .rbx, .rbp, .r12, .r13, .r14, .r15] (after b41 (fS 104)) := by
  decide +kernel

public theorem exit_b42 : exec b42 (fS 104) = some (after b42 (fS 104), .cond alZ lF) :=
  run_b42.trans (by rw [after_eq run_b42]; rfl)
public theorem ok_b42 : TestOk (after b42 (fS 104)) := by decide +kernel

/-! ## The sides (`b43` to `b52`) -/

public theorem exit_b43 : exec b43 (fS 104) =
    some (after b43 (fS 104), .call NativeRustcVmX64.Vm.Kpow.entryLabel) :=
  run_b43.trans (by rw [after_eq run_b43])
public theorem ok_b43 : Mid 96 (after b43 (fS 104)) ∧ W0 96 304 (after b43 (fS 104)) ∧
    Wrote 0 [(248, .reg .r15), (256, .ptr 0 216), (264, .load 0 104 8), (272, .reg .rbp),
      (280, .load 0 104 8), (288, .reg .r12), (296, .ptr 0 352)] (after b43 (fS 104)) ∧
    (after b43 (fS 104)).reg .rdi = some (.un .not .W64 (.bin .shl .W64
      (.lit 18446744073709551615) (.un .trunc .W32 (.reg .r13)))) ∧
    (after b43 (fS 104)).reg .rbx = some (.load 0 104 8) ∧
    Keeps [.rbp, .r12, .r13, .r14, .r15] (after b43 (fS 104)) := by
  decide +kernel

public theorem exit_b44 : exec b44 bS =
    some (after b44 bS, .call NativeRustcVmX64.Vm.Kpow.entryLabel) :=
  run_b44.trans (by rw [after_eq run_b44])
public theorem ok_b44 : Mid 96 (after b44 bS) ∧ W01 96 328 0 100784 (after b44 bS) ∧
    Wrote 0 [(128, .reg .rax), (136, .load 0 1760 8), (304, .load 0 1784 8),
      (312, .load 0 1776 8), (320, .load 0 1768 8)] (after b44 bS) ∧
    Wrote 1 ((List.range 18).map fun i ↦ (5928 * i, .lit 0)) (after b44 bS) ∧
    (after b44 bS).reg .rdi = some (.lit 0) ∧ (after b44 bS).reg .rbp = some (.load 0 112 8) ∧
    (after b44 bS).reg .r12 = some (.load 0 1752 8) ∧
    (after b44 bS).reg .r13 = some (.load 0 1744 8) ∧
    Keeps [.rbx, .r14, .r15] (after b44 bS) := by
  decide +kernel

public theorem exit_b45 : exec b45 (fS 104) = some (after b45 (fS 104),
    .call NativeRustcVmX64.Vm.VerifyBusBalanceClosure0.entryLabel) :=
  run_b45.trans (by rw [after_eq run_b45])
public theorem ok_b45 : Mid 80 (after b45 (fS 104)) ∧ W0 80 96 (after b45 (fS 104)) ∧
    Wrote 0 [(88, .lit 0)] (after b45 (fS 104)) ∧
    (after b45 (fS 104)).reg .rdi = some (.ptr 0 624) ∧
    (after b45 (fS 104)).reg .rsi = some (.ptr 0 248) ∧
    (after b45 (fS 104)).reg .rdx = some (.reg .rax) ∧
    (after b45 (fS 104)).reg .rcx = some (.lit 1) ∧
    (after b45 (fS 104)).reg .r8 = some (.lit 0) ∧
    (after b45 (fS 104)).reg .r9 = some (.lit 1) ∧ Keeps cs (after b45 (fS 104)) := by
  decide +kernel

public theorem exit_b46 : exec b46 (fS 88) = some (after b46 (fS 88),
    .call NativeRustcVmX64.Vm.AccumulateSide.entryLabel) :=
  run_b46.trans (by rw [after_eq run_b46])
public theorem ok_b46 : Mid 0 (after b46 (fS 88)) ∧ W0 0 96 (after b46 (fS 88)) ∧
    Wrote 0 [(8, .ptr 0 2808), (16, .ptr 0 624), (24, .lit 3), (32, .reg .r15), (40, .lit 16),
      (48, .load 0 184 8), (56, .load 0 176 8), (64, .reg .rbx), (72, .load 0 120 8),
      (80, .reg .r13), (88, .reg .r12)] (after b46 (fS 88)) ∧
    (after b46 (fS 88)).reg .rdi = some (.ptr 0 192) ∧
    (after b46 (fS 88)).reg .rsi = some (.reg .rbp) ∧
    (after b46 (fS 88)).reg .rdx = some (.lit 0) ∧
    (after b46 (fS 88)).reg .rcx = some (.label l6) ∧
    (after b46 (fS 88)).reg .r8 = some (.lit 51) ∧
    (after b46 (fS 88)).reg .r9 = some (.reg .r14) ∧
    (after b46 (fS 88)).reg .rbx = some (.ptr 0 624) ∧
    Keeps [.rbp, .r12, .r13, .r14, .r15] (after b46 (fS 88)) := by
  decide +kernel

public theorem exit_b47 : exec b47 (fS 8) = some (after b47 (fS 8), .cond (tag32 192) lF) :=
  run_b47.trans (by rw [after_eq run_b47]; rfl)
public theorem ok_b47 : Mid 104 (after b47 (fS 8)) ∧ (after b47 (fS 8)).mem = [] ∧
    Keeps cs (after b47 (fS 8)) := by
  decide +kernel

public theorem exit_b48 : exec b48 (fS 104) = some (after b48 (fS 104),
    .call NativeRustcVmX64.Vm.VerifyBusBalanceClosure0.entryLabel) :=
  run_b48.trans (by rw [after_eq run_b48])
public theorem ok_b48 : Mid 80 (after b48 (fS 104)) ∧ W0 80 96 (after b48 (fS 104)) ∧
    Wrote 0 [(88, .load 0 144 8)] (after b48 (fS 104)) ∧
    (after b48 (fS 104)).reg .rdi = some (.reg .rbx) ∧
    (after b48 (fS 104)).reg .rsi = some (.ptr 0 248) ∧
    (after b48 (fS 104)).reg .rdx = some (.load 0 128 8) ∧
    (after b48 (fS 104)).reg .rcx = some (.load 0 168 8) ∧
    (after b48 (fS 104)).reg .r8 = some (.load 0 160 8) ∧
    (after b48 (fS 104)).reg .r9 = some (.load 0 152 8) ∧
    (after b48 (fS 104)).reg .r13 = some (.load 0 200 8) ∧
    (after b48 (fS 104)).reg .rbp = some (.load 0 208 8) ∧
    Keeps [.rbx, .r12, .r14, .r15] (after b48 (fS 104)) := by
  decide +kernel

public theorem exit_b49 : exec b49 (fS 88) = some (after b49 (fS 88),
    .call NativeRustcVmX64.Vm.AccumulateSide.entryLabel) :=
  run_b49.trans (by rw [after_eq run_b49])
public theorem ok_b49 : Mid 0 (after b49 (fS 88)) ∧ W0 0 96 (after b49 (fS 88)) ∧
    Wrote 0 [(8, .ptr 0 3696), (16, .reg .rbx), (24, .lit 3), (32, .reg .r15), (40, .lit 16),
      (48, .load 0 184 8), (56, .load 0 176 8), (64, .load 0 104 8), (72, .load 0 120 8),
      (80, .load 0 136 8), (88, .load 0 320 8)] (after b49 (fS 88)) ∧
    (after b49 (fS 88)).reg .rdi = some (.ptr 0 192) ∧
    (after b49 (fS 88)).reg .rsi = some (.load 0 112 8) ∧
    (after b49 (fS 88)).reg .rdx = some (.lit 1) ∧
    (after b49 (fS 88)).reg .rcx = some (.label l7) ∧
    (after b49 (fS 88)).reg .r8 = some (.lit 51) ∧
    (after b49 (fS 88)).reg .r9 = some (.reg .r14) ∧ Keeps cs (after b49 (fS 88)) := by
  decide +kernel

public theorem exit_b50 : exec b50 (fS 8) = some (after b50 (fS 8), .cond (tag8 192) lF) :=
  run_b50.trans (by rw [after_eq run_b50]; rfl)
public theorem ok_b50 : Mid 104 (after b50 (fS 8)) ∧ (after b50 (fS 8)).mem = [] ∧
    Keeps cs (after b50 (fS 8)) := by
  decide +kernel

public theorem exit_b51 : exec b51 (fS 104) = some (after b51 (fS 104),
    .call NativeRustcVmX64.Vm.AccumulateSide.entryLabel) :=
  run_b51.trans (by rw [after_eq run_b51])
public theorem ok_b51 : Mid 0 (after b51 (fS 104)) ∧ W0 0 96 (after b51 (fS 104)) ∧
    Wrote 0 [(8, .ptr 0 4584), (16, .lit 8), (24, .lit 0), (32, .label l9), (40, .lit 1),
      (48, .lit 0), (56, .lit 0), (64, .load 0 104 8), (72, .load 0 120 8),
      (80, .load 0 312 8), (88, .load 0 304 8)] (after b51 (fS 104)) ∧
    (after b51 (fS 104)).reg .rdi = some (.ptr 0 624) ∧
    (after b51 (fS 104)).reg .rsi = some (.load 0 112 8) ∧
    (after b51 (fS 104)).reg .rdx = some (.lit 2) ∧
    (after b51 (fS 104)).reg .rcx = some (.label l8) ∧
    (after b51 (fS 104)).reg .r8 = some (.lit 45) ∧
    (after b51 (fS 104)).reg .r9 = some (.reg .r14) ∧
    (after b51 (fS 104)).reg .rbx = some (.load 0 200 8) ∧
    (after b51 (fS 104)).reg .r15 = some (.load 0 208 8) ∧
    Keeps [.rbp, .r12, .r13, .r14] (after b51 (fS 104)) := by
  decide +kernel

public theorem exit_b52 : exec b52 (fS 8) = some (after b52 (fS 8), .cond (tag8 624) lF) :=
  run_b52.trans (by rw [after_eq run_b52]; rfl)
public theorem ok_b52 : Mid 104 (after b52 (fS 8)) ∧ (after b52 (fS 8)).mem = [] ∧
    Keeps cs (after b52 (fS 8)) := by
  decide +kernel

/-! ## The tail and the exits (`b53` to `b57`) -/

public theorem exit_b53 : exec b53 bS = some (after b53 bS,
    .call NativeRustcVmX64.Vm.BufEW63Extend.entryLabel) :=
  run_b53.trans (by rw [after_eq run_b53])
public theorem ok_b53 : Mid 96 (after b53 bS) ∧ W01 96 104 106704 106712 (after b53 bS) ∧
    Wrote 1 [(106704, .lit 0)] (after b53 bS) ∧
    (after b53 bS).reg .rdi = some (.bin .add .W64 (.load 0 112 8) (.lit 106704)) ∧
    (after b53 bS).reg .rsi = some (.load 0 104 8) ∧
    (after b53 bS).reg .rdx = some (.load 0 120 8) ∧
    (after b53 bS).reg .r14 = some (.load 0 632 8) ∧
    (after b53 bS).reg .r12 = some (.load 0 640 8) ∧
    Keeps [.rbx, .rbp, .r13, .r15] (after b53 bS) := by
  decide +kernel

public theorem exit_b54 : exec b54 (fS 104) = some (after b54 (fS 104), .cond alZ lF) :=
  run_b54.trans (by rw [after_eq run_b54]; rfl)
public theorem ok_b54 : TestOk (after b54 (fS 104)) := by decide +kernel

public theorem exit_b55 : exec b55 bS =
    some (after b55 bS, .jump NativeRustcVmX64.Vm.VerifyBusBalance.label_28) :=
  run_b55.trans (by rw [after_eq run_b55])
public theorem ok_b55 : Mid 104 (after b55 bS) ∧ W01 0 0 107720 107768 (after b55 bS) ∧
    Wrote 1 [(107720, .reg .r13), (107728, .reg .rbp), (107736, .reg .rbx),
      (107744, .reg .r15), (107752, .reg .r14), (107760, .reg .r12)] (after b55 bS) ∧
    (after b55 bS).reg .rax = some (.bin .merge .W8 (.load 0 112 8) (.lit 1)) ∧
    Keeps cs (after b55 bS) := by
  decide +kernel

public theorem exit_b56 : exec b56 (fS 104) = some (after b56 (fS 104), .fall) :=
  run_b56.trans (by rw [after_eq run_b56])
public theorem ok_b56 : Mid 104 (after b56 (fS 104)) ∧ (after b56 (fS 104)).mem = [] ∧
    (after b56 (fS 104)).reg .rax = some (.lit 0) ∧ Keeps cs (after b56 (fS 104)) := by
  decide +kernel

public theorem exit_b57 : exec b57 (fS 104) = some (after b57 (fS 104), .ret (.load 0 5520 8)) :=
  run_b57.trans (by rw [after_eq run_b57])
public theorem ok_b57 : EpiOk 5520 slots (after b57 (fS 104)) = true ∧
    (after b57 (fS 104)).mem = [] ∧ Keeps [.rax] (after b57 (fS 104)) := by
  decide +kernel

end NativeRustcVmX64.Bus.VerifyBusBalance
