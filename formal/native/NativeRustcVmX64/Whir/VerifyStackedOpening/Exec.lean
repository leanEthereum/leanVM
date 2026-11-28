module

public import NativeRustcVmX64.Transcript.Frame
public import NativeRustcVmX64.Code.Vm.VerifyStackedOpening
public meta import NativeRustcVmX64.Code.Vm.VerifyStackedOpening
public meta import NativeRustcVmX64.Transcript.Frame

/-!
# `verify_stacked_opening`'s blocks, run by the symbolic executor (x86-64)

Region 0 is the 512-byte frame below the entry's RSP and the return address (`Frame`, `F = 512`:
the six pushes from `464`, RSP at offset `8` in the body, a callee's return address at `0`; a
spill at `n(%rsp)` is at offset `8 + n`). Each run starts where a block follows a call or a branch
the proof needs a fact at, from a literal state naming the regions it touches:

- `entryS` (`b0`, then `b1`, `b2`, `b3`, `b5` from its end): the claims' count word at R9;
- `cntS`, `cntBS` (the counting loop, unrolled by two): the layout from `RAX − 120`, the pair of
  claims at RSI; `cntBS` with a column below `158` in R9 (`t3`, three times it, below `472`);
- `tailS` (`b16`): the claims from R13, the last one's index in RCX; `tail2S` (`b17`): the layout
  from `RAX − 120`, a column below `158` in RCX;
- `regS`: the frame alone;
- `argScS` (`b24`): the stack arguments (region 1, aliases of `512(%rsp)` to `528(%rsp)`), the
  scales' count word at the second; `scS` (`b25`): the scales' count word at R14; `sc0S` (`b26`):
  the first scale at RCX; `ringS` (`b27`): the ring switch's target at the spilled `ring`;
- `claimS` (`b34`, `b31`): claim `R13 + RBP`; `place2S` (`b35`): the layout from the spilled
  `RAX`, a column below `158` in RAX; `scaleS` (`b37`, `b39`): the scale at R14;
- `argS` (`b38`, `b46`): the stack arguments; `oodS` (`b41`): the out-of-domain claim at R15;
  `layS` (`b42`): the layout's head at R14; `whirS` (`b48`): the `WhirW`'s state at RAX.
-/

namespace NativeRustcVmX64.Whir.VerifyStackedOpening

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.VerifyStackedOpening
open NativeRustcVmX64.Transcript

@[expose] public section

/-- The frame's slots: the pushed registers. -/
def slots : Slots := [(504, .rbp), (496, .r15), (488, .r14), (480, .r13), (472, .r12), (464, .rbx)]

/-- Three times `x`, as `leaq (%x,%x,2)` computes it. -/
def t3 (x : Sym) : Sym := .bin .add .W64 x (.bin .mul .W64 x (.lit 2))

/-- The stack arguments' aliases: `512(%rsp)` to `528(%rsp)` in the body. -/
def argAl : List (Sym × Nat × Int) := [(.ptr 0 520, 1, 0), (.ptr 0 528, 1, 8), (.ptr 0 536, 1, 16)]

/-- The entry: the frame, the claims' count word at R9. -/
def entryS : SState := init [520, 8] [(.rsp, .ptr 0 512)] [] [] [(.reg .r9, 1, 0)]
/-- The frame alone. -/
def regS : SState := init [520] [(.rsp, .ptr 0 8)]

/-- At the copy, the frame and its read-only `memcpy` loader slot. -/
def copyS : SState :=
  (init [520, 8] [(.rsp, .ptr 0 8)] [] [] [(.gotSlot "memcpy", 1, 0)]).withKnownBytes
    1 0 8 (.label "memcpy")
/-- The counting loop: the layout from `RAX − 120`, the pair of claims at RSI. -/
def cntS : SState :=
  init [520, 3912, 1216] [(.rsp, .ptr 0 8)] [] [] [(.reg .rax, 1, 120), (.reg .rsi, 2, 0)]
/-- `cntS` with a column below `158` in R9. -/
def cntBS : SState :=
  init [520, 3912, 1216] [(.rsp, .ptr 0 8)] [] [(t3 (.reg .r9), 472)]
    [(.reg .rax, 1, 120), (.reg .rsi, 2, 0)]
/-- `b16`: the claims from R13, the last one's index (below `160`) in RCX. -/
def tailS : SState := init [520, 97280] [(.rsp, .ptr 0 8)] [] [(.reg .rcx, 160)] [(.reg .r13, 1, 0)]
/-- `b17`: the layout from `RAX − 120`, a column below `158` in RCX. -/
def tail2S : SState :=
  init [520, 3912] [(.rsp, .ptr 0 8)] [] [(t3 (.reg .rcx), 472)] [(.reg .rax, 1, 120)]
/-- `b24`: the stack arguments, the scales' count word at the second. -/
def argScS : SState := init [520, 24, 8] [(.rsp, .ptr 0 8)] [] [] (argAl ++ [(.load 1 8 8, 2, 0)])
/-- `b25`: the scales' count word at R14. -/
def scS : SState := init [520, 8] [(.rsp, .ptr 0 8)] [] [] [(.reg .r14, 1, 0)]
/-- `b26`: the first scale at RCX. -/
def sc0S : SState := init [520, 16] [(.rsp, .ptr 0 8)] [] [] [(.reg .rcx, 1, 0)]
/-- `b27`: the ring switch's target at the spilled `ring` (`56(%rsp)`). -/
def ringS : SState := init [520, 16] [(.rsp, .ptr 0 8)] [] [] [(.load 0 64 8, 1, 0)]
/-- `b34`, `b31`: the claim at `R13 + RBP`. -/
def claimS : SState :=
  init [520, 608] [(.rsp, .ptr 0 8)] [] [] [(.bin .add .W64 (.reg .r13) (.reg .rbp), 1, 0)]
/-- `b35`: the layout from the spilled `RAX` (`88(%rsp)`) − 120, a column below `158` in RAX. -/
def place2S : SState :=
  init [520, 3912] [(.rsp, .ptr 0 8)] [] [(t3 (.reg .rax), 472)] [(.load 0 96 8, 1, 120)]
/-- `b37`, `b39`: the scale at R14. -/
def scaleS : SState := init [520, 16] [(.rsp, .ptr 0 8)] [] [] [(.reg .r14, 1, 0)]
/-- `b38`, `b46`: the stack arguments. -/
def argS : SState := init [520, 24] [(.rsp, .ptr 0 8)] [] [] argAl
/-- `b41`: the out-of-domain claim at R15. -/
def oodS : SState := init [520, 504] [(.rsp, .ptr 0 8)] [] [] [(.reg .r15, 1, 0)]
/-- `b42`: the layout's head at R14. -/
def layS : SState := init [520, 24] [(.rsp, .ptr 0 8)] [] [] [(.reg .r14, 1, 0)]
/-- `b48`: the `WhirW`'s state at RAX. -/
def whirS : SState := init [520, 512] [(.rsp, .ptr 0 8)] [] [] [(.reg .rax, 1, 0)]

/-- The state after `b0`. -/
abbrev S0 : SState := after b0 entryS

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 regS
sym_block run_b2 := exec b2 regS
sym_block run_b3 := exec b3 regS
sym_block run_b4 := exec b4 regS
sym_block run_b5 := exec b5 regS
sym_block run_b7 := exec b7 cntBS
sym_block run_b8 := exec b8 cntS
sym_block run_b9 := exec b9 cntS
sym_block run_b10 := exec b10 cntBS
sym_block run_b11 := exec b11 cntS
sym_block run_b13 := exec b13 cntS
sym_block run_b14 := exec b14 cntS
sym_block run_b15 := exec b15 regS
sym_block run_b16 := exec b16 tailS
sym_block run_b17 := exec b17 tail2S
sym_block run_b18 := exec b18 regS
sym_block run_b19 := exec b19 regS
sym_block run_b20 := exec b20 regS
sym_block run_b21 := exec b21 regS
sym_block run_b22 := exec b22 regS
sym_block run_b23 := exec b23 regS
sym_block run_b24 := exec b24 argScS
sym_block run_b25 := exec b25 scS
sym_block run_b26 := exec b26 sc0S
sym_block run_b27 := exec b27 ringS
sym_block run_b28 := exec b28 regS
sym_block run_b29 := exec b29 regS
sym_block run_b30 := exec b30 regS
sym_block run_b31 := exec b31 claimS
sym_block run_b32 := exec b32 regS
sym_block run_b33 := exec b33 regS
sym_block run_b34 := exec b34 claimS
sym_block run_b35 := exec b35 place2S
sym_block run_b36 := exec b36 regS
sym_block run_b37 := exec b37 scaleS
sym_block run_b38 := exec b38 argS
sym_block run_b39 := exec b39 scaleS
sym_block run_b40 := exec b40 regS
sym_block run_b41 := exec b41 oodS
sym_block run_b42 := exec b42 layS
sym_block run_b43 := exec b43 regS
sym_block run_b44 := exec b44 copyS
sym_block run_b45 := exec b45 regS
sym_block run_b46 := exec b46 argS
sym_block run_b47 := exec b47 regS
sym_block run_b48 := exec b48 whirS
sym_block run_b49 := exec b49 regS
sym_block run_b50 := exec b50 regS
sym_block run_b51 := exec b51 regS

end NativeRustcVmX64.Whir.VerifyStackedOpening
