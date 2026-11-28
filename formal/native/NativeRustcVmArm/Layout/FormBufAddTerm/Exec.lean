module

public import NativeRustcVmArm.Layout.Common
public import NativeRustcVmArm.Code.Vm.FormBufAddTerm
public meta import NativeRustcVmArm.Code.Vm.FormBufAddTerm
public meta import NativeRustcVmArm.Layout.Common

/-!
# `FormBuf::add_term`'s blocks, run by the symbolic executor

- `entryS`: region 0 the count word (X0), region 1 the term `t` (X1). `b0` loads the count `n`
  (above `148`: `b11` returns `0`), `b1` the degree `d` and the end `x0 + 8 + 40 n` (X9); at
  `n = 0` it branches to `b12`; `b2` sets up the search (X13 `t.cols`, X14 `d`, X15 the first
  term).
- `headS`, at `.L4` (`b4`): region 0 term `i`'s degree word (X15). Unequal degrees go to `b3`
  (`regsS`: the next term, or the end, `b10`).
- `regsS`: blocks that touch no memory (`b3`, `b5`, `b6`, `b8`, `b10`, `b11`).
- `cmpS`, at `b7`: region 0 term `i`'s column `j` (X16), region 1 `t`'s (X18).
- `foundS`, at `.L8` (`b9`): region 0 the term found (X11), its coefficient plus `c` stored.
- `pushS`, at `.L11` (`b12`): region 0 the count word (X0), region 1 the slot `n` (X9), region 2
  `t` (X1): the term appended, the count plus one.
-/

namespace NativeRustcVmArm.Layout.FormBufAddTerm

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.FormBufAddTerm

@[expose] public section

/-- At the entry: the count word (region 0, X0), the term (region 1, X1). -/
def entryS : SState := init [(8, false), (40, false)] .sp [(.X0, .ptr 0 0), (.X1, .ptr 1 0)]
/-- At `.L4`: term `i`'s degree word (region 0, X15). -/
def headS : SState := init [(8, false)] .sp [(.X15, .ptr 0 0)]
/-- No memory. -/
def regsS : SState := init [] .sp
/-- At `b7`: term `i`'s column (region 0, X16), `t`'s (region 1, X18). -/
def cmpS : SState := init [(8, false), (8, false)] .sp [(.X16, .ptr 0 0), (.X18, .ptr 1 0)]
/-- At `.L8`: the term found (region 0, X11). -/
def foundS : SState := init [(40, false)] .sp [(.X11, .ptr 0 0)]
/-- At `.L11`: the count word (region 0, X0), the slot (region 1, X9), `t` (region 2, X1). -/
def pushS : SState :=
  init [(8, false), (40, false), (40, false)] .sp [(.X0, .ptr 0 0), (.X9, .ptr 1 0), (.X1, .ptr 2 0)]

/-- The registers `add_term` keeps until it returns, but the callee-saved ones. -/
def args : List XReg := [.X0, .X1, .X2, .X3, .X30]

/-- `S` keeps `S₀`'s SP, callee-saved registers and `args`, and writes nothing. -/
def ok (S₀ S : SState) : Bool :=
  keeps S₀ S && args.all (fun r ↦ (S₀.reg r).isSome && S.reg r == S₀.reg r) && S.mem.isEmpty

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b11 := exec b11 regsS
sym_block run_b1 := exec b1 (after b0 entryS)
sym_block run_b2 := exec b2 (after b1 (after b0 entryS))
sym_block run_b4 := exec b4 headS
sym_block run_b3 := exec b3 regsS
sym_block run_b5 := exec b5 regsS
sym_block run_b6 := exec b6 regsS
sym_block run_b7 := exec b7 cmpS
sym_block run_b8 := exec b8 regsS
sym_block run_b9 := exec b9 foundS
sym_block run_b10 := exec b10 regsS
sym_block run_b12 := exec b12 pushS


public theorem b1_ok : ok entryS (after b1 (after b0 entryS)) = true := by decide +kernel
public theorem b2_ok : ok entryS (after b2 (after b1 (after b0 entryS))) = true := by decide +kernel
public theorem b4_ok : ok headS (after b4 headS) = true := by decide +kernel
public theorem b3_ok : ok regsS (after b3 regsS) = true := by decide +kernel
public theorem b5_ok : ok regsS (after b5 regsS) = true := by decide +kernel
public theorem b6_ok : ok regsS (after b6 regsS) = true := by decide +kernel
public theorem b7_ok : ok cmpS (after b7 cmpS) = true := by decide +kernel
public theorem b8_ok : ok regsS (after b8 regsS) = true := by decide +kernel
public theorem b10_ok : ok regsS (after b10 regsS) = true := by decide +kernel
public theorem b11_keeps : keeps regsS (after b11 regsS) = true := by decide +kernel
public theorem b9_keeps : keeps foundS (after b9 foundS) = true := by decide +kernel
public theorem b12_keeps : keeps pushS (after b12 pushS) = true := by decide +kernel

/-- `b9` writes the coefficient's two words. -/
public theorem b9_mem : ∀ w ∈ (after b9 foundS).mem, w.r = 0 ∧ 24 ≤ w.off ∧ w.off + w.n ≤ 40 := by
  decide +kernel
public theorem b9_w24 : ∀ i < 8, findWrite 0 (24 + i) (after b9 foundS).mem =
    some (.bin .eor .W64 (.load 0 24 8) (.reg .X2), i) := by decide +kernel
public theorem b9_w32 : ∀ i < 8, findWrite 0 (32 + i) (after b9 foundS).mem =
    some (.bin .eor .W64 (.load 0 32 8) (.reg .X3), i) := by decide +kernel

/-- `b12` writes the count word and the slot. -/
public theorem b12_mem : ∀ w ∈ (after b12 pushS).mem,
    (w.r = 0 ∧ w.off + w.n ≤ 8) ∨ (w.r = 1 ∧ w.off + w.n ≤ 40) := by decide +kernel
public theorem b12_len : ∀ i < 8, findWrite 0 (0 + i) (after b12 pushS).mem =
    some (.bin .add .W64 (.reg .X8) (.lit 1), i) := by decide +kernel
public theorem b12_deg : ∀ i < 8, findWrite 1 (0 + i) (after b12 pushS).mem =
    some (.reg .X10, i) := by decide +kernel
public theorem b12_c0 : ∀ i < 8, findWrite 1 (8 + i) (after b12 pushS).mem =
    some (.load 2 8 8, i) := by decide +kernel
public theorem b12_c1 : ∀ i < 8, findWrite 1 (16 + i) (after b12 pushS).mem =
    some (.load 2 16 8, i) := by decide +kernel
public theorem b12_lo : ∀ i < 8, findWrite 1 (24 + i) (after b12 pushS).mem =
    some (.reg .X2, i) := by decide +kernel
public theorem b12_hi : ∀ i < 8, findWrite 1 (32 + i) (after b12 pushS).mem =
    some (.reg .X3, i) := by decide +kernel

end NativeRustcVmArm.Layout.FormBufAddTerm
