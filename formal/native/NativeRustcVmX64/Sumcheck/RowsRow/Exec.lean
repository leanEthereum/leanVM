module

public import NativeRustcVmX64.Transcript.Frame
public import NativeRustcVmX64.Code.Vm.RowsRow
public meta import NativeRustcVmX64.Code.Vm.RowsRow
public meta import NativeRustcVmX64.Transcript.Frame

/-!
# `Rows::row`'s block, run by the symbolic executor (x86-64)

`entryS`: region 0 the return address (RSP), region 1 the `Rows` (RDI, 32 bytes). `b0` computes
the row's start `193 j + 1` and its end `start + width` (`endS`), tests the end against the
slice's length and its carry (`condS`), and returns the slice (`raxS`, the width) or the empty one
(`8`, `0`).
-/

namespace NativeRustcVmX64.Sumcheck.RowsRow

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.RowsRow NativeRustcVmX64.Transcript

@[expose] public section

/-- At the entry: the return address (region 0, RSP) and the `Rows` (region 1, RDI). -/
def entryS : SState := init [8, 32] [(.rsp, .ptr 0 0), (.rdi, .ptr 1 0)]

/-- `193 j`. -/
def mS : Sym := .bin .mul .W64 (.reg .rsi) (.lit 193)

/-- The row's start, `193 j + 1`. -/
def startS : Sym := .bin .add .W64 mS (.lit 1)

/-- The row's end, `width + start`. -/
def endS : Sym := .bin .add .W64 (.load 1 24 8) startS

/-- `seta`: the end past the slice's length. -/
def aboveS : Sym :=
  .ite (.and (.not (.cmp .ult .W64 endS (.load 1 8 8))) (.not (.cmp .eq .W64 endS (.load 1 8 8))))
    (.lit 1) (.lit 0)

/-- CL after `seta`, `or` with `setb`'s DL. -/
def clS : Sym :=
  .bin .merge .W8 (.bin .merge .W8 endS aboveS)
    (.bin .or .W8 (.bin .merge .W8 endS aboveS)
      (.bin .merge .W8 (.reg .rdx) (.ite (.cmp .addC .W64 (.load 1 24 8) startS) (.lit 1) (.lit 0))))

/-- The row fits: CL zero. -/
def condS : SBool := .cmp .eq .W8 (.bin .and .W8 clS clS) (.lit 0)

/-- The row's address: the openings plus `8 (193 j + 1)`. -/
def raxS : Sym :=
  .bin .add .W64 (.load 1 0 8) (.bin .add .W64 (.bin .mul .W64 mS (.lit 8)) (.lit 8))

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS

public theorem ok_b0 : (after b0 entryS).reg .rax = some (.ite condS raxS (.lit 8)) ∧
    (after b0 entryS).reg .rdx = some (.ite condS (.load 1 24 8) (.lit 0)) ∧
    (after b0 entryS).reg .rsp = some (.ptr 0 8) ∧ (after b0 entryS).mem = [] ∧
    keeps entryS (after b0 entryS) = true := by
  decide +kernel

public theorem exit_b0 : exec b0 entryS = some (after b0 entryS, .ret (.load 0 0 8)) :=
  run_b0.trans (by rw [after_eq run_b0])

end NativeRustcVmX64.Sumcheck.RowsRow
