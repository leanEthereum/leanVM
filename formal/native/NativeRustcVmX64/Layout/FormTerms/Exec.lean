module

public import NativeRustcVmX64.Layout.Common
public import NativeRustcVmX64.Code.Vm.FormTerms
public import NativeRustcVmX64.Code.Vm.Names
public meta import NativeRustcVmX64.Code.Vm.FormTerms
public meta import NativeRustcVmX64.Layout.Common

/-!
# `form_terms`'s blocks, run by the symbolic executor (x86-64)

From `entryS`: region 0 the return address at RSP, region 1 `FORMS` (`593` spans of 16 bytes)
at its label. `b0` compares the form with `592`: above, `b2` returns the empty slice; else `b1`
shifts the form to its byte offset (`b1a`), then (`b1b`, from `idxS`: RDI the form, variable `0`,
times `16`, below `593`) loads its span and returns `TERMS` plus `40` times its start and its
length, or the empty slice when the span leaves `TERMS`.
-/

namespace NativeRustcVmX64.Layout.FormTerms

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.FormTerms
open NativeRustcVmX64.Transcript (after after_eq exec_after EpiOk)

@[expose] public section



/-- At the entry: the return address (region 0, RSP), `FORMS` (region 1) at its label. -/
def entryS : SState := init [8, 9488] [(.rsp, .ptr 0 0)] [(NativeRustcVmX64.Vm.Symbols.rodata13Label, 1)]

/-- `b1`'s shift of the form. -/
def b1a : List Directive := b1.take 1

/-- The rest of `b1`. -/
def b1b : List Directive := b1.drop 1

/-- The form's byte offset: the form (variable `0`, below `593`) times `16`. -/
def idxS : SState :=
  init [8, 9488] [(.rsp, .ptr 0 0), (.rdi, .bin .mul .W64 (.var 0) (.lit 16))] [(NativeRustcVmX64.Vm.Symbols.rodata13Label, 1)]
    [(.var 0, 593)]

/-- The span's start. -/
def startS : Sym := .loadx 1 0 (.bin .mul .W64 (.var 0) (.lit 16)) 8

/-- The span's length. -/
def lenS : Sym := .loadx 1 8 (.bin .mul .W64 (.var 0) (.lit 16)) 8

/-- The span's end. -/
def endS : Sym := .bin .add .W64 lenS startS

/-- `b1`'s check: the end does not wrap (`setae %sil`) and is below `770` (`setb %dil`). -/
def condS : SBool :=
  .not (.cmp .eq .W8 (.bin .and .W8
    (.bin .merge .W8 (.reg .rsi) (.ite (.not (.cmp .ult .W64 endS startS)) (.lit 1) (.lit 0)))
    (.bin .merge .W8 (.bin .mul .W64 (.var 0) (.lit 16))
      (.ite (.cmp .ult .W64 endS (.lit 770)) (.lit 1) (.lit 0)))) (.lit 0))

/-- The slice's address: `TERMS` plus `40` times the start, or `8` (dangling). -/
def raxOut : Sym :=
  .ite condS (.bin .add .W64 (.label NativeRustcVmX64.Vm.Symbols.rodata14Label)
    (.bin .mul .W64 (.bin .add .W64 startS (.bin .mul .W64 startS (.lit 4))) (.lit 8))) (.lit 8)

/-- The slice's length, or `0`. -/
def rdxOut : Sym := .ite condS lenS (.lit 0)

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1a := exec b1a (after b0 entryS)
sym_block run_b1b := exec b1b idxS
sym_block run_b2 := exec b2 retS

public theorem ok_b0 : keeps entryS (after b0 entryS) = true ∧ (after b0 entryS).mem = [] ∧
    (after b0 entryS).reg .rsp = some (.ptr 0 0) ∧ (after b0 entryS).reg .rdi = some (.reg .rdi) :=
  by decide +kernel

public theorem ok_b1a : keeps entryS (after b1a (after b0 entryS)) = true ∧
    (after b1a (after b0 entryS)).mem = [] ∧
    (after b1a (after b0 entryS)).reg .rsp = some (.ptr 0 0) ∧
    (after b1a (after b0 entryS)).reg .rdi = some (.bin .shl .W64 (.reg .rdi) (.lit 4)) := by
  decide +kernel

public theorem ok_b1b : EpiOk 0 [] (after b1b idxS) = true ∧ (after b1b idxS).mem = [] ∧
    (after b1b idxS).reg .rax = some raxOut ∧ (after b1b idxS).reg .rdx = some rdxOut := by
  decide +kernel

public theorem ok_b2 : EpiOk 0 [] (after b2 retS) = true ∧ (after b2 retS).mem = [] ∧
    (after b2 retS).reg .rax = some (.lit 8) ∧ (after b2 retS).reg .rdx = some (.lit 0) := by
  decide +kernel

end NativeRustcVmX64.Layout.FormTerms
