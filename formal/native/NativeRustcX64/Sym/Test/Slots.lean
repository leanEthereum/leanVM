module

public import NativeRustcX64.Sym
public meta import NativeRustcVmX64.Code.Vm.NovelEval

/-!
# Indexed stores, and loads through computed pointers

A store at `(%rax,%rsi,8)` with a bound on RSI writes each of the bound's slots (`SState.slots`),
the stored value where RSI is the slot's index; a load at the same address reads the stored value
back, a load at a constant offset the slot's conditional. A pointer loaded from memory is placed by
an alias (`SState.withAlias`). `NovelEval.b7`, a loop storing at `(%r14,%rbp,8)`.
-/

namespace NativeRustcX64.Sym.Test.Slots

set_option Elab.async false

/-- An instruction of 64-bit addresses. -/
abbrev ins {w : Width} (op : Operation w) : Directive := .instr (.regular .W64 w op)

/-- A 64-bit register. -/
abbrev R (r : Reg64) : RegOrMem .W64 := .reg (.low r .W64)

/-- `d(%b,%i,8)`. -/
abbrev idx8 (b i : Reg64) (d : Int64 := 0) : RegOrMem .W64 := .mem ⟨some (.reg b), some ⟨i, .W64⟩, .int64 d⟩

/-- `d(%b)`. -/
abbrev at_ (b : Reg64) (d : Int64 := 0) : RegOrMem .W64 := .mem ⟨some (.reg b), none, .int64 d⟩

/-- `a[i] := rcx`, `rdx := a[i]`, `rdi := a[2]`; `r8 := *rbx`, `r9 := r8[1]`. -/
def blk : List Directive := [
  .label "L",
  ins (.mov (idx8 .rax .rsi) (.regOrMem (R .rcx))),
  ins (.mov (R .rdx) (.regOrMem (idx8 .rax .rsi))),
  ins (.mov (R .rdi) (.regOrMem (at_ .rax 16))),
  ins (.mov (R .r8) (.regOrMem (at_ .rbx))),
  ins (.mov (R .r9) (.regOrMem (at_ .r8 8)))]

/-- RAX the 32-byte array of region 0, RSI below 4, RBX a pointer in region 1 to the 16-byte
region 2. -/
def start : SState :=
  (init [32, 8, 16] [(.rax, .ptr 0 0), (.rbx, .ptr 1 0)] |>.withBound (.reg .rsi) 4).withAlias
    (.load 1 0 8) 2 0

sym_block blk_exec := exec blk start

/-- `a[i]` read back is the stored RCX; `a[2]` is RCX if `i = 2`, else the old word; `r8[1]`
through the alias is region 2's word 1. -/
example : (exec blk start).map (fun r => (r.1.reg .rdx, r.1.reg .rdi, r.1.reg .r9)) =
    some (some (.reg .rcx), some (.ite (.cmp .eq .W64 (.reg .rsi) (.lit 2)) (.reg .rcx) (.load 0 16 8)),
      some (.load 2 8 8)) := by
  rw [blk_exec]
  rfl

open NativeRustcVmX64.Vm in
/-- `NovelEval.b7`: R14 a pointer into the 64-byte region 0, RBP below 4. -/
def novelS : SState := init [64] [(.r14, .ptr 0 16)] [] [(.reg .rbp, 4)]

open NativeRustcVmX64.Vm in
sym_block novel_exec := exec NovelEval.b7 novelS

open NativeRustcVmX64.Vm in
/-- The 4 slots from R14 written, slot 1 RAX if RBP is 1; R14 advanced by 8. -/
example : (exec NovelEval.b7 novelS).map (fun r => (r.1.mem.length, r.1.mem[1]?, r.1.reg .r14)) =
    some (4, some ⟨0, 24, 8, .ite (.cmp .eq .W64 (.reg .rbp) (.lit 1)) (.reg .rax) (.load 0 24 8)⟩,
      some (.ptr 0 24)) := by
  rw [novel_exec]
  rfl

end NativeRustcX64.Sym.Test.Slots
