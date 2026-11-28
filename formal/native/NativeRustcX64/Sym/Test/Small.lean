module

public import NativeRustcX64.Sym

/-!
# Small checks of the x86-64 symbolic executor

The soundness theorem's axioms; `push`/`pop`, 8-bit and 32-bit register writes, `bswap`,
`cmp`/`setb`/`cmovb`, shifts and `shrd` by `%cl`, a rotation, a store read back by `movzbl`, and
`ret` to the address popped; the carry of a shift by a literal, a load at a `cmov`-chosen
address.
-/

namespace NativeRustcX64.Sym.Test.Small

set_option Elab.async false

/-- info: 'NativeRustcX64.Sym.exec_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exec_sound

/-- info: 'NativeRustcX64.Sym.match_init' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms match_init

/-- An instruction of 64-bit addresses. -/
abbrev ins {w : Width} (op : Operation w) : Directive := .instr (.regular .W64 w op)

/-- A register of width `w`. -/
abbrev R (r : Reg64) (w : Width) : RegOrMem w := .reg (.low r w)

/-- `off(%rsp)`. -/
abbrev stk (off : Int64) {w : Width} : RegOrMem w := .mem ⟨some (.reg .rsp), none, .int64 off⟩

def blk : List Directive := [
  .label "L",
  ins (.push (.regOrMem (R .rbx .W64))),
  ins (.mov (R .rax .W64) (.imm (.int64 0x1122334455667788))),
  ins (.mov (R .rax .W8) (.imm (.int64 0x99))),
  ins (.bswap (.low .rax .W64)),
  ins (.mov (R .rcx .W32) (.regOrMem (R .rax .W32))),
  ins (.cmp (R .rdi .W64) (.imm (.int64 5))),
  ins (.setcc .c (R .rdx .W8)),
  ins (.cmovcc .c (.low .r8 .W64) (R .rsi .W64)),
  ins (.shr (R .r9 .W64) .cl),
  ins (.rol (R .r10 .W64) (.imm8 (.int64 1))),
  ins (.shrd (R .r12 .W64) (.low .r11 .W64) .cl),
  ins (.mov (stk 8) (.regOrMem (R .rax .W64))),
  ins (.movzx (R .r13 .W32) (stk 9 (w := .W8))),
  ins (.pop (R .rbx .W64)),
  ins (.ret : Operation .W64)]

/-- RSP 32 bytes into the 64-byte region 0. -/
def start : SState := init [64] [(.rsp, .ptr 0 32)]

sym_block blk_exec := exec blk start

/-- `movb` merges into RAX, `bswap` folds, `movl` zero-extends. -/
example : (exec blk start).map (fun r => (r.1.reg .rax, r.1.reg .rcx)) =
    some (some (.lit 0x9977665544332211), some (.lit 0x44332211)) := by
  rw [blk_exec]
  rfl

/-- The byte `movzbl` reads back from the stored RAX, `pop` restores RBX, `ret` pops what was at
the entry RSP. -/
example : (exec blk start).map (fun r => (r.1.reg .r13, r.1.reg .rbx, r.2)) =
    some (some (.lit 0x22), some (.reg .rbx), .ret (.lit 0x9977665544332211)) := by
  rw [blk_exec]
  rfl

/-- `setb` merges the carry of `cmp` into DL. -/
example : (exec blk start).map (fun r => r.1.reg .rdx) =
    some (some (.bin .merge .W8 (.reg .rdx)
      (.ite (.cmp .ult .W64 (.reg .rdi) (.lit 5)) (.lit 1) (.lit 0)))) := by
  rw [blk_exec]
  rfl

/-- A shift by a literal, its carry read by `setb`; a load at a `cmov`-chosen address. -/
def blk2 : List Directive := [
  .label "M",
  ins (.shr (R .rdi .W64) (.imm8 (.int64 3))),
  ins (.setcc .c (R .rdx .W8)),
  ins (.cmp (R .rsi .W64) (.imm (.int64 0))),
  ins (.cmovcc .z (.low .rax .W64) (R .rcx .W64)),
  ins (.mov (R .rbx .W64) (.regOrMem (.mem ⟨some (.reg .rax), none, .int64 8⟩))),
  ins (.ret : Operation .W64)]

/-- RSP 32 bytes into region 0; RAX and RCX the regions' starts. -/
def start2 : SState := init [64, 16] [(.rsp, .ptr 0 32), (.rax, .ptr 0 0), (.rcx, .ptr 1 0)]

sym_block blk2_exec := exec blk2 start2

/-- `setb` reads the carry of `shrq $3`, bit 2 of RDI; the load at the `cmove`-chosen address is
the conditional of the loads. -/
example : (exec blk2 start2).map (fun r => (r.1.reg .rdx, r.1.reg .rbx)) =
    some (some (.bin .merge .W8 (.reg .rdx)
      (.ite (.msb .W64 (.bin .shl .W64 (.reg .rdi) (.lit 61))) (.lit 1) (.lit 0))),
      some (.ite (.cmp .eq .W64 (.reg .rsi) (.lit 0)) (.load 1 8 8) (.load 0 8 8))) := by
  rw [blk2_exec]
  rfl

end NativeRustcX64.Sym.Test.Small
