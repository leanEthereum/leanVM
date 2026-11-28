module

public import NativeRustcArm.Sym
public meta import NativeRustcVmArm.Code.Vm.BufU64x230Extend

/-!
# Indexed stores, and loads through computed pointers

A store at `[x0, x1, lsl #3]` with a bound on X1 writes each of the bound's slots (`SState.slots`),
the stored value where X1 is the slot's index; a load at the same address reads the stored value
back, a load at a constant offset the slot's conditional. A pointer loaded from memory is placed by
an alias (`SState.withAlias`). `BufU64x230Extend.b3`, the loop of `extend` of a buffer of `u64`.
-/

namespace NativeRustcArm.Sym.Test.Slots

set_option Elab.async false

/-- `a[i] := x2`, `x3 := a[i]`, `x4 := a[2]`; `x5 := *x6`, `x7 := x5[1]`. -/
def blk : List Directive := [
  .label "L",
  .instr ⟨.W64, .STR .X2 ⟨.X0, .reg ⟨⟨.W64, .X1⟩, ⟨.UXTX, .E3⟩⟩⟩⟩,
  .instr ⟨.W64, .LDR .X3 (.addr ⟨.X0, .reg ⟨⟨.W64, .X1⟩, ⟨.UXTX, .E3⟩⟩⟩)⟩,
  .instr ⟨.W64, .LDR .X4 (.addr ⟨.X0, .imm ⟨.int64 16, none⟩⟩)⟩,
  .instr ⟨.W64, .LDR .X5 (.addr ⟨.X6, .imm ⟨.int64 0, none⟩⟩)⟩,
  .instr ⟨.W64, .LDR .X7 (.addr ⟨.X5, .imm ⟨.int64 8, none⟩⟩)⟩]

/-- X0 the 32-byte array of region 0, X1 below 4, X6 a pointer in region 1 to the 16-byte
region 2. -/
def start : SState :=
  (init [(32, false), (8, false), (16, false)] .sp [(.X0, .ptr 0 0), (.X6, .ptr 1 0)]
    |>.withBound (.reg .X1) 4).withAlias (.load 1 0 8) 2 0

sym_block blk_exec := exec blk start

/-- `a[i]` read back is the stored X2; `a[2]` is X2 if `i = 2`, else the old word; `x5[1]` through
the alias is region 2's word 1. -/
example : (exec blk start).map (fun r => (r.1.reg .X3, r.1.reg .X4, r.1.reg .X7)) =
    some (some (.reg .X2), some (.ite (.cmp .eq .W64 (.reg .X1) (.lit 2)) (.reg .X2) (.load 0 16 8)),
      some (.load 2 8 8)) := by
  rw [blk_exec]
  rfl

open NativeRustcVmArm.Vm in
/-- `BufU64x230Extend.b3`: X0 the buffer (its length word, then 230 words), X1 the source, the
length X9 below 231. -/
def bufS : SState :=
  init [(8 * 231, false), (8, false)] .sp [(.X0, .ptr 0 0), (.X1, .ptr 1 0)] [] [(.reg .X9, 231)]

open NativeRustcVmArm.Vm in
sym_block buf_exec := exec BufU64x230Extend.b3 bufS

open NativeRustcVmArm.Vm in
/-- The 231 slots written (slot 0 then overwritten by the length), slot 5 the loaded word if the
length is 5. -/
example : (exec BufU64x230Extend.b3 bufS).map (fun r => (r.1.mem.length, r.1.mem[5]?)) =
    some (231, some ⟨0, 40, 8, .ite (.cmp .eq .W64 (.reg .X9) (.lit 5)) (.load 1 0 8) (.load 0 40 8)⟩) := by
  rw [buf_exec]
  rfl

end NativeRustcArm.Sym.Test.Slots
