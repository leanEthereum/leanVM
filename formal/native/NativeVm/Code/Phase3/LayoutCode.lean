module

public import NativeVm.Code.Phase3.Common

/-!
# Phase 3's placements: the code

`layoutCode` writes the three bus sides' placements (`busLayout`) into `placeR 0 .. 2`, in the
format `SidesAt` reads (`P3.LayoutMath`): placement `i` (the framework blocks', then the table
blocks') its variable count at word `2 i` and its index at word `2 i + 1`; table block `k`'s rows at
word `128 + k`. Then the push side's depth into `depthR`.

A side's code (`sideC`) runs in three steps, with the working area's address in `r15`:

* the framework sizes `0`, `logMemory`, `logBytecode` (`frameC`, push and pull sides only);
* the table blocks' sizes and rows (`fillC`): each table `t` in turn (`fillT t c`) writes its height
  and rows `c` times, `r14` twice the blocks so far;
* the offsets (`offsC`): placement `i`'s offset is the sum of `2^size` over the placements before it
  (larger first, ties by index), the order compared by the key `size · 1024 + 1023 - 2 j`
  (`offsInner`); `rsi` sums `2^size` over all, the stack's size, whose `log2Ceil` is the depth
  (`depthC`).
-/

@[expose] public section

namespace NativeVm.Code.P3

open Native NativeVm.Model NativeVm.Code NativeVm.Transcript

/-! ## Addresses in the working area (`r15`) -/

/-- Word `k` of the working area. -/
abbrev aW (k : Nat) : Addr := at_ .r15 (wdisp k)

/-- Word `k + i` of the working area, `i` in `ix`. -/
abbrev aI (ix : Reg64) (k : Nat) : Addr := { base := .r15, idx := some (ix, .W64), disp := wdisp k }

/-- Word `k + i / 2` of the working area, `i` (even) in `ix`. -/
abbrev aH (ix : Reg64) (k : Nat) : Addr := { base := .r15, idx := some (ix, .W32), disp := wdisp k }

/-! ## A side's sizes -/

/-- The tables' blocks of a side: `(table, count)`, push and pull sides, then the count side. -/
def shapePP : List (Nat × Nat) := [(0, 5), (1, 5), (2, 3), (3, 5), (4, 5), (5, 28)]
def shapeC : List (Nat × Nat) := [(0, 4), (1, 4), (2, 2), (3, 4), (4, 4), (5, 27)]

/-- A side's table blocks, by table. -/
def sideShape (side : Nat) : List (Nat × Nat) := if side = 2 then shapeC else shapePP

/-- A side's framework blocks. -/
def sideFw (side : Nat) : Nat := if side = 2 then 0 else 3

/-- A side's table blocks. -/
def sideNb (side : Nat) : Nat := if side = 2 then 45 else 51

/-- The framework sizes `0`, `logMemory`, `logBytecode` at words `0`, `2`, `4` of `po`. -/
def frameC (po : Nat) : Stmt := blk [
  I (.storei (aW po) 0),
  I (.load .rax (aW layoutR.off)), I (.store (aW (po + 2)) .rax),
  I (.load .rax (aW (layoutR.off + 1))), I (.store (aW (po + 4)) .rax)]

/-- Table `t`'s `c` blocks: its height at words `po + fo + r14`, its rows at `po + 128 + r14 / 2`,
`r14` up by `2` each. -/
def fillT (po fo t c : Nat) : Stmt := blk [
  I (.load .rax (aW (layoutR.off + 4 + t))), I (.load .rbx (aW (layoutR.off + 10 + t))),
  I (.movi .rcx (Int64.ofNat c)),
  .loop (.cmp .ne .rcx (.imm 0)) (blk [
    I (.store (aI .r14 (po + fo)) .rax), I (.store (aH .r14 (po + 128)) .rbx),
    I (.addi .r14 2), I (.subi .rcx 1)])]

/-- Every table's blocks, from `r14 = 0`. -/
def fillC (po fo : Nat) (shape : List (Nat × Nat)) : Stmt :=
  blk (I (.movi .r14 0) :: shape.map fun p ↦ fillT po fo p.1 p.2)

/-- The key of placement `r` (its size in `rax`, twice its index in `r`) into `d`. -/
def keyC (d r : Reg64) : List Stmt :=
  [I (.mov d .rax), I (.shli d 10), I (.addi d 1023), I (.sub d r)]

/-- `r8 := ` the sum of `2^size` over the `n` placements whose key exceeds `rbx`. -/
def offsInner (po n : Nat) : Stmt := blk [
  I (.movi .r8 0), I (.movi .r13 0),
  .loop (.cmp .ne .r13 (.imm (Int64.ofNat (2 * n)))) (blk ([
    I (.load .rax (aI .r13 po))] ++ keyC .rdx .r13 ++ [
    .ite (.cmp .ltu .rbx (.reg .rdx))
      (blk [I (.mov .rcx .rax), I (.movi .rdx 1), I (.shlcl .rdx), I (.add .r8 .rdx)]) .skip,
    I (.addi .r13 2)]))]

/-- The `n` placements' offsets at words `po + 2 i + 1`; `rsi := ` the sum of `2^size`. -/
def offsC (po n : Nat) : Stmt := blk [
  I (.movi .r12 0), I (.movi .rsi 0),
  .loop (.cmp .ne .r12 (.imm (Int64.ofNat (2 * n)))) (blk ([
    I (.load .rax (aI .r12 po))] ++ keyC .rbx .r12 ++ [
    offsInner po n,
    I (.store (aI .r12 (po + 1)) .r8),
    I (.load .rcx (aI .r12 po)), I (.movi .rdx 1), I (.shlcl .rdx), I (.add .rsi .rdx),
    I (.addi .r12 2)]))]

/-- A side's placements into `placeR side`; `rsi` the stack's size. -/
def sideC (side : Nat) : Stmt := blk [
  if side = 2 then .skip else frameC (placeR side).off,
  fillC (placeR side).off (2 * sideFw side) (sideShape side),
  offsC (placeR side).off (sideFw side + sideNb side)]

/-- `depthR := log2Ceil rsi`, the bit length of `rsi - 1`. -/
def depthC : Stmt := blk [
  I (.mov .rax .rsi), I (.subi .rax 1), I (.movi .rdx 0),
  .loop (.cmp .ne .rax (.imm 0)) (blk [I (.shri .rax 1), I (.addi .rdx 1)]),
  I (.store (aW depthR.off) .rdx)]

/-- **Phase 3's placements**: the three sides' into `placeR 0 .. 2`, the push side's depth into
`depthR`. -/
def layoutCode : Stmt := blk [
  I (.load .r15 (cw ctxWork)),
  sideC 0, depthC, sideC 1, sideC 2]

end NativeVm.Code.P3
