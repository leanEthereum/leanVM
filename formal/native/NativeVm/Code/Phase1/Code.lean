module

public import NativeVm.Code.Phase1.Blocks

/-!
# Phase 1's code

`r14` holds the layout's address (`layoutR`) throughout; the layout's words (`LayoutAt`) are
written in place, and nothing else of the working area is.

* `readLoop`: the eight announced scalars (`readScalars (2 + nTables)`), each read by the
  transcript's `readScalar`: its low limb to layout word `9 + i`, its high limb or'd into `r13`.
  Words `10 .. 15` are then the tables' row counts, where `LayoutAt` wants them; words `9` and
  `16`, the memory's log-size and the rate exponent, are moved to words `0` and `3` by `checks`
  before anything else is written there.
* `checks`: the bytecode's length a power of two `2^l` with `4 ≤ l ≤ 34` (`bitLen` of it is
  `l + 1`), its log-size `l - 4` to word `1` (`checkBc`); the high limbs zero, the rate exponent
  in `1 .. 4`, the memory's log-size in `1 .. 30` (`checkScalars`).
* `heights`: each table's row count at most `2^30`, its log-height `max (log2Ceil rows) floor` to
  word `4 + i`.
* `stackC`: the stack's size `sumF κ 0` (`sumC` with `r8 = 0`), its log-size
  `max 16 (log2Ceil size)` checked at most `30`, to word `2`; `q_keccak`'s offset into `rbp`.
* `placeLoop`: every global column's placement, three words from word `16 + 3 c` (`r15`): a
  stacked column's log-size and offset (`sumC` at its key), a `q_keccak` slot's at `rbp` plus the
  slot times `2^κ`, `0` for an output lane.

Every check fails at once (`failIf`); the model rejects exactly then (`tailP`).
-/

@[expose] public section

namespace NativeVm.Code.Phase1

open Native
open NativeVm.Transcript (wdisp cw ctxWork ctxBytecodeLen)

/-! ## Reading -/

/-- Read the eight announced scalars. -/
def readLoop : Stmt := .loop (.cmp .ltu .r12 (.imm 8)) (blk [
  NativeVm.Transcript.readScalar,
  I (.store ⟨.r14, some (.r12, .W64), wdisp 9⟩ .r9),
  I (.or .r13 .r10),
  I (.addi .r12 1)])

/-! ## The checks -/

/-- The bytecode's length a power of two `2^l`, `4 ≤ l ≤ 34`; its log-size `l - 4` to word `1`. -/
def checkBc : Stmt := blk [
  I (.load .rax (cw ctxBytecodeLen)),
  failIf (.cmp .eq .rax (.imm 0)),
  I (.mov .rbx .rax), I (.subi .rbx 1), I (.and .rbx .rax), failIf (.test false .rbx (.reg .rbx)),
  bitLen,
  I (.subi .rdx 5), failIf (.cmp .geu .rdx (.imm 31)),
  I (.store (L 1) .rdx)]

/-- The scalars' high limbs zero, the rate exponent in `1 .. 4` to word `3`, the memory's log-size
in `1 .. 30` to word `0`. -/
def checkScalars : Stmt := blk [
  failIf (.test false .r13 (.reg .r13)),
  I (.load .rax (L 16)), I (.store (L 3) .rax),
  I (.subi .rax 1), failIf (.cmp .geu .rax (.imm 4)),
  I (.load .rax (L 9)), I (.store (L 0) .rax),
  I (.subi .rax 1), failIf (.cmp .geu .rax (.imm 30))]

/-- The checks of the sizes. -/
def checks : Stmt := blk [checkBc, checkScalars]

/-! ## The heights -/

/-- Table `i`'s row count checked and its log-height, at least `floor`. -/
def heightC (i floor : Nat) : Stmt := blk [
  I (.load .rax (L (10 + i))),
  failIf (.cmp .geu .rax (.imm (2 ^ 30 + 1))),
  .ite (.cmp .eq .rax (.imm 0)) .skip (I (.subi .rax 1)),
  bitLen,
  .ite (.cmp .ltu .rdx (.imm (Int64.ofNat floor))) (I (.movi .rdx (Int64.ofNat floor))) .skip,
  I (.store (L (4 + i)) .rdx)]

/-- Every table's. -/
def heights : Stmt := blk ((List.range 6).flatMap fun i ↦ [heightC i (floorF i)])

/-! ## The stack -/

/-- The stack's log-size, checked, and `q_keccak`'s offset into `rbp`. -/
def stackC : Stmt := blk [
  I (.movi .r8 0), sumC,
  I (.mov .rax .r10), .ite (.cmp .eq .rax (.imm 0)) .skip (I (.subi .rax 1)), bitLen,
  .ite (.cmp .ltu .rdx (.imm 16)) (I (.movi .rdx 16)) .skip,
  failIf (.cmp .geu .rdx (.imm 31)),
  I (.store (L 2) .rdx),
  I (.movi .rsi 4), kapC, I (.mov .r8 .rax), I (.shli .r8 8), I (.addi .r8 251), sumC,
  I (.mov .rbp .r10)]

/-! ## The placements -/

/-- A stacked column `r12` of log-size `rax`: its offset, the sizes of the columns of larger key. -/
def blockP : Stmt := blk [
  I (.mov .rbx .rax), I (.mov .r8 .rax), I (.shli .r8 8), I (.addi .r8 255), I (.sub .r8 .r12),
  sumC,
  I (.storei (at_ .r15 (wdisp 0)) 1), I (.store (at_ .r15 (wdisp 1)) .rbx),
  I (.store (at_ .r15 (wdisp 2)) .r10)]

/-- A `q_keccak` slot, the column `r12` less `d`, of log-size `rax`: at `rbp + slot · 2^rax`. -/
def slotP (d : Nat) : Stmt := blk [
  I (.mov .rcx .rax), I (.mov .rdx .r12), I (.subi .rdx (Int64.ofNat d)), I (.shlcl .rdx),
  I (.add .rdx .rbp),
  I (.storei (at_ .r15 (wdisp 0)) 1), I (.store (at_ .r15 (wdisp 1)) .rax),
  I (.store (at_ .r15 (wdisp 2)) .rdx)]

/-- The placement of column `r12`, at `r15`. -/
def placeBody : Stmt := blk [
  I (.mov .rsi .r12), kapC, blockFlag,
  .ite (.cmp .eq .rdx (.imm 1)) blockP
    (.ite (.cmp .ltu .r12 (.imm 80)) (slotP 16)
      (.ite (.cmp .ltu .r12 (.imm 106)) (slotP 81) (I (.storei (at_ .r15 (wdisp 0)) 0)))),
  I (.addi .r12 1), I (.addi .r15 24)]

/-- Every column's placement. -/
def placeLoop : Stmt := blk [
  I (.movi .r12 0), I (.lea .r15 (L 16)), .loop (.cmp .ltu .r12 (.imm 158)) placeBody]

/-! ## After reading -/

/-- Phase 1 after the scalars are read. -/
def tail : Stmt := blk [checks, heights, stackC, placeLoop]

end NativeVm.Code.Phase1
