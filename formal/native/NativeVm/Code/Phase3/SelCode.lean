module

public import NativeVm.Code.Phase3.LayoutCode
public import NativeVm.Field.E

/-!
# Phase 3's selectors and padding weights: the code

At the GKR point (`pointR`, its size in `depthR`), for one side: each framework placement's and each
table placement's `eqAbove` (`eqAb`), into `fselR side` and `tselR side`, and each table block's
`paddingWeight` (`padAb`) into `padWR side`. The working area's address is in `r15`, twice the
placement's index in `r14`; the placements are `SidesAt`'s words in `placeR side`.

* `eqAb src`: the placement `(vc, idx)` at words `src + r14`, `src + r14 + 1`; `A := 1`, then unless
  `vc ≥ n`, `idx` shifted right `vc` times (`rbp`) and the point from coordinate `vc` (`r13`), and
  for each of the `n - vc` coordinates `y`, `A := A · (1 + bit + y)` (`emul`), the next bit of `idx`
  each time.
* `padAb src rows`: the block's log-rows `lr` at word `src + r14`, its rows `R` at
  `rows + r14 / 2`; for each of the first `m = min lr n` coordinates `y`, with `c = 1 + bit` of `R`,
  `A := (A + c)·(y + c) + c` (`r·A` for a set bit, `r + A + r·A` otherwise), then `A := 0` if bit
  `m` of `R` is set.
-/

@[expose] public section

namespace NativeVm.Code.P3

open Native NativeVm.Model NativeVm.Code NativeVm.Transcript NativeVm.Field

/-- `A := eqAbove (vc, idx) point`, the placement at words `src + r14`, `src + r14 + 1`. -/
def eqAb (src : Nat) : Stmt := blk [
  I (.load .rsi (aI .r14 src)), I (.load .rbp (aI .r14 (src + 1))),
  I (.load .r11 (aW depthR.off)),
  I (.movi .r9 1), I (.movi .r10 0),
  .ite (.cmp .geu .rsi (.reg .r11)) .skip (blk [
    I (.sub .r11 .rsi), I (.lea .r13 (aW pointR.off)),
    .loop (.cmp .ne .rsi (.imm 0)) (blk [I (.shri .rbp 1), I (.addi .r13 16), I (.subi .rsi 1)]),
    I (.mov .rsi .r11),
    .loop (.cmp .ne .rsi (.imm 0)) (blk [
      I (.load .r11 (at_ .r13 0)), I (.mov .rax .rbp), I (.andi .rax 1), I (.xor .r11 .rax),
      I (.xori .r11 1), I (.load .r12 (at_ .r13 8)),
      emul,
      I (.shri .rbp 1), I (.addi .r13 16), I (.subi .rsi 1)])])]

/-- `rax := 1 + ` the low bit of `rbp`; `r9 += rax`. -/
def padFlip : List Stmt :=
  [I (.mov .rax .rbp), I (.andi .rax 1), I (.xori .rax 1), I (.xor .r9 .rax)]

/-- `A := paddingWeight (point.extract 0 lr) R`, `lr` at word `src + r14`, `R` at `rows + r14 / 2`. -/
def padAb (src rows : Nat) : Stmt := blk [
  I (.load .rsi (aI .r14 src)), I (.load .rbp (aH .r14 rows)),
  I (.load .r11 (aW depthR.off)),
  I (.movi .r9 1), I (.movi .r10 0),
  .ite (.cmp .ltu .r11 (.reg .rsi)) (I (.mov .rsi .r11)) .skip,
  I (.lea .r13 (aW pointR.off)),
  .loop (.cmp .ne .rsi (.imm 0)) (blk (padFlip ++ [
    I (.load .r11 (at_ .r13 0)), I (.xor .r11 .rax), I (.load .r12 (at_ .r13 8)),
    emul] ++ padFlip ++ [
    I (.shri .rbp 1), I (.addi .r13 16), I (.subi .rsi 1)])),
  .ite (.test true .rbp (.imm 1)) .skip (blk [I (.movi .r9 0), I (.movi .r10 0)])]

/-- The framework selectors: `fw` placements from word `po`, into `fo`. -/
def selFw (po fo fw : Nat) : Stmt := blk [
  I (.movi .r14 0),
  .loop (.cmp .ne .r14 (.imm (Int64.ofNat (2 * fw)))) (blk [
    eqAb po, I (.store (aI .r14 fo) .r9), I (.store (aI .r14 (fo + 1)) .r10),
    I (.addi .r14 2)])]

/-- The table selectors and padding weights: `nb` placements from word `po`, their rows from `ro`,
into `tso` and `wo`. -/
def selTb (po ro tso wo nb : Nat) : Stmt := blk [
  I (.movi .r14 0),
  .loop (.cmp .ne .r14 (.imm (Int64.ofNat (2 * nb)))) (blk [
    eqAb po, I (.store (aI .r14 tso) .r9), I (.store (aI .r14 (tso + 1)) .r10),
    padAb po ro, I (.store (aI .r14 wo) .r9), I (.store (aI .r14 (wo + 1)) .r10),
    I (.addi .r14 2)])]

/-- **A side's selectors and padding weights** at the GKR point. -/
def selCode (side : Nat) : Stmt := blk [
  I (.load .r15 (cw ctxWork)),
  selFw (placeR side).off (fselR side).off (sideFw side),
  selTb ((placeR side).off + 2 * sideFw side) ((placeR side).off + 128) (tselR side).off
    (padWR side).off (sideNb side)]

end NativeVm.Code.P3
