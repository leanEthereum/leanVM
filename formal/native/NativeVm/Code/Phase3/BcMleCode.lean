module

public import NativeVm.Code.Phase3.Common

/-!
# The bytecode's multilinear extension: the code

`bcCode` checks `computedBytecodeValue` (`Model/Bus.lean`): the multilinear extension of the
bytecode's words (each a `K` lane) at `point' = point[0 .. min(logBytecode, |point|)) ++ slot` is the
value at `valueR`.

It copies `point'` (`m ≤ 34` coordinates) into `tmpR` from word `bcPtW`, then streams the bytecode's
first `2^m` words once when there are that many (otherwise the extension is `0`): a binary counter
`i` (`rbp`) of the words read, and a stack of pending left children of the fold tree from word
`bcStW` of `tmpR`, level `l` at elements `l`. Word `i` is `v = T(0, i)`; while bit `l` of `i` is set
(`r15 = i >> l`), `v := S[l] + (S[l] + v)·r_l` and `l := l + 1`; then `S[l] := v`. After `2^m` words
`S[m]` is the root (`BcMleMath`).

Registers while streaming: `r13` the next word's address, `r14` the words left, `rbp` the counter,
`r15` its shifted copy, `rsi` the stack level's address, `A = (r9, r10)` the value carried,
`B = (r11, r12)` the coordinate.
-/

@[expose] public section

namespace NativeVm.Code.P3

open Native NativeVm.Field NativeVm.Transcript NativeVm.Code

/-- The stack of pending nodes: words `tmpR.off ..` (`35` elements at most). -/
def bcStW : Nat := tmpR.off

/-- The point's copy: words `tmpR.off + 72 ..` (`34` elements at most). -/
def bcPtW : Nat := tmpR.off + 72

/-- `rax := min(logBytecode, |point|)`, `r11` the working area. -/
def bcMin : Stmt := blk [
  I (.load .r11 (cw ctxWork)),
  I (.load .rax (at_ .r11 (wdisp (layoutR.off + 1)))),
  I (.load .rbx (at_ .r11 (wdisp depthR.off))),
  .ite (.cmp .ltu .rbx (.reg .rax)) (I (.mov .rax .rbx)) .skip]

/-- Copy `rcx` words from `rsi` to `rdx`, both advanced past them. -/
def bcCopy : Stmt := .loop (.cmp .ne .rcx (.imm 0)) (blk [
  I (.load .r8 (at_ .rsi 0)), I (.store (at_ .rdx 0) .r8),
  I (.addi .rsi 8), I (.addi .rdx 8), I (.subi .rcx 1)])

/-- `point'` into words `bcPtW ..`: the point's first `rax` elements, then the slot's four;
`rax := m`, `r14 := 2^m`. -/
def bcPrep : Stmt := blk [
  bcMin,
  I (.mov .rcx .rax), I (.shli .rcx 1),
  I (.lea .rsi (at_ .r11 (wdisp pointR.off))), I (.lea .rdx (at_ .r11 (wdisp bcPtW))),
  bcCopy,
  I (.lea .rsi (at_ .r11 (wdisp slotR.off))), I (.movi .rcx 8),
  bcCopy,
  I (.addi .rax 4), I (.mov .rcx .rax), I (.movi .r14 1), I (.shlcl .r14)]

/-- One carry: `A := S[l] + (S[l] + A)·r_l`, `rsi` at `S[l]`. -/
def bcCarry : Stmt := blk [
  I (.load .r11 (at_ .rsi (wdisp 72))), I (.load .r12 (at_ .rsi (wdisp 73))),
  I (.load .rax (at_ .rsi 0)), I (.xor .r9 .rax), I (.load .rax (at_ .rsi 8)), I (.xor .r10 .rax),
  emul,
  I (.load .rax (at_ .rsi 0)), I (.xor .r9 .rax), I (.load .rax (at_ .rsi 8)), I (.xor .r10 .rax),
  I (.addi .rsi 16), I (.shri .r15 1)]

/-- One word: `A := T(0, i)`, the carries, the store. -/
def bcWord : Stmt := blk [
  I (.load .r9 (at_ .r13 0)), I (.movi .r10 0),
  I (.mov .r15 .rbp),
  I (.load .rsi (cw ctxWork)), I (.addi .rsi (wdisp bcStW)),
  .loop (.test false .r15 (.imm 1)) bcCarry,
  I (.store (at_ .rsi 0) .r9), I (.store (at_ .rsi 8) .r10),
  I (.addi .r13 8), I (.addi .rbp 1), I (.subi .r14 1)]

/-- The stream over the first `r14 = 2^m` words; `A := S[m]`. -/
def bcStream : Stmt := blk [
  I (.load .r13 (cw ctxBytecode)), I (.movi .rbp 0),
  .loop (.cmp .ne .r14 (.imm 0)) bcWord,
  bcMin, I (.addi .rax 4), I (.shli .rax 4),
  I (.load .rsi (cw ctxWork)), I (.addi .rsi (wdisp bcStW)), I (.add .rsi .rax),
  I (.load .r9 (at_ .rsi 0)), I (.load .r10 (at_ .rsi 8))]

/-- `A` against the value at `valueR`. -/
def bcCheck : Stmt := blk [
  I (.load .r11 (cw ctxWork)),
  I (.load .rax (at_ .r11 (wdisp valueR.off))), failIf (.cmp .ne .r9 (.reg .rax)),
  I (.load .rax (at_ .r11 (wdisp (valueR.off + 1)))), failIf (.cmp .ne .r10 (.reg .rax))]

/-- **`computedBytecodeValue`**: the extension at `point'` in `A`, `0` when the bytecode has fewer
than `2^m` words, then checked against the value. -/
def bcCode : Stmt := blk [
  bcPrep,
  I (.load .rbx (cw ctxBytecodeLen)),
  .ite (.cmp .ltu .rbx (.reg .r14)) (blk [I (.movi .r9 0), I (.movi .r10 0)]) bcStream,
  bcCheck]

end NativeVm.Code.P3
