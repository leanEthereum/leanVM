module

public import NativeRustcVmX64.KeccakGkr.VerifyKeccak.Seq

/-!
# `verify_keccak`'s templates (x86-64)

Region `0` the 3344 bytes below the entry's RSP, the return address and the two stack arguments
(`claims` at `3352`, `out` at `3360`); regions `1` to `4` the `TState`, the scratch, the column
claims and the `KeccakOutW` (`sizes`). Between the calls RSP is at offset `56`, the frame's locals
from there (the assembly's `o(%rsp)` at `56 + o`). A template names the values the code keeps in
callee-saved registers and spills (`.var i`):

- `0`–`5`: the entry's RBP, R15, R14, R13, R12, RBX (pushed at `3336` down to `3296`);
- `6` the `TState`, `7` `logSteps`, `8` `inst`, `9` `|inst|`, `10` the output lanes, `11` the
  scratch; `12` `logSteps - 4` (saturating), `13` `|inst| - 4` (saturating), `14` `min |inst| 4`,
  `15` the address of `inst`'s coordinates past the fourth;
- `16`, `17` the committed outputs' value; `18` the first claim's point's size; `19` the scratch's
  `weights`, `20` its `rows`; `21`, `22` the first opening's value; `23`, `24` the committed word;
  `25`, `26` the last claim's point's slice (size, address); `27`, `28` the last opening's value;
  `29` the output slices' address; `30`, `31` `multilinear_eval`'s result; `32` `bit_length 5`;
  `33`, `34` `dot`'s result; `35` the result (`b71`'s R13).
-/

namespace NativeRustcVmX64.KeccakGkr.VerifyKeccak

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Ring

@[expose] public section

/-- The regions' sizes. -/
def sizes : List Nat := [3368, 760, 205824, 97288, 1608]

/-- The pushed registers: RBP, R15, R14, R13, R12, RBX from offset `3336` down. -/
def pushW : List Write :=
  [⟨0, 3336, 8, .var 0⟩, ⟨0, 3328, 8, .var 1⟩, ⟨0, 3320, 8, .var 2⟩, ⟨0, 3312, 8, .var 3⟩,
    ⟨0, 3304, 8, .var 4⟩, ⟨0, 3296, 8, .var 5⟩]

/-- A spill: the word at `o` the variable `i`. -/
def sp (o i : Nat) : Write := ⟨0, o, 8, .var i⟩

/-- At the entry. -/
def tE : SState := tpl sizes [(.rsp, .ptr 0 3344)] []

/-- The pushes only (the exits). -/
def tM : SState := tpl sizes [(.rsp, .ptr 0 56)] pushW

/-- After `bit_length`. -/
def t1 : SState :=
  tpl sizes [(.rsp, .ptr 0 56), (.rax, .var 32), (.rbx, .var 12), (.rbp, .var 6), (.r12, .var 13),
    (.r13, .lit 0), (.r14, .var 10), (.r15, .var 9)]
    ([sp 56 11, sp 72 7, sp 80 8, sp 136 15, sp 144 14] ++ pushW)

/-- After the grind, the samples, the committed value's read. -/
def t2 : SState :=
  tpl sizes [(.rsp, .ptr 0 56), (.rbx, .var 12), (.rbp, .var 6), (.r12, .var 13),
    (.r13, .lit 0), (.r14, .var 10), (.r15, .var 9)]
    ([sp 56 11, sp 72 7, sp 80 8, sp 136 15, sp 144 14] ++ pushW)

/-- After `first_claim` (RSP at `24`). -/
def t8 : SState :=
  tpl sizes [(.rsp, .ptr 0 24), (.rbx, .var 12), (.rbp, .var 6), (.r12, .var 13), (.r13, .var 16)]
    ([sp 56 11, sp 72 7, sp 80 8, sp 88 17, sp 136 15, sp 144 14] ++ pushW)

/-- `first_claim`'s check. -/
def t9 : SState :=
  tpl sizes [(.rsp, .ptr 0 56), (.rbx, .var 12), (.rbp, .var 6), (.r12, .var 13), (.r13, .var 16)]
    ([sp 56 11, sp 72 7, sp 80 8, sp 88 17, sp 136 15, sp 144 14] ++ pushW)

/-- Only the first copy reads the loader slot; subsequent copies retain its value in R13. -/
def t9R : SState :=
  { t9 with regions := sizes ++ [8], aliases := [(.gotSlot "memcpy", 5, 0)] }

def t9G : SState := t9R.withKnownBytes 5 0 8 (.label "memcpy")

/-- After the first copy. -/
def t10 : SState :=
  tpl sizes [(.rsp, .ptr 0 56), (.rbx, .var 12), (.r12, .var 13), (.r14, .ptr 0 2536),
    (.r13, .label "memcpy")]
    ([sp 56 11, sp 64 6, sp 72 7, sp 80 8, sp 88 17, sp 128 16, sp 136 15, sp 144 14] ++ pushW)

/-- The copies of the first claim. -/
def t11 : SState :=
  tpl sizes [(.rsp, .ptr 0 56), (.rbx, .var 12), (.rbp, .var 18), (.r12, .var 13),
    (.r14, .ptr 0 2536), (.r15, .ptr 0 2816), (.r13, .label "memcpy")]
    ([sp 56 11, sp 64 6, sp 72 7, sp 80 8, sp 88 17, sp 128 16, sp 136 15, sp 144 14] ++ pushW)

/-- After the claim's copy: the first point's size at `120`. -/
def t15 : SState :=
  tpl sizes [(.rsp, .ptr 0 56), (.rbx, .var 12), (.rbp, .var 18), (.r12, .var 13),
    (.r14, .ptr 0 2536), (.r15, .ptr 0 2816), (.r13, .label "memcpy")]
    ([sp 56 11, sp 64 6, sp 72 7, sp 80 8, sp 88 17, sp 120 18, sp 128 16, sp 136 15,
      sp 144 14] ++ pushW)

/-- After the weights' copy. -/
def t16 : SState :=
  tpl sizes [(.rsp, .ptr 0 56), (.rbx, .var 12), (.rbp, .var 19), (.r12, .var 13)]
    ([sp 56 11, sp 64 6, sp 72 7, sp 80 8, sp 88 17, sp 120 18, sp 128 16, sp 136 15,
      sp 144 14] ++ pushW)

/-- The layers. -/
def tL : SState :=
  tpl sizes [(.rsp, .ptr 0 56), (.rbx, .var 12), (.rbp, .var 19), (.r12, .var 13), (.r13, .var 11),
    (.r14, .var 6), (.r15, .var 7)]
    ([sp 56 11, sp 64 6, sp 72 7, sp 80 8, sp 88 17, sp 120 18, sp 128 16, sp 136 15,
      sp 144 14] ++ pushW)

/-- After the first opening (RSP at `8`). -/
def t41 : SState :=
  tpl sizes [(.rsp, .ptr 0 8), (.rbx, .var 12), (.rbp, .var 19), (.r12, .var 13), (.r13, .var 20),
    (.r14, .var 6), (.r15, .var 7)]
    ([sp 56 11, sp 64 6, sp 72 7, sp 80 8, sp 136 15, sp 144 14] ++ pushW)

/-- The first opening's check. -/
def t42 : SState :=
  tpl sizes [(.rsp, .ptr 0 56), (.rbx, .var 12), (.rbp, .var 19), (.r12, .var 13), (.r13, .var 20),
    (.r14, .var 6), (.r15, .var 7)]
    ([sp 56 11, sp 64 6, sp 72 7, sp 80 8, sp 136 15, sp 144 14] ++ pushW)

/-- After the committed word's read. -/
def t43 : SState :=
  tpl sizes [(.rsp, .ptr 0 56), (.rbx, .var 12), (.rbp, .var 19), (.r12, .var 13), (.r13, .var 20),
    (.r14, .var 22), (.r15, .var 21)]
    ([sp 56 11, sp 64 6, sp 72 7, sp 80 8, sp 136 15, sp 144 14] ++ pushW)

/-- The committed word's check: the scratch is region `2`. -/
def t44 : SState :=
  tpl sizes [(.rsp, .ptr 0 56), (.rbx, .var 12), (.rbp, .var 19), (.r12, .var 13), (.r13, .var 20),
    (.r14, .var 22), (.r15, .var 21)]
    ([sp 56 11, sp 64 6, sp 72 7, sp 80 8, sp 136 15, sp 144 14] ++ pushW) [] [(.var 11, 2, 0)]

/-- After the product's check: the committed word at `56`, `88`. -/
def t45 : SState :=
  tpl sizes [(.rsp, .ptr 0 56), (.rbx, .var 12), (.rbp, .var 19), (.r12, .var 13), (.r13, .var 20),
    (.r14, .var 22), (.r15, .var 21)]
    ([sp 56 23, sp 64 6, sp 72 7, sp 80 8, sp 88 24, sp 136 15, sp 144 14] ++ pushW)

/-- After the output point's slot: R12 the slot's address. -/
def t52 : SState :=
  tpl sizes [(.rsp, .ptr 0 56), (.rbx, .var 12), (.rbp, .var 19), (.r12, .ptr 0 232),
    (.r13, .var 20), (.r14, .var 22), (.r15, .var 21)]
    ([sp 56 23, sp 64 6, sp 72 7, sp 80 8, sp 88 24, sp 136 15, sp 144 14] ++ pushW)

/-- After the sumcheck over the instances (RSP at `40`). -/
def t56 : SState :=
  tpl sizes [(.rsp, .ptr 0 40), (.rbx, .var 12), (.rbp, .var 19), (.r12, .ptr 0 232),
    (.r13, .var 20)] ([sp 64 6, sp 72 7] ++ pushW)

/-- The sumcheck's check. -/
def t57 : SState :=
  tpl sizes [(.rsp, .ptr 0 56), (.rbx, .var 12), (.rbp, .var 19), (.r12, .ptr 0 232),
    (.r13, .var 20)] ([sp 64 6, sp 72 7] ++ pushW)

/-- After the last opening (RSP at `8`). -/
def t58 : SState :=
  tpl sizes [(.rsp, .ptr 0 8), (.rbx, .var 12), (.r13, .var 20), (.r14, .var 25), (.r15, .var 26)]
    ([sp 64 6] ++ pushW)

/-- The last opening's check. -/
def t59 : SState :=
  tpl sizes [(.rsp, .ptr 0 56), (.rbx, .var 12), (.r13, .var 20), (.r14, .var 25), (.r15, .var 26)]
    ([sp 64 6] ++ pushW)

/-- After the slices' read: the last opening's value at `56`, `72`, the slices' address at `80`. -/
def t60 : SState :=
  tpl sizes [(.rsp, .ptr 0 56), (.rbx, .var 12), (.r13, .var 20), (.r14, .var 25), (.r15, .var 26)]
    ([sp 56 27, sp 64 6, sp 72 28, sp 80 29] ++ pushW)

/-- After `multilinear_eval`: its result in RAX, RDX. -/
def t61 : SState :=
  tpl sizes [(.rsp, .ptr 0 56), (.rax, .var 30), (.rdx, .var 31), (.rbx, .var 12), (.r13, .var 20),
    (.r14, .var 25), (.r15, .var 26)]
    ([sp 56 27, sp 64 6, sp 72 28, sp 80 29] ++ pushW)

/-- After `dot`: its result in RAX, RDX. -/
def t62 : SState :=
  tpl sizes [(.rsp, .ptr 0 56), (.rax, .var 33), (.rdx, .var 34), (.rbx, .var 12), (.rbp, .var 31),
    (.r12, .var 30), (.r13, .var 20), (.r14, .var 25), (.r15, .var 26)]
    ([sp 56 27, sp 64 6, sp 72 28, sp 80 29] ++ pushW)

/-- The output point's reset: the `KeccakOutW` (the stack argument at `3360`) is region `4`. -/
def t66 : SState := { t60 with aliases := [(.load 0 3360 8, 4, 0)] }

/-- After the output point's second part. -/
def t69 : SState :=
  tpl sizes [(.rsp, .ptr 0 56), (.rbx, .var 12), (.r13, .var 20), (.r15, .var 26)]
    ([sp 56 27, sp 64 6, sp 72 28, sp 80 29] ++ pushW)

/-- At the epilogue, the result in R13. -/
def tOk : SState := tpl sizes [(.rsp, .ptr 0 56), (.r13, .var 35)] pushW

/-- At the epilogue of a failure. -/
def tF : SState := tpl sizes [(.rsp, .ptr 0 56), (.r13, .lit 0)] pushW

end

end NativeRustcVmX64.KeccakGkr.VerifyKeccak
