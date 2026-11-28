module

public import NativeRustcVmX64.Whir.GlueLevel.Seq
public meta import NativeRustcVmX64.Whir.GlueLevel.Seq
public import NativeRustcVmX64.Code.Vm.GlueLevel
public meta import NativeRustcVmX64.Code.Vm.GlueLevel

/-!
# `glue_level`'s blocks, run by the symbolic executor (x86-64)

Region `0` the 96-byte frame (the call slot, the spills at `16` to `47`, the six pushes from `48`),
the return address and the 64 bytes of stack arguments. Then the state's parts: the claim (`1`,
16 bytes), the `α`s (`2`, 488 bytes, read only), the glued claims' count (`3`), the first new glued
claim's header (`4`, 40 bytes) and point (`5`), the second's header (`6`), its queries (`7`) and its
weights (`8`). The
templates `t<k>` describe the state at the start of block `k` (after a call: RSP at offset `8`);
the variables are the entry's pushed registers (`0` to `5`), RAX and RDX after a call (`6`, `7`),
and the values the function keeps (`8` on, `vals`). Region `1` is RBX; regions `2`, `3` the
aliases of their offsets `16`, `504` from it, the glued claims the aliases of their addresses
(`key1`, `key2`, `key3`).
-/

namespace NativeRustcVmX64.Whir.GlueLevel

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Ring NativeRustcVmX64.Vm.GlueLevel

@[expose] public section

/-- The regions' sizes. -/
def sizes : List Nat := [168, 16, 488, 8, 40, 488, 40, 1848, 3688]

/-- The pushes: RBP, R15, R14, R13, R12, RBX from offset `88` down, the variables `0` to `5`. -/
def pushW : List Write :=
  [⟨0, 88, 8, .var 0⟩, ⟨0, 80, 8, .var 1⟩, ⟨0, 72, 8, .var 2⟩, ⟨0, 64, 8, .var 3⟩,
    ⟨0, 56, 8, .var 4⟩, ⟨0, 48, 8, .var 5⟩]

/-- A spill at offset `o`, the variable `i`. -/
def sp (o i : Nat) : Write := ⟨0, o, 8, .var i⟩

/-- A word at offset `o` of region `r`, the variable `i`. -/
def wd (r o i : Nat) : Write := ⟨r, o, 8, .var i⟩

/-- The `α`s' and the count's aliases. -/
def headA : List (Sym × Nat × Int) := [(.ptr 1 16, 2, 0), (.ptr 1 504, 3, 0)]

/-- The first new glued claim's address: `512 + 6064 · count` from the state. -/
def key1 : Sym := .bin .add .W64 (.ptr 1 512) (.bin .mul .W64 (.var 19) (.lit 6064))

/-- The second's, from the count after the first. -/
def key2 : Sym := .bin .add .W64 (.ptr 1 512) (.bin .mul .W64 (.var 24) (.lit 6064))

/-- The second's, from its offset kept in R14. -/
def key3 : Sym := .bin .add .W64 (.var 25) (.ptr 1 512)

/-- The new claim. -/
def claimW : List Write := [wd 1 0 20, wd 1 8 21]

/-- The first new glued claim's header. -/
def g1W : List Write := [wd 4 0 8, wd 4 8 9, wd 4 16 22, wd 4 24 23]

/-- The second's. -/
def g2W : List Write := [wd 6 0 18, wd 6 8 17, wd 6 16 22, wd 6 24 26, wd 6 32 12]

def t0 : SState := tpl sizes [(.rsp, .ptr 0 96), (.rdi, .ptr 1 0)] [] [] headA

def t1 : SState :=
  tpl sizes [(.rsp, .ptr 0 8), (.rbx, .ptr 1 0), (.r14, .var 8), (.rbp, .var 9), (.r12, .var 10),
    (.rax, .var 6), (.rdx, .var 7)] ([sp 16 11, sp 24 12, sp 32 13, sp 40 14] ++ pushW) [] headA

def t2 : SState :=
  tpl sizes [(.rsp, .ptr 0 8), (.rbx, .ptr 1 0), (.r14, .var 8), (.rbp, .var 9), (.r13, .var 15),
    (.r15, .var 16), (.rax, .var 6), (.rdx, .var 7)] ([sp 24 12, sp 32 13, sp 40 14] ++ pushW) []
    headA

def t3 : SState :=
  tpl sizes [(.rsp, .ptr 0 8), (.rbx, .ptr 1 0), (.r14, .var 8), (.rbp, .var 9), (.r13, .var 15),
    (.r15, .var 16), (.r12, .var 17), (.rax, .var 6), (.rdx, .var 7)]
    ([sp 16 18, sp 24 12, sp 32 13, sp 40 14] ++ pushW) [] headA

def t4 : SState :=
  tpl sizes [(.rsp, .ptr 0 8), (.rbx, .ptr 1 0), (.r14, .var 8), (.rbp, .var 9), (.r12, .var 17),
    (.rax, .var 19)] (claimW ++ [sp 16 18, sp 24 12, sp 32 13, sp 40 14] ++ pushW) []
    (headA ++ [(key1, 4, 0), (.bin .add .W64 key1 (.lit 40), 5, 0)])

def t5 : SState :=
  tpl sizes [(.rsp, .ptr 0 8), (.rbx, .ptr 1 0), (.r12, .var 17), (.r13, .ptr 1 512),
    (.r15, .var 22)] (claimW ++ g1W ++ [sp 16 18, sp 24 12] ++ pushW) [] headA

def t7 : SState :=
  tpl sizes [(.rsp, .ptr 0 8), (.rbx, .ptr 1 0), (.r12, .var 17), (.r13, .ptr 1 512),
    (.r15, .var 22), (.rax, .var 24)]
    (claimW ++ [wd 3 0 24] ++ g1W ++ [sp 16 18, sp 24 12] ++ pushW) []
    (headA ++ [(key2, 6, 0), (.bin .add .W64 key2 (.lit 528), 7, 0)])

def t8 : SState :=
  tpl sizes [(.rsp, .ptr 0 8), (.rbx, .ptr 1 0), (.r13, .ptr 1 512), (.r14, .var 25)]
    (claimW ++ [wd 3 0 24] ++ g1W ++ g2W ++ pushW) []
    (headA ++ [(.bin .add .W64 key3 (.lit 2376), 8, 0)])

def t10 : SState :=
  tpl sizes [(.rsp, .ptr 0 8), (.rbx, .ptr 1 0)] (claimW ++ [wd 3 0 24] ++ g1W ++ g2W ++ pushW) []
    headA

def t13 : SState :=
  tpl sizes [(.rsp, .ptr 0 8)] (claimW ++ [wd 3 0 27] ++ g1W ++ g2W ++ pushW) []
    headA

end

set_option Elab.async false

sym_block run_b0 := exec b0 t0
sym_block run_b1 := exec b1 t1
sym_block run_b2 := exec b2 t2
sym_block run_b3 := exec b3 t3
sym_block run_b4 := exec b4 t4
sym_block run_b5 := exec b5 t5
sym_block run_b6 := exec b6 t5
sym_block run_b7 := exec b7 t7
sym_block run_b8 := exec b8 t8
sym_block run_b9 := exec b9 t8
sym_block run_b10 := exec b10 t10
sym_block run_b11 := exec b11 t10
sym_block run_b13 := exec b13 t13

end NativeRustcVmX64.Whir.GlueLevel
