module

public import NativeRustcX64.Sym
public import NativeRustcVmX64.Code.Vm.WriteOpenings
public meta import NativeRustcVmX64.Code.Vm.WriteOpenings

/-!
# `write_openings`' blocks, run by the symbolic executor (x86-64)

Region 0 is the 160-byte frame below the entry's RSP and the return address (`stackBelow m0 160`,
168 bytes: the six pushes at offsets `112` to `152`, the locals from `8`, a callee's return
address at `0`), region 1 the four argument words above the return address (`argAl`: RSP-relative
loads past the frame, aliases of region 1). The other regions are the bytes a block reads or
writes, at a register (or a computed address, `ix`) aliased to their base.

- `entryS`: the prologue (`b0`), region 2 the phase's head at the loaded `out`.
- `frS`: the blocks without memory but the frame's and the arguments'.
- `qS`: a query's word (region 2, RDI) and the 32 bytes at `out + 1544 j` (region 3, RBP plus
  `1544` times the query's number).
- `pS`: a position's word (region 2, RDX plus eight times the index).
- `cS`: four leaf words (region 2) to the opening (region 3); `rS`: one.
- `nS`: the found node (`b16`); `dS`: a level's digest in the opening (`b17`); `kS`: a level's
  sibling count (`b18`).
- `q2S`: the second query of path C's pair (`b47`).
-/

namespace NativeRustcVmX64.Wire.WriteOpenings

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.WriteOpenings

@[expose] public section

/-- The argument words above the return address, RSP-relative from the body (RSP at offset `8`). -/
def argAl : List (Sym × Nat × Int) :=
  [(.ptr 0 168, 1, 0), (.ptr 0 176, 1, 8), (.ptr 0 184, 1, 16), (.ptr 0 192, 1, 24)]

/-- The body's state: the frame, the arguments, the chunks `cs` at the aliases `al`. -/
def fS (cs : List Nat) (al : List (Sym × Nat × Int) := []) : SState :=
  init (168 :: 32 :: cs) [(.rsp, .ptr 0 8)] [] [] (al ++ argAl)

/-- `b + s i`. -/
def ix (b i : Reg64) (s : Nat) : Sym := .bin .add .W64 (.reg b) (.bin .mul .W64 (.reg i) (.lit s))

/-- At the entry: RSP at the return address; the phase's head (region 2) at the loaded `out`. -/
def entryS : SState := init [168, 32, 24] [(.rsp, .ptr 0 160)] [] [] ((.load 1 24 8, 2, 0) :: argAl)

/-- The frame and the arguments. -/
def frS : SState := fS []

/-- A query's word at RDI (region 2), the 32 bytes at `out + 1544 j` (region 3). -/
def qS (j : Reg64) : SState := fS [8, 32] [(.reg .rdi, 2, 0), (ix .rbp j 1544, 3, 0)]

/-- A position's word (region 2). -/
def pS (i : Reg64) : SState := fS [8] [(ix .rdx i 8, 2, 0)]

/-- Four leaf words from `src - 24` (region 2) to `dst + 8 t - 24` (region 3). -/
def cS (src dst t : Reg64) : SState := fS [32, 32] [(.reg src, 2, 24), (ix dst t 8, 3, 24)]

/-- One leaf word from `src + 8 u` (region 2) to `dst + 8 u` (region 3). -/
def rS (src dst u : Reg64) : SState := fS [8, 8] [(ix src u 8, 2, 0), (ix dst u 8, 3, 0)]

/-- The found node: RBP plus `40` RDX (region 2). -/
def nodeAddr : Sym :=
  .bin .add .W64 (.reg .rbp)
    (.bin .mul .W64 (.bin .add .W64 (.reg .rdx) (.bin .mul .W64 (.reg .rdx) (.lit 4))) (.lit 8))

/-- The found node (region 2). -/
def nS : SState := fS [40] [(nodeAddr, 2, 0)]

/-- A level's digest in the opening, from R14 minus 24 (region 2). -/
def dS : SState := fS [32] [(.reg .r14, 2, 24)]

/-- A level's sibling count (region 2). -/
def kS : SState := fS [8] [(.bin .add .W64 (.load 1 16 8) (.bin .mul .W64 (.reg .r13) (.lit 8)), 2, 0)]

/-- Two queries' words at RDI (region 2), the bytes from `out + 1544 j` to the second opening's
query word (region 3, RBP plus R10). -/
def q2S : SState := fS [16, 1576] [(.reg .rdi, 2, 0), (.bin .add .W64 (.reg .rbp) (.reg .r10), 3, 0)]

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 frS
sym_block run_b2 := exec b2 (qS .rsi)
sym_block run_b3 := exec b3 (pS .rsi)
sym_block run_b4 := exec b4 frS
sym_block run_b5 := exec b5 frS
sym_block run_b6 := exec b6 frS
sym_block run_b7 := exec b7 frS
sym_block run_b8 := exec b8 frS
sym_block run_b9 := exec b9 frS
sym_block run_b10 := exec b10 (cS .r9 .r12 .rcx)
sym_block run_b11 := exec b11 frS
sym_block run_b12 := exec b12 frS
sym_block run_b13 := exec b13 (rS .rax .rcx .rdi)
sym_block run_b14 := exec b14 frS
sym_block run_b15 := exec b15 frS
sym_block run_b16 := exec b16 nS
sym_block run_b17 := exec b17 dS
sym_block run_b18 := exec b18 kS
sym_block run_b19 := exec b19 frS
sym_block run_b20 := exec b20 frS
sym_block run_b21 := exec b21 frS
sym_block run_b22 := exec b22 frS
sym_block run_b23 := exec b23 frS
sym_block run_b24 := exec b24 frS
sym_block run_b25 := exec b25 frS
sym_block run_b26 := exec b26 frS
sym_block run_b27 := exec b27 (qS .r9)
sym_block run_b28 := exec b28 (pS .r14)
sym_block run_b29 := exec b29 frS
sym_block run_b30 := exec b30 frS
sym_block run_b31 := exec b31 frS
sym_block run_b32 := exec b32 frS
sym_block run_b33 := exec b33 frS
sym_block run_b34 := exec b34 frS
sym_block run_b35 := exec b35 (cS .r10 .r13 .r11)
sym_block run_b36 := exec b36 frS
sym_block run_b37 := exec b37 frS
sym_block run_b38 := exec b38 (rS .rax .r10 .r11)
sym_block run_b39 := exec b39 frS
sym_block run_b40 := exec b40 frS
sym_block run_b41 := exec b41 frS
sym_block run_b42 := exec b42 (qS .r9)
sym_block run_b43 := exec b43 (pS .r8)
sym_block run_b44 := exec b44 frS
sym_block run_b45 := exec b45 frS
sym_block run_b46 := exec b46 frS
sym_block run_b47 := exec b47 q2S
sym_block run_b48 := exec b48 (pS .r10)
sym_block run_b49 := exec b49 frS
sym_block run_b50 := exec b50 frS
sym_block run_b51 := exec b51 frS
sym_block run_b52 := exec b52 frS
sym_block run_b53 := exec b53 frS
sym_block run_b54 := exec b54 frS

end NativeRustcVmX64.Wire.WriteOpenings
