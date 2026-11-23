module

public import NativeRustcX64.Sym
public import NativeRustcVmX64.Code.Vm.VerifyLayer
public import NativeRustcVmX64.Code.Vm.Names
public meta import NativeRustcVmX64.Code.Vm.VerifyLayer

/-!
# `verify_layer`'s blocks, run by the symbolic executor (x86-64)

Region 0 is the 2016-byte frame below the entry's RSP and the return address (`fr o`, RSP at the
frame's offset `o`: `2016` at the entry, `24` in the body, `8` after the `sumcheck`s, which pop
their stack arguments in the next block); every register its atom. The other regions, by block:
the claim (768 bytes; through R14 in `b2`, the frame's words at `96` and `128` and RCX, RBX),
`RMFE_PROJECT` (128 bytes through R15, the index RCX bounded), a pair of instance or bit weights
(32 bytes through R8, R9 or R10, at offset 24), an instance weight (`a23`), `KECCAK_RC` (192 bytes at
its label, the index `8 (11 - step)` or `8 (23 - step)` bounded), an element of the local equality
kernel or of the layer's weights (16 bytes, `a70`, `a71a`, `a71b`, `a75`). The product's element
in `b5` is the frame's, RAX bounded.
-/

namespace NativeRustcVmX64.KeccakGkr.VerifyLayer

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.VerifyLayer

@[expose] public section

/-- `RMFE_PROJECT`'s label. -/
def projL : Label := NativeRustcVmX64.Vm.Symbols.rodata0Label
/-- `KECCAK_RC`'s label. -/
def rcL : Label := NativeRustcVmX64.Vm.Symbols.rodata1Label

/-- The frame (region 0), RSP at its offset `o`, the regions `ex` beside. -/
def fr (o : Nat) (ex : List Nat := []) (lb : List (Label × Nat) := []) (bd : List (Sym × Nat) := [])
    (al : List (Sym × Nat × Int) := []) : SState :=
  init (2024 :: ex) [(.rsp, .ptr 0 o)] lb bd al

/-- `RMFE_PROJECT` at R15, RCX below `B`. -/
def projS (B : Nat) : SState := fr 24 [128] [] [(.reg .rcx, B)] [(.reg .r15, 1, 0)]
/-- A pair of weights, 24 bytes below `r`. -/
def pairS (r : Reg64) : SState := fr 24 [32] [] [] [(.reg r, 1, 24)]
/-- The claim at `x`. -/
def claimS (x : Sym) : SState := fr 24 [768] [] [] [(x, 1, 0)]

/-- The claim copy additionally reads the loader's `memcpy` slot. -/
def claimCopyS : SState :=
  (fr 24 [768, 8] [] [] [(.load 0 96 8, 1, 0), (.gotSlot "memcpy", 2, 0)]).withKnownBytes
    2 0 8 (.label "memcpy")

/-- `8 (11 - step)`, the step the frame's word at `56`. -/
def i11 : Sym := .bin .shl .W32 (.bin .sub .W32 (.lit 11) (.load 0 56 4)) (.lit 3)
/-- `8 (23 - step)`. -/
def i23 : Sym := .bin .shl .W32 (.bin .sub .W32 (.lit 23) (.load 0 56 4)) (.lit 3)
/-- The instance weight `i` (RCX): the frame's word at `48` plus `16 i`. -/
def a23 : Sym := .bin .add .W64 (.load 0 48 8) (.bin .shl .W64 (.reg .rcx) (.lit 4))
/-- The kernel's element at `NativeRustcVmX64.Vm.VerifyLayer.label_40`. -/
def a70 : Sym := .bin .add .W64 (.bin .shl .W32 (.reg .rsi) (.lit 4))
  (.bin .add .W64 (.load 0 56 8) (.bin .shl .W64 (.reg .rax) (.lit 4)))
/-- The kernel's element `j`: R15 plus RBX (plus `107520`). -/
def a71a : Sym := .bin .add .W64 (.reg .r15) (.reg .rbx)
/-- The scratch (the frame's word at `80`) plus RBX. -/
def a71b : Sym := .bin .add .W64 (.load 0 80 8) (.reg .rbx)
/-- The kernel's element at `NativeRustcVmX64.Vm.VerifyLayer.label_42`'s load. -/
def a75 : Sym := .bin .add .W64 (.bin .shl .W32 (.un .trunc .W32 (.reg .rsi)) (.lit 4))
  (.bin .add .W64 (.load 0 56 8) (.bin .shl .W64 (.reg .rdi) (.lit 4)))

end

set_option Elab.async false

sym_block e0 := exec b0 (fr 2016)
sym_block e1 := exec b1 (fr 24)
sym_block e2 := exec b2 (fr 24 [768] [] [] [(.reg .r14, 1, 0)])
sym_block e4 := exec b4 (fr 24)
sym_block e5 := exec b5 (fr 24 [] [] [(.reg .rax, 752)])
sym_block e6 := exec b6 (fr 24)
sym_block e7 := exec b7 (fr 24)
sym_block e8 := exec b8 (fr 24)
sym_block e9 := exec b9 (fr 24)
sym_block e11 := exec b11 (fr 24)
sym_block e13 := exec b13 (fr 24)
sym_block e15 := exec b15 (fr 24)
sym_block e16 := exec b16 (projS 15)
sym_block e17 := exec b17 (pairS .r8)
sym_block e18 := exec b18 (projS 15)
sym_block e19 := exec b19 (pairS .r8)
sym_block e21 := exec b21 (fr 24)
sym_block e22 := exec b22 (projS 16)
sym_block e23 := exec b23 (fr 24 [16] [] [] [(a23, 1, 0)])
sym_block e24 := exec b24 (claimS (.load 0 96 8))
sym_block e25 := exec b25 (fr 24)
sym_block e26 := exec b26 (fr 24 [192] [(rcL, 1)] [(i11, 89)])
sym_block e28 := exec b28 (pairS .r10)
sym_block e29 := exec b29 (pairS .r10)
sym_block e30 := exec b30 (fr 24)
sym_block e31 := exec b31 (fr 24)
sym_block e32 := exec b32 (fr 24 [192] [] [(i23, 185)] [(.reg .r8, 1, 0)])
sym_block e34 := exec b34 (pairS .r9)
sym_block e35 := exec b35 (pairS .r9)
sym_block e36 := exec b36 (fr 24)
sym_block e37 := exec b37 (fr 24)
sym_block e38 := exec b38 (fr 24)
sym_block e39 := exec b39 (fr 24)
sym_block e40 := exec b40 (fr 24)
sym_block e41 := exec b41 (fr 24)
sym_block e42 := exec b42 (claimS (.load 0 96 8))
sym_block e43 := exec b43 (claimS (.reg .rcx))
sym_block e44 := exec b44 (fr 24)
sym_block e45 := exec b45 (fr 24)
sym_block e46 := exec b46 (fr 24)
sym_block e47 := exec b47 (fr 24)
sym_block e48 := exec b48 (fr 24)
sym_block e49 := exec b49 (fr 24)
sym_block e50 := exec b50 (fr 24 [768] [] [] [(.load 0 128 8, 1, 280)])
sym_block e51 := exec b51 (fr 24)
sym_block e52 := exec b52 (fr 8)
sym_block e53 := exec b53 (fr 24)
sym_block e54 := exec b54 (fr 8)
sym_block e55 := exec b55 (fr 24)
sym_block e56 := exec b56 (fr 24)
sym_block e57 := exec b57 (fr 24)
sym_block e58 := exec b58 (fr 24)
sym_block e59 := exec b59 (fr 24)
sym_block e60 := exec b60 (fr 24)
sym_block e61 := exec b61 (fr 24)
sym_block e62 := exec b62 (fr 24)
sym_block e63 := exec b63 (fr 24)
sym_block e64 := exec b64 (fr 24)
sym_block e65 := exec b65 (fr 24)
sym_block e66 := exec b66 (fr 24)
sym_block e67 := exec b67 (fr 24)
sym_block e68 := exec b68 (fr 24)
sym_block e69 := exec b69 (fr 24)
sym_block e70 := exec b70 (fr 24 [16] [] [] [(a70, 1, 0)])
sym_block e71 := exec b71 (fr 24 [16] [] [] [(a71a, 1, -107520), (a71b, 1, -107520)])
sym_block e72 := exec b72 (fr 24)
sym_block e73 := exec b73 (fr 24 [16] [] [] [(a71b, 1, -51200)])
sym_block e74 := exec b74 (fr 24)
sym_block e75 := exec b75 (fr 24 [16] [] [] [(a75, 1, 0)])
sym_block e76 := exec b76 (fr 24)
sym_block e77 := exec b77 (fr 24)
sym_block e78 := exec b78 (fr 24)
sym_block e79 := exec b79 (fr 24)
sym_block e80 := exec b80 (fr 24)
sym_block e81 := exec b81 (fr 24)
sym_block e82 := exec b82 claimCopyS
sym_block e83 := exec b83 (claimS (.reg .rbx))
sym_block e84 := exec b84 (fr 24)
sym_block e85 := exec b85 (fr 24)
sym_block e86 := exec b86 (fr 24)
sym_block e87 := exec b87 (fr 24)

end NativeRustcVmX64.KeccakGkr.VerifyLayer
