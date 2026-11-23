module

public import NativeRustcX64.Sym
public import NativeRustcX64.Mem.Common
public import NativeRustcVmX64.Code.Vm.InsD
public meta import NativeRustcVmX64.Code.Vm.InsD
public meta import NativeRustcX64.Mem.Common

/-!
# `ins_d`'s blocks, run by the symbolic executor (x86-64)

`ins_d` uses no stack but its return address; each element access `(%rdi,%rk,8)` of index
`zext8 x` (`movzbl`) is placed by an alias (`elem x`) at a region of one element.

- `regS`: no region: the start (`b0`), the scan's count (`b3`), the shift's set-up (`b7`, `b8`,
  `b9`, `b11`) and the alignments (`b1`, `b12`).
- `scanS`: region 0 the element at RCX: the scan's comparison (`b2`), then its second test (`b5`).
- `endS`: region 0 the return address, region 1 the element at RAX: `x` at the end (`b4`).
- `sRet`: the return with nothing inserted (`b6`).
- `remS`: regions 0, 1 the elements at R10 minus one and at R10: a step of the shift's remainder
  loop (`b10`).
- `unrS`: regions 0 to 4 the elements at RSI minus one, RSI, RSI minus two, three and four: four
  steps of the shift (`b13`).
- `storeS`: region 0 the return address, region 1 the element at RCX: `x` in place (`b14`).
-/

namespace NativeRustcVmX64.Wire.InsD

open NativeRustcX64 NativeRustcX64.Sym NativeRustcX64.Mem NativeRustcVmX64.Vm.InsD

@[expose] public section

/-- The state `exec ds S` ends in (`S` where it fails). -/
def after (ds : List Directive) (S : SState) : SState :=
  match exec ds S with
  | some (S', _) => S'
  | none => S

/-- The address of the element of index `zext8 x` (`(%rdi,%rk,8)` after `movzbl`). -/
def elem (x : Sym) : Sym :=
  .bin .add .W64 (.reg .rdi) (.bin .mul .W64 (.un (.zext .W8) .W32 x) (.lit 8))

/-- `RSI - k` in 32 bits (`leal -k(%rsi)`). -/
def tr (k : Nat) : Sym := .un .trunc .W32 (.bin .add .W64 (.reg .rsi) (.lit (2 ^ 64 - k)))

/-- `RSI - 4` (`addq $-4, %rsi`). -/
def rsi4 : Sym := .bin .add .W64 (.lit (2 ^ 64 - 4)) (.reg .rsi)

/-- `R10 - 1` (`leaq -1(%r10)`). -/
def r10m : Sym := .bin .add .W64 (.reg .r10) (.lit (2 ^ 64 - 1))

/-- No region. -/
def regS : SState := init []

/-- The element at RCX. -/
def scanS : SState := init [8] [] [] [] [(elem (.reg .rcx), 0, 0)]

/-- The return address, the element at RAX. -/
def endS : SState := init [8, 8] [(.rsp, .ptr 0 0)] [] [] [(elem (.reg .rax), 1, 0)]

/-- The elements at R10 minus one and at R10. -/
def remS : SState := init [8, 8] [] [] [] [(elem r10m, 0, 0), (elem (.reg .r10), 1, 0)]

/-- The elements at RSI minus one, RSI, RSI minus two, three, four. -/
def unrS : SState := init [8, 8, 8, 8, 8] [] [] []
  [(elem (tr 1), 0, 0), (elem (.reg .rsi), 1, 0), (elem (tr 2), 2, 0), (elem (tr 3), 3, 0),
    (elem rsi4, 4, 0)]

/-- The return address, the element at RCX. -/
def storeS : SState := init [8, 8] [(.rsp, .ptr 0 0)] [] [] [(elem (.reg .rcx), 1, 0)]

end

set_option Elab.async false

sym_block run_b0 := exec b0 regS
sym_block run_b1 := exec b1 regS
sym_block run_b2 := exec b2 scanS
sym_block run_b3 := exec b3 regS
sym_block run_b4 := exec b4 endS
sym_block run_b5 := exec b5 (after b2 scanS)
sym_block run_b6 := exec b6 sRet
sym_block run_b7 := exec b7 regS
sym_block run_b8 := exec b8 regS
sym_block run_b9 := exec b9 regS
sym_block run_b10 := exec b10 remS
sym_block run_b11 := exec b11 regS
sym_block run_b12 := exec b12 regS
sym_block run_b13 := exec b13 unrS
sym_block run_b14 := exec b14 storeS

end NativeRustcVmX64.Wire.InsD
