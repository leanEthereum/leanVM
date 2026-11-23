module

public import NativeRustcVmX64.Field.Parts
public meta import NativeRustcVmX64.Field.Parts
public import NativeRustcVmX64.Field.Frame
public meta import NativeRustcVmX64.Field.Frame
public import NativeRustcVmX64.Code.Vm.KeccakPi
public meta import NativeRustcVmX64.Code.Vm.KeccakPi

/-!
# `keccak_pi`'s block, run by the symbolic executor (x86-64)

One straight-line block (`b0`) without memory accesses, run from `frameS 0` (its return address at
RSP): `i / 5` by a 32-bit multiplication by `205`, `(2 i - 7 (i / 5)) % 5` by a multiply-high by
`⌈2^66 / 5⌉`, then `5 ·` that plus `i / 5`.
-/

namespace NativeRustcVmX64.KeccakGkr.KeccakPi

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Field NativeRustcVmX64.Vm.KeccakPi

@[expose] public section

/-- `i / 5`, by a 32-bit multiplication by `205`. -/
def qS : Sym := .bin .shr .W32 (.un (.zext .W16) .W32 (.bin .mul .W32 (.reg .rdi) (.lit 205))) (.lit 10)
/-- `2 i - 7 (i / 5)`. -/
def cS : Sym :=
  .bin .add .W64 (.bin .sub .W64 qS (.bin .shl .W32 qS (.lit 3))) (.bin .mul .W64 (.reg .rdi) (.lit 2))
/-- `c / 5`, by a multiply-high. -/
def hS : Sym := .bin .shr .W64 (.bin .mulhi .W64 cS (.lit 14757395258967641293)) (.lit 2)
/-- `c % 5`. -/
def rS : Sym := .bin .sub .W64 cS (.bin .add .W64 hS (.bin .mul .W64 hS (.lit 4)))
/-- RAX at the return: `5 (c % 5) + i / 5`. -/
def piS : Sym := .bin .add .W64 qS (.bin .add .W64 rS (.bin .mul .W64 rS (.lit 4)))

end

set_option Elab.async false

sym_part r := exec b0 (frameS 0)

public theorem rax_eq : r.out.reg .rax = some piS := by decide +kernel

public theorem exit_eq : r.exit = .ret (.load 0 0 8) := by decide +kernel

public theorem rsp_eq : r.out.reg .rsp = some (.ptr 0 ((0 + 8 : Nat) : Int)) := by decide +kernel

public theorem keeps_eq : keeps (frameS 0) r.out = true := by decide +kernel

public theorem mem_eq : r.out.mem = [] := by decide +kernel

end NativeRustcVmX64.KeccakGkr.KeccakPi
