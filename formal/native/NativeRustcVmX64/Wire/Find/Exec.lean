module

public import NativeRustcX64.Sym
public import NativeRustcX64.Mem.Common
public import NativeRustcVmX64.Code.Vm.Find
public meta import NativeRustcVmX64.Code.Vm.Find
public meta import NativeRustcX64.Mem.Common

/-!
# `find`'s blocks, run by the symbolic executor (x86-64)

`find` uses no stack but its return address.

- `regS`: no region: the empty check (`b0`), the loop's set-up (`b1`), the count (`b3`).
- `headS`: region 0 the key of the node at RDI plus R8 (an alias): the loop's comparison (`b2`).
- `sRet`: region 0 the return address: the returns (`b4`; `b5`, `None`; `b6`, `Some`).
-/

namespace NativeRustcVmX64.Wire.Find

open NativeRustcX64 NativeRustcX64.Sym NativeRustcX64.Mem NativeRustcVmX64.Vm.Find

@[expose] public section

/-- No region. -/
def regS : SState := init []

/-- The key of the node at RDI plus R8 (region 0). -/
def headS : SState := init [8] [] [] [] [(.bin .add .W64 (.reg .rdi) (.reg .r8), 0, 0)]

end

set_option Elab.async false

sym_block run_b0 := exec b0 regS
sym_block run_b1 := exec b1 regS
sym_block run_b2 := exec b2 headS
sym_block run_b3 := exec b3 regS
sym_block run_b4 := exec b4 sRet
sym_block run_b5 := exec b5 sRet
sym_block run_b6 := exec b6 sRet

end NativeRustcVmX64.Wire.Find
