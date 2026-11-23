module

public import NativeRustcArm.Sym
public import NativeRustcVmArm.Code.Vm.VerifyGkrGrandProducts
public meta import NativeRustcVmArm.Code.Vm.VerifyGkrGrandProducts

/-!
# `verify_gkr_grand_products`'s blocks, run by the symbolic executor

`entryS`, at the entry: region 0 the 96-byte frame below SP. `frS`, in the frame (SP its base).
`frP`: region 1 the `GkrStateW` at X20 (`b4`). `frO`: region 1 the `Option<EW>` at X19 (`b6`,
`b8`).
-/

namespace NativeRustcVmArm.Bus.VerifyGkr

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.VerifyGkrGrandProducts

@[expose] public section

/-- At the entry: the frame (region 0) below SP. -/
def entryS : SState := init [(96, true)] (.ptr 0 96)

/-- In the frame: region 0 at SP. -/
def frS : SState := init [(96, true)] (.ptr 0 0)

/-- In the frame, region 1 the `GkrStateW` at X20. -/
def frP : SState := init [(96, true), (1064, false)] (.ptr 0 0) [(.X20, .ptr 1 0)]

/-- In the frame, region 1 the `Option<EW>` at X19. -/
def frO : SState := init [(96, true), (24, false)] (.ptr 0 0) [(.X19, .ptr 1 0)]

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 frS
sym_block run_b2 := exec b2 frS
sym_block run_b3 := exec b3 frS
sym_block run_b4 := exec b4 frP
sym_block run_b5 := exec b5 frS
sym_block run_b6 := exec b6 frO
sym_block run_b7 := exec b7 frS
sym_block run_b8 := exec b8 frO

end NativeRustcVmArm.Bus.VerifyGkr
