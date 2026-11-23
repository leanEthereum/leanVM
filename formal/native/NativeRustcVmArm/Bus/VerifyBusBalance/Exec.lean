module

public import NativeRustcArm.Sym
public import NativeRustcVmArm.Code.Vm.VerifyBusBalance
public meta import NativeRustcVmArm.Code.Vm.VerifyBusBalance

/-!
# `verify_bus_balance`'s blocks, run by the symbolic executor

`entryS`: region 0 the 5488-byte frame below SP, region 1 the layout at X1 (`b0`). `frS`: in the
frame, SP its base. `frC`: region 1 the claims at X28 (`b24`). `frB`: region 1 the bus at X19
(`b38`, `b47`). `frT`: region 1 the bus, X19 at its point (`b49`).
-/

namespace NativeRustcVmArm.Bus.VerifyBusBalance

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.VerifyBusBalance

@[expose] public section

/-- At the entry: the frame (region 0) below SP, the layout at X1. -/
def entryS : SState := init [(5488, true), (3912, false)] (.ptr 0 5488) [(.X1, .ptr 1 0)]

/-- In the frame: region 0 at SP. -/
def frS : SState := init [(5488, true)] (.ptr 0 0)

/-- In the frame, region 1 the claims at X28. -/
def frC : SState := init [(5488, true), (97288, false)] (.ptr 0 0) [(.X28, .ptr 1 0)]

/-- In the frame, region 1 the bus at X19. -/
def frB : SState := init [(5488, true), (107768, false)] (.ptr 0 0) [(.X19, .ptr 1 0)]

/-- As `frB`, the forms' offsets `b37` set in X23, X29, X27, X24, X21. -/
def frF : SState := init [(5488, true), (107768, false)] (.ptr 0 0)
  [(.X19, .ptr 1 0), (.X23, .lit 35568), (.X29, .lit 41496), (.X27, .lit 47424),
    (.X24, .lit 53352), (.X21, .lit 59280)]

/-- In the frame, region 1 the bus, X19 at its point. -/
def frT : SState := init [(5488, true), (107768, false)] (.ptr 0 0) [(.X19, .ptr 1 106704)]

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 frS
sym_block run_b2 := exec b2 frS
sym_block run_b3 := exec b3 frS
sym_block run_b4 := exec b4 frS
sym_block run_b5 := exec b5 frS
sym_block run_b6 := exec b6 frS
sym_block run_b7 := exec b7 frS
sym_block run_b8 := exec b8 frS
sym_block run_b9 := exec b9 frS
sym_block run_b10 := exec b10 frS
sym_block run_b11 := exec b11 frS
sym_block run_b12 := exec b12 frS
sym_block run_b13 := exec b13 frS
sym_block run_b14 := exec b14 frS
sym_block run_b15 := exec b15 frS
sym_block run_b16 := exec b16 frS
sym_block run_b17 := exec b17 frS
sym_block run_b18 := exec b18 frS
sym_block run_b19 := exec b19 frS
sym_block run_b20 := exec b20 frS
sym_block run_b21 := exec b21 frS
sym_block run_b22 := exec b22 frS
sym_block run_b23 := exec b23 frS
sym_block run_b24 := exec b24 frC
sym_block run_b25 := exec b25 frS
sym_block run_b26 := exec b26 frS
sym_block run_b27 := exec b27 frS
sym_block run_b28 := exec b28 frS
sym_block run_b29 := exec b29 frS
sym_block run_b30 := exec b30 frS
sym_block run_b31 := exec b31 frS
sym_block run_b32 := exec b32 frS
sym_block run_b33 := exec b33 frS
sym_block run_b34 := exec b34 frS
sym_block run_b35 := exec b35 frS
sym_block run_b36 := exec b36 frS
sym_block run_b37 := exec b37 frS
sym_block run_b38 := exec b38 frF
sym_block run_b39 := exec b39 frS
sym_block run_b40 := exec b40 frS
sym_block run_b41 := exec b41 frS
sym_block run_b42 := exec b42 frS
sym_block run_b43 := exec b43 frS
sym_block run_b44 := exec b44 frS
sym_block run_b45 := exec b45 frS
sym_block run_b46 := exec b46 frS
sym_block run_b47 := exec b47 frB
sym_block run_b48 := exec b48 frS
sym_block run_b49 := exec b49 frT
sym_block run_b50 := exec b50 frS
sym_block run_b51 := exec b51 frS

end NativeRustcVmArm.Bus.VerifyBusBalance
