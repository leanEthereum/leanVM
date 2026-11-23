module

public import NativeRustcVmArm.Layout.Common
public import NativeRustcVmArm.Code.Vm.PushClaim
public meta import NativeRustcVmArm.Code.Vm.PushClaim
public meta import NativeRustcVmArm.Layout.Common

/-!
# `push_claim`'s blocks, run by the symbolic executor

Full (`fullS`, region 0 the claims' count word): `b0` branches to `b4`, which returns `0`.

Room (`entryS`): region 0 the 48-byte frame below SP, region 1 the count word (X0), region 2 the
next claim's 608 bytes (`slotS`, the address `b1` computes). `b0` falls through; `b1` saves X19 to
X22 and X30, writes the column and the point's count `0`, and calls `Buf::extend` on the point.

After the call (`retS`, from the machine state the callee returns in): region 0 the frame (SP),
region 1 the count word (X20), region 2 the claim (X22). `b2` branches on W0: `b5` restores and
returns `0`; `b3` writes the value and the count plus one, restores and returns `1`.
-/

namespace NativeRustcVmArm.Layout.PushClaim

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.PushClaim NativeRustcVmArm.Layout

@[expose] public section

/-- At the entry, with no room: the count word (region 0, X0). -/
def fullS : SState := init [(8, false)] .sp [(.X0, .ptr 0 0)]

/-- `x0 + 608 · count`, as `b1` computes it: the next claim's address less `8`. -/
def slotS : Sym := .bin .add .W64 (.bin .mul .W64 (.load 1 0 8) (.lit 608)) (.ptr 1 0)

/-- At the entry, with room: the frame (region 0), the count word (region 1, X0), the next claim
(region 2, `8` bytes past `slotS`). -/
def entryS : SState :=
  init [(48, true), (8, false), (608, false)] (.ptr 0 48) [(.X0, .ptr 1 0)] [] [] [(slotS, (2, -8))]

/-- Where the callee returns: the frame (region 0, SP), the count word (region 1, X20), the claim
(region 2, X22). -/
def retS : SState :=
  init [(48, true), (8, false), (608, false)] (.ptr 0 0) [(.X20, .ptr 1 0), (.X22, .ptr 2 0)]

end

set_option Elab.async false

sym_block run_full := exec b0 fullS
sym_block run_b4 := exec b4 (after b0 fullS)
sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 (after b0 entryS)
sym_block run_b2 := exec b2 retS
sym_block run_b3 := exec b3 (after b2 retS)
sym_block run_b5 := exec b5 (after b2 retS)

end NativeRustcVmArm.Layout.PushClaim
