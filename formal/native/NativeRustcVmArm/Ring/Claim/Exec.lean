module

public import NativeRustcArm.Sym
public import NativeRustcVmArm.Code.Vm.RingClaimWeight
public meta import NativeRustcVmArm.Code.Vm.RingClaimWeight
public import NativeRustcVmArm.Whir.Common
public meta import NativeRustcVmArm.Whir.Common

/-!
# `ring_claim_weight`'s blocks, run by the symbolic executor

- `entryS`, at the entry (`b0`): region 0 the 112-byte frame below SP;
- `midS`, after `eq_eval_fn` (`b1`): region 0 the frame (SP);
- `retS`, after `ring_weight` (`b2` then `b3`) and after `EW::mul` (`b4` then `b5`): region 0 the
  frame (SP), region 1 the `Option<EW>` X19 points to.
-/

namespace NativeRustcVmArm.Ring.Claim

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.RingClaimWeight NativeRustcVmArm.Whir

@[expose] public section

/-- At the entry: the frame (region 0). -/
def entryS : SState := init [(112, true)] (.ptr 0 112)

/-- After `eq_eval_fn`: the frame (region 0, SP). -/
def midS : SState := init [(112, true)] (.ptr 0 0)

/-- After a later call: the frame (region 0, SP), the output (region 1, X19). -/
def retS : SState := init [(112, true), (24, false)] (.ptr 0 0) [(.X19, .ptr 1 0)]

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 midS
sym_block run_b2 := exec b2 retS
sym_block run_b3 := exec b3 (after b2 retS)
sym_block run_b4 := exec b4 retS
sym_block run_b5 := exec b5 (after b4 retS)

end NativeRustcVmArm.Ring.Claim
