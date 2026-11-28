module

public import NativeRustcVmArm.Code.Vm.AccumulateSide.Names
public import NativeRustcVmArm.Code.Vm.BitLength.Names
public import NativeRustcVmArm.Code.Vm.BufEW63Extend.Names
public import NativeRustcVmArm.Code.Vm.BusLayout.Names
public import NativeRustcVmArm.Code.Vm.BytecodeShare.Names
public import NativeRustcVmArm.Code.Vm.ComputedBytecodeValue.Names
public import NativeRustcVmArm.Code.Vm.Kpow.Names
public import NativeRustcVmArm.Code.Vm.Memcpy.Names
public import NativeRustcVmArm.Code.Vm.PushClaim.Names
public import NativeRustcVmArm.Code.Vm.SpongeWSqueeze.Names
public import NativeRustcVmArm.Code.Vm.TStateGrind.Names
public import NativeRustcVmArm.Code.Vm.TStateReadScalar.Names
public import NativeRustcVmArm.Code.Vm.TStateReadScalars.Names
public import NativeRustcVmArm.Code.Vm.TStateSampleChallenges.Names
public import NativeRustcVmArm.Code.Vm.VerifyBusBalance.Names
public import NativeRustcVmArm.Code.Vm.VerifyBusBalanceClosure0.Names
public import NativeRustcVmArm.Code.Vm.VerifyGkrGrandProducts.Names
public import NativeRustcVmArm.Bus.VerifyBusBalance.Grind

/-!
# `verify_bus_balance`

The three layouts (`head_spec`), the grind, the challenges and the GKR walk (`grind_spec`), the
scalars and the claims (`claims_spec`), the bytecode share (`share_spec`), the three sides
(`push_spec`, `pull_spec`, `count_spec`), the point and the totals (`tail_spec`):
`verifyBusBalance_spec`.
-/

namespace NativeRustcVmArm.Bus.VerifyBusBalance

open NativeRustcArm NativeRustcVmArm.Vm.VerifyBusBalance
open NativeVm.Model NativeRustcVm.Bus

public section

variable [Host] {k : Nat}

/-- **`verify_bus_balance` meets its contract.** -/
theorem verifyBusBalance_spec (hp : Placed code k)
    (hbl : ∀ L bl, Spec (Labels.label NativeRustcVmArm.Vm.BusLayout.entryLabel) (BusLayoutPre L bl) (BusLayoutPost L bl))
    (hmc : Spec (Labels.label NativeRustcVmArm.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost)
    (hbit : Spec (Labels.label NativeRustcVmArm.Vm.BitLength.entryLabel) BitLengthPre BitLengthPost)
    (hgr : ∀ a s, Spec (Labels.label NativeRustcVmArm.Vm.TStateGrind.entryLabel) (GrindPre a s) (GrindPost a s))
    (hsc : ∀ a s, Spec (Labels.label NativeRustcVmArm.Vm.TStateSampleChallenges.entryLabel) (SampleChallengesPre a s)
      (SampleChallengesPost a s))
    (hsq : ∀ sp, Spec (Labels.label NativeRustcVmArm.Vm.SpongeWSqueeze.entryLabel) (SqueezePre sp) (SqueezePost sp))
    (hgkr : ∀ a s, Spec (Labels.label NativeRustcVmArm.Vm.VerifyGkrGrandProducts.entryLabel) (VerifyGkrPre a s) (VerifyGkrPost a s))
    (hrss : ∀ a s, Spec (Labels.label NativeRustcVmArm.Vm.TStateReadScalars.entryLabel) (ReadScalarsPre a s)
      (ReadScalarsPost a s))
    (hrs : ∀ a s, Spec (Labels.label NativeRustcVmArm.Vm.TStateReadScalar.entryLabel) (ReadScalarPre a s) (ReadScalarPost a s))
    (hpcl : ∀ cs, Spec (Labels.label NativeRustcVmArm.Vm.PushClaim.entryLabel) (PushClaimPre cs) (PushClaimPost cs))
    (hbs : ∀ a s, Spec (Labels.label NativeRustcVmArm.Vm.BytecodeShare.entryLabel) (BytecodeSharePre a s)
      (BytecodeSharePost a s))
    (hcbv : Spec (Labels.label NativeRustcVmArm.Vm.ComputedBytecodeValue.entryLabel) ComputedBytecodeValuePre
      ComputedBytecodeValuePost)
    (hkp : Spec (Labels.label NativeRustcVmArm.Vm.Kpow.entryLabel) KpowPre KpowPost)
    (hacc : ∀ L rows bl F SL, Spec (Labels.label NativeRustcVmArm.Vm.AccumulateSide.entryLabel)
      (AccumulateSidePre L rows bl F SL) (AccumulateSidePost L rows bl F SL))
    (hext : Spec (Labels.label NativeRustcVmArm.Vm.BufEW63Extend.entryLabel) (BufEWExtendPre 63) (BufEWExtendPost 63))
    (hfc : Spec (Labels.label NativeRustcVmArm.Vm.VerifyBusBalanceClosure0.entryLabel) FpClosurePre FpClosurePost) :
    ∀ a s L, Spec (Labels.label NativeRustcVmArm.Vm.VerifyBusBalance.entryLabel) (VerifyBusBalancePre a s L)
      (VerifyBusBalancePost a s L) := by
  intro a s0 L m0 h
  rw [show Labels.label NativeRustcVmArm.Vm.VerifyBusBalance.entryLabel = Host.addrOf (k + NativeRustcVmArm.Vm.VerifyBusBalance.b0Offset) from hp.label (j := NativeRustcVmArm.Vm.VerifyBusBalance.entryOffset) NativeRustcVmArm.Vm.VerifyBusBalance.entry_at]
  exact head_spec hp h hbl hmc fun _ A ↦ grind_spec hp h hbit hgr hsc hsq hgkr
    (fun _ _ _ _ _ _ A' ↦ claims_spec hp h hrss hrs hpcl hbs hcbv hkp hacc hext hfc A') A

end

end NativeRustcVmArm.Bus.VerifyBusBalance
