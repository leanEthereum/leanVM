module

public import NativeRustcVmX64.Bus.VerifyBusBalance.Head
public import NativeRustcVmX64.Code.Vm.AccumulateSide.Names
public import NativeRustcVmX64.Code.Vm.BitLength.Names
public import NativeRustcVmX64.Code.Vm.BufEW63Extend.Names
public import NativeRustcVmX64.Code.Vm.BusLayout.Names
public import NativeRustcVmX64.Code.Vm.BytecodeShare.Names
public import NativeRustcVmX64.Code.Vm.ComputedBytecodeValue.Names
public import NativeRustcVmX64.Code.Vm.Kpow.Names
public import NativeRustcVmX64.Code.Vm.Memcpy.Names
public import NativeRustcVmX64.Code.Vm.PushClaim.Names
public import NativeRustcVmX64.Code.Vm.SpongeWSqueeze.Names
public import NativeRustcVmX64.Code.Vm.TStateGrind.Names
public import NativeRustcVmX64.Code.Vm.TStateReadScalar.Names
public import NativeRustcVmX64.Code.Vm.TStateReadScalars.Names
public import NativeRustcVmX64.Code.Vm.TStateSampleChallenges.Names
public import NativeRustcVmX64.Code.Vm.VerifyBusBalance.Names
public import NativeRustcVmX64.Code.Vm.VerifyBusBalanceClosure0.Names
public import NativeRustcVmX64.Code.Vm.VerifyGkrGrandProducts.Names

/-!
# `verify_bus_balance` (x86-64)

The three layouts (`head_spec`), the grind, the challenges and the GKR walk (`grind_spec`), the
scalars and the claims (`scal_spec`, `claimsA_spec`, `claimsB_spec`), the bytecode share
(`share_spec`), the three sides (`push_spec`, `pull_spec`, `count_spec`), the point and the totals
(`tail_spec`): `verifyBusBalance_spec`.
-/

namespace NativeRustcVmX64.Bus.VerifyBusBalance

open NativeRustcX64 NativeRustcVmX64.Vm.VerifyBusBalance
open NativeRustcVmX64.Transcript NativeRustcVmX64.Sumcheck
open NativeVm.Model NativeRustcVm.Bus

public section

variable [Host] {k : Nat}

/-- **`verify_bus_balance` meets its contract.** -/
theorem verifyBusBalance_spec (hp : Placed code k)
    (hbl : ∀ L bl, Spec (Labels.label NativeRustcVmX64.Vm.BusLayout.entryLabel) (BusLayoutPre L bl) (BusLayoutPost L bl))
    (hmc : Spec (Labels.label NativeRustcVmX64.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost)
    (hbit : Spec (Labels.label NativeRustcVmX64.Vm.BitLength.entryLabel) BitLengthPre BitLengthPost)
    (hgr : ∀ a s, Spec (Labels.label NativeRustcVmX64.Vm.TStateGrind.entryLabel) (GrindPre a s) (GrindPost a s))
    (hsc : ∀ a s, Spec (Labels.label NativeRustcVmX64.Vm.TStateSampleChallenges.entryLabel) (SampleChallengesPre a s)
      (SampleChallengesPost a s))
    (hsq : ∀ sp, Spec (Labels.label NativeRustcVmX64.Vm.SpongeWSqueeze.entryLabel) (SqueezePre sp) (SqueezePost sp))
    (hgkr : ∀ a s, Spec (Labels.label NativeRustcVmX64.Vm.VerifyGkrGrandProducts.entryLabel) (VerifyGkrPre a s) (VerifyGkrPost a s))
    (hrss : ∀ a s, Spec (Labels.label NativeRustcVmX64.Vm.TStateReadScalars.entryLabel) (ReadScalarsPre a s)
      (ReadScalarsPost a s))
    (hrs : ∀ a s, Spec (Labels.label NativeRustcVmX64.Vm.TStateReadScalar.entryLabel) (ReadScalarPre a s) (ReadScalarPost a s))
    (hpc : ∀ cs, Spec (Labels.label NativeRustcVmX64.Vm.PushClaim.entryLabel) (PushClaimPre cs) (PushClaimPost cs))
    (hbs : ∀ a s, Spec (Labels.label NativeRustcVmX64.Vm.BytecodeShare.entryLabel) (BytecodeSharePre a s)
      (BytecodeSharePost a s))
    (hcbv : Spec (Labels.label NativeRustcVmX64.Vm.ComputedBytecodeValue.entryLabel) ComputedBytecodeValuePre
      ComputedBytecodeValuePost)
    (hkp : Spec (Labels.label NativeRustcVmX64.Vm.Kpow.entryLabel) KpowPre KpowPost)
    (hfc : Spec (Labels.label NativeRustcVmX64.Vm.VerifyBusBalanceClosure0.entryLabel) FpClosurePre FpClosurePost)
    (hacc : ∀ L rows bl F SL, Spec (Labels.label NativeRustcVmX64.Vm.AccumulateSide.entryLabel)
      (AccumulateSidePre L rows bl F SL) (AccumulateSidePost L rows bl F SL))
    (hext : Spec (Labels.label NativeRustcVmX64.Vm.BufEW63Extend.entryLabel) (BufEWExtendPre 63) (BufEWExtendPost 63)) :
    ∀ a s L, Spec (Labels.label NativeRustcVmX64.Vm.VerifyBusBalance.entryLabel) (VerifyBusBalancePre a s L)
      (VerifyBusBalancePost a s L) := by
  intro a s0 L m0 h
  rw [show Labels.label NativeRustcVmX64.Vm.VerifyBusBalance.entryLabel = Host.addrOf (k + NativeRustcVmX64.Vm.VerifyBusBalance.b0Offset) from hp.label NativeRustcVmX64.Vm.VerifyBusBalance.entry_at]
  exact head_spec hp h hbl hmc fun _ A ↦ grind_spec hp h hmc hbit (hgr a) (hsc a) hsq (hgkr a)
    (fun _ _ _ _ _ _ A' ↦ scal_spec hp h (hrss a) (hrs a) hpc (hbs a) hcbv hkp hfc hacc hext A') A

end

end NativeRustcVmX64.Bus.VerifyBusBalance
