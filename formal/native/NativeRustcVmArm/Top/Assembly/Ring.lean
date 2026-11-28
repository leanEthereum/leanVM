module

public import NativeRustcVmArm.Code.Vm.ColumnWeight.Names
public import NativeRustcVmArm.Code.Vm.RingClaimWeight.Names
public import NativeRustcVmArm.Code.Vm.RingCoefficients.Names
public import NativeRustcVmArm.Code.Vm.RingPsi.Names
public import NativeRustcVmArm.Code.Vm.RingSwitch.Names
public import NativeRustcVmArm.Code.Vm.RingTarget.Names
public import NativeRustcVmArm.Code.Vm.RingWeight.Names
public import NativeRustcVmArm.Top.Assembly.Layout
public import NativeRustcVmArm.Ring.Psi
public import NativeRustcVmArm.Ring.Coeff
public import NativeRustcVmArm.Ring.Target
public import NativeRustcVmArm.Ring.Switch
public import NativeRustcVmArm.Ring.Column
public import NativeRustcVmArm.Ring.Claim
public import NativeRustcVmArm.Ring.Weight

/-!
# Ring switching, placed in `leanvm_verify`'s program

Those of `ring.rs` proved so far, instantiated at their places in `Vm.code` with their callees'
instantiated contracts.
-/

namespace NativeRustcVmArm.Assembly

open NativeRustcArm NativeRustcVmArm.Placement

public section

variable [NativeRustcArm.Host] (hP : NativeRustcArm.Host.prog = Vm.code)
include hP

theorem ringPsi : Spec (label NativeRustcVmArm.Vm.RingPsi.entryLabel) RingPsiPre RingPsiPost :=
  Ring.Psi.ringPsi_spec (placed_RingPsi hP) (ewMul hP)

theorem ringCoefficients :
    Spec (label NativeRustcVmArm.Vm.RingCoefficients.entryLabel) RingCoefficientsPre RingCoefficientsPost :=
  Ring.Coeff.ringCoefficients_spec (placed_RingCoefficients hP) (ewMul hP) (ewSqIter hP)

theorem ringTarget : Spec (label NativeRustcVmArm.Vm.RingTarget.entryLabel) RingTargetPre RingTargetPost :=
  Ring.Target.ringTarget_spec (placed_RingTarget hP) (ringPsi hP) (memcpy hP) (ewSqIter hP)
    (polyEval hP) (ewMul hP)

theorem ringSwitch : ∀ a s point,
    Spec (label NativeRustcVmArm.Vm.RingSwitch.entryLabel) (RingSwitchPre a s) (RingSwitchPost a s point) :=
  Ring.Switch.ringSwitch_spec (placed_RingSwitch hP) (grind hP) (sampleChallenges hP)
    (ringCoefficients hP) (ringTarget hP)

theorem columnWeight : Spec (label NativeRustcVmArm.Vm.ColumnWeight.entryLabel) ColumnWeightPre ColumnWeightPost :=
  Ring.Column.columnWeight_spec (placed_ColumnWeight hP) (stackPoint hP) (eqEval hP)

theorem ringWeight : Spec (label NativeRustcVmArm.Vm.RingWeight.entryLabel) RingWeightPre RingWeightPost :=
  Ring.Weight.ringWeight_spec (placed_RingWeight hP) (ewMul hP)

theorem ringClaimWeight :
    Spec (label NativeRustcVmArm.Vm.RingClaimWeight.entryLabel) RingClaimWeightPre RingClaimWeightPost :=
  Ring.Claim.ringClaimWeight_spec (placed_RingClaimWeight hP) (eqEvalFn hP) (ringWeight hP)
    (ewMul hP)

end

end NativeRustcVmArm.Assembly
