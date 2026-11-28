module

public import NativeRustcVmX64.Top.Assembly.Layout
public import NativeRustcVmX64.Ring.Psi
public import NativeRustcVmX64.Ring.Coeff
public import NativeRustcVmX64.Ring.Target
public import NativeRustcVmX64.Ring.Column
public import NativeRustcVmX64.Ring.Weight
public import NativeRustcVmX64.Ring.Claim
public import NativeRustcVmX64.Ring.Switch
public import NativeRustcVmX64.Code.Vm.ColumnWeight.Names
public import NativeRustcVmX64.Code.Vm.RingClaimWeight.Names
public import NativeRustcVmX64.Code.Vm.RingCoefficients.Names
public import NativeRustcVmX64.Code.Vm.RingPsi.Names
public import NativeRustcVmX64.Code.Vm.RingSwitch.Names
public import NativeRustcVmX64.Code.Vm.RingTarget.Names
public import NativeRustcVmX64.Code.Vm.RingWeight.Names

/-!
# Ring switching, placed in `leanvm_verify`'s program

The ring-switching functions and the stack weights (`ring_psi`, `ring_coefficients`, `ring_target`,
`ring_switch`, `column_weight`, `ring_weight`, `ring_claim_weight`), instantiated at their places
in `Vm.code` with their callees' instantiated contracts.
-/

namespace NativeRustcVmX64.Assembly

open NativeRustcX64 NativeRustcVmX64.Placement

public section

variable [Host] (hP : Host.prog = Vm.code)
include hP

theorem ringPsi : Spec (label NativeRustcVmX64.Vm.RingPsi.entryLabel) RingPsiPre RingPsiPost :=
  Ring.Psi.ringPsi_spec (placed_RingPsi hP) (ewMul hP)

theorem ringCoefficients :
    Spec (label NativeRustcVmX64.Vm.RingCoefficients.entryLabel) RingCoefficientsPre RingCoefficientsPost :=
  Ring.Coeff.ringCoefficients_spec (placed_RingCoefficients hP) (ewMul hP) (ewSqIter hP)

theorem ringTarget : Spec (label NativeRustcVmX64.Vm.RingTarget.entryLabel) RingTargetPre RingTargetPost :=
  Ring.Target.ringTarget_spec (placed_RingTarget hP) (ringPsi hP) (memcpy hP) (ewSqIter hP)
    (polyEval hP) (ewMul hP)

theorem ringSwitch : ∀ a s point,
    Spec (label NativeRustcVmX64.Vm.RingSwitch.entryLabel) (RingSwitchPre a s) (RingSwitchPost a s point) :=
  Ring.Switch.ringSwitch_spec (placed_RingSwitch hP) (grind hP) (sampleChallenges hP)
    (ringCoefficients hP) (ringTarget hP)

theorem columnWeight : Spec (label NativeRustcVmX64.Vm.ColumnWeight.entryLabel) ColumnWeightPre ColumnWeightPost :=
  Ring.Column.columnWeight_spec (placed_ColumnWeight hP) (stackPoint hP) (eqEval hP)

theorem ringWeight : Spec (label NativeRustcVmX64.Vm.RingWeight.entryLabel) RingWeightPre RingWeightPost :=
  Ring.Weight.ringWeight_spec (placed_RingWeight hP) (ewMul hP)

theorem ringClaimWeight :
    Spec (label NativeRustcVmX64.Vm.RingClaimWeight.entryLabel) RingClaimWeightPre RingClaimWeightPost :=
  Ring.Claim.ringClaimWeight_spec (placed_RingClaimWeight hP) (eqEvalFn hP) (ringWeight hP)
    (ewMul hP)

end

end NativeRustcVmX64.Assembly
