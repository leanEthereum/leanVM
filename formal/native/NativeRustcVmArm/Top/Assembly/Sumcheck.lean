module

public import NativeRustcVmArm.Code.Vm.Climb.Names
public import NativeRustcVmArm.Code.Vm.OpenPhase.Names
public import NativeRustcVmArm.Code.Vm.RowsRow.Names
public import NativeRustcVmArm.Code.Vm.SumcheckOfGkrStep.Names
public import NativeRustcVmArm.Code.Vm.SumcheckOfSumcheckPlain.Names
public import NativeRustcVmArm.Code.Vm.SumcheckOfVerifyLayer.Names
public import NativeRustcVmArm.Code.Vm.TStateQueryOpenings.Names
public import NativeRustcVmArm.Code.Vm.TStateSumcheckRoundPoly.Names
public import NativeRustcVmArm.Top.Assembly.Base
public import NativeRustcVmArm.Sumcheck.RowsRow
public import NativeRustcVmArm.Sumcheck.Climb
public import NativeRustcVmArm.Sumcheck.RoundPoly
public import NativeRustcVmArm.Sumcheck.Plain
public import NativeRustcVmArm.Sumcheck.Gkr
public import NativeRustcVmArm.Sumcheck.Layer
public import NativeRustcVmArm.Sumcheck.OpenPhase
public import NativeRustcVmArm.Sumcheck.QueryOpenings

/-!
# The sumchecks, placed in `leanvm_verify`'s program

`rows_row`, `climb`, `TState::sumcheck_round_poly` and the three sumcheck instances, instantiated
at their places in `Vm.code` with their callees' instantiated contracts.
-/

namespace NativeRustcVmArm.Assembly

open NativeRustcArm NativeRustcVmArm.Placement

public section

variable [NativeRustcArm.Host] (hP : NativeRustcArm.Host.prog = Vm.code)
include hP

theorem rowsRow : ∀ p rows, Spec (label NativeRustcVmArm.Vm.RowsRow.entryLabel) (RowsRowPre p rows) (RowsRowPost p rows) :=
  Sumcheck.RowsRow.rowsRow_spec (placed_RowsRow hP)

theorem climb : ∀ N P, Spec (label NativeRustcVmArm.Vm.Climb.entryLabel) (ClimbPre N P) (ClimbPost N P) :=
  Sumcheck.Climb.climb_spec (placed_Climb hP) (hashPair hP)

theorem roundPoly :
    ∀ a s e, Spec (label NativeRustcVmArm.Vm.TStateSumcheckRoundPoly.entryLabel) (RoundPolyPre a s e) (RoundPolyPost a s e) :=
  Sumcheck.RoundPoly.roundPoly_spec (placed_TStateSumcheckRoundPoly hP) (readScalar hP)
    (readScalars hP) (sumE hP) (bitLength hP) (grind hP) (ewMul hP)

theorem sumcheckPlain :
    ∀ a s, Spec (label NativeRustcVmArm.Vm.SumcheckOfSumcheckPlain.entryLabel) (SumcheckPlainPre a s) (SumcheckPlainPost a s) :=
  Sumcheck.Plain.sumcheckPlain_spec (placed_SumcheckOfSumcheckPlain hP) (roundPoly hP)
    (squeeze hP) (polyEval hP)

theorem sumcheckGkr : ∀ a s pt n,
    Spec (label NativeRustcVmArm.Vm.SumcheckOfGkrStep.entryLabel) (SumcheckGkrPre a s pt n) (SumcheckGkrPost a s pt n) :=
  Sumcheck.Gkr.sumcheckGkr_spec (placed_SumcheckOfGkrStep hP) (roundPoly hP) (squeeze hP)
    (polyEval hP)

theorem sumcheckLayer : ∀ a s pt,
    Spec (label NativeRustcVmArm.Vm.SumcheckOfVerifyLayer.entryLabel) (SumcheckLayerPre a s pt) (SumcheckLayerPost a s pt) :=
  Sumcheck.Layer.sumcheckLayer_spec (placed_SumcheckOfVerifyLayer hP) (roundPoly hP)
    (squeeze hP) (polyEval hP)

theorem openPhase : ∀ P R Q, Spec (label NativeRustcVmArm.Vm.OpenPhase.entryLabel) (OpenPhasePre P R Q)
    (OpenPhasePost P R Q) :=
  Sumcheck.OpenPhase.openPhase_spec (placed_OpenPhase hP) (keccak256WordsHash hP) (climb hP)

theorem queryOpenings : ∀ a s Q, Spec (label NativeRustcVmArm.Vm.TStateQueryOpenings.entryLabel) (QueryOpeningsPre a s Q)
    (QueryOpeningsPost a s Q) :=
  Sumcheck.QueryOpenings.queryOpenings_spec (placed_TStateQueryOpenings hP) (phase hP)
    (openPhase hP)

end

end NativeRustcVmArm.Assembly
