module

public import NativeRustcVmX64.Top.Assembly.Base
public import NativeRustcVmX64.Sumcheck.RowsRow
public import NativeRustcVmX64.Sumcheck.Climb
public import NativeRustcVmX64.Sumcheck.RoundPoly
public import NativeRustcVmX64.Sumcheck.Plain
public import NativeRustcVmX64.Sumcheck.Gkr
public import NativeRustcVmX64.Sumcheck.Layer
public import NativeRustcVmX64.Sumcheck.OpenPhase
public import NativeRustcVmX64.Sumcheck.QueryOpenings
public import NativeRustcVmX64.Code.Vm.Climb.Names
public import NativeRustcVmX64.Code.Vm.OpenPhase.Names
public import NativeRustcVmX64.Code.Vm.RowsRow.Names
public import NativeRustcVmX64.Code.Vm.SumcheckOfGkrStep.Names
public import NativeRustcVmX64.Code.Vm.SumcheckOfSumcheckPlain.Names
public import NativeRustcVmX64.Code.Vm.SumcheckOfVerifyLayer.Names
public import NativeRustcVmX64.Code.Vm.TStateQueryOpenings.Names
public import NativeRustcVmX64.Code.Vm.TStateSumcheckRoundPoly.Names

/-!
# The sumcheck and openings functions, placed in `leanvm_verify`'s program

`rows_row`, `climb`, `TState::sumcheck_round_poly`, the sumcheck instances, `open_phase` and
`TState::query_openings`, instantiated at their places in `Vm.code` with their callees'
instantiated contracts.
-/

namespace NativeRustcVmX64.Assembly

open NativeRustcX64 NativeRustcVmX64.Placement

public section

variable [Host] (hP : Host.prog = Vm.code)
include hP

theorem rowsRow : ∀ p rows, Spec (label NativeRustcVmX64.Vm.RowsRow.entryLabel) (RowsRowPre p rows) (RowsRowPost p rows) :=
  Sumcheck.RowsRow.rowsRow_spec (placed_RowsRow hP)

theorem climb : ∀ N P, Spec (label NativeRustcVmX64.Vm.Climb.entryLabel) (ClimbPre N P) (ClimbPost N P) :=
  Sumcheck.Climb.climb_spec (placed_Climb hP) (hashPair hP)

theorem roundPoly :
    ∀ a s e, Spec (label NativeRustcVmX64.Vm.TStateSumcheckRoundPoly.entryLabel) (RoundPolyPre a s e) (RoundPolyPost a s e) :=
  Sumcheck.RoundPoly.roundPoly_spec (placed_TStateSumcheckRoundPoly hP) (readScalar hP)
    (readScalars hP) (sumE hP) (bitLength hP) (grind hP) (ewMul hP)

theorem sumcheckPlain :
    ∀ a s, Spec (label NativeRustcVmX64.Vm.SumcheckOfSumcheckPlain.entryLabel) (SumcheckPlainPre a s) (SumcheckPlainPost a s) :=
  Sumcheck.Plain.sumcheckPlain_spec (placed_SumcheckOfSumcheckPlain hP) (roundPoly hP)
    (squeeze hP) (polyEval hP)

theorem sumcheckGkr : ∀ a s pt n,
    Spec (label NativeRustcVmX64.Vm.SumcheckOfGkrStep.entryLabel) (SumcheckGkrPre a s pt n) (SumcheckGkrPost a s pt n) :=
  Sumcheck.Gkr.sumcheckGkr_spec (placed_SumcheckOfGkrStep hP) (roundPoly hP) (squeeze hP)
    (polyEval hP)

theorem sumcheckLayer : ∀ a s pt,
    Spec (label NativeRustcVmX64.Vm.SumcheckOfVerifyLayer.entryLabel) (SumcheckLayerPre a s pt) (SumcheckLayerPost a s pt) :=
  Sumcheck.Layer.sumcheckLayer_spec (placed_SumcheckOfVerifyLayer hP) (roundPoly hP)
    (squeeze hP) (polyEval hP)

theorem openPhase : ∀ P R Q, Spec (label NativeRustcVmX64.Vm.OpenPhase.entryLabel) (OpenPhasePre P R Q)
    (OpenPhasePost P R Q) :=
  Sumcheck.OpenPhase.openPhase_spec (placed_OpenPhase hP) (keccak256WordsHash hP) (climb hP)

theorem queryOpenings : ∀ a s Q, Spec (label NativeRustcVmX64.Vm.TStateQueryOpenings.entryLabel) (QueryOpeningsPre a s Q)
    (QueryOpeningsPost a s Q) :=
  Sumcheck.QueryOpenings.queryOpenings_spec (placed_TStateQueryOpenings hP) (phase hP)
    (openPhase hP)

end

end NativeRustcVmX64.Assembly
