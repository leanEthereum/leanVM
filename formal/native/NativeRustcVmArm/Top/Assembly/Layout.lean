module

public import NativeRustcVmArm.Code.Vm.BuildLayout.Names
public import NativeRustcVmArm.Code.Vm.ColumnKappas.Names
public import NativeRustcVmArm.Code.Vm.CommitStack.Names
public import NativeRustcVmArm.Code.Vm.ConstraintsW.Names
public import NativeRustcVmArm.Code.Vm.Evaluate.Names
public import NativeRustcVmArm.Code.Vm.FormBufAddScaled.Names
public import NativeRustcVmArm.Code.Vm.FormBufAddTerm.Names
public import NativeRustcVmArm.Code.Vm.FormTerms.Names
public import NativeRustcVmArm.Code.Vm.InsertionSortOfStackOffsets.Names
public import NativeRustcVmArm.Code.Vm.Ladder.Names
public import NativeRustcVmArm.Code.Vm.LayoutWPlacement.Names
public import NativeRustcVmArm.Code.Vm.PlacementsOf.Names
public import NativeRustcVmArm.Code.Vm.PushClaim.Names
public import NativeRustcVmArm.Code.Vm.ReadAnnouncedSizes.Names
public import NativeRustcVmArm.Code.Vm.ReadOod.Names
public import NativeRustcVmArm.Code.Vm.StackOffsets.Names
public import NativeRustcVmArm.Code.Vm.StackPoint.Names
public import NativeRustcVmArm.Top.Assembly.Base
public import NativeRustcVmArm.Layout.FormTerms
public import NativeRustcVmArm.Layout.ConstraintsW
public import NativeRustcVmArm.Layout.LayoutWPlacement
public import NativeRustcVmArm.Layout.StackPoint
public import NativeRustcVmArm.Layout.ColumnKappas
public import NativeRustcVmArm.Layout.Evaluate
public import NativeRustcVmArm.Layout.FormBufAddTerm
public import NativeRustcVmArm.Layout.FormBufAddScaled
public import NativeRustcVmArm.Layout.Ladder
public import NativeRustcVmArm.Layout.CommitStack
public import NativeRustcVmArm.Layout.PushClaim
public import NativeRustcVmArm.Layout.InsertionSort
public import NativeRustcVmArm.Layout.BuildLayout
public import NativeRustcVmArm.Layout.ReadAnnouncedSizes
public import NativeRustcVmArm.Layout.ReadOod
public import NativeRustcVmArm.Layout.StackOffsets
public import NativeRustcVmArm.Layout.PlacementsOf

/-!
# The layout's functions, placed in `leanvm_verify`'s program

Those of `layout.rs`, the forms, the stack ladder and commitment, and `push_claim`, instantiated at
their places in `Vm.code` with their callees' instantiated contracts.
-/

namespace NativeRustcVmArm.Assembly

open NativeRustcArm NativeRustcVmArm.Placement

public section

variable [NativeRustcArm.Host] (hP : NativeRustcArm.Host.prog = Vm.code)
include hP

theorem formTerms : Spec (label NativeRustcVmArm.Vm.FormTerms.entryLabel) FormTermsPre FormTermsPost :=
  Layout.FormTerms.formTerms_spec (placed_FormTerms hP)

theorem constraintsW : Spec (label NativeRustcVmArm.Vm.ConstraintsW.entryLabel) ConstraintsWPre ConstraintsWPost :=
  Layout.ConstraintsW.constraintsW_spec (placed_ConstraintsW hP) (ewMul hP)

theorem layoutWPlacement :
    ∀ L, Spec (label NativeRustcVmArm.Vm.LayoutWPlacement.entryLabel) (LayoutWPlacementPre L) (LayoutWPlacementPost L) :=
  Layout.LayoutWPlacement.layoutWPlacement_spec (placed_LayoutWPlacement hP)

theorem stackPoint : Spec (label NativeRustcVmArm.Vm.StackPoint.entryLabel) StackPointPre StackPointPost :=
  Layout.StackPoint.stackPoint_spec (placed_StackPoint hP) (selectorPoint hP)

theorem columnKappas : Spec (label NativeRustcVmArm.Vm.ColumnKappas.entryLabel) ColumnKappasPre ColumnKappasPost :=
  Layout.ColumnKappas.columnKappas_spec (placed_ColumnKappas hP)

theorem evaluate : ∀ f, Spec (label NativeRustcVmArm.Vm.Evaluate.entryLabel) (EvaluatePre f) (EvaluatePost f) :=
  fun _ ↦ Layout.Evaluate.evaluate_spec (placed_Evaluate hP) (ewMul hP)

theorem formBufAddTerm :
    ∀ f t, Spec (label NativeRustcVmArm.Vm.FormBufAddTerm.entryLabel) (FormBufAddTermPre f t) (FormBufAddTermPost f t) :=
  fun _ _ ↦ Layout.FormBufAddTerm.formBufAddTerm_spec (placed_FormBufAddTerm hP)

theorem formBufAddScaled : ∀ f o,
    Spec (label NativeRustcVmArm.Vm.FormBufAddScaled.entryLabel) (FormBufAddScaledPre f o) (FormBufAddScaledPost f o) :=
  fun _ _ ↦ Layout.FormBufAddScaled.formBufAddScaled_spec (placed_FormBufAddScaled hP) (ewMul hP)
    (formBufAddTerm hP)

theorem ladder : Spec (label NativeRustcVmArm.Vm.Ladder.entryLabel) LadderPre LadderPost :=
  Layout.Ladder.ladder_spec (placed_Ladder hP)

theorem commitStack :
    ∀ a s, Spec (label NativeRustcVmArm.Vm.CommitStack.entryLabel) (CommitStackPre a s) (CommitStackPost a s) :=
  Layout.CommitStack.commitStack_spec (placed_CommitStack hP) (ladder hP) (readCommitment hP)

theorem pushClaim : ∀ cs, Spec (label NativeRustcVmArm.Vm.PushClaim.entryLabel) (PushClaimPre cs) (PushClaimPost cs) :=
  Layout.PushClaim.pushClaim_spec (placed_PushClaim hP) (bufEW36Extend hP)

theorem insertionSort : Spec (label NativeRustcVmArm.Vm.InsertionSortOfStackOffsets.entryLabel) InsertionSortPre InsertionSortPost :=
  Layout.InsertionSort.insertionSort_spec (placed_InsertionSortOfStackOffsets hP)

theorem stackOffsets : Spec (label NativeRustcVmArm.Vm.StackOffsets.entryLabel) StackOffsetsPre StackOffsetsPost :=
  Layout.StackOffsets.stackOffsets_spec (placed_StackOffsets hP) (memset hP) (insertionSort hP)
    (bitLength hP)

theorem placementsOf : Spec (label NativeRustcVmArm.Vm.PlacementsOf.entryLabel) PlacementsOfPre PlacementsOfPost :=
  Layout.PlacementsOf.placementsOf_spec (placed_PlacementsOf hP) (memset hP) (stackOffsets hP)

theorem buildLayout :
    ∀ bc, Spec (label NativeRustcVmArm.Vm.BuildLayout.entryLabel) (BuildLayoutPre bc) (BuildLayoutPost bc) :=
  fun _ ↦ Layout.BuildLayout.buildLayout_spec (placed_BuildLayout hP) (bitLength hP)
    (columnKappas hP) (placementsOf hP)

theorem readAnnouncedSizes :
    ∀ bc a s, Spec (label NativeRustcVmArm.Vm.ReadAnnouncedSizes.entryLabel) (ReadAnnouncedSizesPre bc a s)
      (ReadAnnouncedSizesPost bc a s) :=
  Layout.ReadAnnouncedSizes.readAnnouncedSizes_spec (placed_ReadAnnouncedSizes hP)
    (readScalars hP) (buildLayout hP)

theorem readOod : ∀ a s, Spec (label NativeRustcVmArm.Vm.ReadOod.entryLabel) (ReadOodPre a s) (ReadOodPost a s) :=
  Layout.ReadOod.readOod_spec (placed_ReadOod hP) (grind hP) (sampleChallenges hP)
    (readScalar hP)

end

end NativeRustcVmArm.Assembly
