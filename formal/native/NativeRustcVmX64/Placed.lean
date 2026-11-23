module

public import NativeRustcVmX64.Placed.Nodup
public import NativeRustcVmX64.Code.Vm.Offsets

/-!
# Every function of `leanvm_verify`'s program placed

For each of the program's 137 functions `F`, `placed_F`: `Vm.F.code` sits in `Vm.code` at the index
`Code/Vm/Offsets.lean` gives (`F.code_at`), each of its labels the only one of its name
(`labels_nodup`), so `Placed Vm.F.code k` (`placed_of_nodup`).
-/

namespace NativeRustcVmX64.Placement

open NativeRustcX64

public section

variable [Host] (hP : Host.prog = Vm.code)
include hP

theorem placed_SumcheckOfSumcheckPlain : Placed Vm.SumcheckOfSumcheckPlain.code Vm.SumcheckOfSumcheckPlain.programOffset :=
  placed_of_nodup hP labels_nodup Vm.SumcheckOfSumcheckPlain.code_at
theorem placed_SumcheckOfVerifyLayer : Placed Vm.SumcheckOfVerifyLayer.code Vm.SumcheckOfVerifyLayer.programOffset :=
  placed_of_nodup hP labels_nodup Vm.SumcheckOfVerifyLayer.code_at
theorem placed_SumcheckOfGkrStep : Placed Vm.SumcheckOfGkrStep.code Vm.SumcheckOfGkrStep.programOffset :=
  placed_of_nodup hP labels_nodup Vm.SumcheckOfGkrStep.code_at
theorem placed_EachRowOfNextLevel : Placed Vm.EachRowOfNextLevel.code Vm.EachRowOfNextLevel.programOffset :=
  placed_of_nodup hP labels_nodup Vm.EachRowOfNextLevel.code_at
theorem placed_EachRowOfFinalLevel : Placed Vm.EachRowOfFinalLevel.code Vm.EachRowOfFinalLevel.programOffset :=
  placed_of_nodup hP labels_nodup Vm.EachRowOfFinalLevel.code_at
theorem placed_EqEvalFnOfEqAbove : Placed Vm.EqEvalFnOfEqAbove.code Vm.EqEvalFnOfEqAbove.programOffset :=
  placed_of_nodup hP labels_nodup Vm.EqEvalFnOfEqAbove.code_at
theorem placed_MultilinearEvalByOfMultilinearEval :
    Placed Vm.MultilinearEvalByOfMultilinearEval.code Vm.MultilinearEvalByOfMultilinearEval.programOffset :=
  placed_of_nodup hP labels_nodup Vm.MultilinearEvalByOfMultilinearEval.code_at
theorem placed_MultilinearEvalByOfComputedBytecodeValue :
    Placed Vm.MultilinearEvalByOfComputedBytecodeValue.code Vm.MultilinearEvalByOfComputedBytecodeValue.programOffset :=
  placed_of_nodup hP labels_nodup Vm.MultilinearEvalByOfComputedBytecodeValue.code_at
theorem placed_Keccak256WordsOfHashWords : Placed Vm.Keccak256WordsOfHashWords.code Vm.Keccak256WordsOfHashWords.programOffset :=
  placed_of_nodup hP labels_nodup Vm.Keccak256WordsOfHashWords.code_at
theorem placed_Keccak256WordsOfFiatShamirIv : Placed Vm.Keccak256WordsOfFiatShamirIv.code Vm.Keccak256WordsOfFiatShamirIv.programOffset :=
  placed_of_nodup hP labels_nodup Vm.Keccak256WordsOfFiatShamirIv.code_at
theorem placed_InsertionSortOfStackOffsets : Placed Vm.InsertionSortOfStackOffsets.code Vm.InsertionSortOfStackOffsets.programOffset :=
  placed_of_nodup hP labels_nodup Vm.InsertionSortOfStackOffsets.code_at
theorem placed_VerifyBusBalanceClosure0 : Placed Vm.VerifyBusBalanceClosure0.code Vm.VerifyBusBalanceClosure0.programOffset :=
  placed_of_nodup hP labels_nodup Vm.VerifyBusBalanceClosure0.code_at
theorem placed_SpongeWAbsorbNonce : Placed Vm.SpongeWAbsorbNonce.code Vm.SpongeWAbsorbNonce.programOffset :=
  placed_of_nodup hP labels_nodup Vm.SpongeWAbsorbNonce.code_at
theorem placed_SpongeWDuplexInput : Placed Vm.SpongeWDuplexInput.code Vm.SpongeWDuplexInput.programOffset :=
  placed_of_nodup hP labels_nodup Vm.SpongeWDuplexInput.code_at
theorem placed_SpongeWAbsorb : Placed Vm.SpongeWAbsorb.code Vm.SpongeWAbsorb.programOffset :=
  placed_of_nodup hP labels_nodup Vm.SpongeWAbsorb.code_at
theorem placed_SpongeWDuplex : Placed Vm.SpongeWDuplex.code Vm.SpongeWDuplex.programOffset :=
  placed_of_nodup hP labels_nodup Vm.SpongeWDuplex.code_at
theorem placed_SpongeWSqueeze : Placed Vm.SpongeWSqueeze.code Vm.SpongeWSqueeze.programOffset :=
  placed_of_nodup hP labels_nodup Vm.SpongeWSqueeze.code_at
theorem placed_BufEW30Extend : Placed Vm.BufEW30Extend.code Vm.BufEW30Extend.programOffset :=
  placed_of_nodup hP labels_nodup Vm.BufEW30Extend.code_at
theorem placed_BufEW36Extend : Placed Vm.BufEW36Extend.code Vm.BufEW36Extend.programOffset :=
  placed_of_nodup hP labels_nodup Vm.BufEW36Extend.code_at
theorem placed_BufEW63Extend : Placed Vm.BufEW63Extend.code Vm.BufEW63Extend.programOffset :=
  placed_of_nodup hP labels_nodup Vm.BufEW63Extend.code_at
theorem placed_BufEW230Extend : Placed Vm.BufEW230Extend.code Vm.BufEW230Extend.programOffset :=
  placed_of_nodup hP labels_nodup Vm.BufEW230Extend.code_at
theorem placed_BufU64x230Extend : Placed Vm.BufU64x230Extend.code Vm.BufU64x230Extend.programOffset :=
  placed_of_nodup hP labels_nodup Vm.BufU64x230Extend.code_at
theorem placed_BasisWEval : Placed Vm.BasisWEval.code Vm.BasisWEval.programOffset :=
  placed_of_nodup hP labels_nodup Vm.BasisWEval.code_at
theorem placed_ReaderLe : Placed Vm.ReaderLe.code Vm.ReaderLe.programOffset :=
  placed_of_nodup hP labels_nodup Vm.ReaderLe.code_at
theorem placed_ReaderWords : Placed Vm.ReaderWords.code Vm.ReaderWords.programOffset :=
  placed_of_nodup hP labels_nodup Vm.ReaderWords.code_at
theorem placed_ReaderDigest : Placed Vm.ReaderDigest.code Vm.ReaderDigest.programOffset :=
  placed_of_nodup hP labels_nodup Vm.ReaderDigest.code_at
theorem placed_EWMul : Placed Vm.EWMul.code Vm.EWMul.programOffset :=
  placed_of_nodup hP labels_nodup Vm.EWMul.code_at
theorem placed_EWSqIter : Placed Vm.EWSqIter.code Vm.EWSqIter.programOffset :=
  placed_of_nodup hP labels_nodup Vm.EWSqIter.code_at
theorem placed_DecodedPhaseCount : Placed Vm.DecodedPhaseCount.code Vm.DecodedPhaseCount.programOffset :=
  placed_of_nodup hP labels_nodup Vm.DecodedPhaseCount.code_at
theorem placed_DecodedStreamElement : Placed Vm.DecodedStreamElement.code Vm.DecodedStreamElement.programOffset :=
  placed_of_nodup hP labels_nodup Vm.DecodedStreamElement.code_at
theorem placed_DecodedPhase : Placed Vm.DecodedPhase.code Vm.DecodedPhase.programOffset :=
  placed_of_nodup hP labels_nodup Vm.DecodedPhase.code_at
theorem placed_TStateNextScalar : Placed Vm.TStateNextScalar.code Vm.TStateNextScalar.programOffset :=
  placed_of_nodup hP labels_nodup Vm.TStateNextScalar.code_at
theorem placed_TStateReadScalar : Placed Vm.TStateReadScalar.code Vm.TStateReadScalar.programOffset :=
  placed_of_nodup hP labels_nodup Vm.TStateReadScalar.code_at
theorem placed_TStateReadScalars : Placed Vm.TStateReadScalars.code Vm.TStateReadScalars.programOffset :=
  placed_of_nodup hP labels_nodup Vm.TStateReadScalars.code_at
theorem placed_TStateQueryOpenings : Placed Vm.TStateQueryOpenings.code Vm.TStateQueryOpenings.programOffset :=
  placed_of_nodup hP labels_nodup Vm.TStateQueryOpenings.code_at
theorem placed_TStateReadCommitment : Placed Vm.TStateReadCommitment.code Vm.TStateReadCommitment.programOffset :=
  placed_of_nodup hP labels_nodup Vm.TStateReadCommitment.code_at
theorem placed_TStateSampleChallenges : Placed Vm.TStateSampleChallenges.code Vm.TStateSampleChallenges.programOffset :=
  placed_of_nodup hP labels_nodup Vm.TStateSampleChallenges.code_at
theorem placed_TStateSumcheckRoundPoly : Placed Vm.TStateSumcheckRoundPoly.code Vm.TStateSumcheckRoundPoly.programOffset :=
  placed_of_nodup hP labels_nodup Vm.TStateSumcheckRoundPoly.code_at
theorem placed_TStateGrind : Placed Vm.TStateGrind.code Vm.TStateGrind.programOffset :=
  placed_of_nodup hP labels_nodup Vm.TStateGrind.code_at
theorem placed_FormBufAddScaled : Placed Vm.FormBufAddScaled.code Vm.FormBufAddScaled.programOffset :=
  placed_of_nodup hP labels_nodup Vm.FormBufAddScaled.code_at
theorem placed_FormBufAddTerm : Placed Vm.FormBufAddTerm.code Vm.FormBufAddTerm.programOffset :=
  placed_of_nodup hP labels_nodup Vm.FormBufAddTerm.code_at
theorem placed_LayoutWPlacement : Placed Vm.LayoutWPlacement.code Vm.LayoutWPlacement.programOffset :=
  placed_of_nodup hP labels_nodup Vm.LayoutWPlacement.code_at
theorem placed_RowsRow : Placed Vm.RowsRow.code Vm.RowsRow.programOffset :=
  placed_of_nodup hP labels_nodup Vm.RowsRow.code_at
theorem placed_FirstClaim : Placed Vm.FirstClaim.code Vm.FirstClaim.programOffset :=
  placed_of_nodup hP labels_nodup Vm.FirstClaim.code_at
theorem placed_KeccakOpen : Placed Vm.KeccakOpen.code Vm.KeccakOpen.programOffset :=
  placed_of_nodup hP labels_nodup Vm.KeccakOpen.code_at
theorem placed_KeccakPhase : Placed Vm.KeccakPhase.code Vm.KeccakPhase.programOffset :=
  placed_of_nodup hP labels_nodup Vm.KeccakPhase.code_at
theorem placed_SlotWeights : Placed Vm.SlotWeights.code Vm.SlotWeights.programOffset :=
  placed_of_nodup hP labels_nodup Vm.SlotWeights.code_at
theorem placed_VerifyLayer : Placed Vm.VerifyLayer.code Vm.VerifyLayer.programOffset :=
  placed_of_nodup hP labels_nodup Vm.VerifyLayer.code_at
theorem placed_VerifyKeccak : Placed Vm.VerifyKeccak.code Vm.VerifyKeccak.programOffset :=
  placed_of_nodup hP labels_nodup Vm.VerifyKeccak.code_at
theorem placed_InstanceWeights : Placed Vm.InstanceWeights.code Vm.InstanceWeights.programOffset :=
  placed_of_nodup hP labels_nodup Vm.InstanceWeights.code_at
theorem placed_LinearTranspose : Placed Vm.LinearTranspose.code Vm.LinearTranspose.programOffset :=
  placed_of_nodup hP labels_nodup Vm.LinearTranspose.code_at
theorem placed_KeccakPi : Placed Vm.KeccakPi.code Vm.KeccakPi.programOffset :=
  placed_of_nodup hP labels_nodup Vm.KeccakPi.code_at
theorem placed_OpenPhase : Placed Vm.OpenPhase.code Vm.OpenPhase.programOffset :=
  placed_of_nodup hP labels_nodup Vm.OpenPhase.code_at
theorem placed_Climb : Placed Vm.Climb.code Vm.Climb.programOffset :=
  placed_of_nodup hP labels_nodup Vm.Climb.code_at
theorem placed_RingSwitch : Placed Vm.RingSwitch.code Vm.RingSwitch.programOffset :=
  placed_of_nodup hP labels_nodup Vm.RingSwitch.code_at
theorem placed_RingTarget : Placed Vm.RingTarget.code Vm.RingTarget.programOffset :=
  placed_of_nodup hP labels_nodup Vm.RingTarget.code_at
theorem placed_RingCoefficients : Placed Vm.RingCoefficients.code Vm.RingCoefficients.programOffset :=
  placed_of_nodup hP labels_nodup Vm.RingCoefficients.code_at
theorem placed_RingPsi : Placed Vm.RingPsi.code Vm.RingPsi.programOffset :=
  placed_of_nodup hP labels_nodup Vm.RingPsi.code_at
theorem placed_BlockForm : Placed Vm.BlockForm.code Vm.BlockForm.programOffset :=
  placed_of_nodup hP labels_nodup Vm.BlockForm.code_at
theorem placed_BusLayout : Placed Vm.BusLayout.code Vm.BusLayout.programOffset :=
  placed_of_nodup hP labels_nodup Vm.BusLayout.code_at
theorem placed_Fingerprints : Placed Vm.Fingerprints.code Vm.Fingerprints.programOffset :=
  placed_of_nodup hP labels_nodup Vm.Fingerprints.code_at
theorem placed_BytecodeShare : Placed Vm.BytecodeShare.code Vm.BytecodeShare.programOffset :=
  placed_of_nodup hP labels_nodup Vm.BytecodeShare.code_at
theorem placed_AccumulateSide : Placed Vm.AccumulateSide.code Vm.AccumulateSide.programOffset :=
  placed_of_nodup hP labels_nodup Vm.AccumulateSide.code_at
theorem placed_VerifyBusBalance : Placed Vm.VerifyBusBalance.code Vm.VerifyBusBalance.programOffset :=
  placed_of_nodup hP labels_nodup Vm.VerifyBusBalance.code_at
theorem placed_ComputedBytecodeValue : Placed Vm.ComputedBytecodeValue.code Vm.ComputedBytecodeValue.programOffset :=
  placed_of_nodup hP labels_nodup Vm.ComputedBytecodeValue.code_at
theorem placed_GkrLayers : Placed Vm.GkrLayers.code Vm.GkrLayers.programOffset :=
  placed_of_nodup hP labels_nodup Vm.GkrLayers.code_at
theorem placed_VerifyGkrGrandProducts : Placed Vm.VerifyGkrGrandProducts.code Vm.VerifyGkrGrandProducts.programOffset :=
  placed_of_nodup hP labels_nodup Vm.VerifyGkrGrandProducts.code_at
theorem placed_GkrStep : Placed Vm.GkrStep.code Vm.GkrStep.programOffset :=
  placed_of_nodup hP labels_nodup Vm.GkrStep.code_at
theorem placed_FoldRound : Placed Vm.FoldRound.code Vm.FoldRound.programOffset :=
  placed_of_nodup hP labels_nodup Vm.FoldRound.code_at
theorem placed_GlueLevel : Placed Vm.GlueLevel.code Vm.GlueLevel.programOffset :=
  placed_of_nodup hP labels_nodup Vm.GlueLevel.code_at
theorem placed_GluedEval : Placed Vm.GluedEval.code Vm.GluedEval.programOffset :=
  placed_of_nodup hP labels_nodup Vm.GluedEval.code_at
theorem placed_NextLevel : Placed Vm.NextLevel.code Vm.NextLevel.programOffset :=
  placed_of_nodup hP labels_nodup Vm.NextLevel.code_at
theorem placed_NovelEval : Placed Vm.NovelEval.code Vm.NovelEval.programOffset :=
  placed_of_nodup hP labels_nodup Vm.NovelEval.code_at
theorem placed_QueryBits : Placed Vm.QueryBits.code Vm.QueryBits.programOffset :=
  placed_of_nodup hP labels_nodup Vm.QueryBits.code_at
theorem placed_FinalLevel : Placed Vm.FinalLevel.code Vm.FinalLevel.programOffset :=
  placed_of_nodup hP labels_nodup Vm.FinalLevel.code_at
theorem placed_FoldRounds : Placed Vm.FoldRounds.code Vm.FoldRounds.programOffset :=
  placed_of_nodup hP labels_nodup Vm.FoldRounds.code_at
theorem placed_WhirLevels : Placed Vm.WhirLevels.code Vm.WhirLevels.programOffset :=
  placed_of_nodup hP labels_nodup Vm.WhirLevels.code_at
theorem placed_InducedWeight : Placed Vm.InducedWeight.code Vm.InducedWeight.programOffset :=
  placed_of_nodup hP labels_nodup Vm.InducedWeight.code_at
theorem placed_SampleQueries : Placed Vm.SampleQueries.code Vm.SampleQueries.programOffset :=
  placed_of_nodup hP labels_nodup Vm.SampleQueries.code_at
theorem placed_SubspaceTable : Placed Vm.SubspaceTable.code Vm.SubspaceTable.programOffset :=
  placed_of_nodup hP labels_nodup Vm.SubspaceTable.code_at
theorem placed_SubspaceAtTable : Placed Vm.SubspaceAtTable.code Vm.SubspaceAtTable.programOffset :=
  placed_of_nodup hP labels_nodup Vm.SubspaceAtTable.code_at
theorem placed_VerifyStackedOpening : Placed Vm.VerifyStackedOpening.code Vm.VerifyStackedOpening.programOffset :=
  placed_of_nodup hP labels_nodup Vm.VerifyStackedOpening.code_at
theorem placed_Ladder : Placed Vm.Ladder.code Vm.Ladder.programOffset :=
  placed_of_nodup hP labels_nodup Vm.Ladder.code_at
theorem placed_FoldRow : Placed Vm.FoldRow.code Vm.FoldRow.programOffset :=
  placed_of_nodup hP labels_nodup Vm.FoldRow.code_at
theorem placed_LanesOf : Placed Vm.LanesOf.code Vm.LanesOf.programOffset :=
  placed_of_nodup hP labels_nodup Vm.LanesOf.code_at
theorem placed_ClimbLevel : Placed Vm.ClimbLevel.code Vm.ClimbLevel.programOffset :=
  placed_of_nodup hP labels_nodup Vm.ClimbLevel.code_at
theorem placed_WriteOpenings : Placed Vm.WriteOpenings.code Vm.WriteOpenings.programOffset :=
  placed_of_nodup hP labels_nodup Vm.WriteOpenings.code_at
theorem placed_Find : Placed Vm.Find.code Vm.Find.programOffset :=
  placed_of_nodup hP labels_nodup Vm.Find.code_at
theorem placed_InsD : Placed Vm.InsD.code Vm.InsD.programOffset :=
  placed_of_nodup hP labels_nodup Vm.InsD.code_at
theorem placed_Decode : Placed Vm.Decode.code Vm.Decode.programOffset :=
  placed_of_nodup hP labels_nodup Vm.Decode.code_at
theorem placed_PhaseM : Placed Vm.PhaseM.code Vm.PhaseM.programOffset :=
  placed_of_nodup hP labels_nodup Vm.PhaseM.code_at
theorem placed_RdRows : Placed Vm.RdRows.code Vm.RdRows.programOffset :=
  placed_of_nodup hP labels_nodup Vm.RdRows.code_at
theorem placed_BitLength : Placed Vm.BitLength.code Vm.BitLength.programOffset :=
  placed_of_nodup hP labels_nodup Vm.BitLength.code_at
theorem placed_IndexMleFrom : Placed Vm.IndexMleFrom.code Vm.IndexMleFrom.programOffset :=
  placed_of_nodup hP labels_nodup Vm.IndexMleFrom.code_at
theorem placed_PaddingWeight : Placed Vm.PaddingWeight.code Vm.PaddingWeight.programOffset :=
  placed_of_nodup hP labels_nodup Vm.PaddingWeight.code_at
theorem placed_SelectorPoint : Placed Vm.SelectorPoint.code Vm.SelectorPoint.programOffset :=
  placed_of_nodup hP labels_nodup Vm.SelectorPoint.code_at
theorem placed_Dot : Placed Vm.Dot.code Vm.Dot.programOffset :=
  placed_of_nodup hP labels_nodup Vm.Dot.code_at
theorem placed_Kinv : Placed Vm.Kinv.code Vm.Kinv.programOffset :=
  placed_of_nodup hP labels_nodup Vm.Kinv.code_at
theorem placed_Kmul : Placed Vm.Kmul.code Vm.Kmul.programOffset :=
  placed_of_nodup hP labels_nodup Vm.Kmul.code_at
theorem placed_Kpow : Placed Vm.Kpow.code Vm.Kpow.programOffset :=
  placed_of_nodup hP labels_nodup Vm.Kpow.code_at
theorem placed_SumE : Placed Vm.SumE.code Vm.SumE.programOffset :=
  placed_of_nodup hP labels_nodup Vm.SumE.code_at
theorem placed_Powers : Placed Vm.Powers.code Vm.Powers.programOffset :=
  placed_of_nodup hP labels_nodup Vm.Powers.code_at
theorem placed_ProdE : Placed Vm.ProdE.code Vm.ProdE.programOffset :=
  placed_of_nodup hP labels_nodup Vm.ProdE.code_at
theorem placed_EqEval : Placed Vm.EqEval.code Vm.EqEval.programOffset :=
  placed_of_nodup hP labels_nodup Vm.EqEval.code_at
theorem placed_EqKernel : Placed Vm.EqKernel.code Vm.EqKernel.programOffset :=
  placed_of_nodup hP labels_nodup Vm.EqKernel.code_at
theorem placed_PolyEval : Placed Vm.PolyEval.code Vm.PolyEval.programOffset :=
  placed_of_nodup hP labels_nodup Vm.PolyEval.code_at
theorem placed_PushClaim : Placed Vm.PushClaim.code Vm.PushClaim.programOffset :=
  placed_of_nodup hP labels_nodup Vm.PushClaim.code_at
theorem placed_RingWeight : Placed Vm.RingWeight.code Vm.RingWeight.programOffset :=
  placed_of_nodup hP labels_nodup Vm.RingWeight.code_at
theorem placed_CommitStack : Placed Vm.CommitStack.code Vm.CommitStack.programOffset :=
  placed_of_nodup hP labels_nodup Vm.CommitStack.code_at
theorem placed_ColumnWeight : Placed Vm.ColumnWeight.code Vm.ColumnWeight.programOffset :=
  placed_of_nodup hP labels_nodup Vm.ColumnWeight.code_at
theorem placed_RingClaimWeight : Placed Vm.RingClaimWeight.code Vm.RingClaimWeight.programOffset :=
  placed_of_nodup hP labels_nodup Vm.RingClaimWeight.code_at
theorem placed_ReadOod : Placed Vm.ReadOod.code Vm.ReadOod.programOffset :=
  placed_of_nodup hP labels_nodup Vm.ReadOod.code_at
theorem placed_KeccakF : Placed Vm.KeccakF.code Vm.KeccakF.programOffset :=
  placed_of_nodup hP labels_nodup Vm.KeccakF.code_at
theorem placed_HashPair : Placed Vm.HashPair.code Vm.HashPair.programOffset :=
  placed_of_nodup hP labels_nodup Vm.HashPair.code_at
theorem placed_FormTerms : Placed Vm.FormTerms.code Vm.FormTerms.programOffset :=
  placed_of_nodup hP labels_nodup Vm.FormTerms.code_at
theorem placed_StackPoint : Placed Vm.StackPoint.code Vm.StackPoint.programOffset :=
  placed_of_nodup hP labels_nodup Vm.StackPoint.code_at
theorem placed_BuildLayout : Placed Vm.BuildLayout.code Vm.BuildLayout.programOffset :=
  placed_of_nodup hP labels_nodup Vm.BuildLayout.code_at
theorem placed_ColumnKappas : Placed Vm.ColumnKappas.code Vm.ColumnKappas.programOffset :=
  placed_of_nodup hP labels_nodup Vm.ColumnKappas.code_at
theorem placed_ConstraintsW : Placed Vm.ConstraintsW.code Vm.ConstraintsW.programOffset :=
  placed_of_nodup hP labels_nodup Vm.ConstraintsW.code_at
theorem placed_PlacementsOf : Placed Vm.PlacementsOf.code Vm.PlacementsOf.programOffset :=
  placed_of_nodup hP labels_nodup Vm.PlacementsOf.code_at
theorem placed_StackOffsets : Placed Vm.StackOffsets.code Vm.StackOffsets.programOffset :=
  placed_of_nodup hP labels_nodup Vm.StackOffsets.code_at
theorem placed_ReadAnnouncedSizes : Placed Vm.ReadAnnouncedSizes.code Vm.ReadAnnouncedSizes.programOffset :=
  placed_of_nodup hP labels_nodup Vm.ReadAnnouncedSizes.code_at
theorem placed_Evaluate : Placed Vm.Evaluate.code Vm.Evaluate.programOffset :=
  placed_of_nodup hP labels_nodup Vm.Evaluate.code_at
theorem placed_TablePhase : Placed Vm.TablePhase.code Vm.TablePhase.programOffset :=
  placed_of_nodup hP labels_nodup Vm.TablePhase.code_at
theorem placed_TableTerms : Placed Vm.TableTerms.code Vm.TableTerms.programOffset :=
  placed_of_nodup hP labels_nodup Vm.TableTerms.code_at
theorem placed_TableWeights : Placed Vm.TableWeights.code Vm.TableWeights.programOffset :=
  placed_of_nodup hP labels_nodup Vm.TableWeights.code_at
theorem placed_TableSumcheck : Placed Vm.TableSumcheck.code Vm.TableSumcheck.programOffset :=
  placed_of_nodup hP labels_nodup Vm.TableSumcheck.code_at
theorem placed_PublicInputPhase : Placed Vm.PublicInputPhase.code Vm.PublicInputPhase.programOffset :=
  placed_of_nodup hP labels_nodup Vm.PublicInputPhase.code_at
theorem placed_TableColumnClaims : Placed Vm.TableColumnClaims.code Vm.TableColumnClaims.programOffset :=
  placed_of_nodup hP labels_nodup Vm.TableColumnClaims.code_at
theorem placed_VerifyExecution : Placed Vm.VerifyExecution.code Vm.VerifyExecution.programOffset :=
  placed_of_nodup hP labels_nodup Vm.VerifyExecution.code_at
theorem placed_Seed : Placed Vm.Seed.code Vm.Seed.programOffset :=
  placed_of_nodup hP labels_nodup Vm.Seed.code_at
theorem placed_Verify : Placed Vm.Verify.code Vm.Verify.programOffset :=
  placed_of_nodup hP labels_nodup Vm.Verify.code_at
theorem placed_IvWord : Placed Vm.IvWord.code Vm.IvWord.programOffset :=
  placed_of_nodup hP labels_nodup Vm.IvWord.code_at
theorem placed_KinvSq : Placed Vm.KinvSq.code Vm.KinvSq.programOffset :=
  placed_of_nodup hP labels_nodup Vm.KinvSq.code_at
theorem placed_LeanvmVerify : Placed Vm.LeanvmVerify.code Vm.LeanvmVerify.programOffset :=
  placed_of_nodup hP labels_nodup Vm.LeanvmVerify.code_at
theorem placed_Memcpy : Placed Vm.Memcpy.code Vm.Memcpy.programOffset :=
  placed_of_nodup hP labels_nodup Vm.Memcpy.code_at
theorem placed_Memset : Placed Vm.Memset.code Vm.Memset.programOffset :=
  placed_of_nodup hP labels_nodup Vm.Memset.code_at

end

end NativeRustcVmX64.Placement
