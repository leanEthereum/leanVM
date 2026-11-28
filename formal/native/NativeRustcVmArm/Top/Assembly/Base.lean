module

public import NativeRustcVmArm.Code.Vm.BitLength.Names
public import NativeRustcVmArm.Code.Vm.BufEW230Extend.Names
public import NativeRustcVmArm.Code.Vm.BufEW30Extend.Names
public import NativeRustcVmArm.Code.Vm.BufEW36Extend.Names
public import NativeRustcVmArm.Code.Vm.BufEW63Extend.Names
public import NativeRustcVmArm.Code.Vm.BufU64x230Extend.Names
public import NativeRustcVmArm.Code.Vm.DecodedPhase.Names
public import NativeRustcVmArm.Code.Vm.DecodedPhaseCount.Names
public import NativeRustcVmArm.Code.Vm.DecodedStreamElement.Names
public import NativeRustcVmArm.Code.Vm.Dot.Names
public import NativeRustcVmArm.Code.Vm.EWMul.Names
public import NativeRustcVmArm.Code.Vm.EWSqIter.Names
public import NativeRustcVmArm.Code.Vm.EqEval.Names
public import NativeRustcVmArm.Code.Vm.EqEvalFnOfEqAbove.Names
public import NativeRustcVmArm.Code.Vm.EqKernel.Names
public import NativeRustcVmArm.Code.Vm.HashPair.Names
public import NativeRustcVmArm.Code.Vm.IndexMleFrom.Names
public import NativeRustcVmArm.Code.Vm.IvWord.Names
public import NativeRustcVmArm.Code.Vm.Keccak256WordsOfFiatShamirIv.Names
public import NativeRustcVmArm.Code.Vm.Keccak256WordsOfHashWords.Names
public import NativeRustcVmArm.Code.Vm.KeccakF.Names
public import NativeRustcVmArm.Code.Vm.Kinv.Names
public import NativeRustcVmArm.Code.Vm.KinvSq.Names
public import NativeRustcVmArm.Code.Vm.Kmul.Names
public import NativeRustcVmArm.Code.Vm.Kpow.Names
public import NativeRustcVmArm.Code.Vm.Memcpy.Names
public import NativeRustcVmArm.Code.Vm.Memset.Names
public import NativeRustcVmArm.Code.Vm.MultilinearEvalByOfComputedBytecodeValue.Names
public import NativeRustcVmArm.Code.Vm.MultilinearEvalByOfMultilinearEval.Names
public import NativeRustcVmArm.Code.Vm.PaddingWeight.Names
public import NativeRustcVmArm.Code.Vm.PolyEval.Names
public import NativeRustcVmArm.Code.Vm.Powers.Names
public import NativeRustcVmArm.Code.Vm.ProdE.Names
public import NativeRustcVmArm.Code.Vm.SelectorPoint.Names
public import NativeRustcVmArm.Code.Vm.SpongeWAbsorb.Names
public import NativeRustcVmArm.Code.Vm.SpongeWAbsorbNonce.Names
public import NativeRustcVmArm.Code.Vm.SpongeWDuplex.Names
public import NativeRustcVmArm.Code.Vm.SpongeWDuplexInput.Names
public import NativeRustcVmArm.Code.Vm.SpongeWSqueeze.Names
public import NativeRustcVmArm.Code.Vm.SumE.Names
public import NativeRustcVmArm.Code.Vm.TStateGrind.Names
public import NativeRustcVmArm.Code.Vm.TStateNextScalar.Names
public import NativeRustcVmArm.Code.Vm.TStateReadCommitment.Names
public import NativeRustcVmArm.Code.Vm.TStateReadScalar.Names
public import NativeRustcVmArm.Code.Vm.TStateReadScalars.Names
public import NativeRustcVmArm.Code.Vm.TStateSampleChallenges.Names
public import NativeRustcVmArm.Mem
public import NativeRustcVmArm.Placed
public import NativeRustcVmArm.Field
public import NativeRustcVmArm.Arrays
public import NativeRustcVmArm.Arrays.EqKernel
public import NativeRustcVmArm.Arrays.MultilinearEvalByOfMultilinearEval
public import NativeRustcVmArm.Arrays.MultilinearEvalByOfComputedBytecodeValue
public import NativeRustcVmArm.Keccak
public import NativeRustcVmArm.Transcript

/-!
# The call tree's leaves, placed in `leanvm_verify`'s program

Each proved contract of `field.rs`, the arrays, `keccak.rs`, `transcript.rs`/`input.rs`, `memcpy`
and `memset`, instantiated at its function's place in `Vm.code` (`Placement.placed_<Fn> hP`) and
with its callees' instantiated contracts, in the form its callers take it.
-/

namespace NativeRustcVmArm.Assembly

open NativeRustcArm NativeRustcVmArm.Placement

public section

variable [NativeRustcArm.Host] (hP : NativeRustcArm.Host.prog = Vm.code)
include hP

theorem memcpy : Spec (label NativeRustcVmArm.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost :=
  Mem.memcpy_spec (placed_Memcpy hP)

theorem memset : Spec (label NativeRustcVmArm.Vm.Memset.entryLabel) MemsetPre MemsetPost :=
  Mem.memset_spec (placed_Memset hP)

/-! ## `field.rs` -/

theorem kmul : Spec (label NativeRustcVmArm.Vm.Kmul.entryLabel) KmulPre KmulPost :=
  Field.Kmul.kmul_spec (placed_Kmul hP)

theorem ewMul : Spec (label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost :=
  Field.EWMul.ewMul_spec (placed_EWMul hP)

theorem kinvSq : Spec (label NativeRustcVmArm.Vm.KinvSq.entryLabel) KinvSqPre KinvSqPost :=
  Field.KinvSq.kinvSq_spec (placed_KinvSq hP) (kmul hP)

theorem kinv : Spec (label NativeRustcVmArm.Vm.Kinv.entryLabel) KinvPre KinvPost :=
  Field.Kinv.kinv_spec (placed_Kinv hP) (kmul hP) (kinvSq hP)

theorem kpow : Spec (label NativeRustcVmArm.Vm.Kpow.entryLabel) KpowPre KpowPost :=
  Field.Kpow.kpow_spec (placed_Kpow hP) (kmul hP)

theorem ewSqIter : Spec (label NativeRustcVmArm.Vm.EWSqIter.entryLabel) EWSqIterPre EWSqIterPost :=
  Field.EWSqIter.ewSqIter_spec (placed_EWSqIter hP) (ewMul hP)

theorem bitLength : Spec (label NativeRustcVmArm.Vm.BitLength.entryLabel) BitLengthPre BitLengthPost :=
  Field.BitLength.bitLength_spec (placed_BitLength hP)

/-! ## Arrays -/

theorem dot : Spec (label NativeRustcVmArm.Vm.Dot.entryLabel) DotPre DotPost :=
  Arrays.Dot.dot_spec (placed_Dot hP) (ewMul hP)

theorem eqEval : Spec (label NativeRustcVmArm.Vm.EqEval.entryLabel) EqEvalPre EqEvalPost :=
  Arrays.EqEval.eqEval_spec (placed_EqEval hP) (ewMul hP)

theorem eqEvalFn :
    Spec (label NativeRustcVmArm.Vm.EqEvalFnOfEqAbove.entryLabel) EqEvalFnOfEqAbovePre EqEvalFnOfEqAbovePost :=
  Arrays.EqEvalFn.eqEvalFn_spec (placed_EqEvalFnOfEqAbove hP) (ewMul hP)

theorem polyEval : Spec (label NativeRustcVmArm.Vm.PolyEval.entryLabel) PolyEvalPre PolyEvalPost :=
  Arrays.PolyEval.polyEval_spec (placed_PolyEval hP) (ewMul hP)

theorem indexMleFrom : Spec (label NativeRustcVmArm.Vm.IndexMleFrom.entryLabel) IndexMleFromPre IndexMleFromPost :=
  Arrays.IndexMleFrom.indexMleFrom_spec (placed_IndexMleFrom hP) (ewMul hP)

theorem paddingWeight : Spec (label NativeRustcVmArm.Vm.PaddingWeight.entryLabel) PaddingWeightPre PaddingWeightPost :=
  Arrays.PaddingWeight.paddingWeight_spec (placed_PaddingWeight hP) (ewMul hP)

theorem powers : Spec (label NativeRustcVmArm.Vm.Powers.entryLabel) PowersPre PowersPost :=
  Arrays.Powers.powers_spec (placed_Powers hP) (ewMul hP)

theorem prodE : Spec (label NativeRustcVmArm.Vm.ProdE.entryLabel) ProdEPre ProdEPost :=
  Arrays.ProdE.prodE_spec (placed_ProdE hP) (ewMul hP)

theorem sumE : Spec (label NativeRustcVmArm.Vm.SumE.entryLabel) SumEPre SumEPost :=
  Arrays.SumE.sumE_spec (placed_SumE hP)

theorem selectorPoint : Spec (label NativeRustcVmArm.Vm.SelectorPoint.entryLabel) SelectorPointPre SelectorPointPost :=
  Arrays.SelectorPoint.selectorPoint_spec (placed_SelectorPoint hP)

theorem bufEW30Extend :
    Spec (label NativeRustcVmArm.Vm.BufEW30Extend.entryLabel) (BufEWExtendPre 30) (BufEWExtendPost 30) :=
  Arrays.BufEW30Extend.bufEW30Extend_spec (placed_BufEW30Extend hP)

theorem bufEW36Extend :
    Spec (label NativeRustcVmArm.Vm.BufEW36Extend.entryLabel) (BufEWExtendPre 36) (BufEWExtendPost 36) :=
  Arrays.BufEW36Extend.bufEW36Extend_spec (placed_BufEW36Extend hP)

theorem bufEW63Extend :
    Spec (label NativeRustcVmArm.Vm.BufEW63Extend.entryLabel) (BufEWExtendPre 63) (BufEWExtendPost 63) :=
  Arrays.BufEW63Extend.bufEW63Extend_spec (placed_BufEW63Extend hP)

theorem bufEW230Extend :
    Spec (label NativeRustcVmArm.Vm.BufEW230Extend.entryLabel) (BufEWExtendPre 230) (BufEWExtendPost 230) :=
  Arrays.BufEW230Extend.bufEW230Extend_spec (placed_BufEW230Extend hP)

theorem bufU64x230Extend :
    Spec (label NativeRustcVmArm.Vm.BufU64x230Extend.entryLabel) (BufU64ExtendPre 230) (BufU64ExtendPost 230) :=
  Arrays.BufU64x230Extend.bufU64x230Extend_spec (placed_BufU64x230Extend hP)

theorem eqKernel : Spec (label NativeRustcVmArm.Vm.EqKernel.entryLabel) EqKernelPre EqKernelPost :=
  Arrays.EqKernel.eqKernel_spec (placed_EqKernel hP) (ewMul hP)

theorem mleOfMultilinearEval :
    Spec (label NativeRustcVmArm.Vm.MultilinearEvalByOfMultilinearEval.entryLabel) MleOfMultilinearEvalPre MleOfMultilinearEvalPost :=
  Arrays.MleOfMultilinearEval.mleOfMultilinearEval_spec
    (placed_MultilinearEvalByOfMultilinearEval hP) (ewMul hP)

theorem mleOfComputedBytecodeValue : Spec (label NativeRustcVmArm.Vm.MultilinearEvalByOfComputedBytecodeValue.entryLabel)
    MleOfComputedBytecodeValuePre MleOfComputedBytecodeValuePost :=
  Arrays.MleOfComputedBytecodeValue.mleOfComputedBytecodeValue_spec
    (placed_MultilinearEvalByOfComputedBytecodeValue hP) (ewMul hP)

/-! ## `keccak.rs` -/

theorem keccakF : Spec (label NativeRustcVmArm.Vm.KeccakF.entryLabel) KeccakFPre KeccakFPost :=
  keccakF_spec (placed_KeccakF hP) (memcpy hP)

theorem keccak256WordsHash :
    Spec (label NativeRustcVmArm.Vm.Keccak256WordsOfHashWords.entryLabel) Keccak256WordsHashPre Keccak256WordsHashPost :=
  keccak256WordsHash_spec (placed_Keccak256WordsOfHashWords hP) (memset hP) (keccakF hP)

theorem ivWord : Spec (label NativeRustcVmArm.Vm.IvWord.entryLabel) IvWordPre IvWordPost :=
  ivWord_spec (placed_IvWord hP)

theorem keccak256WordsIv :
    Spec (label NativeRustcVmArm.Vm.Keccak256WordsOfFiatShamirIv.entryLabel) Keccak256WordsIvPre Keccak256WordsIvPost :=
  keccak256WordsIv_spec (placed_Keccak256WordsOfFiatShamirIv hP) (memset hP) (ivWord hP)
    (keccakF hP)

theorem hashPair : Spec (label NativeRustcVmArm.Vm.HashPair.entryLabel) HashPairPre HashPairPost :=
  hashPair_spec (placed_HashPair hP) (keccak256WordsHash hP)

/-! ## `transcript.rs`, `input.rs` -/

theorem duplexInput :
    ∀ sp, Spec (label NativeRustcVmArm.Vm.SpongeWDuplexInput.entryLabel) (DuplexInputPre sp) (DuplexInputPost sp) :=
  Transcript.DuplexInput.duplexInput_spec (placed_SpongeWDuplexInput hP)

theorem duplex : ∀ sp, Spec (label NativeRustcVmArm.Vm.SpongeWDuplex.entryLabel) (DuplexPre sp) (DuplexPost sp) :=
  Transcript.Duplex.duplex_spec (placed_SpongeWDuplex hP) (duplexInput hP) (keccakF hP)

theorem absorb : ∀ sp, Spec (label NativeRustcVmArm.Vm.SpongeWAbsorb.entryLabel) (AbsorbPre sp) (AbsorbPost sp) :=
  Transcript.Absorb.absorb_spec (placed_SpongeWAbsorb hP) (duplex hP)

theorem squeeze : ∀ sp, Spec (label NativeRustcVmArm.Vm.SpongeWSqueeze.entryLabel) (SqueezePre sp) (SqueezePost sp) :=
  Transcript.Squeeze.squeeze_spec (placed_SpongeWSqueeze hP) (duplex hP)

theorem absorbNonce :
    ∀ sp, Spec (label NativeRustcVmArm.Vm.SpongeWAbsorbNonce.entryLabel) (AbsorbNoncePre sp) (AbsorbNoncePost sp) :=
  Transcript.AbsorbNonce.absorbNonce_spec (placed_SpongeWAbsorbNonce hP) (absorb hP) (duplex hP)

theorem streamElement : ∀ a stream openings, Spec (label NativeRustcVmArm.Vm.DecodedStreamElement.entryLabel)
    (StreamElementPre a stream openings) (StreamElementPost stream) :=
  Transcript.StreamElement.streamElement_spec (placed_DecodedStreamElement hP)

theorem phaseCount : ∀ a stream openings, Spec (label NativeRustcVmArm.Vm.DecodedPhaseCount.entryLabel)
    (PhaseCountPre a stream openings) (PhaseCountPost openings) :=
  Transcript.PhaseCount.phaseCount_spec (placed_DecodedPhaseCount hP)

theorem phase : ∀ a stream openings, Spec (label NativeRustcVmArm.Vm.DecodedPhase.entryLabel) (PhasePre a stream openings)
    (PhasePost a openings) :=
  Transcript.Phase.phase_spec (placed_DecodedPhase hP) (phaseCount hP)

theorem nextScalar :
    ∀ a s, Spec (label NativeRustcVmArm.Vm.TStateNextScalar.entryLabel) (NextScalarPre a s) (NextScalarPost a s) :=
  Transcript.NextScalar.nextScalar_spec (placed_TStateNextScalar hP) (streamElement hP)

theorem readScalar :
    ∀ a s, Spec (label NativeRustcVmArm.Vm.TStateReadScalar.entryLabel) (ReadScalarPre a s) (ReadScalarPost a s) :=
  Transcript.ReadScalar.readScalar_spec (placed_TStateReadScalar hP) (nextScalar hP) (absorb hP)

theorem readScalars :
    ∀ a s, Spec (label NativeRustcVmArm.Vm.TStateReadScalars.entryLabel) (ReadScalarsPre a s) (ReadScalarsPost a s) :=
  Transcript.ReadScalars.readScalars_spec (placed_TStateReadScalars hP) (readScalar hP)

theorem sampleChallenges : ∀ a s, Spec (label NativeRustcVmArm.Vm.TStateSampleChallenges.entryLabel)
    (SampleChallengesPre a s) (SampleChallengesPost a s) :=
  Transcript.SampleChallenges.sampleChallenges_spec (placed_TStateSampleChallenges hP)
    (squeeze hP)

theorem grind : ∀ a s, Spec (label NativeRustcVmArm.Vm.TStateGrind.entryLabel) (GrindPre a s) (GrindPost a s) :=
  Transcript.Grind.grind_spec (placed_TStateGrind hP) (nextScalar hP) (absorbNonce hP)

theorem readCommitment : ∀ a s, Spec (label NativeRustcVmArm.Vm.TStateReadCommitment.entryLabel) (ReadCommitmentPre a s)
    (ReadCommitmentPost a s) :=
  Transcript.ReadCommitment.readCommitment_spec (placed_TStateReadCommitment hP) (readScalar hP)

end

end NativeRustcVmArm.Assembly
