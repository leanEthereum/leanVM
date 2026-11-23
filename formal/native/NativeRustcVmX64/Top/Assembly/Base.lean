module

public import NativeRustcVmX64.Mem
public import NativeRustcVmX64.Placed
public import NativeRustcVmX64.Field.Kmul
public import NativeRustcVmX64.Field.EWMul
public import NativeRustcVmX64.Field.KinvSq
public import NativeRustcVmX64.Field.Kinv
public import NativeRustcVmX64.Field.Kpow
public import NativeRustcVmX64.Field.EWSqIter
public import NativeRustcVmX64.Field.BitLength
public import NativeRustcVmX64.Arrays.Dot
public import NativeRustcVmX64.Arrays.EqEval
public import NativeRustcVmX64.Arrays.Powers
public import NativeRustcVmX64.Arrays.PolyEval
public import NativeRustcVmX64.Arrays.IndexMleFrom
public import NativeRustcVmX64.Arrays.EqEvalFn
public import NativeRustcVmX64.Arrays.SumE
public import NativeRustcVmX64.Arrays.ProdE
public import NativeRustcVmX64.Arrays.BufEW30Extend
public import NativeRustcVmX64.Arrays.BufEW36Extend
public import NativeRustcVmX64.Arrays.BufEW63Extend
public import NativeRustcVmX64.Arrays.BufEW230Extend
public import NativeRustcVmX64.Arrays.BufU64x230Extend
public import NativeRustcVmX64.Arrays.MultilinearEvalBy
public import NativeRustcVmX64.Arrays.EqKernel
public import NativeRustcVmX64.Arrays.SelectorPoint
public import NativeRustcVmX64.Arrays.PaddingWeight
public import NativeRustcVmX64.Keccak.KeccakF
public import NativeRustcVmX64.Keccak.IvWord
public import NativeRustcVmX64.Keccak.HashPair
public import NativeRustcVmX64.Keccak.WordsHash
public import NativeRustcVmX64.Keccak.WordsIv
public import NativeRustcVmX64.Transcript.DuplexInput
public import NativeRustcVmX64.Transcript.Duplex
public import NativeRustcVmX64.Transcript.Absorb
public import NativeRustcVmX64.Transcript.Squeeze
public import NativeRustcVmX64.Transcript.AbsorbNonce
public import NativeRustcVmX64.Transcript.StreamElement
public import NativeRustcVmX64.Transcript.PhaseCount
public import NativeRustcVmX64.Transcript.Phase
public import NativeRustcVmX64.Transcript.NextScalar
public import NativeRustcVmX64.Transcript.ReadScalar
public import NativeRustcVmX64.Transcript.ReadScalars
public import NativeRustcVmX64.Transcript.SampleChallenges
public import NativeRustcVmX64.Transcript.Grind
public import NativeRustcVmX64.Transcript.ReadCommitment
public import NativeRustcVmX64.Code.Vm.BitLength.Names
public import NativeRustcVmX64.Code.Vm.BufEW230Extend.Names
public import NativeRustcVmX64.Code.Vm.BufEW30Extend.Names
public import NativeRustcVmX64.Code.Vm.BufEW36Extend.Names
public import NativeRustcVmX64.Code.Vm.BufEW63Extend.Names
public import NativeRustcVmX64.Code.Vm.BufU64x230Extend.Names
public import NativeRustcVmX64.Code.Vm.DecodedPhase.Names
public import NativeRustcVmX64.Code.Vm.DecodedPhaseCount.Names
public import NativeRustcVmX64.Code.Vm.DecodedStreamElement.Names
public import NativeRustcVmX64.Code.Vm.Dot.Names
public import NativeRustcVmX64.Code.Vm.EWMul.Names
public import NativeRustcVmX64.Code.Vm.EWSqIter.Names
public import NativeRustcVmX64.Code.Vm.EqEval.Names
public import NativeRustcVmX64.Code.Vm.EqEvalFnOfEqAbove.Names
public import NativeRustcVmX64.Code.Vm.EqKernel.Names
public import NativeRustcVmX64.Code.Vm.HashPair.Names
public import NativeRustcVmX64.Code.Vm.IndexMleFrom.Names
public import NativeRustcVmX64.Code.Vm.IvWord.Names
public import NativeRustcVmX64.Code.Vm.Keccak256WordsOfFiatShamirIv.Names
public import NativeRustcVmX64.Code.Vm.Keccak256WordsOfHashWords.Names
public import NativeRustcVmX64.Code.Vm.KeccakF.Names
public import NativeRustcVmX64.Code.Vm.Kinv.Names
public import NativeRustcVmX64.Code.Vm.KinvSq.Names
public import NativeRustcVmX64.Code.Vm.Kmul.Names
public import NativeRustcVmX64.Code.Vm.Kpow.Names
public import NativeRustcVmX64.Code.Vm.Memcpy.Names
public import NativeRustcVmX64.Code.Vm.Memset.Names
public import NativeRustcVmX64.Code.Vm.MultilinearEvalByOfComputedBytecodeValue.Names
public import NativeRustcVmX64.Code.Vm.MultilinearEvalByOfMultilinearEval.Names
public import NativeRustcVmX64.Code.Vm.PaddingWeight.Names
public import NativeRustcVmX64.Code.Vm.PolyEval.Names
public import NativeRustcVmX64.Code.Vm.Powers.Names
public import NativeRustcVmX64.Code.Vm.ProdE.Names
public import NativeRustcVmX64.Code.Vm.SelectorPoint.Names
public import NativeRustcVmX64.Code.Vm.SpongeWAbsorb.Names
public import NativeRustcVmX64.Code.Vm.SpongeWAbsorbNonce.Names
public import NativeRustcVmX64.Code.Vm.SpongeWDuplex.Names
public import NativeRustcVmX64.Code.Vm.SpongeWDuplexInput.Names
public import NativeRustcVmX64.Code.Vm.SpongeWSqueeze.Names
public import NativeRustcVmX64.Code.Vm.SumE.Names
public import NativeRustcVmX64.Code.Vm.TStateGrind.Names
public import NativeRustcVmX64.Code.Vm.TStateNextScalar.Names
public import NativeRustcVmX64.Code.Vm.TStateReadCommitment.Names
public import NativeRustcVmX64.Code.Vm.TStateReadScalar.Names
public import NativeRustcVmX64.Code.Vm.TStateReadScalars.Names
public import NativeRustcVmX64.Code.Vm.TStateSampleChallenges.Names

/-!
# The call tree's leaves, placed in `leanvm_verify`'s program

Each proved contract of `field.rs`, the arrays, `keccak.rs`, `transcript.rs`/`input.rs`, `memcpy`
and `memset`, instantiated at its function's place in `Vm.code` (`Placement.placed_<Fn> hP`) and
with its callees' instantiated contracts, in the form its callers take it.
-/

namespace NativeRustcVmX64.Assembly

open NativeRustcX64 NativeRustcVmX64.Placement NativeRustcVm.Transcript NativeVm.Model

public section

variable [Host] (hP : Host.prog = Vm.code)
include hP

theorem memcpy : Spec (label NativeRustcVmX64.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost :=
  Mem.memcpy_spec (placed_Memcpy hP)

theorem memset : Spec (label NativeRustcVmX64.Vm.Memset.entryLabel) MemsetPre MemsetPost :=
  Mem.memset_spec (placed_Memset hP)

/-! ## `field.rs` -/

theorem kmul : Spec (label NativeRustcVmX64.Vm.Kmul.entryLabel) KmulPre KmulPost :=
  Field.Kmul.kmul_spec (placed_Kmul hP)

theorem ewMul : Spec (label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost :=
  Field.EWMul.ewMul_spec (placed_EWMul hP)

theorem kinvSq : Spec (label NativeRustcVmX64.Vm.KinvSq.entryLabel) KinvSqPre KinvSqPost :=
  Field.KinvSq.kinvSq_spec (placed_KinvSq hP) (kmul hP)

theorem kinv : Spec (label NativeRustcVmX64.Vm.Kinv.entryLabel) KinvPre KinvPost :=
  Field.Kinv.kinv_spec (placed_Kinv hP) (kmul hP) (kinvSq hP)

theorem kpow : Spec (label NativeRustcVmX64.Vm.Kpow.entryLabel) KpowPre KpowPost :=
  Field.Kpow.kpow_spec (placed_Kpow hP) (kmul hP)

theorem ewSqIter : Spec (label NativeRustcVmX64.Vm.EWSqIter.entryLabel) EWSqIterPre EWSqIterPost :=
  Field.EWSqIter.ewSqIter_spec (placed_EWSqIter hP) (ewMul hP)

theorem bitLength : Spec (label NativeRustcVmX64.Vm.BitLength.entryLabel) BitLengthPre BitLengthPost :=
  Field.BitLength.bitLength_spec (placed_BitLength hP)

/-! ## Arrays -/

theorem dot : Spec (label NativeRustcVmX64.Vm.Dot.entryLabel) DotPre DotPost :=
  Arrays.Dot.dot_spec (placed_Dot hP) (ewMul hP)

theorem eqEval : Spec (label NativeRustcVmX64.Vm.EqEval.entryLabel) EqEvalPre EqEvalPost :=
  Arrays.EqEval.eqEval_spec (placed_EqEval hP) (ewMul hP)

theorem polyEval : Spec (label NativeRustcVmX64.Vm.PolyEval.entryLabel) PolyEvalPre PolyEvalPost :=
  Arrays.PolyEval.polyEval_spec (placed_PolyEval hP) (ewMul hP)

theorem indexMleFrom : Spec (label NativeRustcVmX64.Vm.IndexMleFrom.entryLabel) IndexMleFromPre IndexMleFromPost :=
  Arrays.IndexMleFrom.indexMleFrom_spec (placed_IndexMleFrom hP) (ewMul hP)

theorem paddingWeight : Spec (label NativeRustcVmX64.Vm.PaddingWeight.entryLabel) PaddingWeightPre PaddingWeightPost :=
  Arrays.PaddingWeight.paddingWeight_spec (placed_PaddingWeight hP) (ewMul hP)

theorem powers : Spec (label NativeRustcVmX64.Vm.Powers.entryLabel) PowersPre PowersPost :=
  Arrays.Powers.powers_spec (placed_Powers hP) (ewMul hP)

theorem eqEvalFn :
    Spec (label NativeRustcVmX64.Vm.EqEvalFnOfEqAbove.entryLabel) EqEvalFnOfEqAbovePre EqEvalFnOfEqAbovePost :=
  Arrays.EqEvalFn.eqEvalFn_spec (placed_EqEvalFnOfEqAbove hP) (ewMul hP)

theorem prodE : Spec (label NativeRustcVmX64.Vm.ProdE.entryLabel) ProdEPre ProdEPost :=
  Arrays.ProdE.prodE_spec (placed_ProdE hP) (ewMul hP)

theorem sumE : Spec (label NativeRustcVmX64.Vm.SumE.entryLabel) SumEPre SumEPost :=
  Arrays.SumE.sumE_spec (placed_SumE hP)

theorem bufEW30Extend :
    Spec (label NativeRustcVmX64.Vm.BufEW30Extend.entryLabel) (BufEWExtendPre 30) (BufEWExtendPost 30) :=
  Arrays.BufEW30Extend.bufEW30Extend_spec (placed_BufEW30Extend hP)

theorem bufEW36Extend :
    Spec (label NativeRustcVmX64.Vm.BufEW36Extend.entryLabel) (BufEWExtendPre 36) (BufEWExtendPost 36) :=
  Arrays.BufEW36Extend.bufEW36Extend_spec (placed_BufEW36Extend hP)

theorem bufEW63Extend :
    Spec (label NativeRustcVmX64.Vm.BufEW63Extend.entryLabel) (BufEWExtendPre 63) (BufEWExtendPost 63) :=
  Arrays.BufEW63Extend.bufEW63Extend_spec (placed_BufEW63Extend hP)

theorem bufEW230Extend :
    Spec (label NativeRustcVmX64.Vm.BufEW230Extend.entryLabel) (BufEWExtendPre 230) (BufEWExtendPost 230) :=
  Arrays.BufEW230Extend.bufEW230Extend_spec (placed_BufEW230Extend hP)

theorem bufU64x230Extend :
    Spec (label NativeRustcVmX64.Vm.BufU64x230Extend.entryLabel) (BufU64ExtendPre 230) (BufU64ExtendPost 230) :=
  Arrays.BufU64x230Extend.bufU64x230Extend_spec (placed_BufU64x230Extend hP)

theorem eqKernel : Spec (label NativeRustcVmX64.Vm.EqKernel.entryLabel) EqKernelPre EqKernelPost :=
  Arrays.EqKernel.eqKernel_spec (placed_EqKernel hP) (ewMul hP)

theorem selectorPoint : Spec (label NativeRustcVmX64.Vm.SelectorPoint.entryLabel) SelectorPointPre SelectorPointPost :=
  Arrays.SelectorPoint.selectorPoint_spec (placed_SelectorPoint hP)

theorem mleOfMultilinearEval :
    Spec (label NativeRustcVmX64.Vm.MultilinearEvalByOfMultilinearEval.entryLabel) MleOfMultilinearEvalPre MleOfMultilinearEvalPost :=
  Arrays.MleOfMultilinearEval.mleOfMultilinearEval_spec
    (placed_MultilinearEvalByOfMultilinearEval hP) (ewMul hP)

theorem mleOfComputedBytecodeValue : Spec (label NativeRustcVmX64.Vm.MultilinearEvalByOfComputedBytecodeValue.entryLabel)
    MleOfComputedBytecodeValuePre MleOfComputedBytecodeValuePost :=
  Arrays.MleOfComputedBytecodeValue.mleOfComputedBytecodeValue_spec
    (placed_MultilinearEvalByOfComputedBytecodeValue hP) (ewMul hP)

/-! ## `keccak.rs` -/

theorem keccakF : Spec (label NativeRustcVmX64.Vm.KeccakF.entryLabel) KeccakFPre KeccakFPost :=
  keccakF_spec (placed_KeccakF hP) (memcpy hP)

theorem keccak256WordsHash :
    Spec (label NativeRustcVmX64.Vm.Keccak256WordsOfHashWords.entryLabel) Keccak256WordsHashPre Keccak256WordsHashPost :=
  keccak256WordsHash_spec (placed_Keccak256WordsOfHashWords hP) (memset hP) (keccakF hP)

theorem ivWord : Spec (label NativeRustcVmX64.Vm.IvWord.entryLabel) IvWordPre IvWordPost :=
  IvWordRun.ivWord_spec (placed_IvWord hP)

theorem hashPair : Spec (label NativeRustcVmX64.Vm.HashPair.entryLabel) HashPairPre HashPairPost :=
  HashPairRun.hashPair_spec (placed_HashPair hP) (keccak256WordsHash hP)

theorem keccak256WordsIv :
    Spec (label NativeRustcVmX64.Vm.Keccak256WordsOfFiatShamirIv.entryLabel) Keccak256WordsIvPre Keccak256WordsIvPost :=
  keccak256WordsIv_spec (placed_Keccak256WordsOfFiatShamirIv hP) (memset hP) (ivWord hP)
    (keccakF hP)

/-! ## `transcript.rs`, `input.rs` -/

theorem duplexInput :
    ∀ sp, Spec (label NativeRustcVmX64.Vm.SpongeWDuplexInput.entryLabel) (DuplexInputPre sp) (DuplexInputPost sp) :=
  Transcript.DuplexInput.duplexInput_spec (placed_SpongeWDuplexInput hP)

theorem duplex : ∀ sp, Spec (label NativeRustcVmX64.Vm.SpongeWDuplex.entryLabel) (DuplexPre sp) (DuplexPost sp) :=
  Transcript.Duplex.duplex_spec (placed_SpongeWDuplex hP) (duplexInput hP) (keccakF hP)

theorem absorb : ∀ sp, Spec (label NativeRustcVmX64.Vm.SpongeWAbsorb.entryLabel) (AbsorbPre sp) (AbsorbPost sp) :=
  Transcript.Absorb.absorb_spec (placed_SpongeWAbsorb hP) (duplex hP)

theorem squeeze : ∀ sp, Spec (label NativeRustcVmX64.Vm.SpongeWSqueeze.entryLabel) (SqueezePre sp) (SqueezePost sp) :=
  Transcript.Squeeze.squeeze_spec (placed_SpongeWSqueeze hP) (duplex hP)

theorem absorbNonce :
    ∀ sp, Spec (label NativeRustcVmX64.Vm.SpongeWAbsorbNonce.entryLabel) (AbsorbNoncePre sp) (AbsorbNoncePost sp) :=
  Transcript.AbsorbNonce.absorbNonce_spec (placed_SpongeWAbsorbNonce hP) (absorb hP) (duplex hP)

theorem streamElement : ∀ a stream openings, Spec (label NativeRustcVmX64.Vm.DecodedStreamElement.entryLabel)
    (StreamElementPre a stream openings) (StreamElementPost stream) :=
  Transcript.StreamElement.streamElement_spec (placed_DecodedStreamElement hP)

theorem phaseCount : ∀ a stream openings, Spec (label NativeRustcVmX64.Vm.DecodedPhaseCount.entryLabel)
    (PhaseCountPre a stream openings) (PhaseCountPost openings) :=
  Transcript.PhaseCount.phaseCount_spec (placed_DecodedPhaseCount hP)

theorem phase : ∀ a stream openings, Spec (label NativeRustcVmX64.Vm.DecodedPhase.entryLabel) (PhasePre a stream openings)
    (PhasePost a openings) :=
  Transcript.Phase.phase_spec (placed_DecodedPhase hP) (phaseCount hP)

theorem nextScalar :
    ∀ a s, Spec (label NativeRustcVmX64.Vm.TStateNextScalar.entryLabel) (NextScalarPre a s) (NextScalarPost a s) :=
  Transcript.NextScalar.nextScalar_spec (placed_TStateNextScalar hP) (streamElement hP)

theorem readScalar :
    ∀ a s, Spec (label NativeRustcVmX64.Vm.TStateReadScalar.entryLabel) (ReadScalarPre a s) (ReadScalarPost a s) :=
  Transcript.ReadScalar.readScalar_spec (placed_TStateReadScalar hP) (nextScalar hP) (absorb hP)

theorem readScalars :
    ∀ a s, Spec (label NativeRustcVmX64.Vm.TStateReadScalars.entryLabel) (ReadScalarsPre a s) (ReadScalarsPost a s) :=
  Transcript.ReadScalars.readScalars_spec (placed_TStateReadScalars hP) (readScalar hP)

theorem sampleChallenges : ∀ a s, Spec (label NativeRustcVmX64.Vm.TStateSampleChallenges.entryLabel)
    (SampleChallengesPre a s) (SampleChallengesPost a s) :=
  Transcript.SampleChallenges.sampleChallenges_spec (placed_TStateSampleChallenges hP)
    (squeeze hP)

theorem grind : ∀ a s, Spec (label NativeRustcVmX64.Vm.TStateGrind.entryLabel) (GrindPre a s) (GrindPost a s) :=
  Transcript.Grind.grind_spec (placed_TStateGrind hP) (nextScalar hP) (absorbNonce hP)

theorem readCommitment : ∀ a s, Spec (label NativeRustcVmX64.Vm.TStateReadCommitment.entryLabel) (ReadCommitmentPre a s)
    (ReadCommitmentPost a s) :=
  Transcript.ReadCommitment.readCommitment_spec (placed_TStateReadCommitment hP) (readScalar hP)

end

end NativeRustcVmX64.Assembly
