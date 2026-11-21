module

public import NativeVm.Code.Phase3.TailCode
public import NativeVm.Code.Phase3.Gkr
public import NativeVm.Code.Phase3.Share
public import NativeVm.Code.Phase3.BcMle
public import NativeVm.Code.Phase3.LayoutSpec
public import NativeVm.Code.Phase3.Checks

/-!
# Phase 3's code

`verifyBusBalance`'s steps in order: the sides' placements and the push side's depth
(`layoutCode`), the depth's check and the grind, the slot weights and `β`, the GKR walk and the
count root's check, the memory's limbs and the two final counters, the bytecode share and its value's
check against the bytecode's multilinear extension, then what is computed from them (`tailCode`).
-/

@[expose] public section

namespace NativeVm.Code.P3

open Native NativeVm.Model NativeVm.Code NativeVm.Transcript LeanVM.Parameters

/-- **Phase 3's code.** -/
def code : Stmt := blk [
  layoutCode, checkDepth, grindBus, I (.movi .r12 16), samplesTo wR.off, sampleTo betaR.off,
  gkrCode, checkCount, I (.movi .r12 2), readsTo memR.off, readTo memFinalR.off,
  readTo bcFinalR.off, shareCode, bcCode, tailCode]

end NativeVm.Code.P3
