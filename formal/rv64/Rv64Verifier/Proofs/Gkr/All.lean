import Rv64Verifier.Proofs.Transcript.All
import Rv64Verifier.Proofs.Gkr.Open
import Rv64Verifier.Proofs.Gkr.LayerScalars
import Rv64Verifier.Proofs.Gkr.LayerProj
import Rv64Verifier.Proofs.Gkr.LayerIota
import Rv64Verifier.Proofs.Gkr.LayerCheck
import Rv64Verifier.Proofs.Gkr.LayerSample
import Rv64Verifier.Proofs.Gkr.LayerWeights
import Rv64Verifier.Proofs.Gkr.LayerR7
import Rv64Verifier.Proofs.Gkr.Layer
import Rv64Verifier.Proofs.Gkr.KeccakSpec
import Rv64Verifier.Proofs.Gkr.LayerR17
import Rv64Verifier.Proofs.Gkr.LayerR8c
import Rv64Verifier.Proofs.Gkr.LayerFirst
import Rv64Verifier.Proofs.Multilinear.All

/-!
# The Keccak reduction's contracts, their callees' discharged

`eq_kernel`'s contract as the multilinear proof gives it; `open`, `verify_layer` and
`verify_keccak` closed.
-/

namespace Rv64Verifier.Gkr

theorem eqKernel : EqKernelSpec := fun s hpc h ↦
  (Proofs.Multilinear.eqKernel s hpc
    ⟨h.heap, h.out, h.point, h.stack, h.outFree, h.pointFree, h.outStack, h.pointStack,
      h.pointOut, h.rodata, h.outRodata⟩).imp fun _ ⟨hr, ht⟩ ↦
    ⟨hr, ht.imp_left fun ⟨a, b, c⟩ ↦ ⟨a, b, ⟨c.heap, c.mono, c.value, c.frame⟩⟩⟩

theorem «open» : OpenSpec :=
  Open.open_spec Proofs.Multilinear.optFromElemGkr Transcript.sumcheck eqKernel Proofs.Field.mul
    Runtime.memcpy

/-- `verify_layer` from `J12` to the return, its callees' contracts discharged. -/
theorem secondHalf : Layer.SecondHalf :=
  Layer.second_half Runtime.alloc_spec Runtime.reserveFresh_80008a10 Proofs.Field.mul
    Proofs.Multilinear.fromElem

/-- `verify_layer` from the entry to the second check, its callees' contracts discharged. -/
theorem firstHalf : Layer.FirstHalf :=
  Layer.first_half Transcript.nextScalars Proofs.Field.mul eqKernel Proofs.Field.eSum
    Transcript.duplex Runtime.alloc_spec Runtime.reserveFresh_80008a10 Proofs.Multilinear.polyEval
    Runtime.tryAllocZeroed Transcript.roundPoly Runtime.growOneFresh_80011c78 Transcript.sumcheck
    Proofs.Multilinear.dot

theorem verifyLayer : VerifyLayerSpec :=
  Layer.verify_layer_spec firstHalf Transcript.duplex Proofs.Field.mul Runtime.memcpy secondHalf

/-- `verify_keccak`, its callees' contracts discharged but `verify_layer`'s. -/
theorem verifyKeccak (hVL : VerifyLayerSpec) : VerifyKeccakSpec :=
  Keccak.verify_keccak_spec Transcript.samples Proofs.Multilinear.sliceConcat eqKernel
    Runtime.alloc_spec Runtime.reserveFast_80008a10 Proofs.Field.mulK Proofs.Multilinear.dot
    Proofs.Field.mul Transcript.nextScalar hVL Runtime.memcpy «open» Transcript.sumcheck
    Transcript.nextScalars Proofs.Multilinear.mleEval

theorem verifyKeccakClosed : VerifyKeccakSpec := verifyKeccak verifyLayer

end Rv64Verifier.Gkr

/-! Lean's three axioms, nothing native. -/

/-- info: 'Rv64Verifier.Gkr.open' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Gkr.open

/-- info: 'Rv64Verifier.Gkr.Layer.weights' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Gkr.Layer.weights

/-- info: 'Rv64Verifier.Gkr.Layer.pack_start' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Gkr.Layer.pack_start

/-- info: 'Rv64Verifier.Gkr.Layer.verify_layer_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Gkr.Layer.verify_layer_spec

/-- info: 'Rv64Verifier.Gkr.secondHalf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Gkr.secondHalf

/-- info: 'Rv64Verifier.Gkr.Layer.pack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Gkr.Layer.pack

/-- info: 'Rv64Verifier.Gkr.verifyKeccak' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Gkr.verifyKeccak

/-- info: 'Rv64Verifier.Gkr.verifyLayer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Gkr.verifyLayer

/-- info: 'Rv64Verifier.Gkr.verifyKeccakClosed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Gkr.verifyKeccakClosed
