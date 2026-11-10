import Rv64Verifier.Proofs.Gkr.Open
import Rv64Verifier.Proofs.Gkr.LayerScalars
import Rv64Verifier.Proofs.Gkr.LayerProj
import Rv64Verifier.Proofs.Gkr.LayerIota
import Rv64Verifier.Proofs.Gkr.LayerCheck
import Rv64Verifier.Proofs.Gkr.LayerSample
import Rv64Verifier.Proofs.Gkr.LayerWeights
import Rv64Verifier.Proofs.Multilinear.All

/-!
# The Keccak reduction's contracts, their callees' discharged

`eq_kernel`'s contract as the multilinear proof gives it; `open` still takes `sumcheck`'s.
-/

namespace Rv64Verifier.Gkr

theorem eqKernel : EqKernelSpec := fun s hpc h ↦
  (Proofs.Multilinear.eqKernel s hpc
    ⟨h.heap, h.out, h.point, h.stack, h.outFree, h.pointFree, h.outStack, h.pointStack,
      h.pointOut, h.rodata, h.outRodata⟩).imp fun _ ⟨hr, ht⟩ ↦
    ⟨hr, ht.imp_left fun ⟨a, b, c⟩ ↦ ⟨a, b, ⟨c.heap, c.mono, c.value, c.frame⟩⟩⟩

theorem «open» (hSC : Transcript.SumcheckSpec) : OpenSpec :=
  Open.open_spec Proofs.Multilinear.optFromElemGkr hSC eqKernel Proofs.Field.mul Runtime.memcpy

end Rv64Verifier.Gkr

/-! Lean's three axioms, nothing native. -/

/-- info: 'Rv64Verifier.Gkr.open' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Gkr.open
