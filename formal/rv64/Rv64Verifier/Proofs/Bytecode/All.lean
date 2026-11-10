import Rv64Verifier.Proofs.Bytecode.Evaluate
import Rv64Verifier.Proofs.Bytecode.Digest
import Rv64Verifier.Proofs.Multilinear.All

/-!
# `Bytecode::evaluate` and `Input::digest`, their callees' discharged

`eq_kernel`'s contract as `evaluate` states it (`eqKernel`), from the multilinear proof;
`evaluate` takes it.
-/

namespace Rv64Verifier.Proofs.Bytecode
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime

open Rv64Verifier.Model in
/-- `eq_kernel`'s proved contract gives `EqKernelPost`. -/
theorem eqKernelPost {s t : MachineState} (c : MultilinearContracts.EqKernelPost s t) :
    EqKernelPost s t := by
  have hv := c.value
  have hl : (vecLen t (s.getReg .x10)).toNat = 2 ^ (s.getReg .x12).toNat := by
    have := congrArg List.length hv.elems
    rwa [vecEs, eListAt_length, eqKernelRust_eq, eqKernel_length, eListAt_length] at this
  refine ⟨c.heap, c.mono, hv.vec, hl, hv.elems, ?_, c.frame⟩
  have hb := hv.buf
  have hle := hv.vec.len
  have hp := Nat.two_pow_pos (s.getReg .x12).toNat
  simp only [NewBuf] at hb ⊢
  refine ⟨hb.1, Or.inr ?_⟩
  rcases hb.2 with h0 | h0
  · omega
  · exact ⟨h0.1, by omega⟩

/-- `eq_kernel`, as `Bytecode::evaluate` calls it, from the multilinear proof. -/
theorem eqKernel : EqKernelSpec := fun s hpc h ↦
  (Multilinear.eqKernel s hpc
    ⟨h.heap, h.out, Or.inr h.point, h.stack, h.outFree, Or.inr h.pointFree, h.outStack,
      h.pointStack, h.pointOut, h.rodata, h.outRodata⟩).imp fun _ ⟨hr, ht⟩ ↦
    ⟨hr, ht.imp_left fun ⟨a, b, c⟩ ↦ ⟨a, b, eqKernelPost c⟩⟩

theorem evaluate (hEK : EqKernelSpec) : EvaluateSpec :=
  Eval.evaluate_spec hEK Multilinear.fromElem Field.mul

end Rv64Verifier.Proofs.Bytecode

/-! Lean's three axioms, nothing native. -/

/-- info: 'Rv64Verifier.Proofs.Bytecode.eqKernel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Bytecode.eqKernel

/-- info: 'Rv64Verifier.Proofs.Bytecode.evaluate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Bytecode.evaluate

/-- info: 'Rv64Verifier.Proofs.Bytecode.digest_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Bytecode.digest_spec
