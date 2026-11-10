import Rv64Verifier.Proofs.Walk.R19N
import Rv64Verifier.Proofs.Walk.AllD
import Rv64Verifier.Proofs.Gkr.All
import Rv64Verifier.Proofs.Layout.All
import Rv64Verifier.Proofs.Bus.TsSpec

/-!
# `walk` from `AtR17` to `ring_switch`'s call, closed

`toR21Closed`: `toR21` with every callee's contract the proved one. `verifyKeccakE` is
`Gkr.verifyKeccakClosedW` (`verify_keccak` with `a7` free). `cloneE`, `tableSumcheckClosed` and
`vbbEqKernel` restate `Final/All.lean`'s and `Bus/All.lean`'s without importing `Bus.All`.
`derefToR10Closed` is `front`'s `hDJ`.
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
  LeanVM.Protocol.Verifier Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript
  Rv64Verifier.Bus

/-- `verify_keccak` as `walk` calls it. -/
theorem verifyKeccakE : VerifyKeccakSpecE := fun s hpc h ↦
  (Gkr.verifyKeccakClosedW s hpc
    { toTPre := h.toTPre, depth := h.depth, checked := h.checked, inst := h.inst,
      output := h.output, instFree := h.instFree, outputFree := h.outputFree,
      instStack := h.instStack, outputStack := h.outputStack, instOut := h.instOut,
      outputOut := h.outputOut, instSelf := h.instSelf, outputSelf := h.outputSelf }).imp
    fun _ ⟨hr, ht⟩ ↦ ⟨hr, ht.imp_left fun ⟨a, b, c⟩ ↦ ⟨a, b, ⟨c.heap, c.mono, c.value, c.frame⟩⟩⟩

/-- `clone` with the slice asked for only when it is not empty. -/
theorem cloneE : CloneSpecE := fun s hpc h ↦
  Multilinear.Clone.clone_spec_e Runtime.tryAllocZeroed Runtime.memcpy s hpc
    ⟨h.heap, h.out, h.src, h.srcAlign, h.stack, h.outFree, h.outStack, h.srcFree, h.srcOut,
      h.srcStack⟩

/-- `table_sumcheck`, closed. -/
theorem tableSumcheckClosed : TableSumcheckSpec :=
  Proofs.Bus.TableSumcheck.table_sumcheck_spec
    (Multilinear.OptFromElem.opt_from_elem_below Runtime.tryAllocZeroed
      Runtime.Reserve.reserve_fast_8001086c)
    Transcript.sumcheck Runtime.tryAllocZeroed Runtime.reserveFresh_80008a10
    Multilinear.fromElem Field.mul Runtime.memcpy Transcript.nextScalars alloc_spec Multilinear.dot
    Layout.form_evaluate_e_proved

/-- **`walk` from `AtR17` to `AtR21`**, an `Err` return or a dead end: `toR21` closed. -/
theorem toR21Closed {OI : MachineState → Word → List (List Opening) → Prop} {s u₀ : MachineState}
    {layout : LayoutMirror.LayoutRust} {rows : List (BitVec 64)} {lir : BitVec 64}
    {bus : BusResultRust} (hpre : WalkPre s) (h : AtR17 OI s u₀ layout rows lir bus) :
    ∃ v, Reaches Image.code u₀ v ∧ ((∃ w t evs P C L cl pt sl ks ke,
      AtR21 OI s u₀ w t v layout rows lir bus evs P C L cl pt sl ks ke) ∨
      Done OI s v ∨ Dead Image.code v) :=
  toR21 Transcript.duplex Multilinear.powers Multilinear.dot tableSumcheckClosed
    Runtime.Drop.drop_nop_spec Runtime.dropLayout cloneE Runtime.growAmortized Multilinear.fromElem
    alloc_spec Runtime.reserveFast_80008a10 Multilinear.scalerNew Field.mul
    Runtime.growOneFresh_8000c0a4 verifyKeccakE hpre h

/-- DEREF, JUMP and R9 closed: `front`'s `hDJ`. -/
theorem derefToR10Closed {OI : MachineState → Word → List (List Opening) → Prop} :
    ∀ s u A k R Q B Bb, WalkPre s → AtDeref OI s u A k R Q B Bb →
      ∃ t, Reaches Image.code u t ∧ ((∃ A k R Q B, AtR10 OI s t A k R Q B) ∨ Done OI s t ∨
        Dead Image.code t) := fun _ _ _ _ _ _ _ _ hpre h ↦ by
  obtain ⟨t, hr, ht | ht⟩ := derefToR10 Layout.col_proved Layout.prod_proved
    Layout.add_scaled_proved Layout.state_step_proved Layout.state_derived_proved alloc_spec
    Layout.term_proved Layout.bytecode_proved Layout.memory_cols_proved Layout.memory_proved
    Multilinear.fromElem Runtime.memcpy hpre h
  · exact ⟨t, hr, Or.inl ⟨_, _, _, _, _, ht⟩⟩
  · exact ⟨t, hr, Or.inr (Or.inr ht)⟩

end Rv64Verifier.Proofs.Walk

/-! Lean's three axioms, nothing native. -/

/-- info: 'Rv64Verifier.Proofs.Walk.verifyKeccakE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.verifyKeccakE

/-- info: 'Rv64Verifier.Proofs.Walk.cloneE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.cloneE

/-- info: 'Rv64Verifier.Proofs.Walk.tableSumcheckClosed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.tableSumcheckClosed

/-- info: 'Rv64Verifier.Proofs.Walk.toR21Closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.toR21Closed

/-- info: 'Rv64Verifier.Proofs.Walk.derefToR10Closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Walk.derefToR10Closed
