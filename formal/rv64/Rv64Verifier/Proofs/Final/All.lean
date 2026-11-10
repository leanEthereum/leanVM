import Rv64Verifier.Proofs.Final.Bridge
import Rv64Verifier.Proofs.Main.All
import Rv64Verifier.Proofs.Walk.Spec
import Rv64Verifier.Proofs.Walk.All
import Rv64Verifier.Proofs.Walk.R18K
import Rv64Verifier.Proofs.Bus.All
import Rv64Verifier.Proofs.Multilinear.All
import Rv64Verifier.Proofs.Pcs.Contracts

/-!
# Soundness, assembled

`soundness`: `Sound image` from `walk`'s two halves (`WalkFront`, `WalkTail`, for the openings
`OI` of `Bridge.lean`), the tail taking `verify_stacked_opening`'s contract (`VsoSpec`) and the
bus's tail (`TailStage`, from `SidesEntry` and `SideStage`). `main`, the bridge and every other
callee are proved; `cloneE` and `tableSumcheckClosed` discharge the walk's `CloneSpecE` and
`TableSumcheckSpec`.
-/

namespace Rv64Verifier.Proofs.Final
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Compile Rv64Verifier.Model Rv64Verifier.Proofs.End

/-- `clone` with the slice asked for only when it is not empty. -/
theorem cloneE : Walk.CloneSpecE := fun s hpc h ↦
  Multilinear.Clone.clone_spec_e Runtime.tryAllocZeroed Runtime.memcpy s hpc
    ⟨h.heap, h.out, h.src, h.srcAlign, h.stack, h.outFree, h.outStack, h.srcFree, h.srcOut,
      h.srcStack⟩

/-- `vec![None; n]` with its buffer below `NEXT`. -/
theorem optFromElemBelow : Bus.TableSumcheck.OptFromElemBelowSpec :=
  Multilinear.OptFromElem.opt_from_elem_below Runtime.tryAllocZeroed
    Runtime.Reserve.reserve_fast_8001086c

theorem tableSumcheckClosed : Rv64Verifier.Bus.TableSumcheckSpec :=
  Bus.tableSumcheck optFromElemBelow

/-- `walk` from its entry to `0x800035f0` (`AtR17`), or returned, or dead. -/
def WalkFront : Prop :=
  ∀ s, s.pc = 0x80000ef8 → Walk.WalkPre s → ∃ u, Reaches Image.code s u ∧
    ((∃ layout rows lir bus, Walk.AtR17 OI s u layout rows lir bus) ∨ Walk.Done OI s u ∨
      Dead Image.code u)

/-- `walk` from `AtR17` to its return, or dead. -/
def WalkTail : Prop :=
  ∀ s u (layout : LayoutMirror.LayoutRust) (rows : List (BitVec 64)) (lir : BitVec 64)
    (bus : BusResultRust), Walk.WalkPre s → Walk.AtR17 OI s u layout rows lir bus →
    ∃ t, Reaches Image.code u t ∧ (Walk.Done OI s t ∨ Dead Image.code t)

/-- **Soundness**: the image halts with `1` only on an input that decodes to an accepted proof,
given `walk`'s front, its tail (from `verify_stacked_opening`'s contract and the bus's tail), and
those two. -/
theorem soundness {OA : MachineState → Word → TState → Prop}
    {BcOk : MachineState → Nat → Word → Prop} {bev : MachineState → Word → List E → Option E}
    (hVso : PcsContracts.VsoSpec OA) (hE : Bus.VerifyBusBalance.SidesEntry BcOk bev)
    (hS : Bus.VerifyBusBalance.SideStage bev) (hFront : WalkFront)
    (hTail : PcsContracts.VsoSpec OA → Bus.VerifyBusBalance.TailStage BcOk bev → WalkTail) :
    Sound image :=
  Main.sound_of_walk
    (walkCall_of_walk (Walk.walk_spec_of hFront (hTail hVso (Bus.vbbTailStage hE hS))))

end Rv64Verifier.Proofs.Final

/-! Lean's three axioms, nothing native. -/

/-- info: 'Rv64Verifier.Proofs.Final.soundness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Final.soundness

/-- info: 'Rv64Verifier.Proofs.Final.walkCall_of_walk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Final.walkCall_of_walk

/-- info: 'Rv64Verifier.Proofs.Final.OI.openingsAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Final.OI.openingsAt

/-- info: 'Rv64Verifier.Proofs.Final.OI.openFits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Final.OI.openFits

/-- info: 'Rv64Verifier.Proofs.Final.cloneE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Final.cloneE

/-- info: 'Rv64Verifier.Proofs.Final.tableSumcheckClosed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Final.tableSumcheckClosed
