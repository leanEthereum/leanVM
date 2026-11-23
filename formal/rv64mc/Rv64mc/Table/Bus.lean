/-
  Rv64mc.Table.Bus

  `bus.rs`'s contracts at the image (`liftProg Gen.fns`): each `ok` at its function's index
  (`Rv64mc/Gen/index.tsv`), with the generated link and stack (`Gen.Needs`), from the contracts not proved here:
  `grinding_bits`, `stack_point` and `panic_bounds_check`.
-/

import Rv64mc.Proof.Bus.BusGrindingBits
import Rv64mc.Proof.Bus.OnStack
import Rv64mc.Gen.Link.Verifier.Bus
import Rv64mc.Gen.Needs

namespace Rv64mc.Table.Bus

open MachineChecked.RiscV.Lift Rv64mc.Gen

variable (env : Env)

theorem busGrindingBits
    (hgb : Spec.Transcript.GrindingBits.spec env (liftProg fns) Idx.Verifier.Transcript.GrindingBits Needs.Verifier.Transcript.GrindingBits) :
    Spec.Bus.BusGrindingBits.spec env (liftProg fns) Idx.Verifier.Bus.BusGrindingBits Needs.Verifier.Bus.BusGrindingBits :=
  Proof.Bus.BusGrindingBits.ok env _ Idx.Verifier.Bus.BusGrindingBits _ Verifier.Bus.BusGrindingBits.tmpl_eq Verifier.Bus.BusGrindingBits.wf hgb

theorem onStack
    (hsp : Spec.Multilinear.StackPoint.spec env (liftProg fns) Idx.Verifier.Multilinear.Placement.StackPoint Needs.Verifier.Multilinear.Placement.StackPoint)
    (hpanic : Spec.Runtime.NoReturn env (liftProg fns) Idx.Core.Panicking.PanicBoundsCheck 0) :
    Spec.Bus.OnStack.spec env (liftProg fns) Idx.Verifier.Bus.ColumnClaim.OnStack Needs.Verifier.Bus.ColumnClaim.OnStack :=
  Proof.Bus.OnStack.ok env _ Idx.Verifier.Bus.ColumnClaim.OnStack _ Verifier.Bus.ColumnClaim.OnStack.tmpl_eq Verifier.Bus.ColumnClaim.OnStack.wf
    (by decide) hsp hpanic

end Rv64mc.Table.Bus

/-- info: 'Rv64mc.Table.Bus.onStack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.Bus.onStack

/-- info: 'Rv64mc.Table.Bus.busGrindingBits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.Bus.busGrindingBits
