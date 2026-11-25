/-
  Rv64mc.Table.BusT

  `bus_grinding_bits`' total contract at the image (`liftProg Gen.fns`), over `grinding_bits`' (`TranscriptT`). No
  hypothesis.

  ## Main results

  * `busGrindingBits`
-/

import Rv64mc.Proof.Bus.BusGrindingBitsT
import Rv64mc.Proof.Transcript.GrindingBitsT
import Rv64mc.Gen.Needs
import Rv64mc.Gen.Link.Verifier.Bus
import Rv64mc.Gen.Link.Verifier.Transcript

namespace Rv64mc.Table.BusT

open MachineChecked.RiscV.Lift Rv64mc.Gen Rv64mc.Proof

variable (env : Env)

theorem busGrindingBits :
    Bus.BusGrindingBitsT.specT env (liftProg fns) Idx.Verifier.Bus.BusGrindingBits Needs.Verifier.Bus.BusGrindingBits :=
  Bus.BusGrindingBitsT.total env _ _ _ Verifier.Bus.BusGrindingBits.tmpl_eq Verifier.Bus.BusGrindingBits.wf
    (Transcript.GrindingBitsT.total env _ _ _ Verifier.Transcript.GrindingBits.tmpl_eq
      Verifier.Transcript.GrindingBits.wf)

end Rv64mc.Table.BusT

/-- info: 'Rv64mc.Table.BusT.busGrindingBits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.BusT.busGrindingBits
