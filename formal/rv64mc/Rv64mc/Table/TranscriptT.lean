/-
  Rv64mc.Table.TranscriptT

  The transcript's leaves' total contracts at the image (`liftProg Gen.fns`): `grinding_bits`,
  `Transcript::finish` and `Transcript::next`, each at its index with the generated link and the stack `Gen.Needs`
  gives. Leaves: no hypothesis.

  ## Main results

  * `grindingBits`, `finish`, `next`
-/

import Rv64mc.Proof.Transcript.GrindingBitsT
import Rv64mc.Proof.Transcript.FinishT
import Rv64mc.Proof.Transcript.NextT
import Rv64mc.Gen.Needs
import Rv64mc.Gen.Link.Verifier.Transcript

namespace Rv64mc.Table.TranscriptT

open MachineChecked.RiscV.Lift Rv64mc.Gen Rv64mc.Proof.Transcript

variable (env : Env)

theorem grindingBits :
    GrindingBitsT.specT env (liftProg fns) Idx.Verifier.Transcript.GrindingBits
      Needs.Verifier.Transcript.GrindingBits :=
  GrindingBitsT.total env _ _ _ Verifier.Transcript.GrindingBits.tmpl_eq Verifier.Transcript.GrindingBits.wf

theorem finish :
    FinishT.specT env (liftProg fns) Idx.Verifier.Transcript.Transcript.Finish
      Needs.Verifier.Transcript.Transcript.Finish :=
  FinishT.total env _ _ _ Verifier.Transcript.Transcript.Finish.tmpl_eq Verifier.Transcript.Transcript.Finish.wf _

theorem next :
    NextT.specT env (liftProg fns) Idx.Verifier.Transcript.Transcript.Next Needs.Verifier.Transcript.Transcript.Next :=
  NextT.total env _ _ _ Verifier.Transcript.Transcript.Next.tmpl_eq Verifier.Transcript.Transcript.Next.wf _

end Rv64mc.Table.TranscriptT

/-- info: 'Rv64mc.Table.TranscriptT.grindingBits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.TranscriptT.grindingBits

/-- info: 'Rv64mc.Table.TranscriptT.finish' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.TranscriptT.finish

/-- info: 'Rv64mc.Table.TranscriptT.next' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.TranscriptT.next
