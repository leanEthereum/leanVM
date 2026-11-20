/-
  Rv64mc.Table.Transcript

  The transcript's contracts at the image (`liftProg Gen.fns`): each `ok` at its function's index, with the
  generated link (`Gen.….link`, `tmpl_eq`, `wf`) and the stack each needs (`Gen.Needs`), from the contracts of the
  callees of other areas as hypotheses where they are not proved at the image yet. The indices are the generator's
  (`Rv64mc/Gen/index.tsv`).
-/

import Rv64mc.Proof.Transcript.Next
import Rv64mc.Proof.Transcript.Finish
import Rv64mc.Gen.Needs
import Rv64mc.Gen.Link.Verifier.Transcript.Transcript.Next
import Rv64mc.Gen.Link.Verifier.Transcript.Transcript.Finish

namespace Rv64mc.Table.Transcript

open MachineChecked.RiscV.Lift Rv64mc.Gen

variable (env : Env)

theorem next : Spec.Transcript.Next.spec env (liftProg fns) 111 Needs.Verifier.Transcript.Transcript.Next :=
  Proof.Transcript.Next.ok env _ 111 _ Verifier.Transcript.Transcript.Next.tmpl_eq
    Verifier.Transcript.Transcript.Next.wf

theorem finish : Spec.Transcript.Finish.spec env (liftProg fns) 67 Needs.Verifier.Transcript.Transcript.Finish :=
  Proof.Transcript.Finish.ok env _ 67 _ Verifier.Transcript.Transcript.Finish.tmpl_eq
    Verifier.Transcript.Transcript.Finish.wf

end Rv64mc.Table.Transcript

/-- info: 'Rv64mc.Table.Transcript.next' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.Transcript.next

/-- info: 'Rv64mc.Table.Transcript.finish' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.Transcript.finish
