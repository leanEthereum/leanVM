/-
  Rv64mc.Table.RuntimeT6f

  `Input::digest`'s total contract at the image (`liftProg Gen.fns`): its total theorem at its index, with the
  generated link, the stack `Gen.Needs` gives (a bound over `Input::word`'s by `decide`), and `Input::word`'s total
  theorem (`RuntimeT.inputWord`). No hypothesis is left.

  ## Main results

  * `inputDigest`
-/

import Rv64mc.Table.RuntimeT
import Rv64mc.Proof.Runtime.InputDigestT
import Rv64mc.Gen.Link.Misc

namespace Rv64mc.Table.RuntimeT6f

open MachineChecked.RiscV.Lift Rv64mc.Gen Rv64mc.Proof.Runtime

variable (env : Env)

/-- `Input::digest` (5). -/
theorem inputDigest :
    InputDigestT.InputDigestSpecT env (liftProg fns) Idx.VerifierRv64.Input.Digest Needs.VerifierRv64.Input.Digest :=
  InputDigestT.total VerifierRv64.Input.Digest.link _ _ VerifierRv64.Input.Digest.tmpl_eq
    VerifierRv64.Input.Digest.wf (by decide) (RuntimeT.inputWord env)

end Rv64mc.Table.RuntimeT6f

/-- info: 'Rv64mc.Table.RuntimeT6f.inputDigest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.RuntimeT6f.inputDigest
