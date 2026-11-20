/-
  Rv64mc.Table.Hash

  The contracts of `hash.rs` and `merkle.rs` at the image (`liftProg Gen.fns`): each `ok` at its function's index,
  with the generated link and the stack each needs (`Gen.Needs`). The indices are the generator's
  (`Rv64mc/Gen/index.tsv`).
-/

import Rv64mc.Proof.Hash.DigestFromHalves
import Rv64mc.Gen.Needs
import Rv64mc.Gen.Link.Verifier.Hash.Digest.FromHalves

namespace Rv64mc.Table.Hash

open MachineChecked.RiscV.Lift Rv64mc.Gen

variable (env : Env)

theorem digestFromHalves :
    Spec.Hash.DigestFromHalves.spec env (liftProg fns) 46 Needs.Verifier.Hash.Digest.FromHalves :=
  Proof.Hash.DigestFromHalves.ok env _ 46 _ Verifier.Hash.Digest.FromHalves.tmpl_eq _

end Rv64mc.Table.Hash

/-- info: 'Rv64mc.Table.Hash.digestFromHalves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.Hash.digestFromHalves
