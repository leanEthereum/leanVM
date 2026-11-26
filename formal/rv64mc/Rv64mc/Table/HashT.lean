/-
  Rv64mc.Table.HashT

  The total contracts of the hash functions proved total, at the image: `xor_block` (`XorBlockSafeT`), a leaf.

  ## Main results

  * `xorBlockT`
-/

import Rv64mc.Proof.Hash.XorBlockT
import Rv64mc.Gen.Needs
import Rv64mc.Gen.Link.Verifier.Hash

namespace Rv64mc.Table.HashT

open MachineChecked.RiscV.Lift Rv64mc.Gen

variable (env : Env)

/-- **`xor_block` at the image** (function 123). -/
theorem xorBlockT : Proof.Hash.XorBlockT.XorBlockSafeT env (liftProg fns) Idx.Verifier.Hash.XorBlock
    Needs.Verifier.Hash.XorBlock :=
  HoldsT.mono_need (Proof.Hash.XorBlockT.total Verifier.Hash.XorBlock.tmpl_eq) (by decide)

end Rv64mc.Table.HashT

/-- info: 'Rv64mc.Table.HashT.xorBlockT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.HashT.xorBlockT
