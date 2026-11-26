/-
  Rv64mc.Table.MerkleT

  The Merkle functions' total contracts at the image (`liftProg Gen.fns`): each function's total theorem at its index,
  with the generated link, the stack `Gen.Needs` gives (a caller's bound over its callee's by `decide`), and its
  callees' total theorems (`CopyUseT.memcpy`, `HashT.keccakHashT`). Left as a hypothesis: `keccak_f`'s constant
  tables in the image's static data (`HashT.KeccakTables`), an environment fact.

  ## Main results

  * `hashPair`
-/

import Rv64mc.Table.HashT
import Rv64mc.Table.CopyUseT
import Rv64mc.Proof.Merkle.HashPairT
import Rv64mc.Gen.Link.Verifier

namespace Rv64mc.Table.MerkleT

open MachineChecked.RiscV.Lift Rv64mc.Gen Rv64mc.Proof.Merkle

variable (env : Env)

theorem hashPair (hd : HashT.KeccakTables env) :
    HashPairT.specT env (liftProg fns) Idx.Verifier.Merkle.HashPair Needs.Verifier.Merkle.HashPair :=
  HashPairT.total env _ _ _ Verifier.Merkle.HashPair.tmpl_eq Verifier.Merkle.HashPair.wf (by decide) (by decide)
    (CopyUseT.memcpy env) (HashT.keccakHashT env hd)

end Rv64mc.Table.MerkleT

/-- info: 'Rv64mc.Table.MerkleT.hashPair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.MerkleT.hashPair
