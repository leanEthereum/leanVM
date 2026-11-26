/-
  Rv64mc.Table.MerkleT

  The Merkle functions' total contracts at the image (`liftProg Gen.fns`): each function's total theorem at its index,
  with the generated link, the stack `Gen.Needs` gives (a caller's bound over its callee's by `decide`), and its
  callees' total theorems (`CopyUseT.memcpy`, `HashT.keccakHashT`, and for `hash_leaf` `RuntimeT.alloc`,
  `RuntimeT.handleError`, `AllocT.reserveU8`). Left as hypotheses: `keccak_f`'s constant tables in the image's static
  data (`HashT.KeccakTables`), and for `hash_leaf` the allocator's two facts (`NEXT`'s data reference and the heap's
  end), environment facts.

  ## Main results

  * `hashPair`, `hashLeaf`
-/

import Rv64mc.Table.HashT
import Rv64mc.Table.CopyUseT
import Rv64mc.Proof.Merkle.HashPairT
import Rv64mc.Proof.Merkle.HashLeafT
import Rv64mc.Table.AllocT
import Rv64mc.Gen.Link.Verifier

namespace Rv64mc.Table.MerkleT

open MachineChecked.RiscV.Lift Rv64mc.Gen Rv64mc.Proof.Merkle

variable (env : Env)

theorem hashPair (hd : HashT.KeccakTables env) :
    HashPairT.specT env (liftProg fns) Idx.Verifier.Merkle.HashPair Needs.Verifier.Merkle.HashPair :=
  HashPairT.total env _ _ _ Verifier.Merkle.HashPair.tmpl_eq Verifier.Merkle.HashPair.wf (by decide) (by decide)
    (CopyUseT.memcpy env) (HashT.keccakHashT env hd)

theorem hashLeaf (hnext : VerifierRv64.Bump.AsGlobalAlloc.Alloc.link.d_NEXT.addr = env.nextAddr)
    (hend : env.heapEnd = 0x78000000#64) (hd : HashT.KeccakTables env) :
    HashLeafT.specT env (liftProg fns) Idx.Verifier.Merkle.HashLeaf Needs.Verifier.Merkle.HashLeaf :=
  HashLeafT.total env _ _ _ Verifier.Merkle.HashLeaf.tmpl_eq Verifier.Merkle.HashLeaf.wf (by decide) (by decide)
    (by decide) (by decide) (by decide) (RuntimeT.alloc env hnext hend) (RuntimeT.handleError env)
    (AllocT.reserveU8 env hnext hend) (CopyUseT.memcpy env) (HashT.keccakHashT env hd)

end Rv64mc.Table.MerkleT

/-- info: 'Rv64mc.Table.MerkleT.hashPair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.MerkleT.hashPair

/-- info: 'Rv64mc.Table.MerkleT.hashLeaf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.MerkleT.hashLeaf
