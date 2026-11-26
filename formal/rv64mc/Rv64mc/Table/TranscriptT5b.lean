/-
  Rv64mc.Table.TranscriptT5b

  `Transcript::merkle`'s total contract at the image (`liftProg Gen.fns`), next to `TranscriptT4.lean`: its total
  theorem at its index, with the generated link, the stack `Gen.Needs` gives (its bound over each callee's by
  `decide`), and its callees' total theorems (`MerklePath::root`, `memcmp`, `alloc`, `handle_error`). Left as a
  hypothesis: `log2_strict`'s two constant tables in the image's static data (`DataRef.InData`), `keccak_f`'s
  (`HashT.KeccakTables`, through `root`), and the allocator's two facts (`NEXT`'s data reference and the heap's
  end), environment facts.

  ## Main results

  * `merkle`
-/

import Rv64mc.Table.MerkleT
import Rv64mc.Table.RuntimeT
import Rv64mc.Proof.Transcript.MerkleT
import Rv64mc.Gen.Link.Verifier.Transcript

namespace Rv64mc.Table.TranscriptT5b

open MachineChecked.RiscV.Lift Rv64mc.Gen Rv64mc.Proof Rv64mc.Proof.Transcript

variable (env : Env)

/-- `Transcript::merkle`. -/
theorem merkle (hd : HashT.KeccakTables env)
    (hdat : DataRef.InData env (MerkleT.tables Verifier.Transcript.Transcript.Merkle.link))
    (hnext : VerifierRv64.Bump.AsGlobalAlloc.Alloc.link.d_NEXT.addr = env.nextAddr)
    (hend : env.heapEnd = 0x78000000#64) :
    MerkleT.specT env (liftProg fns) Idx.Verifier.Transcript.Transcript.Merkle
      Needs.Verifier.Transcript.Transcript.Merkle :=
  MerkleT.total env _ _ _ Verifier.Transcript.Transcript.Merkle.tmpl_eq Verifier.Transcript.Transcript.Merkle.wf hdat
    (needR := Needs.Verifier.Merkle.MerklePath.Root) (needC := Needs.Memcmp)
    (needA := Needs.VerifierRv64.Bump.AsGlobalAlloc.Alloc) (needH := Needs.Alloc.RawVec.HandleError)
    (by decide) (by decide) (by decide) (by decide)
    (MerkleT.root env hnext hend hd) (RuntimeT.memcmp env) (RuntimeT.alloc env hnext hend) (RuntimeT.handleError env)

end Rv64mc.Table.TranscriptT5b

/-- info: 'Rv64mc.Table.TranscriptT5b.merkle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.TranscriptT5b.merkle
