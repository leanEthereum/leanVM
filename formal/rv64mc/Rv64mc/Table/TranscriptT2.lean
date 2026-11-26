/-
  Rv64mc.Table.TranscriptT2

  The sponge's total contracts at the image (`liftProg Gen.fns`), next to `TranscriptT.lean`: each function's total
  theorem at its index, with the generated link, the stack `Gen.Needs` gives (a caller's bound over its callee's by
  `decide`), and its callees' total theorems (`CopyUseT.memcpy`, `VecT.memset`, `HashT.keccakFT`,
  `RuntimeT.sliceIndexFail`). Left as a hypothesis: `keccak_f`'s constant tables in the image's static data
  (`HashT.KeccakTables`), an environment fact.

  ## Main results

  * `duplex`
-/

import Rv64mc.Table.HashT
import Rv64mc.Table.VecT
import Rv64mc.Proof.Transcript.DuplexT
import Rv64mc.Gen.Link.Verifier.Transcript

namespace Rv64mc.Table.TranscriptT2

open MachineChecked.RiscV.Lift Rv64mc.Gen Rv64mc.Proof.Transcript

variable (env : Env)

theorem duplex (hd : HashT.KeccakTables env) :
    DuplexT.specT env (liftProg fns) Idx.Verifier.Transcript.Sponge.Duplex Needs.Verifier.Transcript.Sponge.Duplex :=
  DuplexT.total env _ _ _ Verifier.Transcript.Sponge.Duplex.tmpl_eq Verifier.Transcript.Sponge.Duplex.wf (by decide)
    (by decide) (by decide) (by decide) (CopyUseT.memcpy env) (VecT.memset env) (HashT.keccakFT env hd)
    (RuntimeT.sliceIndexFail env)

end Rv64mc.Table.TranscriptT2

/-- info: 'Rv64mc.Table.TranscriptT2.duplex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.TranscriptT2.duplex
