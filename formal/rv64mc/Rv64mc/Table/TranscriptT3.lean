/-
  Rv64mc.Table.TranscriptT3

  The transcript chain's total contracts at the image (`liftProg Gen.fns`), next to `TranscriptT2.lean`: each
  function's total theorem at its index, with the generated link, the stack `Gen.Needs` gives (a caller's bound over
  its callee's by `decide`), and its callees' total theorems. Left as a hypothesis: `keccak_f`'s constant tables in
  the image's static data (`HashT.KeccakTables`), an environment fact.

  ## Main results

  * `spongeNew`, `absorb`
-/

import Rv64mc.Table.HashT
import Rv64mc.Table.VecT
import Rv64mc.Table.CopyUseT
import Rv64mc.Proof.Transcript.SpongeNewT
import Rv64mc.Proof.Transcript.AbsorbT
import Rv64mc.Table.TranscriptT2
import Rv64mc.Gen.Link.Verifier.Transcript

namespace Rv64mc.Table.TranscriptT3

open MachineChecked.RiscV.Lift Rv64mc.Gen Rv64mc.Proof.Transcript

variable (env : Env)

theorem spongeNew (hd : HashT.KeccakTables env) :
    SpongeNewT.specT env (liftProg fns) Idx.Verifier.Transcript.Sponge.New Needs.Verifier.Transcript.Sponge.New :=
  SpongeNewT.total env _ _ _ Verifier.Transcript.Sponge.New.tmpl_eq Verifier.Transcript.Sponge.New.wf (by decide)
    (by decide) (by decide) (by decide) (CopyUseT.digestWords env) (VecT.memset env) (HashT.keccakFT env hd)
    (CopyUseT.memcpy env)

theorem absorb (hd : HashT.KeccakTables env) :
    AbsorbT.specT env (liftProg fns) Idx.Verifier.Transcript.Sponge.Absorb Needs.Verifier.Transcript.Sponge.Absorb :=
  AbsorbT.total env _ _ _ Verifier.Transcript.Sponge.Absorb.tmpl_eq Verifier.Transcript.Sponge.Absorb.wf (by decide)
    (by decide) (by decide) (TranscriptT2.duplex env hd) (RuntimeT.panicFmt env) (RuntimeT.panicBoundsCheck env)

end Rv64mc.Table.TranscriptT3

/-- info: 'Rv64mc.Table.TranscriptT3.spongeNew' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.TranscriptT3.spongeNew

/-- info: 'Rv64mc.Table.TranscriptT3.absorb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.TranscriptT3.absorb
