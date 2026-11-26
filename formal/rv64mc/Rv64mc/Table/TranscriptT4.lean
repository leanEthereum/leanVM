/-
  Rv64mc.Table.TranscriptT4

  The total contracts of the transcript's remaining callers at the image (`liftProg Gen.fns`), next to
  `TranscriptT3.lean`: each function's total theorem at its index, with the generated link, the stack `Gen.Needs`
  gives (a caller's bound over its callee's by `decide`), and its callees' total theorems. Left as a hypothesis:
  `keccak_f`'s constant tables in the image's static data (`HashT.KeccakTables`), and for `next_scalars` and
  `read_ood` the allocator's two facts (`NEXT`'s data reference and the heap's end), environment facts. `read_ood`
  sits here with the transcript's other callers.

  ## Main results

  * `scalarsIter`, `nextScalars`, `readOod`
-/

import Rv64mc.Table.TranscriptT3
import Rv64mc.Proof.Transcript.ScalarsIterT
import Rv64mc.Proof.Transcript.NextScalarsT
import Rv64mc.Table.AllocT
import Rv64mc.Proof.Whir.ReadOodT
import Rv64mc.Gen.Link.Core
import Rv64mc.Gen.Link.Verifier

namespace Rv64mc.Table.TranscriptT4

open MachineChecked.RiscV.Lift Rv64mc.Gen Rv64mc.Proof Rv64mc.Proof.Transcript

variable (env : Env)

/-- `next_scalars`' iterator (`GenericShunt<Map<Range<usize>, next_scalars::{closure}>, _>::next`). -/
theorem scalarsIter (hd : HashT.KeccakTables env) :
    ScalarsIterT.specT env (liftProg fns) Idx.Core.Iter.Adapters.GenericShuntMapRangeUsizHcc804615.AsIterator.Next
      Needs.Core.Iter.Adapters.GenericShuntMapRangeUsizHcc804615.AsIterator.Next :=
  ScalarsIterT.total env _ _ _ Core.Iter.Adapters.GenericShuntMapRangeUsizHcc804615.AsIterator.Next.tmpl_eq
    Core.Iter.Adapters.GenericShuntMapRangeUsizHcc804615.AsIterator.Next.wf (by decide)
    (TranscriptT3.nextScalar env hd)

theorem nextScalars (hd : HashT.KeccakTables env)
    (hnext : VerifierRv64.Bump.AsGlobalAlloc.Alloc.link.d_NEXT.addr = env.nextAddr)
    (hend : env.heapEnd = 0x78000000#64) :
    NextScalarsT.specT env (liftProg fns) Idx.Verifier.Transcript.Transcript.NextScalars
      Needs.Verifier.Transcript.Transcript.NextScalars :=
  NextScalarsT.total env _ _ _ Verifier.Transcript.Transcript.NextScalars.tmpl_eq
    Verifier.Transcript.Transcript.NextScalars.wf (by decide) (by decide) (by decide) (by decide) (scalarsIter env hd)
    (RuntimeT.alloc env hnext hend) (AllocT.reserveE env hnext hend) (RuntimeT.handleError env)

theorem readOod (hd : HashT.KeccakTables env)
    (hnext : VerifierRv64.Bump.AsGlobalAlloc.Alloc.link.d_NEXT.addr = env.nextAddr)
    (hend : env.heapEnd = 0x78000000#64) :
    Whir.ReadOodT.specT env (liftProg fns) Idx.Verifier.ReadOod Needs.Verifier.ReadOod :=
  Whir.ReadOodT.total env _ _ _ Verifier.ReadOod.tmpl_eq Verifier.ReadOod.wf (by decide) (by decide) (by decide)
    (TranscriptT3.grindCheck env hd) (TranscriptT3.samples env hd hnext hend) (TranscriptT3.nextScalar env hd)

end Rv64mc.Table.TranscriptT4

/-- info: 'Rv64mc.Table.TranscriptT4.scalarsIter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.TranscriptT4.scalarsIter

/-- info: 'Rv64mc.Table.TranscriptT4.nextScalars' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.TranscriptT4.nextScalars

/-- info: 'Rv64mc.Table.TranscriptT4.readOod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.TranscriptT4.readOod
