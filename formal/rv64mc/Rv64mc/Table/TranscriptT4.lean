/-
  Rv64mc.Table.TranscriptT4

  The total contracts of the transcript's remaining callers at the image (`liftProg Gen.fns`), next to
  `TranscriptT3.lean`: each function's total theorem at its index, with the generated link, the stack `Gen.Needs`
  gives (a caller's bound over its callee's by `decide`), and its callees' total theorems. Left as a hypothesis:
  `keccak_f`'s constant tables in the image's static data (`HashT.KeccakTables`), and for `next_scalars` the
  allocator's two facts (`NEXT`'s data reference and the heap's end), environment facts.

  ## Main results

  * `scalarsIter`, `nextScalars`
-/

import Rv64mc.Table.TranscriptT3
import Rv64mc.Proof.Transcript.ScalarsIterT
import Rv64mc.Proof.Transcript.NextScalarsT
import Rv64mc.Table.AllocT
import Rv64mc.Gen.Link.Core

namespace Rv64mc.Table.TranscriptT4

open MachineChecked.RiscV.Lift Rv64mc.Gen Rv64mc.Proof.Transcript

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

end Rv64mc.Table.TranscriptT4

/-- info: 'Rv64mc.Table.TranscriptT4.scalarsIter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.TranscriptT4.scalarsIter

/-- info: 'Rv64mc.Table.TranscriptT4.nextScalars' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.TranscriptT4.nextScalars
