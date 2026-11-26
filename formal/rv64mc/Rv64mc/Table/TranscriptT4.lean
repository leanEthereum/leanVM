/-
  Rv64mc.Table.TranscriptT4

  The total contracts of the transcript's remaining callers at the image (`liftProg Gen.fns`), next to
  `TranscriptT3.lean`: each function's total theorem at its index, with the generated link, the stack `Gen.Needs`
  gives (a caller's bound over its callee's by `decide`), and its callees' total theorems. Left as a hypothesis:
  `keccak_f`'s constant tables in the image's static data (`HashT.KeccakTables`), an environment fact.

  ## Main results

  * `scalarsIter`
-/

import Rv64mc.Table.TranscriptT3
import Rv64mc.Proof.Transcript.ScalarsIterT
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

end Rv64mc.Table.TranscriptT4

/-- info: 'Rv64mc.Table.TranscriptT4.scalarsIter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.TranscriptT4.scalarsIter
