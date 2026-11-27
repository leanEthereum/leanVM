/-
  Rv64mc.Table.WhirT6b

  The WHIR functions' total contracts of wave 6b at the image (`liftProg Gen.fns`): each function's total theorem at
  its index, with the generated link, the stack `Gen.Needs` gives (its bound over each callee's by `decide`), and its
  callees' total theorems (`sample_queries`: `TranscriptT3.sample`, `RuntimeT.alloc`, `RuntimeT.handleError`). Left
  as hypotheses: `log2_strict`'s two constant tables in the image's static data (`DataRef.InData`, as
  `TranscriptT5b.merkle` takes its own), `keccak_f`'s (`HashT.KeccakTables`, through `Sponge::sample`), and the
  allocator's two facts (`NEXT`'s data reference and the heap's end), environment facts.

  ## Main results

  * `sampleQueries`
-/

import Rv64mc.Table.TranscriptT3
import Rv64mc.Table.RuntimeT
import Rv64mc.Proof.Whir.SampleQueriesT
import Rv64mc.Gen.Link.Verifier.Whir

namespace Rv64mc.Table.WhirT6b

open MachineChecked.RiscV.Lift Rv64mc.Gen Rv64mc.Proof.Whir

variable (env : Env)

/-- `sample_queries`. -/
theorem sampleQueries (hd : HashT.KeccakTables env)
    (hdat : DataRef.InData env (SampleQueriesT.tables Verifier.Whir.SampleQueries.link))
    (hnext : VerifierRv64.Bump.AsGlobalAlloc.Alloc.link.d_NEXT.addr = env.nextAddr)
    (hend : env.heapEnd = 0x78000000#64) :
    SampleQueriesT.specT env (liftProg fns) Idx.Verifier.Whir.SampleQueries Needs.Verifier.Whir.SampleQueries :=
  SampleQueriesT.total env _ _ _ Verifier.Whir.SampleQueries.tmpl_eq Verifier.Whir.SampleQueries.wf hdat
    (needS := Needs.Verifier.Transcript.Sponge.Sample) (needA := Needs.VerifierRv64.Bump.AsGlobalAlloc.Alloc)
    (needH := Needs.Alloc.RawVec.HandleError) (by decide) (by decide) (by decide)
    (TranscriptT3.sample env hd) (RuntimeT.alloc env hnext hend) (RuntimeT.handleError env)

end Rv64mc.Table.WhirT6b

/-- info: 'Rv64mc.Table.WhirT6b.sampleQueries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.WhirT6b.sampleQueries
