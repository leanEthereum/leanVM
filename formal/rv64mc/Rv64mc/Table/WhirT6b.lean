/-
  Rv64mc.Table.WhirT6b

  The WHIR functions' total contracts of wave 6b at the image (`liftProg Gen.fns`): each function's total theorem at
  its index, with the generated link, the stack `Gen.Needs` gives (its bound over each callee's by `decide`), and its
  callees' total theorems (`sample_queries`: `TranscriptT3.sample`, `RuntimeT.alloc`, `RuntimeT.handleError`;
  `Subspace::at`: `FieldT.baseMul`, `FieldT.spread`, `FieldT.reduce`, `RuntimeT.alloc`, `RuntimeT.handleError`;
  `ext_row`: `AllocT.reserveE`, `RuntimeT.alloc`, `RuntimeT.handleError`; `novel_basis`: `AllocT.reserveK`,
  `RuntimeT.alloc`, `RuntimeT.handleError`, `FieldT.baseMul`, `CopyUseT.memcpy`, `RuntimeT.panicNounwindFmt`,
  `RuntimeT.panicFmt`). Left
  as hypotheses: `log2_strict`'s two constant tables in the image's static data (`DataRef.InData`, as
  `TranscriptT5b.merkle` takes its own), `keccak_f`'s (`HashT.KeccakTables`, through `Sponge::sample`), `clmul_low`'s
  (`FieldT.ClmulTable`, through `base_mul`), and the allocator's two facts (`NEXT`'s data reference and the heap's
  end), environment facts.

  ## Main results

  * `sampleQueries`, `subspaceAt`, `extRow`, `novelBasis`
-/

import Rv64mc.Table.TranscriptT3
import Rv64mc.Table.RuntimeT
import Rv64mc.Table.FieldT
import Rv64mc.Proof.Whir.SampleQueriesT
import Rv64mc.Proof.Whir.SubspaceAtT
import Rv64mc.Proof.Whir.ExtRowT
import Rv64mc.Table.AllocT
import Rv64mc.Table.CopyUseT
import Rv64mc.Proof.Whir.NovelBasisT
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

/-- `Subspace::at`. -/
theorem subspaceAt (hd : FieldT.ClmulTable env)
    (hnext : VerifierRv64.Bump.AsGlobalAlloc.Alloc.link.d_NEXT.addr = env.nextAddr)
    (hend : env.heapEnd = 0x78000000#64) :
    SubspaceAtT.specT env (liftProg fns) Idx.Verifier.Whir.Subspace.At Needs.Verifier.Whir.Subspace.At :=
  SubspaceAtT.total env _ _ _ Verifier.Whir.Subspace.At.tmpl_eq Verifier.Whir.Subspace.At.wf
    (needB := Needs.Verifier.Field.BaseMul) (needS := Needs.Verifier.Field.Spread)
    (needR := Needs.Verifier.Field.Reduce) (needA := Needs.VerifierRv64.Bump.AsGlobalAlloc.Alloc)
    (needH := Needs.Alloc.RawVec.HandleError) (by decide) (by decide) (by decide) (by decide) (by decide)
    (FieldT.baseMul env hd) (FieldT.spread env) (FieldT.reduce env) (RuntimeT.alloc env hnext hend)
    (RuntimeT.handleError env)

/-- `ext_row`. -/
theorem extRow (hnext : VerifierRv64.Bump.AsGlobalAlloc.Alloc.link.d_NEXT.addr = env.nextAddr)
    (hend : env.heapEnd = 0x78000000#64) :
    ExtRowT.specT env (liftProg fns) Idx.Verifier.Whir.ExtRow Needs.Verifier.Whir.ExtRow :=
  ExtRowT.total env _ _ _ Verifier.Whir.ExtRow.tmpl_eq Verifier.Whir.ExtRow.wf
    (needR := Needs.Alloc.Vec.VecE.Reserve) (needA := Needs.VerifierRv64.Bump.AsGlobalAlloc.Alloc)
    (needH := Needs.Alloc.RawVec.HandleError) (by decide) (by decide) (by decide)
    (AllocT.reserveE env hnext hend) (RuntimeT.alloc env hnext hend) (RuntimeT.handleError env)

/-- `novel_basis`. -/
theorem novelBasis (hd : FieldT.ClmulTable env)
    (hnext : VerifierRv64.Bump.AsGlobalAlloc.Alloc.link.d_NEXT.addr = env.nextAddr)
    (hend : env.heapEnd = 0x78000000#64) :
    NovelBasisT.specT env (liftProg fns) Idx.Verifier.Whir.NovelBasis Needs.Verifier.Whir.NovelBasis :=
  NovelBasisT.total env _ _ _ Verifier.Whir.NovelBasis.tmpl_eq Verifier.Whir.NovelBasis.wf
    (needR := Needs.Alloc.Vec.VecK.Reserve) (needA := Needs.VerifierRv64.Bump.AsGlobalAlloc.Alloc)
    (needH := Needs.Alloc.RawVec.HandleError) (needB := Needs.Verifier.Field.BaseMul) (needM := Needs.Memcpy)
    (needP := Needs.Core.Panicking.PanicNounwindFmt) (needQ := Needs.Core.Panicking.PanicFmt)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (AllocT.reserveK env hnext hend) (RuntimeT.alloc env hnext hend) (RuntimeT.handleError env)
    (FieldT.baseMul env hd) (CopyUseT.memcpy env) (RuntimeT.panicNounwindFmt env) (RuntimeT.panicFmt env)

end Rv64mc.Table.WhirT6b

/-- info: 'Rv64mc.Table.WhirT6b.sampleQueries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.WhirT6b.sampleQueries

/-- info: 'Rv64mc.Table.WhirT6b.subspaceAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.WhirT6b.subspaceAt

/-- info: 'Rv64mc.Table.WhirT6b.extRow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.WhirT6b.extRow

/-- info: 'Rv64mc.Table.WhirT6b.novelBasis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.WhirT6b.novelBasis
