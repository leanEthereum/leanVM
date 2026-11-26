/-
  Rv64mc.Table.TranscriptT3

  The transcript chain's total contracts at the image (`liftProg Gen.fns`), next to `TranscriptT2.lean`: each
  function's total theorem at its index, with the generated link, the stack `Gen.Needs` gives (a caller's bound over
  its callee's by `decide`), and its callees' total theorems. Left as a hypothesis: `keccak_f`'s constant tables in
  the image's static data (`HashT.KeccakTables`), and for `samples` the allocator's two facts (`NEXT`'s data reference
  and the heap's end), environment facts.

  ## Main results

  * `spongeNew`, `absorb`, `sample`, `absorbNonce`, `nextSafe`, `transcriptNew`, `nextScalar`, `grindCheck`, `samples`
-/

import Rv64mc.Table.HashT
import Rv64mc.Table.VecT
import Rv64mc.Table.CopyUseT
import Rv64mc.Proof.Transcript.SpongeNewT
import Rv64mc.Proof.Transcript.AbsorbT
import Rv64mc.Proof.Transcript.SampleT
import Rv64mc.Proof.Transcript.AbsorbNonceT
import Rv64mc.Proof.Transcript.NextSafeT
import Rv64mc.Proof.Transcript.TranscriptNewT
import Rv64mc.Proof.Transcript.NextScalarT
import Rv64mc.Proof.Transcript.GrindCheckT
import Rv64mc.Proof.Transcript.SamplesT
import Rv64mc.Table.AllocT
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

theorem sample (hd : HashT.KeccakTables env) :
    SampleT.specT env (liftProg fns) Idx.Verifier.Transcript.Sponge.Sample Needs.Verifier.Transcript.Sponge.Sample :=
  SampleT.total env _ _ _ Verifier.Transcript.Sponge.Sample.tmpl_eq Verifier.Transcript.Sponge.Sample.wf (by decide)
    (TranscriptT2.duplex env hd)

theorem absorbNonce (hd : HashT.KeccakTables env) :
    AbsorbNonceT.specT env (liftProg fns) Idx.Verifier.Transcript.Sponge.AbsorbNonce
      Needs.Verifier.Transcript.Sponge.AbsorbNonce :=
  AbsorbNonceT.total env _ _ _ Verifier.Transcript.Sponge.AbsorbNonce.tmpl_eq
    Verifier.Transcript.Sponge.AbsorbNonce.wf (by decide) (by decide) (absorb env hd) (TranscriptT2.duplex env hd)

/-- `Transcript::next`'s second total contract (`NextSafeT`), beside `Table.TranscriptT.next`. -/
theorem nextSafe :
    NextSafeT.specT env (liftProg fns) Idx.Verifier.Transcript.Transcript.Next
      Needs.Verifier.Transcript.Transcript.Next :=
  NextSafeT.total env _ _ _ Verifier.Transcript.Transcript.Next.tmpl_eq _

theorem transcriptNew (hd : HashT.KeccakTables env) :
    TranscriptNewT.specT env (liftProg fns) Idx.Verifier.Transcript.Transcript.New
      Needs.Verifier.Transcript.Transcript.New :=
  TranscriptNewT.total env _ _ _ Verifier.Transcript.Transcript.New.tmpl_eq Verifier.Transcript.Transcript.New.wf
    (by decide) (spongeNew env hd)

theorem nextScalar (hd : HashT.KeccakTables env) :
    NextScalarT.specT env (liftProg fns) Idx.Verifier.Transcript.Transcript.NextScalar
      Needs.Verifier.Transcript.Transcript.NextScalar :=
  NextScalarT.total env _ _ _ Verifier.Transcript.Transcript.NextScalar.tmpl_eq
    Verifier.Transcript.Transcript.NextScalar.wf (by decide) (by decide) (nextSafe env) (absorb env hd)

theorem grindCheck (hd : HashT.KeccakTables env) :
    GrindCheckT.specT env (liftProg fns) Idx.Verifier.Transcript.Transcript.GrindCheck
      Needs.Verifier.Transcript.Transcript.GrindCheck :=
  GrindCheckT.total env _ _ _ Verifier.Transcript.Transcript.GrindCheck.tmpl_eq
    Verifier.Transcript.Transcript.GrindCheck.wf (by decide) (by decide) (nextSafe env) (absorbNonce env hd)

theorem samples (hd : HashT.KeccakTables env)
    (hnext : VerifierRv64.Bump.AsGlobalAlloc.Alloc.link.d_NEXT.addr = env.nextAddr)
    (hend : env.heapEnd = 0x78000000#64) :
    SamplesT.specT env (liftProg fns) Idx.Verifier.Transcript.Transcript.Samples
      Needs.Verifier.Transcript.Transcript.Samples :=
  SamplesT.total env _ _ _ Verifier.Transcript.Transcript.Samples.tmpl_eq Verifier.Transcript.Transcript.Samples.wf
    (by decide) (by decide) (by decide) (by decide) (RuntimeT.alloc env hnext hend) (AllocT.reserveE env hnext hend)
    (RuntimeT.handleError env) (sample env hd)

end Rv64mc.Table.TranscriptT3

/-- info: 'Rv64mc.Table.TranscriptT3.spongeNew' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.TranscriptT3.spongeNew

/-- info: 'Rv64mc.Table.TranscriptT3.absorb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.TranscriptT3.absorb

/-- info: 'Rv64mc.Table.TranscriptT3.sample' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.TranscriptT3.sample

/-- info: 'Rv64mc.Table.TranscriptT3.absorbNonce' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.TranscriptT3.absorbNonce

/-- info: 'Rv64mc.Table.TranscriptT3.nextSafe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.TranscriptT3.nextSafe

/-- info: 'Rv64mc.Table.TranscriptT3.transcriptNew' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.TranscriptT3.transcriptNew

/-- info: 'Rv64mc.Table.TranscriptT3.nextScalar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.TranscriptT3.nextScalar

/-- info: 'Rv64mc.Table.TranscriptT3.grindCheck' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.TranscriptT3.grindCheck

/-- info: 'Rv64mc.Table.TranscriptT3.samples' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.TranscriptT3.samples
