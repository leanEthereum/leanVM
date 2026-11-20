/-
  Rv64mc.Table.Transcript

  The transcript's contracts at the image (`liftProg Gen.fns`): each `ok` at its function's index, with the
  generated link (`Gen.….link`, `tmpl_eq`, `wf`) and the stack each needs (`Gen.Needs`, each bound by `decide`),
  from the runtime's table and, where a callee is not proved at the image yet (`compiler_builtins`' `memcpy` and
  `memset`, `keccak_f`, `Sponge::new`, `alloc`, `Vec::reserve`), its contract as a hypothesis. The indices are the generator's (`Rv64mc/Gen/index.tsv`).
-/

import Rv64mc.Proof.Transcript.Next
import Rv64mc.Proof.Transcript.Finish
import Rv64mc.Proof.Transcript.Absorb
import Rv64mc.Proof.Transcript.Sample
import Rv64mc.Proof.Transcript.AbsorbNonce
import Rv64mc.Proof.Transcript.NextScalar
import Rv64mc.Proof.Transcript.GrindCheck
import Rv64mc.Proof.Transcript.GrindingBits
import Rv64mc.Proof.Transcript.New
import Rv64mc.Proof.Transcript.Duplex
import Rv64mc.Proof.Transcript.Samples
import Rv64mc.Gen.Link.Verifier.Transcript.Transcript.Samples
import Rv64mc.Gen.Link.Verifier.Transcript.Sponge.Duplex
import Rv64mc.Table.Runtime
import Rv64mc.Gen.Needs
import Rv64mc.Gen.Link.Verifier.Transcript.Transcript.Next
import Rv64mc.Gen.Link.Verifier.Transcript.Transcript.Finish
import Rv64mc.Gen.Link.Verifier.Transcript.Sponge.Absorb
import Rv64mc.Gen.Link.Verifier.Transcript.Sponge.Sample
import Rv64mc.Gen.Link.Verifier.Transcript.Sponge.AbsorbNonce
import Rv64mc.Gen.Link.Verifier.Transcript.Transcript.NextScalar
import Rv64mc.Gen.Link.Verifier.Transcript.Transcript.GrindCheck
import Rv64mc.Gen.Link.Verifier.Transcript.GrindingBits
import Rv64mc.Gen.Link.Verifier.Transcript.Transcript.New

namespace Rv64mc.Table.Transcript

open MachineChecked.RiscV.Lift Rv64mc.Gen

variable (env : Env)

theorem next : Spec.Transcript.Next.spec env (liftProg fns) Idx.Verifier.Transcript.Transcript.Next Needs.Verifier.Transcript.Transcript.Next :=
  Proof.Transcript.Next.ok env _ Idx.Verifier.Transcript.Transcript.Next _ Verifier.Transcript.Transcript.Next.tmpl_eq
    Verifier.Transcript.Transcript.Next.wf

theorem finish : Spec.Transcript.Finish.spec env (liftProg fns) Idx.Verifier.Transcript.Transcript.Finish Needs.Verifier.Transcript.Transcript.Finish :=
  Proof.Transcript.Finish.ok env _ Idx.Verifier.Transcript.Transcript.Finish _ Verifier.Transcript.Transcript.Finish.tmpl_eq
    Verifier.Transcript.Transcript.Finish.wf

theorem grindingBits :
    Spec.Transcript.GrindingBits.spec env (liftProg fns) Idx.Verifier.Transcript.GrindingBits Needs.Verifier.Transcript.GrindingBits :=
  Proof.Transcript.GrindingBits.ok env _ Idx.Verifier.Transcript.GrindingBits _ Verifier.Transcript.GrindingBits.tmpl_eq
    Verifier.Transcript.GrindingBits.wf

section Duplex

variable (hcb : Spec.Runtime.MemcpySpec env (liftProg fns) Idx.CompilerBuiltins.Mem.Memcpy Needs.CompilerBuiltins.Mem.Memcpy)
  (hsb : Spec.Runtime.MemsetSpec env (liftProg fns) Idx.CompilerBuiltins.Mem.Memset Needs.CompilerBuiltins.Mem.Memset)
  (hkf : Spec.Hash.KeccakF.spec env (liftProg fns) Idx.Verifier.Hash.KeccakF Needs.Verifier.Hash.KeccakF)
include hcb hsb hkf

theorem duplex : Spec.Transcript.Duplex.spec env (liftProg fns) Idx.Verifier.Transcript.Sponge.Duplex Needs.Verifier.Transcript.Sponge.Duplex :=
  Proof.Transcript.Duplex.ok env _ Idx.Verifier.Transcript.Sponge.Duplex _ Verifier.Transcript.Sponge.Duplex.tmpl_eq
    Verifier.Transcript.Sponge.Duplex.wf (by decide) (by decide) (by decide) (by decide)
    (Table.Runtime.memcpy env hcb) (Table.Runtime.memset env hsb) hkf (Table.Runtime.sliceIndexFail env)

theorem absorb : Spec.Transcript.Absorb.spec env (liftProg fns) Idx.Verifier.Transcript.Sponge.Absorb Needs.Verifier.Transcript.Sponge.Absorb :=
  Proof.Transcript.Absorb.ok env _ Idx.Verifier.Transcript.Sponge.Absorb _ Verifier.Transcript.Sponge.Absorb.tmpl_eq
    Verifier.Transcript.Sponge.Absorb.wf (by decide) (by decide) (by decide) (duplex env hcb hsb hkf) (Table.Runtime.panicFmt env)
    (Table.Runtime.panicBoundsCheck env)

theorem sample : Spec.Transcript.Sample.spec env (liftProg fns) Idx.Verifier.Transcript.Sponge.Sample Needs.Verifier.Transcript.Sponge.Sample :=
  Proof.Transcript.Sample.ok env _ Idx.Verifier.Transcript.Sponge.Sample _ Verifier.Transcript.Sponge.Sample.tmpl_eq
    Verifier.Transcript.Sponge.Sample.wf (by decide) (duplex env hcb hsb hkf)

theorem absorbNonce :
    Spec.Transcript.AbsorbNonce.spec env (liftProg fns) Idx.Verifier.Transcript.Sponge.AbsorbNonce Needs.Verifier.Transcript.Sponge.AbsorbNonce :=
  Proof.Transcript.AbsorbNonce.ok env _ Idx.Verifier.Transcript.Sponge.AbsorbNonce _ Verifier.Transcript.Sponge.AbsorbNonce.tmpl_eq
    Verifier.Transcript.Sponge.AbsorbNonce.wf (by decide) (by decide) (absorb env hcb hsb hkf) (duplex env hcb hsb hkf)

theorem nextScalar :
    Spec.Transcript.NextScalar.spec env (liftProg fns) Idx.Verifier.Transcript.Transcript.NextScalar Needs.Verifier.Transcript.Transcript.NextScalar :=
  Proof.Transcript.NextScalar.ok env _ Idx.Verifier.Transcript.Transcript.NextScalar _ Verifier.Transcript.Transcript.NextScalar.tmpl_eq
    Verifier.Transcript.Transcript.NextScalar.wf (by decide) (by decide) (next env) (absorb env hcb hsb hkf)

theorem grindCheck :
    Spec.Transcript.GrindCheck.spec env (liftProg fns) Idx.Verifier.Transcript.Transcript.GrindCheck Needs.Verifier.Transcript.Transcript.GrindCheck :=
  Proof.Transcript.GrindCheck.ok env _ Idx.Verifier.Transcript.Transcript.GrindCheck _ Verifier.Transcript.Transcript.GrindCheck.tmpl_eq
    Verifier.Transcript.Transcript.GrindCheck.wf (by decide) (by decide) (next env) (absorbNonce env hcb hsb hkf)

theorem samples
    (hal : Spec.Runtime.AllocSpec env (liftProg fns) Idx.VerifierRv64.Bump.AsGlobalAlloc.Alloc
      Needs.VerifierRv64.Bump.AsGlobalAlloc.Alloc)
    (hres : Spec.Runtime.ReserveSpec env 8 16 (liftProg fns) Idx.Alloc.Vec.VecE.Reserve Needs.Alloc.Vec.VecE.Reserve) :
    Spec.Transcript.Samples.spec env (liftProg fns) 132 Needs.Verifier.Transcript.Transcript.Samples :=
  Proof.Transcript.Samples.ok env _ 132 _ Verifier.Transcript.Transcript.Samples.tmpl_eq
    Verifier.Transcript.Transcript.Samples.wf (by decide) (by decide) (by decide) (by decide) hal hres
    (Table.Runtime.handleError env) (sample env hcb hsb hkf)

end Duplex

theorem new (hsn : Spec.Transcript.SpongeNew.spec env (liftProg fns) Idx.Verifier.Transcript.Sponge.New Needs.Verifier.Transcript.Sponge.New) :
    Spec.Transcript.New.spec env (liftProg fns) Idx.Verifier.Transcript.Transcript.New Needs.Verifier.Transcript.Transcript.New :=
  Proof.Transcript.New.ok env _ Idx.Verifier.Transcript.Transcript.New _ Verifier.Transcript.Transcript.New.tmpl_eq
    Verifier.Transcript.Transcript.New.wf (by decide) hsn

end Rv64mc.Table.Transcript

/-- info: 'Rv64mc.Table.Transcript.grindCheck' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.Transcript.grindCheck

/-- info: 'Rv64mc.Table.Transcript.new' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.Transcript.new

/-- info: 'Rv64mc.Table.Transcript.grindingBits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.Transcript.grindingBits

/-- info: 'Rv64mc.Table.Transcript.samples' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.Transcript.samples
