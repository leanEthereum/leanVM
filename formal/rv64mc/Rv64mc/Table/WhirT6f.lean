/-
  Rv64mc.Table.WhirT6f

  Wave 6f's WHIR functions' total contracts at the image (`liftProg Gen.fns`): each function's total theorem at its
  index, with the generated link, the stack `Gen.Needs` gives (bounds over the callees' by `decide`), and the callees'
  total theorems (`WhirT6b.novelBasis`, `WhirT6b.extRow`, `SumT6f.eSumNovel`, `TranscriptT3.grindCheck`,
  `TranscriptT3.samples`, `WhirT6d.ringCoefficients`, `WhirT6d.ringTarget`, `WhirT6d.subspaceNew`,
  `WhirT6b.subspaceAt`, `FieldT.baseMul`, `FieldT.eMul`). Open: `clmul_low`'s table
  (`FieldT.ClmulTable`), the keccak tables (`HashT.KeccakTables`), `NEXT`'s data reference and the heap's end
  (`env`): environment facts.

  ## Main results

  * `novelEval`, `ringSwitch`, `lanesOf`, `inducedWeight`
-/

import Rv64mc.Table.WhirT6b
import Rv64mc.Table.WhirT6d
import Rv64mc.Table.TranscriptT3
import Rv64mc.Table.SumT6f
import Rv64mc.Proof.Whir.NovelEvalT
import Rv64mc.Proof.Whir.RingSwitchT
import Rv64mc.Proof.Whir.LanesOfT
import Rv64mc.Proof.Whir.InducedWeightT
import Rv64mc.Gen.Link.Verifier.Whir
import Rv64mc.Gen.Link.Verifier.RingSwitch

namespace Rv64mc.Table.WhirT6f

open MachineChecked.RiscV.Lift Rv64mc.Gen Rv64mc.Proof.Whir

variable (env : Env)

/-- `novel_eval` (80). -/
theorem novelEval (hd : FieldT.ClmulTable env)
    (hnext : VerifierRv64.Bump.AsGlobalAlloc.Alloc.link.d_NEXT.addr = env.nextAddr)
    (hend : env.heapEnd = 0x78000000#64) :
    NovelEvalT.specT env (liftProg fns) Idx.Verifier.Whir.NovelEval Needs.Verifier.Whir.NovelEval :=
  NovelEvalT.total env _ _ _ Verifier.Whir.NovelEval.tmpl_eq Verifier.Whir.NovelEval.wf (by decide) (by decide)
    (WhirT6b.novelBasis env hd hnext hend) (SumT6f.eSumNovel env hd)

/-- `ring_switch` (61). -/
theorem ringSwitch (hd : FieldT.ClmulTable env) (hk : HashT.KeccakTables env)
    (hnext : VerifierRv64.Bump.AsGlobalAlloc.Alloc.link.d_NEXT.addr = env.nextAddr)
    (hend : env.heapEnd = 0x78000000#64) :
    RingSwitchT.specT env (liftProg fns) Idx.Verifier.RingSwitch.RingSwitch Needs.Verifier.RingSwitch.RingSwitch :=
  RingSwitchT.total env _ _ _ Verifier.RingSwitch.RingSwitch.tmpl_eq Verifier.RingSwitch.RingSwitch.wf
    (needG := Needs.Verifier.Transcript.Transcript.GrindCheck) (needS := Needs.Verifier.Transcript.Transcript.Samples)
    (needC := Needs.Verifier.RingSwitch.RingCoefficients) (needT := Needs.Verifier.RingSwitch.RingTarget)
    (by decide) (by decide) (by decide) (by decide) (TranscriptT3.grindCheck env hk)
    (TranscriptT3.samples env hk hnext hend) (WhirT6d.ringCoefficients env hd hnext hend)
    (WhirT6d.ringTarget env hd hnext hend)

/-- `verify_whir`'s closure `lanes_of` (86). -/
theorem lanesOf (hnext : VerifierRv64.Bump.AsGlobalAlloc.Alloc.link.d_NEXT.addr = env.nextAddr)
    (hend : env.heapEnd = 0x78000000#64) :
    LanesOfT.specT env (liftProg fns) Idx.Verifier.Whir.VerifyWhirVerifyStackedOpeningClosure1.Closure0
      Needs.Verifier.Whir.VerifyWhirVerifyStackedOpeningClosure1.Closure0 :=
  LanesOfT.total env _ _ _ Verifier.Whir.VerifyWhirVerifyStackedOpeningClosure1.Closure0.tmpl_eq
    Verifier.Whir.VerifyWhirVerifyStackedOpeningClosure1.Closure0.wf
    (needE := Needs.Verifier.Whir.ExtRow) (needR := Needs.Alloc.Vec.VecE.Reserve)
    (needA := Needs.VerifierRv64.Bump.AsGlobalAlloc.Alloc) (needH := Needs.Alloc.RawVec.HandleError)
    (by decide) (by decide) (by decide) (by decide) (WhirT6b.extRow env hnext hend) (AllocT.reserveE env hnext hend)
    (RuntimeT.alloc env hnext hend) (RuntimeT.handleError env)

/-- `induced_weight` (97). -/
theorem inducedWeight (hd : FieldT.ClmulTable env)
    (hnext : VerifierRv64.Bump.AsGlobalAlloc.Alloc.link.d_NEXT.addr = env.nextAddr)
    (hend : env.heapEnd = 0x78000000#64) :
    InducedWeightT.specT env (liftProg fns) Idx.Verifier.Whir.InducedWeight Needs.Verifier.Whir.InducedWeight :=
  InducedWeightT.total env _ _ _ Verifier.Whir.InducedWeight.tmpl_eq Verifier.Whir.InducedWeight.wf
    (needN := Needs.Verifier.Whir.Subspace.New) (needA := Needs.Verifier.Whir.Subspace.At)
    (needB := Needs.Verifier.Field.BaseMul) (needU := Needs.Verifier.Field.E.AsMul.Mul)
    (by decide) (by decide) (by decide) (by decide) (WhirT6d.subspaceNew env hd hnext hend)
    (WhirT6b.subspaceAt env hd hnext hend) (FieldT.baseMul env hd) (FieldT.eMul env hd)

end Rv64mc.Table.WhirT6f

/-- info: 'Rv64mc.Table.WhirT6f.novelEval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.WhirT6f.novelEval

/-- info: 'Rv64mc.Table.WhirT6f.ringSwitch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.WhirT6f.ringSwitch

/-- info: 'Rv64mc.Table.WhirT6f.lanesOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.WhirT6f.lanesOf

/-- info: 'Rv64mc.Table.WhirT6f.inducedWeight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.WhirT6f.inducedWeight
