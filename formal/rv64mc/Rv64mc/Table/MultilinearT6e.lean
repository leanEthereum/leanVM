/-
  Rv64mc.Table.MultilinearT6e

  The multilinear leaves' second total contracts at the image (`liftProg Gen.fns`), next to `MultilinearT.lean`'s
  first ones: over slices none or owned by the caller (`OwnSliceT.OwnSlice`), with the generated link, the stack
  `Gen.Needs` gives and their callees' total theorems (`FieldT`, `RuntimeT`); and `Placement::eq_above` over
  `eqEvalOwn` and `MultilinearT2.selectorPoint`. Left as hypotheses: `clmul_low`'s constant in the image's static data
  (`FieldT.ClmulTable`), and for `eq_above` the allocator's two facts about the image (`NEXT`'s data reference,
  the heap's end), environment facts.

  ## Main results

  * `eqEvalOwn`, `polyEvalOwn`, `indexMleOwn`, `paddingWeightOwn`, `ringPsiOwn`, `eqAbove`
-/

import Rv64mc.Table.FieldT
import Rv64mc.Table.RuntimeT
import Rv64mc.Table.MultilinearT2
import Rv64mc.Proof.Multilinear.EqAboveT
import Rv64mc.Proof.Multilinear.EqEvalOwnT
import Rv64mc.Proof.Multilinear.PolyEvalOwnT
import Rv64mc.Proof.Multilinear.IndexMleOwnT
import Rv64mc.Proof.Multilinear.PaddingWeightOwnT
import Rv64mc.Proof.Whir.RingPsiOwnT
import Rv64mc.Gen.Link.Verifier.Multilinear
import Rv64mc.Gen.Link.Verifier.RingSwitch

namespace Rv64mc.Table.MultilinearT6e

open MachineChecked.RiscV.Lift Rv64mc.Gen Rv64mc.Proof.Multilinear Rv64mc.Proof.Whir

variable (env : Env)

section
variable (hd : FieldT.ClmulTable env)
include hd

theorem eqEvalOwn :
    EqEvalOwnT.specT env (liftProg fns) Idx.Verifier.Multilinear.EqEval Needs.Verifier.Multilinear.EqEval :=
  EqEvalOwnT.total env _ _ _ Verifier.Multilinear.EqEval.tmpl_eq Verifier.Multilinear.EqEval.wf (by decide)
    (by decide) (FieldT.eMul env hd) (RuntimeT.assertFailedUsizeUsize env)

theorem polyEvalOwn :
    PolyEvalOwnT.specT env (liftProg fns) Idx.Verifier.Multilinear.PolyEval Needs.Verifier.Multilinear.PolyEval :=
  PolyEvalOwnT.total env _ _ _ Verifier.Multilinear.PolyEval.tmpl_eq Verifier.Multilinear.PolyEval.wf (by decide)
    (FieldT.eMul env hd)

theorem indexMleOwn :
    IndexMleOwnT.specT env (liftProg fns) Idx.Verifier.Multilinear.IndexMle Needs.Verifier.Multilinear.IndexMle :=
  IndexMleOwnT.total env _ _ _ Verifier.Multilinear.IndexMle.tmpl_eq Verifier.Multilinear.IndexMle.wf (by decide)
    (by decide) (FieldT.eMul env hd) (FieldT.eSquare env)

theorem paddingWeightOwn :
    PaddingWeightOwnT.specT env (liftProg fns) Idx.Verifier.Multilinear.PaddingWeight
      Needs.Verifier.Multilinear.PaddingWeight :=
  PaddingWeightOwnT.total env _ _ _ Verifier.Multilinear.PaddingWeight.tmpl_eq
    Verifier.Multilinear.PaddingWeight.wf (by decide) (FieldT.eMul env hd)

theorem ringPsiOwn :
    RingPsiOwnT.specT env (liftProg fns) Idx.Verifier.RingSwitch.RingPsi Needs.Verifier.RingSwitch.RingPsi :=
  RingPsiOwnT.total env _ _ _ Verifier.RingSwitch.RingPsi.tmpl_eq Verifier.RingSwitch.RingPsi.wf (by decide)
    (by decide) (FieldT.eMul env hd) (FieldT.eSquare env)

end

/-- **`Placement::eq_above` at the image** (function 101). -/
theorem eqAbove (hd : FieldT.ClmulTable env) (hnext : VerifierRv64.Bump.AsGlobalAlloc.Alloc.link.d_NEXT.addr = env.nextAddr)
    (hend : env.heapEnd = 0x78000000#64) :
    EqAboveT.specT env (liftProg fns) Idx.Verifier.Multilinear.Placement.EqAbove
      Needs.Verifier.Multilinear.Placement.EqAbove :=
  EqAboveT.total env _ _ _ Verifier.Multilinear.Placement.EqAbove.tmpl_eq Verifier.Multilinear.Placement.EqAbove.wf
    (by decide) (by decide) (by decide) (MultilinearT2.selectorPoint env hnext hend) (eqEvalOwn env hd)
    (RuntimeT.sliceIndexFail env)

end Rv64mc.Table.MultilinearT6e

/-- info: 'Rv64mc.Table.MultilinearT6e.eqEvalOwn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.MultilinearT6e.eqEvalOwn

/-- info: 'Rv64mc.Table.MultilinearT6e.polyEvalOwn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.MultilinearT6e.polyEvalOwn

/-- info: 'Rv64mc.Table.MultilinearT6e.indexMleOwn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.MultilinearT6e.indexMleOwn

/-- info: 'Rv64mc.Table.MultilinearT6e.paddingWeightOwn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.MultilinearT6e.paddingWeightOwn

/-- info: 'Rv64mc.Table.MultilinearT6e.ringPsiOwn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.MultilinearT6e.ringPsiOwn

/-- info: 'Rv64mc.Table.MultilinearT6e.eqAbove' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.MultilinearT6e.eqAbove
