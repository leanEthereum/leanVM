/-
  Rv64mc.Table.MultilinearT

  The total contracts of the multilinear functions at the image (`liftProg Gen.fns`), the total counterpart of
  `Multilinear.lean`, with `ring_psi` and `Scaled::mul`, which only these call: each function's total theorem at its
  index, with the generated link, the stack `Gen.Needs` gives (a caller's bound over its callee's by `decide`), and
  its callees' total theorems (`FieldT`, `RuntimeT`). Left as a hypothesis: `clmul_low`'s constant table in the
  image's static data (`FieldT.ClmulTable`), an environment fact, for the functions that multiply.

  ## Main results

  * `polyEval`, `ringPsi`, `indexMle`, `paddingWeight`, `dot`, `eqEval`, `scaledMul`, `scalerMul`
-/

import Rv64mc.Table.FieldT
import Rv64mc.Table.RuntimeT
import Rv64mc.Proof.Multilinear.PolyEvalT
import Rv64mc.Proof.Whir.RingPsiT
import Rv64mc.Proof.Multilinear.IndexMleT
import Rv64mc.Proof.Multilinear.PaddingWeightT
import Rv64mc.Proof.Multilinear.DotT
import Rv64mc.Proof.Multilinear.EqEvalT
import Rv64mc.Proof.Field.ScaledMulT
import Rv64mc.Proof.Multilinear.ScalerMulT
import Rv64mc.Gen.Link.Verifier.Multilinear
import Rv64mc.Gen.Link.Verifier.RingSwitch

namespace Rv64mc.Table.MultilinearT

open MachineChecked.RiscV.Lift Rv64mc.Gen Rv64mc.Proof.Multilinear Rv64mc.Proof.Field Rv64mc.Proof.Whir

variable (env : Env)

theorem scaledMul :
    ScaledMulT.mulSpecT env (liftProg fns) Idx.Verifier.Field.Scaled.Mul Needs.Verifier.Field.Scaled.Mul :=
  ScaledMulT.total env _ _ _ Verifier.Field.Scaled.Mul.tmpl_eq Verifier.Field.Scaled.Mul.wf (by decide)
    (RuntimeT.panicBoundsCheck env)

section
variable (hd : FieldT.ClmulTable env)
include hd

theorem polyEval :
    PolyEvalT.specT env (liftProg fns) Idx.Verifier.Multilinear.PolyEval Needs.Verifier.Multilinear.PolyEval :=
  PolyEvalT.total env _ _ _ Verifier.Multilinear.PolyEval.tmpl_eq Verifier.Multilinear.PolyEval.wf (by decide)
    (FieldT.eMul env hd)

theorem ringPsi : RingPsiT.specT env (liftProg fns) Idx.Verifier.RingSwitch.RingPsi Needs.Verifier.RingSwitch.RingPsi :=
  RingPsiT.total env _ _ _ Verifier.RingSwitch.RingPsi.tmpl_eq Verifier.RingSwitch.RingPsi.wf (by decide) (by decide)
    (FieldT.eMul env hd) (FieldT.eSquare env)

theorem indexMle :
    IndexMleT.specT env (liftProg fns) Idx.Verifier.Multilinear.IndexMle Needs.Verifier.Multilinear.IndexMle :=
  IndexMleT.total env _ _ _ Verifier.Multilinear.IndexMle.tmpl_eq Verifier.Multilinear.IndexMle.wf (by decide)
    (by decide) (FieldT.eMul env hd) (FieldT.eSquare env)

theorem paddingWeight :
    PaddingWeightT.specT env (liftProg fns) Idx.Verifier.Multilinear.PaddingWeight
      Needs.Verifier.Multilinear.PaddingWeight :=
  PaddingWeightT.total env _ _ _ Verifier.Multilinear.PaddingWeight.tmpl_eq Verifier.Multilinear.PaddingWeight.wf
    (by decide) (FieldT.eMul env hd)

theorem dot : DotT.specT env (liftProg fns) Idx.Verifier.Multilinear.Dot Needs.Verifier.Multilinear.Dot :=
  DotT.total env _ _ _ Verifier.Multilinear.Dot.tmpl_eq Verifier.Multilinear.Dot.wf (by decide) (by decide)
    (FieldT.eMul env hd) (RuntimeT.assertFailedUsizeUsize env)

theorem eqEval : EqEvalT.specT env (liftProg fns) Idx.Verifier.Multilinear.EqEval Needs.Verifier.Multilinear.EqEval :=
  EqEvalT.total env _ _ _ Verifier.Multilinear.EqEval.tmpl_eq Verifier.Multilinear.EqEval.wf (by decide) (by decide)
    (FieldT.eMul env hd) (RuntimeT.assertFailedUsizeUsize env)

theorem scalerMul :
    ScalerMulT.mulSpecT env (liftProg fns) Idx.Verifier.Multilinear.Scaler.Mul Needs.Verifier.Multilinear.Scaler.Mul :=
  ScalerMulT.total env _ _ _ Verifier.Multilinear.Scaler.Mul.tmpl_eq Verifier.Multilinear.Scaler.Mul.wf (by decide)
    (by decide) (scaledMul env) (FieldT.eMul env hd)

end

end Rv64mc.Table.MultilinearT

/-- info: 'Rv64mc.Table.MultilinearT.scaledMul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.MultilinearT.scaledMul

/-- info: 'Rv64mc.Table.MultilinearT.polyEval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.MultilinearT.polyEval

/-- info: 'Rv64mc.Table.MultilinearT.ringPsi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.MultilinearT.ringPsi

/-- info: 'Rv64mc.Table.MultilinearT.indexMle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.MultilinearT.indexMle

/-- info: 'Rv64mc.Table.MultilinearT.paddingWeight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.MultilinearT.paddingWeight

/-- info: 'Rv64mc.Table.MultilinearT.dot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.MultilinearT.dot

/-- info: 'Rv64mc.Table.MultilinearT.eqEval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.MultilinearT.eqEval

/-- info: 'Rv64mc.Table.MultilinearT.scalerMul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.MultilinearT.scalerMul
