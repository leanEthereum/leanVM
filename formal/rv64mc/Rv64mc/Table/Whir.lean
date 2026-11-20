/-
  Rv64mc.Table.Whir

  The WHIR family's contracts at the image (`liftProg Gen.fns`): each `ok` at its function's index, with the
  generated link (`Gen.….link`, `tmpl_eq`, `wf`) and the stack each needs (`Gen.Needs`, a caller's bound over its
  callee's checked by `decide`), from the field's contracts (`Table.Field`) and what is not proved yet: `clmul_low`'s
  constant (`DataRef.Words`, as in `Table.Field`), `WHIR_QUERIES` (`Spec.Whir.WhirQueries.Table`, its slice headers
  and their arrays in the image's `env.data`), the panic chain's `assert_failed`, and the callees not proved
  (`induced_weight`, `ring_weight`, `Placement::eq_above`, `slice_index_fail`).
-/

import Rv64mc.Table.Field
import Rv64mc.Proof.Whir.WhirQueries
import Rv64mc.Proof.Whir.Frobenius8
import Rv64mc.Proof.Whir.RingPsi
import Rv64mc.Proof.Whir.GluedWeightEvaluate
import Rv64mc.Proof.Whir.RingWeightEvaluate
import Rv64mc.Proof.Whir.StackWeightEvaluate
import Rv64mc.Gen.Link.Verifier.Whir.WhirQueries
import Rv64mc.Gen.Link.Verifier.RingSwitch.Frobenius8
import Rv64mc.Gen.Link.Verifier.RingSwitch.RingPsi
import Rv64mc.Gen.Link.Verifier.Whir.GluedWeight.Evaluate
import Rv64mc.Gen.Link.Verifier.RingSwitch.RingWeight.Evaluate
import Rv64mc.Gen.Link.Verifier.StackWeight.Evaluate

namespace Rv64mc.Table.Whir

open MachineChecked.RiscV.Lift Rv64mc.Gen

variable (env : Env)

theorem whirQueries (htab : Spec.Whir.WhirQueries.Table env Verifier.Whir.WhirQueries.link.d_c960_dba1010e.addr) :
    Spec.Whir.WhirQueries.spec env (liftProg fns) Idx.Verifier.Whir.WhirQueries Needs.Verifier.Whir.WhirQueries :=
  Proof.Whir.WhirQueries.ok env _ Idx.Verifier.Whir.WhirQueries _ Verifier.Whir.WhirQueries.tmpl_eq Verifier.Whir.WhirQueries.wf htab

theorem frobenius8 : Spec.Whir.Frobenius8.spec env (liftProg fns) Idx.Verifier.RingSwitch.Frobenius8 Needs.Verifier.RingSwitch.Frobenius8 :=
  Proof.Whir.Frobenius8.ok env _ Idx.Verifier.RingSwitch.Frobenius8 _ Verifier.RingSwitch.Frobenius8.tmpl_eq Verifier.RingSwitch.Frobenius8.wf
    (by decide) (Table.Field.eSquare env)

theorem ringPsi
    (hd : DataRef.Words env Verifier.Field.ClmulLow.link.d_c8_d07a1b83 Verifier.Field.ClmulLow.d_c8_d07a1b83_words) :
    Spec.Whir.RingPsi.spec env (liftProg fns) Idx.Verifier.RingSwitch.RingPsi Needs.Verifier.RingSwitch.RingPsi :=
  Proof.Whir.RingPsi.ok env _ Idx.Verifier.RingSwitch.RingPsi _ Verifier.RingSwitch.RingPsi.tmpl_eq Verifier.RingSwitch.RingPsi.wf (by decide)
    (by decide) (Table.Field.eMul env hd) (Table.Field.eSquare env)

theorem gluedWeightEvaluate
    (hd : DataRef.Words env Verifier.Field.ClmulLow.link.d_c8_d07a1b83 Verifier.Field.ClmulLow.d_c8_d07a1b83_words)
    (hfail : Spec.Runtime.NoReturn env (liftProg fns) Idx.Core.Panicking.AssertFailedUsizeUsize Needs.Core.Panicking.AssertFailedUsizeUsize)
    (hiw : Spec.Whir.InducedWeight.spec env (liftProg fns) Idx.Verifier.Whir.InducedWeight Needs.Verifier.Whir.InducedWeight) :
    Spec.Whir.GluedWeightEvaluate.spec env (liftProg fns) Idx.Verifier.Whir.GluedWeight.Evaluate Needs.Verifier.Whir.GluedWeight.Evaluate :=
  Proof.Whir.GluedWeightEvaluate.ok env _ Idx.Verifier.Whir.GluedWeight.Evaluate _ Verifier.Whir.GluedWeight.Evaluate.tmpl_eq
    Verifier.Whir.GluedWeight.Evaluate.wf (by decide) (by decide) hiw (Table.Field.eqEval env hd hfail)

theorem ringWeightEvaluate
    (hrw : Spec.Whir.RingWeight.spec env (liftProg fns) Idx.Verifier.RingSwitch.RingWeight Needs.Verifier.RingSwitch.RingWeight) :
    Spec.Whir.RingWeight.evaluateSpec env (liftProg fns) Idx.Verifier.RingSwitch.RingWeight.Evaluate Needs.Verifier.RingSwitch.RingWeight.Evaluate :=
  Proof.Whir.RingWeightEvaluate.ok env _ Idx.Verifier.RingSwitch.RingWeight.Evaluate _ Verifier.RingSwitch.RingWeight.Evaluate.tmpl_eq
    Verifier.RingSwitch.RingWeight.Evaluate.wf (by decide) hrw

theorem stackWeightEvaluate
    (hd : DataRef.Words env Verifier.Field.ClmulLow.link.d_c8_d07a1b83 Verifier.Field.ClmulLow.d_c8_d07a1b83_words)
    (hfail : Spec.Runtime.NoReturn env (liftProg fns) Idx.Core.Panicking.AssertFailedUsizeUsize Needs.Core.Panicking.AssertFailedUsizeUsize)
    (hslice : Spec.Runtime.NoReturn env (liftProg fns) Idx.Core.Slice.Index.SliceIndexFail Needs.Core.Slice.Index.SliceIndexFail)
    (hrw : Spec.Whir.RingWeight.spec env (liftProg fns) Idx.Verifier.RingSwitch.RingWeight Needs.Verifier.RingSwitch.RingWeight)
    (hea : Spec.Multilinear.EqAbove.spec env (liftProg fns) Idx.Verifier.Multilinear.Placement.EqAbove Needs.Verifier.Multilinear.Placement.EqAbove) :
    Spec.Whir.StackWeight.spec env (liftProg fns) Idx.Verifier.StackWeight.Evaluate Needs.Verifier.StackWeight.Evaluate :=
  Proof.Whir.StackWeightEvaluate.ok env _ Idx.Verifier.StackWeight.Evaluate _ Verifier.StackWeight.Evaluate.tmpl_eq Verifier.StackWeight.Evaluate.wf
    (by decide) (by decide) (by decide) (by decide) (by decide) (ringWeightEvaluate env hrw)
    (Table.Field.eqEval env hd hfail) hea (Table.Field.eMul env hd) hslice

end Rv64mc.Table.Whir

/-- info: 'Rv64mc.Table.Whir.gluedWeightEvaluate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.Whir.gluedWeightEvaluate

/-- info: 'Rv64mc.Table.Whir.stackWeightEvaluate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.Whir.stackWeightEvaluate
