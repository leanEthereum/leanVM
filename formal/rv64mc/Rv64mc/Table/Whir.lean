/-
  Rv64mc.Table.Whir

  The WHIR family's contracts at the image (`liftProg Gen.fns`): each `ok` at its function's index, with the
  generated link (`Gen.….link`, `tmpl_eq`, `wf`) and the stack each needs (`Gen.Needs`, a caller's bound over its
  callee's checked by `decide`), from the field's contracts (`Table.Field`) and what is not proved yet: `clmul_low`'s
  constant (`DataRef.Words`, as in `Table.Field`), the template's tables in the image's `env.data`
  (`DataRef.InData`: `WHIR_QUERIES`'s slice headers, each pointer the address of its row's array, a field of the
  link, and the arrays; `whirQueriesTable` checks them against `Model.whirQueriesTable` by evaluation), the panic
  chain's `assert_failed`, and the callees not proved (`induced_weight`, `ring_weight`, `Placement::eq_above`,
  `slice_index_fail`).
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

/-- What `whirQueriesTable` evaluates: every header's pointer not null, the header's words and its row's among the
    template's tables' (`DataRef.pairs`), the row's words `Model.whirQueriesTable`'s. -/
def tableCheck : Prop :=
  ∀ r (hr : r < Model.whirQueriesTable.length) c (hc : c < (Model.whirQueriesTable[r]).length),
    (Verifier.Whir.WhirQueries.d_c960_dba1010e_words Verifier.Whir.WhirQueries.link).getD (30 * r + 2 * c) 0 ≠ 0#64 ∧
    (∀ k (hk : k < 2), (Verifier.Whir.WhirQueries.link.d_c960_dba1010e.addr + BitVec.ofNat 64 (240 * r + 16 * c) +
      BitVec.ofNat 64 (8 * k),
      [(Verifier.Whir.WhirQueries.d_c960_dba1010e_words Verifier.Whir.WhirQueries.link).getD (30 * r + 2 * c) 0,
        BitVec.ofNat 64 (Model.whirQueriesTable[r][c]).length][k]'(by simpa using hk)) ∈
      DataRef.pairs (Verifier.Whir.WhirQueries.tables Verifier.Whir.WhirQueries.link)) ∧
    ∀ k (hk : k < (Model.whirQueriesTable[r][c]).length),
      ((Verifier.Whir.WhirQueries.d_c960_dba1010e_words Verifier.Whir.WhirQueries.link).getD (30 * r + 2 * c) 0 +
        BitVec.ofNat 64 (8 * k), BitVec.ofNat 64 (Model.whirQueriesTable[r][c][k])) ∈
      DataRef.pairs (Verifier.Whir.WhirQueries.tables Verifier.Whir.WhirQueries.link)

theorem tableCheck_true : tableCheck := by unfold tableCheck; decide +kernel

/-- **`WHIR_QUERIES` and its rows are where the template's tables say**: `Spec.Whir.WhirQueries.Table` from the
    tables in `env.data`, each header's pointer the address of its row's array (`tableCheck`). -/
theorem whirQueriesTable (hdata : DataRef.InData env (Verifier.Whir.WhirQueries.tables Verifier.Whir.WhirQueries.link)) :
    Spec.Whir.WhirQueries.Table env Verifier.Whir.WhirQueries.link.d_c960_dba1010e.addr := by
  intro r c hr hc
  obtain ⟨h0, h1, h2⟩ := tableCheck_true r hr c hc
  refine ⟨_, h0, fun k hk => hdata.mem _ (h1 k (by simpa using hk)), fun k hk => ?_⟩
  have hk' : k < (Model.whirQueriesTable[r][c]).length := by simpa using hk
  simpa using hdata.mem _ (h2 k hk')

theorem whirQueries (hdata : DataRef.InData env (Verifier.Whir.WhirQueries.tables Verifier.Whir.WhirQueries.link)) :
    Spec.Whir.WhirQueries.spec env (liftProg fns) Idx.Verifier.Whir.WhirQueries Needs.Verifier.Whir.WhirQueries :=
  Proof.Whir.WhirQueries.ok env _ Idx.Verifier.Whir.WhirQueries _ Verifier.Whir.WhirQueries.tmpl_eq Verifier.Whir.WhirQueries.wf
    (whirQueriesTable env hdata)

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
