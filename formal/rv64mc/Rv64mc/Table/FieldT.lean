/-
  Rv64mc.Table.FieldT

  The field's total contracts at the image (`liftProg Gen.fns`), the total counterpart of `Field.lean`: each
  function's total theorem at its index, with the generated link, the stack `Gen.Needs` gives (a caller's bound over
  its callee's by `decide`), and its callees' total theorems here. Left as a hypothesis: `clmul_low`'s constant
  table in the image's static data (`DataRef.InData`), an environment fact.

  ## Main results

  * `reduce`, `spread`, `eSquare`, `clmulLow`, `clmul`, `baseMul`, `eMul`, `eSumCopied`
-/

import Rv64mc.Proof.Field.ReduceT
import Rv64mc.Proof.Field.SpreadT
import Rv64mc.Proof.Field.ESquareT
import Rv64mc.Proof.Field.ClmulLowT
import Rv64mc.Proof.Field.ClmulT
import Rv64mc.Proof.Field.BaseMulT
import Rv64mc.Proof.Field.EMulT
import Rv64mc.Proof.Field.ESumCopiedT
import Rv64mc.Gen.Needs
import Rv64mc.Gen.Link.Verifier.Field
import Rv64mc.Gen.Link.Verifier.Field.E

namespace Rv64mc.Table.FieldT

open MachineChecked.RiscV.Lift Rv64mc.Gen Rv64mc.Proof.Field

variable (env : Env)

/-- `clmul_low`'s constant table in the image's static data. -/
abbrev ClmulTable : Prop :=
  DataRef.InData env [(Verifier.Field.ClmulLow.link.d_c8_d07a1b83, Verifier.Field.ClmulLow.d_c8_d07a1b83_words)]

theorem reduce : ReduceT.specT env (liftProg fns) Idx.Verifier.Field.Reduce Needs.Verifier.Field.Reduce :=
  ReduceT.total env _ _ _ Verifier.Field.Reduce.tmpl_eq _

theorem spread : SpreadT.specT env (liftProg fns) Idx.Verifier.Field.Spread Needs.Verifier.Field.Spread :=
  SpreadT.total env _ _ _ Verifier.Field.Spread.tmpl_eq _

theorem eSquare : ESquareT.specT env (liftProg fns) Idx.Verifier.Field.E.Square Needs.Verifier.Field.E.Square :=
  ESquareT.total env _ _ _ Verifier.Field.E.Square.tmpl_eq Verifier.Field.E.Square.wf (by decide) (by decide)
    (spread env) (reduce env)

theorem clmulLow (hd : ClmulTable env) :
    ClmulLowT.specT env (liftProg fns) Idx.Verifier.Field.ClmulLow Needs.Verifier.Field.ClmulLow :=
  ClmulLowT.total env _ _ _ Verifier.Field.ClmulLow.tmpl_eq hd (by decide)

theorem clmul (hd : ClmulTable env) :
    ClmulT.specT env (liftProg fns) Idx.Verifier.Field.Clmul Needs.Verifier.Field.Clmul :=
  ClmulT.total env _ _ _ Verifier.Field.Clmul.tmpl_eq Verifier.Field.Clmul.wf (by decide) (clmulLow env hd)

theorem baseMul (hd : ClmulTable env) :
    BaseMulT.specT env (liftProg fns) Idx.Verifier.Field.BaseMul Needs.Verifier.Field.BaseMul :=
  BaseMulT.total env _ _ _ Verifier.Field.BaseMul.tmpl_eq Verifier.Field.BaseMul.wf (by decide) (by decide)
    (clmul env hd) (reduce env)

theorem eMul (hd : ClmulTable env) :
    EMulT.specT env (liftProg fns) Idx.Verifier.Field.E.AsMul.Mul Needs.Verifier.Field.E.AsMul.Mul :=
  EMulT.total env _ _ _ Verifier.Field.E.AsMul.Mul.tmpl_eq Verifier.Field.E.AsMul.Mul.wf (by decide) (by decide)
    (clmul env hd) (reduce env)

theorem eSumCopied :
    ESumCopiedT.specT env (liftProg fns) Idx.Verifier.Field.E.SumCopiedIterE Needs.Verifier.Field.E.SumCopiedIterE :=
  ESumCopiedT.total env _ _ _ Verifier.Field.E.SumCopiedIterE.tmpl_eq _

end Rv64mc.Table.FieldT

/-- info: 'Rv64mc.Table.FieldT.reduce' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.FieldT.reduce

/-- info: 'Rv64mc.Table.FieldT.spread' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.FieldT.spread

/-- info: 'Rv64mc.Table.FieldT.eSquare' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.FieldT.eSquare

/-- info: 'Rv64mc.Table.FieldT.clmulLow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.FieldT.clmulLow

/-- info: 'Rv64mc.Table.FieldT.clmul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.FieldT.clmul

/-- info: 'Rv64mc.Table.FieldT.baseMul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.FieldT.baseMul

/-- info: 'Rv64mc.Table.FieldT.eMul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.FieldT.eMul

/-- info: 'Rv64mc.Table.FieldT.eSumCopied' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.FieldT.eSumCopied
