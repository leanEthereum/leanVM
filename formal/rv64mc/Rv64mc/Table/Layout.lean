/-
  Rv64mc.Table.Layout

  `layout.rs`'s contracts at the image (`liftProg Gen.fns`): each `ok` at its function's index
  (`Rv64mc/Gen/index.tsv`), with the generated link, from the contracts not proved here (`alloc`, the panics,
  which do not return, and `E::pow`) and the constant tables the code reads (`NConstraintsData`, `CountColumnsData`, facts of
  the image's static data, discharged where the environment is the image's).
-/

import Rv64mc.Proof.Layout.IsOutputLane
import Rv64mc.Proof.Layout.QkeccakSlot
import Rv64mc.Proof.Layout.KeccakShape
import Rv64mc.Proof.Layout.Table
import Rv64mc.Proof.Layout.Committed
import Rv64mc.Proof.Layout.Gpow
import Rv64mc.Proof.Layout.Term
import Rv64mc.Gen.Link.Verifier.Layout.IsOutputLane
import Rv64mc.Gen.Link.Verifier.Layout.QkeccakSlot
import Rv64mc.Gen.Link.Verifier.Layout.KeccakShape
import Rv64mc.Gen.Link.Verifier.Layout.Table.NConstraints
import Rv64mc.Gen.Link.Verifier.Layout.Table.CountColumns
import Rv64mc.Gen.Link.Verifier.Layout.Layout.Committed
import Rv64mc.Gen.Link.Verifier.Layout.Gpow
import Rv64mc.Gen.Link.Verifier.Layout.Form.Term

namespace Rv64mc.Table.Layout

open MachineChecked.RiscV.Lift Rv64mc.Gen

variable (env : Env)

theorem isOutputLane : Spec.Layout.IsOutputLane.spec env (liftProg fns) Idx.Verifier.Layout.IsOutputLane :=
  Proof.Layout.IsOutputLane.ok env _ Idx.Verifier.Layout.IsOutputLane _ Verifier.Layout.IsOutputLane.tmpl_eq

theorem qkeccakSlot : Spec.Layout.QkeccakSlot.spec env (liftProg fns) Idx.Verifier.Layout.QkeccakSlot :=
  Proof.Layout.QkeccakSlot.ok env _ Idx.Verifier.Layout.QkeccakSlot _ Verifier.Layout.QkeccakSlot.tmpl_eq

theorem keccakShape (hpanic : Spec.Runtime.NoReturn env (liftProg fns) Idx.Core.Panicking.PanicBoundsCheck 0) :
    Spec.Layout.KeccakShape.spec env (liftProg fns) Idx.Verifier.Layout.KeccakShape :=
  Proof.Layout.KeccakShape.ok env _ Idx.Verifier.Layout.KeccakShape _ Verifier.Layout.KeccakShape.tmpl_eq Verifier.Layout.KeccakShape.wf hpanic

theorem nConstraints (hpanic : Spec.Runtime.NoReturn env (liftProg fns) Idx.Core.Panicking.PanicBoundsCheck 0)
    (hdata : Spec.Layout.Table.NConstraintsData env Verifier.Layout.Table.NConstraints.link.d_c48_401b839e) :
    Spec.Layout.Table.nConstraintsSpec env (liftProg fns) Idx.Verifier.Layout.Table.NConstraints :=
  Proof.Layout.Table.nConstraints env _ Idx.Verifier.Layout.Table.NConstraints _ Verifier.Layout.Table.NConstraints.tmpl_eq
    Verifier.Layout.Table.NConstraints.wf hpanic hdata

theorem countColumns (hpanic : Spec.Runtime.NoReturn env (liftProg fns) Idx.Core.Panicking.PanicBoundsCheck 0)
    (hdata : Spec.Layout.Table.CountColumnsData env Verifier.Layout.Table.CountColumns.link.d_c96_da3654e1) :
    Spec.Layout.Table.countColumnsSpec env (liftProg fns) Idx.Verifier.Layout.Table.CountColumns :=
  Proof.Layout.Table.countColumns env _ Idx.Verifier.Layout.Table.CountColumns _ Verifier.Layout.Table.CountColumns.tmpl_eq
    Verifier.Layout.Table.CountColumns.wf hpanic hdata

theorem committed : Spec.Layout.Committed.spec env (liftProg fns) Idx.Verifier.Layout.Layout.Committed :=
  Proof.Layout.Committed.ok env _ Idx.Verifier.Layout.Layout.Committed _ Verifier.Layout.Layout.Committed.tmpl_eq

theorem gpow {need : Nat} (hpow : Spec.Field.EPow.spec env (liftProg fns) Idx.Verifier.Field.E.Pow need) :
    Spec.Layout.Gpow.spec env (liftProg fns) Idx.Verifier.Layout.Gpow need :=
  Proof.Layout.Gpow.ok env _ Idx.Verifier.Layout.Gpow need _ Verifier.Layout.Gpow.tmpl_eq Verifier.Layout.Gpow.wf hpow

theorem term (halloc : Spec.Runtime.AllocSpec env (liftProg fns) Idx.VerifierRv64.Bump.AsGlobalAlloc.Alloc 0)
    (hpanic : Spec.Runtime.NoReturn env (liftProg fns) Idx.Core.Panicking.PanicNounwindFmt 0) : Spec.Layout.Term.spec env (liftProg fns) Idx.Verifier.Layout.Form.Term :=
  Proof.Layout.Term.ok env _ Idx.Verifier.Layout.Form.Term _ Verifier.Layout.Form.Term.tmpl_eq Verifier.Layout.Form.Term.wf halloc hpanic

end Rv64mc.Table.Layout

/-- info: 'Rv64mc.Table.Layout.countColumns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.Layout.countColumns

/-- info: 'Rv64mc.Table.Layout.term' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.Layout.term
