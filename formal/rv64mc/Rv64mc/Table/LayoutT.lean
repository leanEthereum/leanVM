/-
  Rv64mc.Table.LayoutT

  `layout.rs`'s total contracts at the image (`liftProg Gen.fns`), new in wave 2a: `keccak_shape`,
  `Table::n_constraints` and `Table::count_columns`, each at its index with the generated link, the stack
  `Gen.Needs` gives, and `panic_bounds_check`'s `Aborts` (`RuntimeT`). Left as hypotheses, environment facts about
  the image's static data: the tables the two `Table` methods read in `env.data` (`DataRef.InData`, as
  `FieldT.ClmulTable`), and `COUNT_COLUMNS`' contents (`CountColumnsData`, which `Table/Layout.lean` leaves open too).

  ## Main results

  * `keccakShape`, `nConstraints`, `countColumns`
-/

import Rv64mc.Table.RuntimeT
import Rv64mc.Proof.Layout.KeccakShapeT
import Rv64mc.Proof.Layout.TableT
import Rv64mc.Gen.Link.Verifier.Layout

namespace Rv64mc.Table.LayoutT

open MachineChecked.RiscV.Lift Rv64mc.Gen Rv64mc.Proof.Layout

variable (env : Env)

theorem keccakShape :
    KeccakShapeT.specT env (liftProg fns) Idx.Verifier.Layout.KeccakShape Needs.Verifier.Layout.KeccakShape :=
  KeccakShapeT.total env _ _ _ Verifier.Layout.KeccakShape.tmpl_eq Verifier.Layout.KeccakShape.wf
    (HoldsT.mono_need (RuntimeT.panicBoundsCheck env) (by decide))

theorem nConstraints (hd : DataRef.InData env [(Verifier.Layout.Table.NConstraints.link.d_c48_401b839e,
      Verifier.Layout.Table.NConstraints.d_c48_401b839e_words)]) :
    TableT.nConstraintsSpecT env (liftProg fns) Idx.Verifier.Layout.Table.NConstraints
      Needs.Verifier.Layout.Table.NConstraints :=
  TableT.nConstraints_total env _ _ _ Verifier.Layout.Table.NConstraints.tmpl_eq hd
    (HoldsT.mono_need (RuntimeT.panicBoundsCheck env) (by decide)) Verifier.Layout.Table.NConstraints.wf

theorem countColumns (hin : DataRef.InData env [(Verifier.Layout.Table.CountColumns.link.d_c96_da3654e1,
      Verifier.Layout.Table.CountColumns.d_c96_da3654e1_words Verifier.Layout.Table.CountColumns.link)])
    (hd : Spec.Layout.Table.CountColumnsData env Verifier.Layout.Table.CountColumns.link.d_c96_da3654e1) :
    TableT.countColumnsSpecT env (liftProg fns) Idx.Verifier.Layout.Table.CountColumns
      Needs.Verifier.Layout.Table.CountColumns :=
  TableT.countColumns_total env _ _ _ Verifier.Layout.Table.CountColumns.tmpl_eq hin hd
    (HoldsT.mono_need (RuntimeT.panicBoundsCheck env) (by decide)) Verifier.Layout.Table.CountColumns.wf

end Rv64mc.Table.LayoutT

/-- info: 'Rv64mc.Table.LayoutT.keccakShape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.LayoutT.keccakShape

/-- info: 'Rv64mc.Table.LayoutT.nConstraints' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.LayoutT.nConstraints

/-- info: 'Rv64mc.Table.LayoutT.countColumns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.LayoutT.countColumns
