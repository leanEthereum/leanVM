/-
  Rv64mc.Table.LayoutT

  `layout.rs`'s total contracts at the image (`liftProg Gen.fns`), new in wave 2a: `keccak_shape`,
  `Table::n_constraints`, `Table::count_columns`, `Form::term`, `constant`, `E::pow` (`GEN.pow`, here for `gpow`, its
  only caller), `gpow`, `col` and `prod`, each at its index with the generated link, the stack `Gen.Needs` gives, and
  its callees' total theorems (`RuntimeT`, `FieldT`, here). Left as hypotheses, environment facts: `alloc`'s two
  (`RuntimeT.alloc`), `clmul_low`'s table (`FieldT.ClmulTable`, which `E::mul` reads), the tables the two `Table`
  methods read in `env.data` (`DataRef.InData`, as `FieldT.ClmulTable`), and `COUNT_COLUMNS`' contents
  (`CountColumnsData`, which `Table/Layout.lean` leaves open too).

  ## Main results

  * `keccakShape`, `nConstraints`, `countColumns`, `term`, `constant`, `ePow`, `gpow`, `col`, `prod`
-/

import Rv64mc.Table.RuntimeT
import Rv64mc.Proof.Layout.KeccakShapeT
import Rv64mc.Proof.Layout.TableT
import Rv64mc.Proof.Layout.ConstantT
import Rv64mc.Proof.Layout.ColT
import Rv64mc.Proof.Layout.ProdT
import Rv64mc.Table.FieldT
import Rv64mc.Gen.Link.Verifier.Field.E
import Rv64mc.Gen.Link.Verifier.Layout.Form
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

theorem term (hnext : VerifierRv64.Bump.AsGlobalAlloc.Alloc.link.d_NEXT.addr = env.nextAddr)
    (hend : env.heapEnd = 0x78000000#64) : TermT.specT env (liftProg fns) Idx.Verifier.Layout.Form.Term :=
  TermT.total env _ _ _ Verifier.Layout.Form.Term.tmpl_eq Verifier.Layout.Form.Term.wf
    (RuntimeT.alloc env hnext hend) (RuntimeT.panicNounwindFmt env)

theorem constant (hnext : VerifierRv64.Bump.AsGlobalAlloc.Alloc.link.d_NEXT.addr = env.nextAddr)
    (hend : env.heapEnd = 0x78000000#64) : ConstantT.specT env (liftProg fns) Idx.Verifier.Layout.Constant :=
  ConstantT.total env _ _ _ Verifier.Layout.Constant.tmpl_eq Verifier.Layout.Constant.wf (term env hnext hend)

theorem ePow (hd : FieldT.ClmulTable env) :
    Rv64mc.Proof.Field.EPowT.specT env (liftProg fns) Idx.Verifier.Field.E.Pow Needs.Verifier.Field.E.Pow :=
  Rv64mc.Proof.Field.EPowT.total env _ _ _ Verifier.Field.E.Pow.tmpl_eq Verifier.Field.E.Pow.wf (by decide) (by decide)
    (FieldT.eSquare env) (FieldT.eMul env hd)

theorem gpow (hd : FieldT.ClmulTable env) :
    GpowT.specT env (liftProg fns) Idx.Verifier.Layout.Gpow Needs.Verifier.Layout.Gpow :=
  GpowT.total env _ _ _ _ Verifier.Layout.Gpow.tmpl_eq Verifier.Layout.Gpow.wf (ePow env hd)

theorem col (hnext : VerifierRv64.Bump.AsGlobalAlloc.Alloc.link.d_NEXT.addr = env.nextAddr)
    (hend : env.heapEnd = 0x78000000#64) (hd : FieldT.ClmulTable env) :
    ColT.colSpecT env (liftProg fns) Idx.Verifier.Layout.Col Needs.Verifier.Layout.Col :=
  ColT.total env _ _ _ _ _ Verifier.Layout.Col.tmpl_eq Verifier.Layout.Col.wf (RuntimeT.alloc env hnext hend)
    (gpow env hd) (term env hnext hend) (RuntimeT.panicNounwindFmt env) (by decide) (by decide)

theorem prod (hnext : VerifierRv64.Bump.AsGlobalAlloc.Alloc.link.d_NEXT.addr = env.nextAddr)
    (hend : env.heapEnd = 0x78000000#64) (hd : FieldT.ClmulTable env) :
    ProdT.prodSpecT env (liftProg fns) Idx.Verifier.Layout.Prod Needs.Verifier.Layout.Prod :=
  ProdT.total env _ _ _ _ _ Verifier.Layout.Prod.tmpl_eq Verifier.Layout.Prod.wf (RuntimeT.alloc env hnext hend)
    (gpow env hd) (term env hnext hend) (RuntimeT.panicNounwindFmt env) (by decide) (by decide)

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

/-- info: 'Rv64mc.Table.LayoutT.term' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.LayoutT.term

/-- info: 'Rv64mc.Table.LayoutT.constant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.LayoutT.constant

/-- info: 'Rv64mc.Table.LayoutT.ePow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.LayoutT.ePow

/-- info: 'Rv64mc.Table.LayoutT.gpow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.LayoutT.gpow

/-- info: 'Rv64mc.Table.LayoutT.col' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.LayoutT.col

/-- info: 'Rv64mc.Table.LayoutT.prod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.LayoutT.prod
