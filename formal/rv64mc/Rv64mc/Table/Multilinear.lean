/-
  Rv64mc.Table.Multilinear

  The multilinear contracts at the image (`liftProg Gen.fns`): each `ok` at its function's index
  (`Rv64mc/Gen/index.tsv`), with the generated link (`tmpl_eq`, `wf`) and stack (`Gen.Needs`, a caller's bound over
  its callee's by `decide`). `E::mul` is `Table.Field.eMul` (from `clmul_low`'s constant, `hd`); what is not proved
  at the image yet is a hypothesis: `E::square`, `Scaled::new` and `Scaled::mul`, and the panic chain's
  `assert_failed`.
-/

import Rv64mc.Table.Field
import Rv64mc.Proof.Multilinear.Dot
import Rv64mc.Proof.Multilinear.PolyEval
import Rv64mc.Proof.Multilinear.IndexMle
import Rv64mc.Proof.Multilinear.PaddingWeight
import Rv64mc.Proof.Multilinear.ScalerNew
import Rv64mc.Proof.Multilinear.ScalerMul
import Rv64mc.Gen.Link.Verifier.Multilinear.Dot
import Rv64mc.Gen.Link.Verifier.Multilinear.PolyEval
import Rv64mc.Gen.Link.Verifier.Multilinear.IndexMle
import Rv64mc.Gen.Link.Verifier.Multilinear.PaddingWeight
import Rv64mc.Gen.Link.Verifier.Multilinear.Scaler.New
import Rv64mc.Gen.Link.Verifier.Multilinear.Scaler.Mul

namespace Rv64mc.Table.Multilinear

open MachineChecked.RiscV.Lift Rv64mc.Gen

variable (env : Env)
  (hd : DataRef.Words env Verifier.Field.ClmulLow.link.d_c8_d07a1b83 Verifier.Field.ClmulLow.d_c8_d07a1b83_words)
include hd

theorem dot (hfail : Spec.Runtime.NoReturn env (liftProg fns) 14 Needs.Core.Panicking.AssertFailedUsizeUsize) :
    Spec.Multilinear.Dot.spec env (liftProg fns) 28 Needs.Verifier.Multilinear.Dot :=
  Proof.Multilinear.Dot.ok env _ 28 _ Verifier.Multilinear.Dot.tmpl_eq Verifier.Multilinear.Dot.wf
    (by decide) (by decide) (Field.eMul env hd) hfail

theorem polyEval : Spec.Multilinear.PolyEval.spec env (liftProg fns) 108 Needs.Verifier.Multilinear.PolyEval :=
  Proof.Multilinear.PolyEval.ok env _ 108 _ Verifier.Multilinear.PolyEval.tmpl_eq Verifier.Multilinear.PolyEval.wf
    (by decide) (Field.eMul env hd)

theorem indexMle (hsq : Spec.Field.ESquare.spec env (liftProg fns) 104 Needs.Verifier.Field.E.Square) :
    Spec.Multilinear.IndexMle.spec env (liftProg fns) 156 Needs.Verifier.Multilinear.IndexMle :=
  Proof.Multilinear.IndexMle.ok env _ 156 _ Verifier.Multilinear.IndexMle.tmpl_eq Verifier.Multilinear.IndexMle.wf
    (by decide) (by decide) (Field.eMul env hd) hsq

theorem paddingWeight :
    Spec.Multilinear.PaddingWeight.spec env (liftProg fns) 164 Needs.Verifier.Multilinear.PaddingWeight :=
  Proof.Multilinear.PaddingWeight.ok env _ 164 _ Verifier.Multilinear.PaddingWeight.tmpl_eq
    Verifier.Multilinear.PaddingWeight.wf (by decide) (Field.eMul env hd)

omit hd in
theorem scalerNew (hsn : Spec.Field.Scaled.newSpec env (liftProg fns) 96 Needs.Verifier.Field.Scaled.New) :
    Spec.Multilinear.Scaler.newSpec env (liftProg fns) 93 Needs.Verifier.Multilinear.Scaler.New :=
  Proof.Multilinear.ScalerNew.ok env _ 93 _ Verifier.Multilinear.Scaler.New.tmpl_eq Verifier.Multilinear.Scaler.New.wf
    (by decide) hsn

theorem scalerMul (hsm : Spec.Field.Scaled.mulSpec env (liftProg fns) 95 Needs.Verifier.Field.Scaled.Mul) :
    Spec.Multilinear.Scaler.mulSpec env (liftProg fns) 94 Needs.Verifier.Multilinear.Scaler.Mul :=
  Proof.Multilinear.ScalerMul.ok env _ 94 _ Verifier.Multilinear.Scaler.Mul.tmpl_eq Verifier.Multilinear.Scaler.Mul.wf
    (by decide) (by decide) hsm (Field.eMul env hd)

end Rv64mc.Table.Multilinear

/-- info: 'Rv64mc.Table.Multilinear.indexMle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.Multilinear.indexMle
