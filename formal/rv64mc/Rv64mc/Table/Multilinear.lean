/-
  Rv64mc.Table.Multilinear

  The multilinear contracts at the image (`liftProg Gen.fns`): each `ok` at its function's index
  (`Rv64mc/Gen/index.tsv`), with the generated link (`tmpl_eq`, `wf`) and stack (`Gen.Needs`, a caller's bound over
  its callee's by `decide`). `E::mul` is `Table.Field.eMul` (from `clmul_low`'s constant, `hd`); what is not proved
  at the image yet is a hypothesis: `E::square`, `Scaled::new` and `Scaled::mul`, `alloc`, `Vec::reserve`, and the
  panic chain's `assert_failed` and `handle_error`.
-/

import Rv64mc.Table.Field
import Rv64mc.Proof.Multilinear.Dot
import Rv64mc.Proof.Multilinear.PolyEval
import Rv64mc.Proof.Multilinear.IndexMle
import Rv64mc.Proof.Multilinear.PaddingWeight
import Rv64mc.Proof.Multilinear.ScalerNew
import Rv64mc.Proof.Multilinear.ScalerMul
import Rv64mc.Proof.Multilinear.SelectorPoint
import Rv64mc.Gen.Link.Verifier.Multilinear

namespace Rv64mc.Table.Multilinear

open MachineChecked.RiscV.Lift Rv64mc.Gen

variable (env : Env)
  (hd : DataRef.Words env Verifier.Field.ClmulLow.link.d_c8_d07a1b83 Verifier.Field.ClmulLow.d_c8_d07a1b83_words)
include hd

theorem dot (hfail : Spec.Runtime.NoReturn env (liftProg fns) Idx.Core.Panicking.AssertFailedUsizeUsize Needs.Core.Panicking.AssertFailedUsizeUsize) :
    Spec.Multilinear.Dot.spec env (liftProg fns) Idx.Verifier.Multilinear.Dot Needs.Verifier.Multilinear.Dot :=
  Proof.Multilinear.Dot.ok env _ Idx.Verifier.Multilinear.Dot _ Verifier.Multilinear.Dot.tmpl_eq Verifier.Multilinear.Dot.wf
    (by decide) (by decide) (Field.eMul env hd) hfail

theorem polyEval : Spec.Multilinear.PolyEval.spec env (liftProg fns) Idx.Verifier.Multilinear.PolyEval Needs.Verifier.Multilinear.PolyEval :=
  Proof.Multilinear.PolyEval.ok env _ Idx.Verifier.Multilinear.PolyEval _ Verifier.Multilinear.PolyEval.tmpl_eq Verifier.Multilinear.PolyEval.wf
    (by decide) (Field.eMul env hd)

theorem indexMle (hsq : Spec.Field.ESquare.spec env (liftProg fns) Idx.Verifier.Field.E.Square Needs.Verifier.Field.E.Square) :
    Spec.Multilinear.IndexMle.spec env (liftProg fns) Idx.Verifier.Multilinear.IndexMle Needs.Verifier.Multilinear.IndexMle :=
  Proof.Multilinear.IndexMle.ok env _ Idx.Verifier.Multilinear.IndexMle _ Verifier.Multilinear.IndexMle.tmpl_eq Verifier.Multilinear.IndexMle.wf
    (by decide) (by decide) (Field.eMul env hd) hsq

theorem paddingWeight :
    Spec.Multilinear.PaddingWeight.spec env (liftProg fns) Idx.Verifier.Multilinear.PaddingWeight Needs.Verifier.Multilinear.PaddingWeight :=
  Proof.Multilinear.PaddingWeight.ok env _ Idx.Verifier.Multilinear.PaddingWeight _ Verifier.Multilinear.PaddingWeight.tmpl_eq
    Verifier.Multilinear.PaddingWeight.wf (by decide) (Field.eMul env hd)

omit hd in
theorem scalerNew (hsn : Spec.Field.Scaled.newSpec env (liftProg fns) Idx.Verifier.Field.Scaled.New Needs.Verifier.Field.Scaled.New) :
    Spec.Multilinear.Scaler.newSpec env (liftProg fns) Idx.Verifier.Multilinear.Scaler.New Needs.Verifier.Multilinear.Scaler.New :=
  Proof.Multilinear.ScalerNew.ok env _ Idx.Verifier.Multilinear.Scaler.New _ Verifier.Multilinear.Scaler.New.tmpl_eq Verifier.Multilinear.Scaler.New.wf
    (by decide) hsn

theorem scalerMul (hsm : Spec.Field.Scaled.mulSpec env (liftProg fns) Idx.Verifier.Field.Scaled.Mul Needs.Verifier.Field.Scaled.Mul) :
    Spec.Multilinear.Scaler.mulSpec env (liftProg fns) Idx.Verifier.Multilinear.Scaler.Mul Needs.Verifier.Multilinear.Scaler.Mul :=
  Proof.Multilinear.ScalerMul.ok env _ Idx.Verifier.Multilinear.Scaler.Mul _ Verifier.Multilinear.Scaler.Mul.tmpl_eq Verifier.Multilinear.Scaler.Mul.wf
    (by decide) (by decide) hsm (Field.eMul env hd)

omit hd in
theorem selectorPoint
    (hal : Spec.Runtime.AllocSpec env (liftProg fns) Idx.VerifierRv64.Bump.AsGlobalAlloc.Alloc Needs.VerifierRv64.Bump.AsGlobalAlloc.Alloc)
    (hres : Spec.Runtime.ReserveSpec env 8 16 (liftProg fns) Idx.Alloc.Vec.VecE.Reserve Needs.Alloc.Vec.VecE.Reserve)
    (hhe : Spec.Runtime.NoReturn env (liftProg fns) Idx.Alloc.RawVec.HandleError Needs.Alloc.RawVec.HandleError) :
    Spec.Multilinear.SelectorPoint.spec env (liftProg fns) Idx.Verifier.Multilinear.SelectorPoint Needs.Verifier.Multilinear.SelectorPoint :=
  Proof.Multilinear.SelectorPoint.ok env _ Idx.Verifier.Multilinear.SelectorPoint _ Verifier.Multilinear.SelectorPoint.tmpl_eq
    Verifier.Multilinear.SelectorPoint.wf (by decide) (by decide) (by decide) hal hres hhe

end Rv64mc.Table.Multilinear

/-- info: 'Rv64mc.Table.Multilinear.indexMle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.Multilinear.indexMle
