/-
  Rv64mc.Table.Field

  The field's contracts and `eq_eval`'s at the image (`liftProg Gen.fns`): each `ok` at its function's index, with
  the generated link (`Gen.….link`, `tmpl_eq`, `wf`), the stack each needs (`Gen.Needs`, a caller's bound over its
  callee's checked by `decide`), and what is not proved here: `clmul_low`'s constant (`DataRef.Words`, which the
  image's `env.data` gives: `DataRef.Words.of_data`) and the panic chain's `assert_failed`. The indices are the
  generator's (`Rv64mc/Gen/index.tsv`); a link's callee index is its function's by the link's definition, so each
  callee's theorem is passed as it is.
-/

import Rv64mc.Proof.Field.Reduce
import Rv64mc.Proof.Field.ClmulLow
import Rv64mc.Proof.Field.Clmul
import Rv64mc.Proof.Field.EMul
import Rv64mc.Proof.Multilinear.EqEval
import Rv64mc.Proof.Field.Spread
import Rv64mc.Proof.Field.BaseMul
import Rv64mc.Proof.Field.ESquare
import Rv64mc.Proof.Field.EPow
import Rv64mc.Proof.Field.ESumCopied
import Rv64mc.Proof.Field.KInv
import Rv64mc.Proof.Field.ScaledMul
import Rv64mc.Gen.Needs
import Rv64mc.Gen.Link.Verifier.Field.Reduce
import Rv64mc.Gen.Link.Verifier.Field.ClmulLow
import Rv64mc.Gen.Link.Verifier.Field.Clmul
import Rv64mc.Gen.Link.Verifier.Field.E.AsMul.Mul
import Rv64mc.Gen.Link.Verifier.Multilinear.EqEval
import Rv64mc.Gen.Link.Verifier.Field.Spread
import Rv64mc.Gen.Link.Verifier.Field.BaseMul
import Rv64mc.Gen.Link.Verifier.Field.E.Square
import Rv64mc.Gen.Link.Verifier.Field.E.Pow
import Rv64mc.Gen.Link.Verifier.Field.E.SumCopiedIterE
import Rv64mc.Gen.Link.Verifier.Field.K.Inv
import Rv64mc.Gen.Link.Verifier.Field.Scaled.Mul

namespace Rv64mc.Table.Field

open MachineChecked.RiscV.Lift Rv64mc.Gen

variable (env : Env)

theorem reduce : Spec.Field.Reduce.spec env (liftProg fns) Idx.Verifier.Field.Reduce Needs.Verifier.Field.Reduce :=
  Proof.Field.Reduce.ok env _ Idx.Verifier.Field.Reduce _ Verifier.Field.Reduce.tmpl_eq _

theorem clmulLow
    (hd : DataRef.Words env Verifier.Field.ClmulLow.link.d_c8_d07a1b83 Verifier.Field.ClmulLow.d_c8_d07a1b83_words) :
    Spec.Field.ClmulLow.spec env (liftProg fns) Idx.Verifier.Field.ClmulLow Needs.Verifier.Field.ClmulLow :=
  Proof.Field.ClmulLow.ok env _ Idx.Verifier.Field.ClmulLow _ Verifier.Field.ClmulLow.tmpl_eq hd (by decide)

theorem clmul
    (hd : DataRef.Words env Verifier.Field.ClmulLow.link.d_c8_d07a1b83 Verifier.Field.ClmulLow.d_c8_d07a1b83_words) :
    Spec.Field.Clmul.spec env (liftProg fns) Idx.Verifier.Field.Clmul Needs.Verifier.Field.Clmul :=
  Proof.Field.Clmul.ok env _ Idx.Verifier.Field.Clmul _ Verifier.Field.Clmul.tmpl_eq Verifier.Field.Clmul.wf (by decide) (clmulLow env hd)

theorem eMul
    (hd : DataRef.Words env Verifier.Field.ClmulLow.link.d_c8_d07a1b83 Verifier.Field.ClmulLow.d_c8_d07a1b83_words) :
    Spec.Field.EMul.spec env (liftProg fns) Idx.Verifier.Field.E.AsMul.Mul Needs.Verifier.Field.E.AsMul.Mul :=
  Proof.Field.EMul.ok env _ Idx.Verifier.Field.E.AsMul.Mul _ Verifier.Field.E.AsMul.Mul.tmpl_eq Verifier.Field.E.AsMul.Mul.wf (by decide)
    (by decide) (clmul env hd) (reduce env)

theorem eqEval
    (hd : DataRef.Words env Verifier.Field.ClmulLow.link.d_c8_d07a1b83 Verifier.Field.ClmulLow.d_c8_d07a1b83_words)
    (hfail : Spec.Runtime.NoReturn env (liftProg fns) Idx.Core.Panicking.AssertFailedUsizeUsize Needs.Core.Panicking.AssertFailedUsizeUsize) :
    Spec.Multilinear.EqEval.spec env (liftProg fns) Idx.Verifier.Multilinear.EqEval Needs.Verifier.Multilinear.EqEval :=
  Proof.Multilinear.EqEval.ok env _ Idx.Verifier.Multilinear.EqEval _ Verifier.Multilinear.EqEval.tmpl_eq Verifier.Multilinear.EqEval.wf
    (by decide) (by decide) (eMul env hd) hfail

theorem spread : Spec.Field.Spread.spec env (liftProg fns) Idx.Verifier.Field.Spread Needs.Verifier.Field.Spread :=
  Proof.Field.Spread.ok env _ Idx.Verifier.Field.Spread _ Verifier.Field.Spread.tmpl_eq _

theorem baseMul
    (hd : DataRef.Words env Verifier.Field.ClmulLow.link.d_c8_d07a1b83 Verifier.Field.ClmulLow.d_c8_d07a1b83_words) :
    Spec.Field.BaseMul.spec env (liftProg fns) Idx.Verifier.Field.BaseMul Needs.Verifier.Field.BaseMul :=
  Proof.Field.BaseMul.ok env _ Idx.Verifier.Field.BaseMul _ Verifier.Field.BaseMul.tmpl_eq Verifier.Field.BaseMul.wf (by decide) (by decide)
    (clmul env hd) (reduce env)

theorem eSquare : Spec.Field.ESquare.spec env (liftProg fns) Idx.Verifier.Field.E.Square Needs.Verifier.Field.E.Square :=
  Proof.Field.ESquare.ok env _ Idx.Verifier.Field.E.Square _ Verifier.Field.E.Square.tmpl_eq Verifier.Field.E.Square.wf (by decide)
    (by decide) (spread env) (reduce env)

theorem ePow
    (hd : DataRef.Words env Verifier.Field.ClmulLow.link.d_c8_d07a1b83 Verifier.Field.ClmulLow.d_c8_d07a1b83_words) :
    Spec.Field.EPow.spec env (liftProg fns) Idx.Verifier.Field.E.Pow Needs.Verifier.Field.E.Pow :=
  Proof.Field.EPow.ok env _ Idx.Verifier.Field.E.Pow _ Verifier.Field.E.Pow.tmpl_eq Verifier.Field.E.Pow.wf (by decide) (by decide)
    (eSquare env) (eMul env hd)

theorem eSumCopied : Spec.Field.ESumCopied.spec env (liftProg fns) Idx.Verifier.Field.E.SumCopiedIterE Needs.Verifier.Field.E.SumCopiedIterE :=
  Proof.Field.ESumCopied.ok env _ Idx.Verifier.Field.E.SumCopiedIterE _ Verifier.Field.E.SumCopiedIterE.tmpl_eq _

theorem kInv
    (hd : DataRef.Words env Verifier.Field.ClmulLow.link.d_c8_d07a1b83 Verifier.Field.ClmulLow.d_c8_d07a1b83_words) :
    Spec.Field.KInv.spec env (liftProg fns) Idx.Verifier.Field.K.Inv Needs.Verifier.Field.K.Inv :=
  Proof.Field.KInv.ok env _ Idx.Verifier.Field.K.Inv _ Verifier.Field.K.Inv.tmpl_eq Verifier.Field.K.Inv.wf (by decide) (by decide)
    (by decide) (spread env) (reduce env) (baseMul env hd)

theorem scaledMul (hpanic : Spec.Runtime.NoReturn env (liftProg fns) Idx.Core.Panicking.PanicBoundsCheck Needs.Core.Panicking.PanicBoundsCheck) :
    Spec.Field.Scaled.mulSpec env (liftProg fns) Idx.Verifier.Field.Scaled.Mul Needs.Verifier.Field.Scaled.Mul :=
  Proof.Field.ScaledMul.ok env _ Idx.Verifier.Field.Scaled.Mul _ Verifier.Field.Scaled.Mul.tmpl_eq Verifier.Field.Scaled.Mul.wf (by decide) hpanic

end Rv64mc.Table.Field

/-- info: 'Rv64mc.Table.Field.eqEval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.Field.eqEval

/-- info: 'Rv64mc.Table.Field.ePow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.Field.ePow
