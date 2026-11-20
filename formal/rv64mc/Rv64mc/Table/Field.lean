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
import Rv64mc.Gen.Needs
import Rv64mc.Gen.Link.Verifier.Field.Reduce
import Rv64mc.Gen.Link.Verifier.Field.ClmulLow
import Rv64mc.Gen.Link.Verifier.Field.Clmul
import Rv64mc.Gen.Link.Verifier.Field.E.AsMul.Mul
import Rv64mc.Gen.Link.Verifier.Multilinear.EqEval

namespace Rv64mc.Table.Field

open MachineChecked.RiscV.Lift Rv64mc.Gen

variable (env : Env)

theorem reduce : Spec.Field.Reduce.spec env (liftProg fns) 21 Needs.Verifier.Field.Reduce :=
  Proof.Field.Reduce.ok env _ 21 _ Verifier.Field.Reduce.tmpl_eq _

theorem clmulLow
    (hd : DataRef.Words env Verifier.Field.ClmulLow.link.d_c8_d07a1b83 Verifier.Field.ClmulLow.d_c8_d07a1b83_words) :
    Spec.Field.ClmulLow.spec env (liftProg fns) 22 Needs.Verifier.Field.ClmulLow :=
  Proof.Field.ClmulLow.ok env _ 22 _ Verifier.Field.ClmulLow.tmpl_eq hd (by decide)

theorem clmul
    (hd : DataRef.Words env Verifier.Field.ClmulLow.link.d_c8_d07a1b83 Verifier.Field.ClmulLow.d_c8_d07a1b83_words) :
    Spec.Field.Clmul.spec env (liftProg fns) 20 Needs.Verifier.Field.Clmul :=
  Proof.Field.Clmul.ok env _ 20 _ Verifier.Field.Clmul.tmpl_eq Verifier.Field.Clmul.wf (by decide) (clmulLow env hd)

theorem eMul
    (hd : DataRef.Words env Verifier.Field.ClmulLow.link.d_c8_d07a1b83 Verifier.Field.ClmulLow.d_c8_d07a1b83_words) :
    Spec.Field.EMul.spec env (liftProg fns) 25 Needs.Verifier.Field.E.AsMul.Mul :=
  Proof.Field.EMul.ok env _ 25 _ Verifier.Field.E.AsMul.Mul.tmpl_eq Verifier.Field.E.AsMul.Mul.wf (by decide)
    (by decide) (clmul env hd) (reduce env)

theorem eqEval
    (hd : DataRef.Words env Verifier.Field.ClmulLow.link.d_c8_d07a1b83 Verifier.Field.ClmulLow.d_c8_d07a1b83_words)
    (hfail : Spec.Runtime.NoReturn env (liftProg fns) 14 Needs.Core.Panicking.AssertFailedUsizeUsize) :
    Spec.Multilinear.EqEval.spec env (liftProg fns) 98 Needs.Verifier.Multilinear.EqEval :=
  Proof.Multilinear.EqEval.ok env _ 98 _ Verifier.Multilinear.EqEval.tmpl_eq Verifier.Multilinear.EqEval.wf
    (by decide) (by decide) (eMul env hd) hfail

end Rv64mc.Table.Field

/-- info: 'Rv64mc.Table.Field.eqEval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.Field.eqEval
