/-
  Rv64mc.Table.Field

  The field's contracts and `eq_eval`'s at the image (`liftProg Gen.fns`): each `ok` at its function's index, with
  the generated link (`Gen.….link`, `tmpl_eq`, `wf`), from the contracts not proved yet (`clmul`, the panic chain's
  `assert_failed`). The indices are the generator's (`Rv64mc/Gen/index.tsv`); a link's callee index is its
  function's by the link's definition, so each callee's theorem is passed as it is.
-/

import Rv64mc.Proof.Field.Reduce
import Rv64mc.Proof.Field.EMul
import Rv64mc.Proof.Multilinear.EqEval
import Rv64mc.Gen.Link.Verifier.Field.Reduce
import Rv64mc.Gen.Link.Verifier.Field.E.AsMul.Mul
import Rv64mc.Gen.Link.Verifier.Multilinear.EqEval

namespace Rv64mc.Table.Field

open MachineChecked.RiscV.Lift Rv64mc.Gen

variable (env : Env)

theorem reduce : Spec.Field.Reduce.spec env (liftProg fns) 21 :=
  Proof.Field.Reduce.ok env _ 21 _ Verifier.Field.Reduce.tmpl_eq

theorem eMul (hcl : Spec.Field.Clmul.spec env (liftProg fns) 20) : Spec.Field.EMul.spec env (liftProg fns) 25 :=
  Proof.Field.EMul.ok env _ 25 _ Verifier.Field.E.AsMul.Mul.tmpl_eq Verifier.Field.E.AsMul.Mul.wf hcl (reduce env)

theorem eqEval (hcl : Spec.Field.Clmul.spec env (liftProg fns) 20)
    (hfail : Spec.Runtime.NoReturn env (liftProg fns) 14 0) : Spec.Multilinear.EqEval.spec env (liftProg fns) 98 :=
  Proof.Multilinear.EqEval.ok env _ 98 _ Verifier.Multilinear.EqEval.tmpl_eq Verifier.Multilinear.EqEval.wf
    (eMul env hcl) hfail

end Rv64mc.Table.Field

/-- info: 'Rv64mc.Table.Field.eqEval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.Field.eqEval
