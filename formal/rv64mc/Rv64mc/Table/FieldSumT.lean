/-
  Rv64mc.Table.FieldSumT

  `E::sum::<Chain<vec::IntoIter<E>, vec::IntoIter<E>>>`'s total contract (`SumChainSafeT`) at the image, a leaf.

  ## Main results

  * `sumChainT`
-/

import Rv64mc.Proof.Field.SumChainT
import Rv64mc.Gen.Needs
import Rv64mc.Gen.Link.Verifier.Field.E

namespace Rv64mc.Table.FieldSumT

open MachineChecked.RiscV.Lift Rv64mc.Gen

variable (env : Env)

/-- **`E::sum::<Chain<…>>` at the image** (function 34). -/
theorem sumChainT : Proof.Field.SumChainT.SumChainSafeT env (liftProg fns)
    Idx.Verifier.Field.E.SumChainIntoIterEIntoIterE Needs.Verifier.Field.E.SumChainIntoIterEIntoIterE :=
  HoldsT.mono_need (Proof.Field.SumChainT.total Verifier.Field.E.SumChainIntoIterEIntoIterE.tmpl_eq) (by decide)

end Rv64mc.Table.FieldSumT

/-- info: 'Rv64mc.Table.FieldSumT.sumChainT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.FieldSumT.sumChainT
