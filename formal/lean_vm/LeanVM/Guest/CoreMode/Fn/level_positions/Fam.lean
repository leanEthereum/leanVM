/-
  LeanVM.Guest.CoreMode.Fn.level_positions.Fam

  `level_positions`' own residual family (`CoreMode/FnReg.lean`): its count of squeezes at least `g^2`.
-/

module

public import LeanVM.Guest.CoreMode.CoreRes
public import LeanVM.Guest.CoreMode.Fn.level_positions.Data
public meta import LeanVM.Guest.CoreRef
import LeanVM.Guest.Data.Source

namespace LeanVM.Guest.CoreMode.Own.level_positions

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- **Its family**: `e(squeezes_g) > 1` (its loop writes the rows from `2`, its body row `1`), `squeezes_g` its parameter
`V.n p`. -/
noncomputable def fams : List (String × (Fn → CRes → Bool)) :=
  names.map fun k ↦ (k, fun fn r ↦ decide (r = .lt (.num 1) (.val (param% level_positions "squeezes_g"))) &&
    decide (fn.params[param% level_positions "squeezes_g"]? = some (V.n (param% level_positions "squeezes_g"))))

end

end LeanVM.Guest.CoreMode.Own.level_positions
