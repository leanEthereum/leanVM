/-
  LeanVM.Guest.CoreMode.Fn.gkr_layers.Data

  `gkr_layers`'s own routing data (`CoreMode/FnReg.lean`): its exponent facts and its callers.
-/

module

public meta import LeanVM.Guest.CoreRef
public import LeanVM.Guest.Data.NameStrings
public import LeanVM.Guest.Renumber
public import LeanVM.Guest.CoreMode.Fam.ParamRef
import LeanVM.Guest.Data.Source

namespace LeanVM.Guest.CoreMode.Own.gkr_layers

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- **Its exponent facts**: `gkr_layers__L{o}`'s `n_four` and `rem_g`, below `4` (`EndExec.GlsQ`). -/
def expFacts : List (String × ℕ × Option ℕ × ℕ) :=
  [(name% «gkr_layers__L0», param% gkr_layers "n_four", none, 4),
    (name% «gkr_layers__L0», param% gkr_layers "rem_g", none, 4),
    (name% «gkr_layers__L1», param% gkr_layers "n_four", none, 4),
    (name% «gkr_layers__L1», param% gkr_layers "rem_g", none, 4)]

/-- **Its callers** (`Res.callersM`): `gkr_layers__L{o}` called by `verify_bus_gkr`, its loop by it. -/
def glCallers : List (String × List String) :=
  [(name% «gkr_layers__L0», [name% «verify_bus_gkr»]),
    (name% «gkr_layers__L0_loop0», [name% «gkr_layers__L0»]),
    (name% «gkr_layers__L1», [name% «verify_bus_gkr»]),
    (name% «gkr_layers__L1_loop0», [name% «gkr_layers__L1»])]

end

end LeanVM.Guest.CoreMode.Own.gkr_layers
