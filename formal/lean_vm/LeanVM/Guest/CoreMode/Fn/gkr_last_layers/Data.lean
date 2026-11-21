/-
  LeanVM.Guest.CoreMode.Fn.gkr_last_layers.Data

  `gkr_last_layers`'s own routing data (`CoreMode/FnReg.lean`): its callers.
-/

module

public meta import LeanVM.Guest.CoreRef
public import LeanVM.Guest.Data.NameStrings
public import LeanVM.Guest.Renumber

namespace LeanVM.Guest.CoreMode.Own.gkr_last_layers

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- **Its callers** (`Res.callersM`): `gkr_last_layers__L{r}_L{o}` called by `gkr_layers__L{o}`. -/
def glCallers : List (String × List String) :=
  [(name% «gkr_last_layers__L0_L0», [name% «gkr_layers__L0»]),
    (name% «gkr_last_layers__L1_L0», [name% «gkr_layers__L0»]),
    (name% «gkr_last_layers__L2_L0», [name% «gkr_layers__L0»]),
    (name% «gkr_last_layers__L3_L0», [name% «gkr_layers__L0»]),
    (name% «gkr_last_layers__L0_L1», [name% «gkr_layers__L1»]),
    (name% «gkr_last_layers__L1_L1», [name% «gkr_layers__L1»]),
    (name% «gkr_last_layers__L2_L1», [name% «gkr_layers__L1»]),
    (name% «gkr_last_layers__L3_L1», [name% «gkr_layers__L1»])]

end

end LeanVM.Guest.CoreMode.Own.gkr_last_layers
