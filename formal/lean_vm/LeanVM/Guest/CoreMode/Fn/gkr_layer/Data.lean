/-
  LeanVM.Guest.CoreMode.Fn.gkr_layer.Data

  `gkr_layer`'s own routing data (`CoreMode/FnReg.lean`): its exponent facts, its loop's reads of the proof stream, its callers.
-/

module

public meta import LeanVM.Guest.CoreRef
public import LeanVM.Guest.Data.NameStrings
public import LeanVM.Guest.Renumber
public import LeanVM.Guest.CoreMode.Fam.ParamRef
import LeanVM.Guest.Data.Source
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«gkr_layer__L»
import LeanVM.Guest.Data.ValNames.«gkr_layer__L_loop0»

namespace LeanVM.Guest.CoreMode.Own.gkr_layer

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- **Its exponent facts**: each `gkr_layer__L{p}_L{o}`'s `x_m`, below `4` (`EndExec.GlQ`). -/
def expFacts : List (String × ℕ × Option ℕ × ℕ) :=
  [name% «gkr_layer__L0_L0», name% «gkr_layer__L0_L1», name% «gkr_layer__L1_L0», name% «gkr_layer__L1_L1»,
    name% «gkr_layer__L2_L0», name% «gkr_layer__L2_L1», name% «gkr_layer__L3_L0», name% «gkr_layer__L3_L1»].map
    fun n ↦ (n, param% gkr_layer "x_m", none, 4)

/-- **Its loop reads the proof stream past its cursor** (`CoreMode.stLoops`): the stream its caller's cell (`2 +` the
value `stream`), the cursor its value `cur`, `32` words an iteration. -/
def stLoops : List (String × ℕ × ℕ × ℕ) :=
  [name% «gkr_layer__L0_L0_loop0», name% «gkr_layer__L1_L0_loop0», name% «gkr_layer__L2_L0_loop0»,
    name% «gkr_layer__L3_L0_loop0», name% «gkr_layer__L0_L1_loop0», name% «gkr_layer__L1_L1_loop0»,
    name% «gkr_layer__L2_L1_loop0», name% «gkr_layer__L3_L1_loop0»].map
    fun n ↦ (n, 2 + valf% «gkr_layer» "stream", valf% «gkr_layer» «_loop0» "cur", 32)

/-- **Its callers** (`Res.callersM`): `gkr_layer__L{p}_L{o}` called by `gkr_layers__L{o}`'s loop and by
`gkr_last_layers__L{r}_L{o}`, `r > p`, its loop by it. -/
def glCallers : List (String × List String) :=
  [(name% «gkr_layer__L0_L0», [name% «gkr_layers__L0_loop0», name% «gkr_last_layers__L1_L0»,
      name% «gkr_last_layers__L2_L0», name% «gkr_last_layers__L3_L0»]),
    (name% «gkr_layer__L1_L0», [name% «gkr_layers__L0_loop0», name% «gkr_last_layers__L2_L0»,
      name% «gkr_last_layers__L3_L0»]),
    (name% «gkr_layer__L2_L0», [name% «gkr_layers__L0_loop0», name% «gkr_last_layers__L3_L0»]),
    (name% «gkr_layer__L3_L0», [name% «gkr_layers__L0_loop0»]),
    (name% «gkr_layer__L0_L0_loop0», [name% «gkr_layer__L0_L0»]),
    (name% «gkr_layer__L1_L0_loop0», [name% «gkr_layer__L1_L0»]),
    (name% «gkr_layer__L2_L0_loop0», [name% «gkr_layer__L2_L0»]),
    (name% «gkr_layer__L3_L0_loop0», [name% «gkr_layer__L3_L0»]),
    (name% «gkr_layer__L0_L1», [name% «gkr_layers__L1_loop0», name% «gkr_last_layers__L1_L1»,
      name% «gkr_last_layers__L2_L1», name% «gkr_last_layers__L3_L1»]),
    (name% «gkr_layer__L1_L1», [name% «gkr_layers__L1_loop0», name% «gkr_last_layers__L2_L1»,
      name% «gkr_last_layers__L3_L1»]),
    (name% «gkr_layer__L2_L1», [name% «gkr_layers__L1_loop0», name% «gkr_last_layers__L3_L1»]),
    (name% «gkr_layer__L3_L1», [name% «gkr_layers__L1_loop0»]),
    (name% «gkr_layer__L0_L1_loop0», [name% «gkr_layer__L0_L1»]),
    (name% «gkr_layer__L1_L1_loop0», [name% «gkr_layer__L1_L1»]),
    (name% «gkr_layer__L2_L1_loop0», [name% «gkr_layer__L2_L1»]),
    (name% «gkr_layer__L3_L1_loop0», [name% «gkr_layer__L3_L1»])]

end

end LeanVM.Guest.CoreMode.Own.gkr_layer
