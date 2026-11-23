/-
  LeanVM.Guest.CoreMode.Fn.gkr_layer.Fam

  `gkr_layer`'s own residual families (`CoreMode/FnReg.lean`): its reads past its cursors.
-/

module

public import LeanVM.Guest.CoreMode.CoreRes
public meta import LeanVM.Guest.CoreRef
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«gkr_layer__L»
import LeanVM.Guest.Data.ValNames.«gkr_layer__L0_L0»
import LeanVM.Guest.Data.ValNames.«gkr_layer__L0_L1»
import LeanVM.Guest.Data.ValNames.«gkr_layer__L1_L0»
import LeanVM.Guest.Data.ValNames.«gkr_layer__L1_L1»
import LeanVM.Guest.Data.ValNames.«gkr_layer__L2_L0»
import LeanVM.Guest.Data.ValNames.«gkr_layer__L2_L1»
import LeanVM.Guest.Data.ValNames.«gkr_layer__L3_L0»
import LeanVM.Guest.Data.ValNames.«gkr_layer__L3_L1»

namespace LeanVM.Guest.CoreMode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- **`gkr_layer__L{p}_L{o}`'s cursors** (`EndExec.gl_curs`): the value its layer record's cursor is loaded to (`s4#0`),
read `8p` words past (its first `2p` rounds), and its last record's (`tcur`), read `4 (2 - o) + 12` words past (its last
rounds and the children). -/
def glCurs : List (String × List (ℕ × ℕ)) :=
  [(name% «gkr_layer__L0_L0», [(val% «gkr_layer__L0_L0» "tcur", 20)]),
    (name% «gkr_layer__L1_L0», [(valf% «gkr_layer» "s4#0", 8), (val% «gkr_layer__L1_L0» "tcur", 20)]),
    (name% «gkr_layer__L2_L0», [(valf% «gkr_layer» "s4#0", 16), (val% «gkr_layer__L2_L0» "tcur", 20)]),
    (name% «gkr_layer__L3_L0», [(valf% «gkr_layer» "s4#0", 24), (val% «gkr_layer__L3_L0» "tcur", 20)]),
    (name% «gkr_layer__L0_L1», [(val% «gkr_layer__L0_L1» "tcur", 16)]),
    (name% «gkr_layer__L1_L1», [(valf% «gkr_layer» "s4#0", 8), (val% «gkr_layer__L1_L1» "tcur", 16)]),
    (name% «gkr_layer__L2_L1», [(valf% «gkr_layer» "s4#0", 16), (val% «gkr_layer__L2_L1» "tcur", 16)]),
    (name% «gkr_layer__L3_L1», [(valf% «gkr_layer» "s4#0", 24), (val% «gkr_layer__L3_L1» "tcur", 16)])]

/-- **`gkr_layer`'s family** (`EndExec.GlQ`): a read `c` words past one of its cursors (`glCurs`), below its count, one
of its stream's, parameter `stream`'s `[0, 8192)`, either under branch conditions (`EndExec.glQC_inst`). -/
def glQC (fn : Fn) : CRes → Bool
  | .sub c q => (glCurs.lookup fn.name).any (fun cs ↦ match c.bases with
      | [(x, 1)] => cs.any fun p ↦ Nat.beq p.1 x && Nat.blt c.off p.2
      | _ => false) && decide (q = ⟨⟨[(valf% «gkr_layer» "stream", 1)], 0⟩, 1, .num 0, .num 8192⟩)
  | .under _ r => glQC fn r
  | _ => false

end

end LeanVM.Guest.CoreMode

namespace LeanVM.Guest.CoreMode.Own.gkr_layer

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- **Its family** (`glQC`). -/
noncomputable def fams : List (String × (Fn → CRes → Bool)) :=
  [name% «gkr_layer__L0_L0», name% «gkr_layer__L1_L0», name% «gkr_layer__L2_L0», name% «gkr_layer__L3_L0»,
    name% «gkr_layer__L0_L1», name% «gkr_layer__L1_L1», name% «gkr_layer__L2_L1», name% «gkr_layer__L3_L1»].map
    fun n ↦ (n, glQC)

end

end LeanVM.Guest.CoreMode.Own.gkr_layer
