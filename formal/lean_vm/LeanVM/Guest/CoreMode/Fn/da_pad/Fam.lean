/-
  LeanVM.Guest.CoreMode.Fn.da_pad.Fam

  `da_pad`'s own residual families (`CoreMode/FnReg.lean`): its gap.
-/

module

public import LeanVM.Guest.CoreMode.CoreRes
public meta import LeanVM.Guest.CoreRef
public import LeanVM.Guest.GuestConst
import LeanVM.Guest.Data.Consts
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«da_pad»

namespace LeanVM.Guest.CoreMode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- **`da_pad`'s gap** (`EndExec.DaPadQ`): its parameter `gap_g`, the gap `g^(DA_MAX_ROWS - n)` `da_verify` hands it, has
an exponent below `m`, `DA_MAX_ROWS ≤ m`, under branch conditions (`EndExec.daPadGap_inst`). -/
def daPadGap (fn : Fn) : CRes → Bool
  | .lt a (.num m) => decide (m < capE) && fn.name == name% «da_pad» && decide (a = .val (val% «da_pad» "gap_g")) &&
      decide (guest_const% DA_MAX_ROWS ≤ m)
  | .under _ r => daPadGap fn r
  | _ => false

end

end LeanVM.Guest.CoreMode

namespace LeanVM.Guest.CoreMode.Own.da_pad

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- **Its family** (`daPadGap`). -/
noncomputable def fams : List (String × (Fn → CRes → Bool)) := [(name% «da_pad», daPadGap)]

end

end LeanVM.Guest.CoreMode.Own.da_pad
