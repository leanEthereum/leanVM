/-
  LeanVM.Guest.CoreMode.Fn.da_verify.Fam

  `da_verify`'s own residual families (`CoreMode/FnReg.lean`): its blob count and gap.
-/

module

public import LeanVM.Guest.CoreMode.CoreRes
public meta import LeanVM.Guest.CoreRef
public import LeanVM.Guest.GuestConst
import LeanVM.Guest.Data.Consts
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«da_verify»

namespace LeanVM.Guest.CoreMode

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- **`da_verify`'s blob count and gap** (`EndExec.daV_inst`): its value `n_blob_g`, the blob count `g^n`, below `m`,
`DA_MAX_ROWS < m`, and its value `gap_g`, the gap, below `m`, `DA_MAX_ROWS ≤ m`, under branch conditions
(`EndExec.daVerifyGap_inst`). -/
def daVerifyGap (fn : Fn) : CRes → Bool
  | .lt a (.num m) => decide (m < capE) && fn.name == name% «da_verify» &&
      ((decide (a = .val (val% «da_verify» "n_blob_g")) && decide (guest_const% DA_MAX_ROWS < m)) ||
        (decide (a = .val (val% «da_verify» "gap_g")) && decide (guest_const% DA_MAX_ROWS ≤ m)))
  | .under _ r => daVerifyGap fn r
  | _ => false

end

end LeanVM.Guest.CoreMode

namespace LeanVM.Guest.CoreMode.Own.da_verify

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- **Its family** (`daVerifyGap`). -/
noncomputable def fams : List (String × (Fn → CRes → Bool)) := [(name% «da_verify», daVerifyGap)]

end

end LeanVM.Guest.CoreMode.Own.da_verify
