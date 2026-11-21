/-
  LeanVM.Guest.CoreMode.Fn.child_claim_list_mono.Data

  `child_claim_list_mono`'s own routing data (`CoreMode/FnReg.lean`): its frame loops.
-/

module

public meta import LeanVM.Guest.CoreRef
public import LeanVM.Guest.Data.NameStrings
public import LeanVM.Guest.Renumber
public import LeanVM.Guest.GuestConst
import LeanVM.Guest.Data.Consts

namespace LeanVM.Guest.CoreMode.Own.child_claim_list_mono

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- **Its frame loops** (`CoreMode.cmK`): their claims a frame, `CLAIM_BIG` and `CLAIM_GROUP`. -/
def cmLoops : List (String × ℕ) :=
  [(name% «child_claim_list_mono_loop0», guest_const% CLAIM_BIG),
    (name% «child_claim_list_mono_loop1», guest_const% CLAIM_GROUP)]

end

end LeanVM.Guest.CoreMode.Own.child_claim_list_mono
