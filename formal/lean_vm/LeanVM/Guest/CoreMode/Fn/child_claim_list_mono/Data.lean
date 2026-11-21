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
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.child_claim_list_mono_loop0
import LeanVM.Guest.Data.ValNames.child_claim_list_mono_loop1

namespace LeanVM.Guest.CoreMode.Own.child_claim_list_mono

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- **Its frame loops** (`CoreMode.cmK`): their claims a frame, `CLAIM_BIG` and `CLAIM_GROUP`; claim `jj`'s entry
`[s4#1]·Π_{i ≤ jj}[gap@1 + 10i]^4`, each iteration's gap ten values on; its frame's cells `2` (the entries) and `5`
(`limit`) their first two ghost slots (`CoreMode.cmGl`). -/
def cmLoops : List (String × ℕ × ℕ × ℕ × ℕ × List ℕ) :=
  [(name% «child_claim_list_mono_loop0», guest_const% CLAIM_BIG,
      val% «child_claim_list_mono_loop0» «child_claim_list_mono_loop1» "s4#1",
      val% «child_claim_list_mono_loop0» «child_claim_list_mono_loop1» "gap@1", 10, [2, 5]),
    (name% «child_claim_list_mono_loop1», guest_const% CLAIM_GROUP,
      val% «child_claim_list_mono_loop0» «child_claim_list_mono_loop1» "s4#1",
      val% «child_claim_list_mono_loop0» «child_claim_list_mono_loop1» "gap@1", 10, [2, 5])]

end

end LeanVM.Guest.CoreMode.Own.child_claim_list_mono
