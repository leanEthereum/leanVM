/-
  LeanVM.Guest.B1.Sig.XmssBound

  The range bound of `__loop2`'s 8-bit dispatches is `g^255`.
-/

module

public import LeanVM.Guest.B1.Sig.XmssSegT

/-!
# `g^255`

`bound255_eq`: the reduced word `bound255` the windows and the digit words are range-checked
against is `g^255`, so a range check against it has witnesses at `k` and `255 - k`.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

theorem bound255_eq : bound255 = ofK (addressOfIndex 255) := by
  rw [bound255, word, Value.ofBits_zero, ← ofK_eq_ofLimbs]
  exact congrArg ofK (by decide +kernel)

end
end LeanVM.Guest.B1.Sig
