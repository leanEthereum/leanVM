/-
  LeanVM.Guest.B1.VsC.VsWord

  A constant word `2^j` is `g^j`.
-/

module

public import LeanVM.Guest.Value.Bits
public import LeanVM.Guest.Core
import LeanVM.Guest.B1.Sig.CwComplete

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Protocol.Verifier

@[expose] public section

theorem wordG {j : ℕ} (hj : j < 64) : word (2 ^ j) 0 = gen ^ j := by
  rw [B1.Sig.word_two_pow_eq hj, Value.gen_pow_eq_ofK]

end
end LeanVM.Guest.B1.VsC
