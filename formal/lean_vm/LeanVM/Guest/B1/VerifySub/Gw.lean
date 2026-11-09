/-
  LeanVM.Guest.B1.VerifySub.Gw

  The constant `g^107` of `verify_sub`'s call of `verify_keccak`, as a word.
-/

module

public import LeanVM.Guest.B1.Common.Basic

/-!
# `g^107`

`word_g107`: the word `237494511599616` is `g^107`, the offset of the output lanes' values in
`col_eval_words` (claims `112 .. 136`, the buffer starting at claim `5`; G:3435).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol.Verifier

@[expose] public section

set_option maxRecDepth 100000 in
theorem word_g107 : word 237494511599616 0 0 = gen ^ 107 := by
  rw [word_eOfNat, gen_pow_eq_ofK, ← gpowK_eq (by unfold u128Bound; omega)]
  show ofK (K.ofBits 237494511599616) = ofK (gpowK 107)
  congr 1

end
end LeanVM.Guest.B1.VerifySub
