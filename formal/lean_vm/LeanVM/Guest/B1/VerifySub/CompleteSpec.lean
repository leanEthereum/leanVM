/-
  LeanVM.Guest.B1.VerifySub.CompleteSpec

  What a caller of `verify_sub` holds for its completeness: the exponent tables at `g^sqE`.
-/

module

public import LeanVM.Guest.B1.VerifySub.Interface
public import LeanVM.Guest.Limits
public import LeanVM.Guest.Hints
public import LeanVM.Guest.Memory.LiftPure
public import LeanVM.Guest.B1.Bits.QueryWindowsAt
public import LeanVM.Guest.B1.Bits.Log2Placed
public import LeanVM.Guest.B1.Bits.Tables
public import LeanVM.Guest.AcceptableChild

/-!
# The caller's exponent tables

`vsExpLin sqE`: the words a caller of `verify_sub` holds at `g^sqE`, the exponent table and its
window section (`expTabAllWords`). `verify_sub`'s completeness is bounded, by its callees' trees
(`VerifySub/CompleteBT`'s `verify_sub_completeBT`): no statement at every frame size remains.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node LeanVM.Guest.B1.Main

@[expose] public section

/-- The caller's exponent tables at `g^sqE`: the exponent table and its window section. -/
def vsExpLin (sqE : ℕ) : Main.Layout := [(sqE, expTabAllWords)]

end
end LeanVM.Guest.B1.VerifySub
