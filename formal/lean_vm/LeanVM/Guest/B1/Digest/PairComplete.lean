/-
  LeanVM.Guest.B1.Digest.PairComplete

  A load that holds reads its word.
-/

module

public import LeanVM.Guest.B1.Digest.Basic
public import LeanVM.Guest.B1.Fwd.Canon

/-!
# Loads on an evaluated valuation

`rdAt_of_load`: a load that holds reads its word.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Guest.B1.Fwd

@[expose] public section

variable {rd : Reader}

theorem rdAt_of_load {p : E} {k : ℕ} {v : E} (h : LoadHolds rd p k v) : rdAt rd p k = v := by
  unfold rdAt; rw [h.2]; rfl

end
end LeanVM.Guest.B1.Digest
