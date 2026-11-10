/-
  LeanVM.Guest.B1.Digest.PairComplete

  Loads and limb hints on an evaluated valuation (`pack_pair`'s module, kept for its lemmas).
-/

module

public import LeanVM.Guest.B1.Digest.Basic
public import LeanVM.Guest.B1.Fwd.Canon

/-!
# Loads and limbs on an evaluated valuation

`rdAt_of_load`: a load that holds reads its word; `limbAt_zero`, `limbAt_one`: a limb hint's
words.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Guest.B1.Fwd

@[expose] public section

variable {rd : Reader}

theorem rdAt_of_load {p : E} {k : ℕ} {v : E} (h : LoadHolds rd p k v) : rdAt rd p k = v := by
  unfold rdAt; rw [h.2]; rfl

theorem limbAt_zero (x : E) : limbAt x 0 = ofK (x.limb 0) := rfl

theorem limbAt_one (x : E) : limbAt x 1 = ofK (x.limb 1) := rfl

end
end LeanVM.Guest.B1.Digest
