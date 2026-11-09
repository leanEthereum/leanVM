/-
  LeanVM.Guest.B1.Opening.QueriesPlacedL

  `opening_queries`' own words as layouts: its chain buffer; an honest query from the memory
  holding its windows, weights, cap leaf and flag.
-/

module

public import LeanVM.Guest.B1.Opening.QueriesPlaced10
public import LeanVM.Guest.Memory.Uniform
public import LeanVM.Guest.AcceptableChild

/-!
# The function's own words, as layouts

`oqChainVals`: the chain buffer's `N + 1` words `oqChain … i`, the function's only own words
(its queries' path children are hinted into their `walk_path` frames, 40f877dc). `qdOk_of_mem`: a memory
holding a query's windows, weights, cap leaf and flag gives the honest query `QD.Ok`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Main (MemL RegionL)

@[expose] public section

/-- The chain buffer's words. -/
def oqChainVals (odd base : ℕ) (lam : E) (ds : ℕ → E) (N : ℕ) : List E :=
  (List.range (N + 1)).map (oqChain odd base lam⁻¹ ds)

/-- **An honest query from the memory holding its windows**, weights, cap leaf and flag. -/
theorem qdOk_of_mem {rd : Reader} {s : Oq} {b : ℕ} {emit : Bool} {pr : ℕ} {row : List K}
    {w : ℕ → E} {q : ℕ} {sibs : List Digest} {cap flags wp bpv : E}
    (hrow : row.length = s.R) (hsl : sibs.length = s.pd) (hq : q < 2 ^ (s.pd + s.cd))
    (hwin : ∀ i < qwN (s.pd + s.cd) s.cd, LoadHolds rd bpv i (gen ^ qwVal (s.pd + s.cd) s.cd q i))
    (hw : ∀ l < s.lo + s.I / s.lo, LoadHolds rd wp l (w l))
    (hc0 : LoadHolds rd cap (2 * (2 ^ s.cd + q / 2 ^ s.pd))
      (digestHalves (climbD (merkleLeafDigest row) q sibs)).1)
    (hc1 : LoadHolds rd cap (2 * (2 ^ s.cd + q / 2 ^ s.pd) + 1)
      (digestHalves (climbD (merkleLeafDigest row) q sibs)).2)
    (hfl : LoadHolds rd flags (2 ^ (s.cd - 1) + q / 2 ^ (s.pd + 1)) 1) :
    (⟨s, b, emit, pr, row, w, q, sibs, cap, flags⟩ : QD).Ok rd wp bpv :=
  ⟨hsl, hrow, ⟨hwin, hc0, hc1, hfl⟩, hw, hq⟩

end
end LeanVM.Guest.B1
