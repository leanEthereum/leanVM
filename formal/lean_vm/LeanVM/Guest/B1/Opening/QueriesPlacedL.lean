/-
  LeanVM.Guest.B1.Opening.QueriesPlacedL

  `opening_queries`' own words as layouts: its chain buffer; an honest query from the memory
  holding its windows, challenges, final coefficients, cap leaf and flag.
-/

module

public import LeanVM.Guest.B1.Opening.QueriesPlaced10
public import LeanVM.Guest.Memory.Uniform
public import LeanVM.Guest.AcceptableChild

/-!
# The function's own words, as layouts

`oqChainVals`: the chain buffer's `N + 1` words `oqChain … i`, the function's only own words
(its queries' path children are hinted into their `walk_path` frames). `qdOk_of_mem`: a memory
holding a query's windows, challenges, final coefficients, cap leaf and flag, with the opening's
static facts, gives the honest query `QD.Ok`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Main (MemL RegionL)

@[expose] public section

/-- The chain buffer's words. -/
def oqChainVals (odd base : ℕ) (lamInv : E) (ds : ℕ → E) (N : ℕ) : List E :=
  (List.range (N + 1)).map (oqChain odd base lamInv ds)

/-- **An honest query from the memory holding its windows**, challenges, final coefficients, cap
leaf and flag. -/
theorem qdOk_of_mem {rd : Reader} {s : Oq} {b : ℕ} {emit : Bool} {pr : ℕ} {w : QW}
    {cap flags coefs hsp bpv : E} {rounds : List FoldRound} {hsv : List E}
    (hrow : w.2.1.length = rowLen s.base s.folds) (hsl : w.2.2.length = s.pd)
    (hq : w.1 < 2 ^ (s.pd + s.cd))
    (hwin : ∀ i < qwN (s.pd + s.cd) s.cd, LoadHolds rd bpv i (gen ^ qwVal (s.pd + s.cd) s.cd w.1 i))
    (hc0 : LoadHolds rd cap (2 * (2 ^ s.cd + w.1 / 2 ^ s.pd))
      (digestHalves (climbD (merkleLeafDigest w.2.1) w.1 w.2.2)).1)
    (hc1 : LoadHolds rd cap (2 * (2 ^ s.cd + w.1 / 2 ^ s.pd) + 1)
      (digestHalves (climbD (merkleLeafDigest w.2.1) w.1 w.2.2)).2)
    (hfl : LoadHolds rd flags (2 ^ (s.cd - 1) + w.1 / 2 ^ (s.pd + 1)) 1)
    (hR : RoundsAt rd coefs rounds) (hrl : rounds.length = s.folds)
    (hfin : s.final = 1 → WordsAt rd hsp hsv ∧ hsv.length = s.nHs ∧
      foldRow (lanesOf s.base w.2.1) (K.ofBits w.1) rounds =
        novelSum hsv (wsChain (s.vs.map K.ofBits) (eOfNat w.1)) s.nHs s.hsBits) :
    (oqQD s b emit pr cap flags rounds hsv w).Ok rd coefs hsp bpv :=
  ⟨hsl, hrow, ⟨hwin, hc0, hc1, hfl⟩, hq, hR, hrl, hfin⟩

end
end LeanVM.Guest.B1
