/-
  LeanVM.Guest.B1.VsC.CapDepth

  The honest Merkle hints' cap depth is the one the guest's opening is specialized at, at every
  stack size, rate and level.
-/

module

public import LeanVM.Guest.B1.Whir.Config
public import Statement.LeanVmGuestProver

/-!
# The cap depth of the honest Merkle hints

The honest prover pushes each level's cap at `capDepthOf count depth` (`levelHints`,
`Statement/LeanVmGuestProver.lean`, from `merkle_cap_depth`, `child.rs`), at the level's query
count and the height of the commitment it opens; `open_stacked` reads it at `LIG_CAP_DEPTH`, a
table the compiler bakes into each level's `level_queries` and `level_positions` specialization.
`capDepth_honest`: at every size `16 + m`, `m < 15`, every rate `r + 1`, `r < 4`, and every level,
the two agree, on the level's `LIG_QUERIES` and `LIG_TREE_DEPTH` (which `Whir/Facts` shows are the
verifier's query count and the commitment's height). Decided by the kernel.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Guest.B1.Whir

@[expose] public section

/-- **The honest cap depth is `LIG_CAP_DEPTH`** at every size, rate and level. -/
theorem capDepth_honest : ∀ m < ligNSizes, ∀ r < ligNRates, ∀ lvl < osNLevels m,
    Prover.capDepthOf (osLvR m r lvl).queries (osLvR m r lvl).depth = (osLvR m r lvl).capDepth := by
  decide +kernel

end
end LeanVM.Guest.B1.VsC
