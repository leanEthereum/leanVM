/-
  LeanVM.Guest.B1.Gkr.VbgBound

  `verify_bus_gkr`'s words bound (`vbgBound`) and its parts, as definitions only.
-/

module

public import LeanVM.Guest.B1.Gkr.Holds
public import LeanVM.Guest.Budget.Chain
public import LeanVM.Guest.B1.Tables.FlatLiftT
public import LeanVM.Guest.Data.NameStrings

/-!
# `verify_bus_gkr`'s words

The definitions of `vbgBound` (`VbgB`'s `verify_bus_gkr_completeAtTB` proves it), apart from the
completeness chain so that the budget can cite them: `vbgSizes` (the buffers) and `vbgBound`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core

@[expose] public section

/-- The buffers' sizes: `layers`, `gkr_sizes`, the round records and the point rows at the depth,
the tables `depth_odd`, `four_bounds`, `four_rem`, and the last slot's values. -/
def vbgSizes (depth : ℕ) : List ℕ :=
  [10 * (depth + 2), 66, 7 * gkRecCount depth, (depth / 2 + 2) * 40, 33, 33, 33, 3]

/-- `verify_bus_gkr`'s words: its frame, its buffers, the radix-four layers' call tree
(`gkr_layers__L{o}`, at most `KL` words), `verify_bus_gkr_loop0`'s run (`depth` iterations of at
most `K8` words and its one phantom frame), and the frames of its two conditional calls. -/
noncomputable def vbgBound (fs : String → ℕ) (KL K8 depth : ℕ) : ℕ :=
  fs "verify_bus_gkr" + (vbgSizes depth).sum +
    ([KL, depth * K8 + fs name% «verify_bus_gkr_loop0»].sum + ifFrames fs vbgPre)

end
end LeanVM.Guest.B1.Tables
