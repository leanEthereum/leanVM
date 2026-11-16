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
completeness chain so that the budget can cite them: `ly7W29`, `ly7B` (`Loop7T`'s iteration
bounds), `ly7Total` (`verify_bus_gkr_loop0`'s chain), `vbgSizes` (the buffers) and `vbgBound`.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core

@[expose] public section

/-- The words of `verify_bus_gkr_loop0_loop0` called below `g^j`: its run's `j` iterations and its
one phantom frame, or its frame when not entered. -/
def ly7W29 (fs : String → ℕ) (K29 j : ℕ) : ℕ := fs name% «verify_bus_gkr_loop0_loop0» + j * K29

/-- Iteration `c`'s words: its frame, `verify_bus_gkr_loop0_loop0`'s and `R` for its last rounds. -/
def ly7B (fs : String → ℕ) (K29 R : ℕ) (c : ℕ) : ℕ :=
  fs name% «verify_bus_gkr_loop0» + ly7W29 fs K29 c + R

/-- The buffers' sizes. -/
def vbgSizes (depth : ℕ) : List ℕ := [10 * (depth + 2), 6034, 1640, 33, 33, 3]

/-- `verify_bus_gkr_loop0`'s words from `1` below `g^((depth - 1)/2)`: the iterations' bounds and
the last tail's frame. -/
def ly7Total (fs : String → ℕ) (K29 R depth : ℕ) : ℕ :=
  Budget.iterSum (ly7B fs K29 R) 0 ((depth - 1) / 2) + fs name% «verify_bus_gkr_loop0»

/-- `verify_bus_gkr`'s words: its frame, its buffers, `verify_bus_gkr_loop0`'s chain,
`verify_bus_gkr_loop1`'s run (`depth` iterations of at most `K8` words and its one phantom frame),
and the frames of its two conditional
calls. -/
noncomputable def vbgBound (fs : String → ℕ) (K29 R K8 depth : ℕ) : ℕ :=
  fs "verify_bus_gkr" + (vbgSizes depth).sum +
    ([ly7Total fs K29 R depth, depth * K8 + fs name% «verify_bus_gkr_loop1»].sum + ifFrames fs
        vbgPre)

end
end LeanVM.Guest.B1.Tables
