/-
  LeanVM.Guest.B1.Place.Lr

  `level_residual` complete placed, at every specialization of `lrTable`: the statement.
-/

module

public import LeanVM.Guest.B1.Place.HelperAt
public import LeanVM.Guest.B1.Bits.QueryWindowsAt
public import LeanVM.Guest.B1.Whir.CLr
public import LeanVM.Guest.B1.Whir.HelperAll
public import LeanVM.Guest.Lift.OsCallees

/-!
# `level_residual`, placed

`level_residual__L{q}_L{cols}(positions, row_d, mu)` (`lrBody q loop1 loop2`) runs the chain
`h ← (h + R(p))·μ` over its `q` positions: the batches' loop (`lrLoop1Body cols`, one
`residual_batch__L{cols}` of eight positions an iteration, its chain a `HeapBuf` of
`q / 8 + 1` cells), then, when `8 ∤ q`, the rest's loop (`lrLoop2Body cols`, its chain a second
`HeapBuf`), and returns the chain's end `lrAcc D cols μ p q`.

**The statement** (`LrAtO`): on every memory holding the caller's words `Lin` (the positions `p i`,
`i < q`, at `positions`, row `D s`, `s < cols`, of `basis_d` at `row_d`, both where `RegPtrs`
says), the helper relates `[positions, row_d, μ]` to `[lrAcc D cols μ p q]`, by a tree within
`Bd` when given. `level_residual_completeAt_Spec`: every entry of `lrTable`.

**Design note for the proof.** Build on:
* `lr_complete` and `rb_complete` (`Whir/CLr.lean`): the unplaced relations, from the two chain
  buffers holding the honest chain (`lrAcc`); `lrTable_ok`, `rbTable_ok` for the bodies.
* `residual_batch` is a leaf of its loop: placed from its relation like a leaf (its loads the
  batch's eight positions and the row, `RegPtrs [(0, 8), (1, cols)]`).
* the placement of two loops with one callee an iteration (the old `Place/ResAt.lean`,
  `os_res_completeAtD`, placed `open_stacked`'s residual loop, without the chain buffers), the
  bound by `TotalLe` at `Bd = some B`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)
open LeanVM.Guest.B1.Whir (lrAcc lrTable)

@[expose] public section

/-- **`level_residual` at `(name, q, cols)`, placed**: its loads among the caller's words, on every
memory holding the positions `p` and the row `D`, complete by a tree within `Bd` when given,
returning the chain's end. -/
def LrAtO (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ) (name : String) (q cols : ℕ)
    (Bd : Option ℕ) : Prop :=
  ∀ (Lin : Layout) (P BD M : E) (D p : ℕ → E),
    RegPtrs [(0, q), (1, cols)] [P, BD, M] (RegionL Lin) →
    (∀ rd, LowDef κ rd → MemL rd Lin →
      (∀ i < q, LoadHolds rd P i (p i)) ∧ ∀ s < cols, LoadHolds rd BD s (D s)) →
    BoundsAt fs name Bd →
    CompleteAtO fs cert κ name Lin [P, BD, M] (Returns [lrAcc D cols M p q]) Bd

/-- **`level_residual` is complete placed at every specialization**: for frame runs fitting their
frames, their cells consecutive, on memories defined below `2^κ`, `7 ≤ κ`, each entry
`(name, q, cols, loop1, loop2)` of `lrTable` is `LrAtO` at every bound. -/
def level_residual_completeAt_Spec : Prop :=
  ∀ (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ), Lift.RunsFit fs cert → RunsConsec cert →
    7 ≤ κ → ∀ e ∈ lrTable, ∀ Bd : Option ℕ, LrAtO fs cert κ e.1 e.2.1 e.2.2.1 Bd

end
end LeanVM.Guest.B1
