/-
  LeanVM.Guest.B1.Place.Lr

  `level_residual` complete placed, at every specialization of `lrTable`: the statement.
-/

module

public import LeanVM.Guest.B1.Place.HelperAt
public import LeanVM.Guest.B1.Bits.QueryWindowsAt
public import LeanVM.Guest.B1.Whir.HelperTables
public import LeanVM.Guest.B1.Whir.HelperT
public import LeanVM.Guest.B1.Whir.LrSound
public import LeanVM.Guest.Lift.RegD

/-!
# `level_residual`, placed

`level_residual__L{q}_L{cols}_L{nhs}_L{hbits}(positions, row_d, hs, mu)` (`lrBody q loop1 loop2`)
runs the chains `h ← (h + P(p))·μ`, `hh ← (hh + H(p))·μ` over its `q` positions: the batches'
loop (`lrLoop1Body`, `resBatch` positions an iteration, its chains a `HeapBuf` of `2(q/resBatch +
1)` cells), then, when `8 ∤ q`, the rest's loop (`lrLoop2Body`, its chains a second `HeapBuf`), and
returns the chains' ends (`MeaningLevelResidual`'s values).

**The statement** (`LrAtD`): on every memory holding the caller's words `Lin` (the positions `p i`,
`i < q`, at `positions`, row `D s`, `s < cols`, of `basis_d` at `row_d`, the high part's `nhs`
coefficients at `hs`, all where `RegPtrs` says), the helper relates `[positions, row_d, hs, μ]`
to the chains' ends. `level_residual_completeAt_Spec`: every entry of `lrTable`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)
open LeanVM.Guest.B1.Whir

@[expose] public section

/-- The chains' ends `level_residual` returns over the positions `p`, the row `D`, the high
part `hsv`, at `μ`. -/
def lrRet (q cols nhs hbits : ℕ) (D : ℕ → E) (hsv : List E) (p : ℕ → E) (M : E) : E × E :=
  resFold (lrP cols D) (lrH cols nhs hbits hsv) M (0, 0) ((List.range q).map p)

/-- **`level_residual` at `(name, q, cols, nhs, hbits)`, placed**: its loads among the caller's
words, on every memory holding the positions `p`, the row `D` and the high part `hsv`, complete,
returning the chains' ends. -/
def LrAtD (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ) (name : String)
    (q cols nhs hbits : ℕ) : Prop :=
  ∀ (Lin : Layout) (P BD HS M : E) (D p : ℕ → E) (hsv : List E), hsv.length = nhs →
    RegPtrs [(0, q), (1, cols), (2, nhs)] [P, BD, HS, M] (RegionL Lin) →
    (∀ rd, LowDef κ rd → MemL rd Lin →
      (∀ i < q, LoadHolds rd P i (p i)) ∧ (∀ s < cols, LoadHolds rd BD s (D s)) ∧
        ∀ c < nhs, LoadHolds rd HS c (hsv.getD c 0)) →
    CompleteAtD fs cert κ name Lin [P, BD, HS, M]
      (Returns [(lrRet q cols nhs hbits D hsv p M).1, (lrRet q cols nhs hbits D hsv p M).2])

/-- **`level_residual` is complete placed at every specialization**: for frame runs fitting their
frames, their cells consecutive, on memories defined below `2^κ`, each entry
`(name, q, cols, nhs, hbits, loop1, loop2)` of `lrTable` is `LrAtD`. -/
def level_residual_completeAt_Spec : Prop :=
  ∀ (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ), Lift.RunsFit fs cert → RunsConsec cert →
    11 ≤ κ → ∀ e ∈ lrTable, LrAtD fs cert κ e.1 e.2.1 e.2.2.1 e.2.2.2.1 e.2.2.2.2.1

end
end LeanVM.Guest.B1
