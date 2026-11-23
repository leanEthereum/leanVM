/-
  LeanVM.Guest.B1.Place.Ls

  `level_residual_slow` complete placed, at every specialization `open_stacked` dispatches into: the
  statement.
-/

module

public import LeanVM.Guest.B1.Place.HelperAt
public import LeanVM.Guest.B1.Bits.QueryWindowsAt
public import LeanVM.Guest.B1.Whir.SlowSpec
public import LeanVM.Guest.B1.Whir.Config
public import LeanVM.Guest.Lift.RegD

/-!
# `level_residual_slow`, placed

`level_residual_slow__L{Q}_L{pre}_L{yr}_L{vo}(positions, fold_cs, tail_cs, λ, z)` returns `0` at
`z = 0` and, at `z = 1`, the unfactored sum over its `Q` positions (`slowVal`).

**The statement** (`LsAtO`): on every memory holding the caller's words `Lin` (the positions `p k`,
`k < Q`, at `positions`, the challenges `cs t` at `fold_cs` for `t < pre` and at `tail_cs` for the
`yr` after, all where `RegPtrs` says), at a flag `z ∈ {0, 1}`, the helper relates
`[positions, fold_cs, tail_cs, λ, z]` to `slowVal`, within the optional bound.
`level_residual_slow_completeAt_Spec`: every non-final level of every arm, at no bound and, frames
below `2^32`, within every bound of its trees.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)
open LeanVM.Guest.B1.Whir

@[expose] public section

/-- **`level_residual_slow` at `(name, Q, pre, yr, vo)`, placed at an optional words bound**: its loads
among the caller's words, on every memory holding the positions `p` and the challenges `cs`, at a
flag `z ∈ {0, 1}`, complete, returning `slowVal`. -/
def LsAtO (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ) (name : String) (Q pre yr vo : ℕ)
    (Bd : Option ℕ) : Prop :=
  ∀ (Lin : Layout) (P F T lam z : E) (p cs : ℕ → E), (z = 0 ∨ z = 1) →
    RegPtrs [(0, Q), (1, pre), (2, yr)] [P, F, T, lam, z] (RegionL Lin) →
    (∀ rd, LowDef κ rd → MemL rd Lin →
      (∀ k < Q, LoadHolds rd P k (p k)) ∧ (∀ t < pre, LoadHolds rd F t (cs t)) ∧
        ∀ j < yr, LoadHolds rd T j (cs (pre + j))) →
    CompleteAtO fs cert κ name Lin [P, F, T, lam, z] (Returns [slowVal Q (pre + yr) vo p cs lam z]) Bd

/-- **`level_residual_slow` is complete placed at every specialization `open_stacked` dispatches
into**: for frame runs fitting their frames, their cells consecutive, on memories defined below
`2^κ`, at every non-final level `l` of every arm, at no bound and, frames below `2^32`, within
every bound of its trees. -/
def level_residual_slow_completeAt_Spec : Prop :=
  ∀ (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ), Lift.RunsFit fs cert → RunsConsec cert →
    11 ≤ κ → ∀ m < 11, ∀ ri < 4, ∀ l < (osCfgR m ri).yrLevel, ∀ Bd : Option ℕ,
      (∀ B ∈ Bd, (∀ f, fs f < 2 ^ 32) ∧
        TotalLe coreProgram fs (osSlowName (osCfgR m ri) ((osCfgR m ri).levels.getD l default))
          (fun _ ↦ B)) →
      LsAtO fs cert κ (osSlowName (osCfgR m ri) ((osCfgR m ri).levels.getD l default))
        ((osCfgR m ri).levels.getD l default).queries ((osCfgR m ri).levels.getD l default).prefixLen
        (osCfgR m ri).yrLog ((osCfgR m ri).levels.getD l default).vanish Bd

end
end LeanVM.Guest.B1
