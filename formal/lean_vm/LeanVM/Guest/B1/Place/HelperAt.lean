/-
  LeanVM.Guest.B1.Place.HelperAt

  The placed form of `open_stacked`'s helpers' completeness: on disjoint layouts, with or without a
  words bound, reading a fixed layout or one that depends on the frame pointer.
-/

module

public import LeanVM.Guest.Memory.Uniform
public import LeanVM.Guest.Memory.Size

/-!
# The helpers' placed form

`open_stacked`'s arm calls three helpers by a dispatch on the rate's selector: `level_positions`,
`level_queries` and `level_residual` (`Whir/HelperT.lean`). Each one's placed completeness
(`Place/Lp.lean`, `Lq.lean`, `Lr.lean`) takes an optional words bound `Bd`: with `none` it is
`CompleteAtD`, with `some B`, a bound of every valid tree of the helper (`TotalLe`, what
`OsLeafBounds` gives the arm), it is `CompleteAtB … B`. One statement gives both the arm's
`open_stacked_completeAtD` and its `open_stacked_completeAtB`.

* `CompleteAtO … Bd`: `CompleteAtD` or `CompleteAtB`, by `Bd` (`toD`, `toB` and back, `toO`).
* `CompleteAtPO … Lin rets Lout Bd`: the same with the words read (`Lin fp`) and the buffers
  handed back (`Lout fp`) depending on the frame pointer `fp`. `level_positions` takes this form:
  the caller's window pointers point into its decoders' frames.
* `BoundsAt fs f Bd`: `Bd` bounds every valid tree of `f`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

/-- `Bd`, when given, bounds every valid tree of `f` (`TotalLe`). -/
def BoundsAt (fs : String → ℕ) (f : String) (Bd : Option ℕ) : Prop :=
  ∀ B ∈ Bd, TotalLe coreProgram fs f (fun _ ↦ B)

/-- **`f` is complete at every frame pointer, on disjoint layouts, by a tree within `Bd` when
given**: `CompleteAtD` at `none`, `CompleteAtB … B` at `some B`. -/
def CompleteAtO (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) (f : String) (Lin : Layout)
    (args : List E) (Out : List E → Layout → Prop) (Bd : Option ℕ) : Prop :=
  ∀ fp, ∃ (n : ℕ) (Lown : Layout) (rets : List E) (Lout : Layout), Out rets Lout ∧
    Within (Lout ++ Lown) fp n ∧ DisjL (Lout ++ Lown) ∧ (∀ B ∈ Bd, n ≤ B) ∧ ∀ rd, LowDef k rd →
      MemL rd (Lout ++ Lown ++ Lin) →
      RelAtIn coreProgram fs cert rd (RegionL Lin) (RegionL Lout) fp n f args rets

/-- **`f` is complete at every frame pointer `fp`, on disjoint layouts, reading `Lin fp` and
handing back the buffers `Lout fp`**, by a tree within `Bd` when given. -/
def CompleteAtPO (fs : String → ℕ) (cert : String → V → ℕ) (k : ℕ) (f : String)
    (Lin : ℕ → Layout) (args rets : List E) (Lout : ℕ → Layout) (Bd : Option ℕ) : Prop :=
  ∀ fp, ∃ (n : ℕ) (Lown : Layout), Within (Lout fp ++ Lown) fp n ∧ DisjL (Lout fp ++ Lown) ∧
    (∀ B ∈ Bd, n ≤ B) ∧ ∀ rd, LowDef k rd → MemL rd (Lout fp ++ Lown ++ Lin fp) →
      RelAtIn coreProgram fs cert rd (RegionL (Lin fp)) (RegionL (Lout fp)) fp n f args rets

variable {fs : String → ℕ} {cert : String → V → ℕ} {k : ℕ} {f : String}

theorem CompleteAtO.toD {Lin : Layout} {args : List E} {Out : List E → Layout → Prop}
    (h : CompleteAtO fs cert k f Lin args Out none) : CompleteAtD fs cert k f Lin args Out := fun fp ↦
  let ⟨n, Lown, rets, Lout, ho, hw, hd, _, hr⟩ := h fp
  ⟨n, Lown, rets, Lout, ho, hw, hd, hr⟩

theorem CompleteAtO.toB {Lin : Layout} {args : List E} {Out : List E → Layout → Prop} {B : ℕ}
    (h : CompleteAtO fs cert k f Lin args Out (some B)) : CompleteAtB fs cert k f Lin args Out B :=
  fun fp ↦
    let ⟨n, Lown, rets, Lout, ho, hw, hd, hn, hr⟩ := h fp
    ⟨n, Lown, rets, Lout, ho, hw, hd, hn B rfl, hr⟩

theorem CompleteAtD.toO {Lin : Layout} {args : List E} {Out : List E → Layout → Prop}
    (h : CompleteAtD fs cert k f Lin args Out) : CompleteAtO fs cert k f Lin args Out none := fun fp ↦
  let ⟨n, Lown, rets, Lout, ho, hw, hd, hr⟩ := h fp
  ⟨n, Lown, rets, Lout, ho, hw, hd, fun _ h ↦ by simp at h, hr⟩

theorem CompleteAtB.toO {Lin : Layout} {args : List E} {Out : List E → Layout → Prop} {B : ℕ}
    (h : CompleteAtB fs cert k f Lin args Out B) : CompleteAtO fs cert k f Lin args Out (some B) :=
  fun fp ↦
    let ⟨n, Lown, rets, Lout, ho, hw, hd, hn, hr⟩ := h fp
    ⟨n, Lown, rets, Lout, ho, hw, hd, fun _ h ↦ by cases h; exact hn, hr⟩

end
end LeanVM.Guest.B1
