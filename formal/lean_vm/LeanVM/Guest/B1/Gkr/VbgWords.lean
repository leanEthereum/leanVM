/-
  LeanVM.Guest.B1.Gkr.VbgWords

  `verify_bus_gkr`'s words interface: what its bound needs of the frame sizes (`VbgWords`) and its bound over the
  depths (`vbgMax`).
-/

module

public import LeanVM.Guest.B1.Lmax
public import LeanVM.Guest.B1.Gkr.VbgBound
public import LeanVM.Guest.B1.Gkr.GlCLayers
public import LeanVM.Guest.Budget.Static
public import LeanVM.Guest.Memory.LoopPre
public import LeanVM.Guest.Data.NameStrings

/-!
# `verify_bus_gkr`'s words

Its callers name only this interface: `VbgWords fs`, its callees' words facts at the frame sizes `fs` (the
radix-four layers' trees, `KL`; its loop's per iteration, `K8`); `vbgMax fs W`, its bound over the depths below
`32`. `VbgWordsC` proves its completeness within it.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node LeanVM.Guest.Memory

@[expose] public section

/-- **`verify_bus_gkr`'s words facts** at the frame sizes `fs`: the radix-four layers' trees (`gkr_layers__L{o}`,
on its dispatch's arguments) and its loop's words per iteration, its run's one phantom frame charged once by the
`TotalLeOn … LoopPre` fact. -/
structure VbgWords (fs : String → ℕ) : Type where
  KL : ℕ
  K8 : ℕ
  hL : ∀ o < 2, TotalLeOn coreProgram fs (glcLsN o)
    (fun a ↦ ∃ n ≤ 3, ∃ r < 4, a.getD 3 0 = gen ^ n ∧ a.getD 4 0 = gen ^ r) (fun _ ↦ KL)
  h8 : TotalLeOn coreProgram fs name% «verify_bus_gkr_loop0» LoopPre (fun a ↦ logG (a.getD 1 0) *
      K8 + fs name% «verify_bus_gkr_loop0»)

/-- `verify_bus_gkr`'s bound over the depths below `32`, from its words' numbers. -/
@[irreducible] noncomputable def vbgMaxOf (fs : String → ℕ) (KL K8 : ℕ) : ℕ :=
  lmax ((List.range 32).map (vbgBound fs KL K8))

/-- **`verify_bus_gkr`'s bound** over the depths below `32`. -/
noncomputable def vbgMax (fs : String → ℕ) (W : VbgWords fs) : ℕ := vbgMaxOf fs W.KL W.K8

theorem vbgBound_le_vbgMax {fs : String → ℕ} (W : VbgWords fs) {d : ℕ} (hd : d < 32) :
    vbgBound fs W.KL W.K8 d ≤ vbgMax fs W := by
  unfold vbgMax vbgMaxOf
  exact le_lmax (List.mem_map.2 ⟨d, List.mem_range.2 hd, rfl⟩)

end
end LeanVM.Guest.B1.Tables
