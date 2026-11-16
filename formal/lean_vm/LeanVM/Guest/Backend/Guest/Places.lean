/-
  LeanVM.Guest.Backend.Guest.Places

  The places of the guest's values, read off the back end's input alone, and the guest world's
  valuation by them.
-/

module

public import LeanVM.Guest.Backend.Guest.World

/-!
# The guest's places

`gLocs g` is where `placeProgram guestTraced` puts the values of function `g` (`World.locs` of a
world whose input is `guestTraced`, on the empty memory `gWorld`). It depends on the input only
(`locs_of_p`), so every guest world places as it does (`world_locs`), and its valuation of `g` at
`fp` is the valuation by `gLocs g` (`vf_eq`).
-/

namespace LeanVM.Guest.Backend

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- The back end's input for the guest as a world on the empty memory: what places its values
(`World.locs`) reads of a world is its input. -/
noncomputable def gWorld : World 0 :=
  ⟨guestTraced, [], #[], 0, Nat.zero_le _, fun _ => 0, fun _ _ => True⟩

/-- **The places of the guest function `g`'s values**: `placeProgram guestTraced`'s. -/
noncomputable def gLocs (g : String) : VMap Loc := gWorld.locs g

theorem locs_of_p {κ κ' : ℕ} {W : World κ} {W' : World κ'} (h : W.p = W'.p) (g : String) :
    W.locs g = W'.locs g := by
  unfold World.locs World.placed
  rw [h]

theorem gWorld_p : gWorld.p = guestTraced := rfl

theorem world_locs {κ : ℕ} {fns : List Lowered} {slots : Array KVal} {L : MemoryImage κ}
    {U : String → List E → Prop} (g : String) : (guestWorld fns slots L U).locs g = gLocs g :=
  locs_of_p (guestWorld_p.trans gWorld_p.symm) g

/-- The guest world's valuation of `g` at `fp` is the valuation by `gLocs g`. -/
theorem vf_eq {κ : ℕ} {fns : List Lowered} {slots : Array KVal} {L : MemoryImage κ}
    {U : String → List E → Prop} (g : String) (fp : K) :
    (guestWorld fns slots L U).vf g fp = valP L fp (gLocs g) := by
  unfold World.vf
  rw [world_locs]
  rfl

end
end LeanVM.Guest.Backend
