/-
  LeanVM.Protocol.ToArkLib.Refinement

  A refinement of relations: a witness map that preserves validity, and how an extractor
  follows it. Candidate for ArkLib.
-/

module

public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Option.Basic

/-!
# Refinements

A `Refinement R S` between two relations over the same statements is a map on witnesses that
sends every witness valid for `R` to one valid for `S`. Knowledge of `R` then yields knowledge of
`S` by applying the map to whatever an extractor returns: `map_option_valid` is that step on an
extractor's output slot (a witness, or a failure).
-/

namespace LeanVM.Protocol

@[expose] public section

/-- A witness map between two relations over the same statements, preserving validity. -/
structure Refinement {Stmt : Type} {W₁ W₂ : Type _} (R : Set (Stmt × W₁))
    (S : Set (Stmt × W₂)) where
  /-- The witness map, at each statement. -/
  map : Stmt → W₁ → W₂
  /-- A witness valid for `R` maps to one valid for `S`. -/
  map_valid : ∀ x w, (x, w) ∈ R → (x, map x w) ∈ S

namespace Refinement

variable {Stmt : Type} {W₁ W₂ W₃ : Type _}

/-- The identity refinement. -/
def id (R : Set (Stmt × W₁)) : Refinement R R where
  map := fun _ w ↦ w
  map_valid := fun _ _ h ↦ h

/-- `g.comp f` is `g` after `f`. -/
def comp {R : Set (Stmt × W₁)} {S : Set (Stmt × W₂)} {T : Set (Stmt × W₃)}
    (g : Refinement S T) (f : Refinement R S) : Refinement R T where
  map := fun x w ↦ g.map x (f.map x w)
  map_valid := fun x w h ↦ g.map_valid x _ (f.map_valid x w h)

/-- On an extractor's output slot: if every witness the slot may hold is valid for `R`, every
witness the mapped slot may hold is valid for `S`. -/
theorem map_option_valid {R : Set (Stmt × W₁)} {S : Set (Stmt × W₂)} (f : Refinement R S)
    (x : Stmt) (w? : Option W₁) (h : ∀ w ∈ w?, (x, w) ∈ R) :
    ∀ w' ∈ w?.map (f.map x), (x, w') ∈ S := by
  intro w' hw'
  obtain ⟨w, hw, rfl⟩ := Option.mem_map.mp hw'
  exact f.map_valid x w (h w hw)

end Refinement

end
end LeanVM.Protocol
