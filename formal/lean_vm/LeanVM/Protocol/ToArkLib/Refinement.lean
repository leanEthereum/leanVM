/-
  LeanVM.Protocol.ToArkLib.Refinement

  A refinement of relations: a witness map that preserves validity, and how an extractor
  follows it. Candidate for ArkLib.
-/

module

public import ArkLib.Interaction.Oracle.Security.Knowledge

/-!
# Refinements

A `Refinement R S` between two relations over the same statements is a map on witnesses that
sends every witness valid for `R` to one valid for `S`. Knowledge of `R` then yields knowledge of
`S` by applying the map to whatever an extractor returns: `map_option_valid` is that step on an
extractor's output slot (a witness, or a failure), and `knowledge_transport` is the step on a
knowledge certificate: on a path whose terminal witness holds, if the extracted witness mapped by
the refinement is invalid for `S`, the extracted witness is invalid for `R`, so a challenge on
the path was bad (ArkLib's `extraction_failure_implies_bad_challenge`), the event each challenge's
error bounds.
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

open Interaction.Oracle.Security in
/-- **Knowledge transports along a refinement.** For a knowledge certificate from `R` at a
statement, on a path whose terminal witness holds, if the extracted witness mapped by the
refinement is invalid for `S`, a challenge on the path turned the state from false to true. -/
theorem Refinement.knowledge_transport {Stmt W₁ W₂ : Type} {R : Set (Stmt × W₁)}
    {S : Set (Stmt × W₂)} (f : Refinement R S) (x : Stmt) {tree : Interaction.Oracle.TypeTree}
    {roles : tree.RoleDecoration} (cert : KnowledgeCertificate tree roles ⟨W₁, fun w ↦ (x, w) ∈ R⟩)
    (path : tree.ExecutionPath) (w : (cert.extractor.terminalState path).Witness)
    (hgood : (cert.extractor.terminalState path).holds w)
    (hbad : (x, f.map x (cert.extractor.extractWitness path w)) ∉ S) :
    RoundExtractor.BadChallengeOnPath cert.extractor roles path w :=
  RoundExtractor.extraction_failure_implies_bad_challenge _ _ cert.prover_preserving path w hgood
    fun h ↦ hbad (f.map_valid x _ h)

end
end LeanVM.Protocol
