/-
  LeanVM.Prover.Complete.Opening

  The last phases of `verify_execution` and of the honest script: ring switching and the stacked
  opening; and the stack's commitment.
-/

module

public import LeanVM.Prover.Complete.StackLayout
public import LeanVM.Prover.Complete.Prefix
public import LeanVM.Protocol.Whir.Complete.Opening
import LeanVM.Prover.Ntt

/-!
# The opening phases

`openingProgram` is `verifyExecution` after the Keccak reduction (steps 6 and 7 of `walk`), and
`openingScript` is `honestScript` after the Keccak phase, their bodies copied from the two
definitions, with `claims` for the column claims gathered before (`linkColumnClaims link ++
publicClaims ++ outputs`).

`stackCommitted W ρ` is the stack's commitment as `commitStack` reads it: the level-0 shape and
the stack's word; `wins_commitStack`: the honest script's commitment wins step 2.
-/

@[expose] public section

namespace LeanVM.Prover

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

/-- **The verifier's last steps** (`verifyExecution` after `keccakValidity`): ring switching, the
memory term, and the stacked opening of every claim. -/
def openingProgram (layout : Layout) (ρ : ℕ) (ood : StackClaim) (link : LinkEnd)
    (claims : List ColumnClaim) (keccakPoint keccakSlices : List E) : VerifierProgram Unit := do
  let qkeccakPlacement ← liftOption (layout.placements.getD qkeccak none)
  let (ring, batching) ←
    ringSwitch [keccakRingClaim qkeccakPlacement keccakPoint keccakSlices, link.ring]
  let memoryTerm ← memoryTermClaim layout link
  verifyStackedOpening layout.stackLog ρ
    (ring :: memoryTerm :: claims.filterMap (·.onStack layout) ++ [ood]) batching

/-- **The honest script's last phases** (`honestScript` after the Keccak phase): ring switching,
then the opening of the verifier's claims. -/
def openingScript (W : Witness) (ρ : ℕ) (oodPoint : List E) (link : LinkEnd)
    (claims : List ColumnClaim) (keccakPoint keccakSlices : List E) : Script Unit := do
  let layout := W.layout
  let qkeccakPlacement := (layout.placements.getD qkeccak none).getD default
  let ring ← ringFast true
  let placed := fun (column : ℕ) ↦ (layout.placements.getD column none).getD default
  let columnClaims := claims.filterMap fun c ↦
    (layout.placements.getD c.column none).map fun p ↦ ClaimDesc.cells [(p, c.point, 1)]
  openingFast layout.stackLog ρ W.stack
    (.ring [keccakRingClaim qkeccakPlacement keccakPoint keccakSlices, link.ring] ring.f ring.g
        ring.rho ::
      .cells [(placed memory0, link.memoryPoint, link.memoryScales.1),
        (placed memory1, link.memoryPoint, link.memoryScales.2)] ::
      columnClaims ++ [.ood oodPoint])
    ring.batching

/-- **The stack's commitment**: the shape `commitStack` reads (level `0`'s), and the stack's
word. -/
def stackCommitted (W : Witness) (ρ : ℕ) : Committed :=
  match Whir.ladder W.layout.stackLog ρ with
  | some (level :: _) =>
    ⟨(levelShape W.layout.stackLog level (2 ^ level.fold)).1,
      (levelShape W.layout.stackLog level (2 ^ level.fold)).2,
      stackWordFast W.layout.stackLog ρ W.stack⟩
  | _ => ⟨0, 0, stackWordFast W.layout.stackLog ρ W.stack⟩

section Witness

variable {prog : LeanIsaProgram} {input : PublicInput} {t : Execution prog} {W : Witness}

/-- The honest stack has `2^stackLog` words. -/
theorem stack_size_witness (hW : witness? prog input t = some W) :
    W.stack.size = 2 ^ W.layout.stackLog := by
  obtain ⟨-, -, -, -, -, hstack⟩ := witness_spec hW
  rw [hstack, stackArray_eq, size_writeBlocks, Array.size_replicate]

/-- The honest stack as a column of `stackLog` variables. -/
def stackColumn (W : Witness) (h : W.stack.size = 2 ^ W.layout.stackLog) :
    LeanVM.Protocol.Column W.layout.stackLog :=
  ⟨⟨W.stack, h⟩⟩

/-- The stack and the rate are admissible. -/
theorem admissible_witness (hW : witness? prog input t = some W) {ρ : ℕ} (hρ : 1 ≤ ρ ∧ ρ ≤ 4) :
    Whir.Admissible W.layout.stackLog ρ := by
  obtain ⟨-, steps, -, -, hl, hlog, -⟩ := witness?_spec hW
  obtain ⟨-, -, -, -, -, hmin⟩ := buildLayout_spec hl
  exact ⟨hmin, hlog, hρ⟩

/-- **The stack's commitment wins step 2.** -/
theorem wins_commitStack (hW : witness? prog input t = some W) {ρ : ℕ} (hρ : 1 ≤ ρ ∧ ρ ≤ 4) :
    Wins 17 (fun _ _ g cs ↦ g = false ∧ cs = [stackCommitted W ρ])
      (commitStack W.layout.stackLog ρ)
      (Script.commitS (stackWordFast W.layout.stackLog ρ W.stack)) false [] := by
  have hadm := admissible_witness hW hρ
  obtain ⟨q₀, rest, hc, -⟩ := LeanVM.Protocol.Whir.Complete.exists_ladder hadm
  have hS := stack_size_witness hW
  have hshape : WellShaped (2 ^ 6) (stackWordFast W.layout.stackLog ρ W.stack) := by
    have := LeanVM.Protocol.Whir.Complete.wellShaped_stackWord W.layout.stackLog ρ (stackColumn W hS)
    rwa [← Enc.stackWordFast_eq (by have := hadm.2.1; simp [Whir.maxLogStack] at this; omega)]
      at this
  simp only [commitStack, hc, LeanVM.Protocol.Verifier.liftOption, VerifierProgram.bind_eq,
    VerifierProgram.readCommitment, Script.commitS]
  refine ⟨rfl, hshape, rfl, ?_⟩
  simp [stackCommitted, hc]

end Witness

end LeanVM.Prover

end
