/-
  LeanVM.Guest.LimitsNZ

  The zero-challenge refusal restricts the Spec's deferring verifier: a child's proof the verifier refusing
  a zero challenge accepts, the Spec's accepts.
-/

module

public import LeanVM.Protocol.Verifier.WhirTarget
public import LeanVM.Protocol.Verifier.Claims
public import LeanVM.Guest.Limits
public import LeanVM.Guest.NZProgram
public import LeanVM.Protocol.WithHashBridge
public import LeanVM.Protocol.WithHash
public import LeanVM.Guest.Refines

/-!
# The zero-challenge refusal is a restriction

`Refines P' P` (`Refines.lean`): the program `P'` is `P` with failures inserted, step for step. The
deferring program refusing a zero fold, tail or level batching challenge refines the deferring
program (`deferredProgramNZ_refines`), so `AcceptableChild`'s refusal gives every child's acceptance by the
Spec's deferring verifier (`verifyDeferred_of_nz`): it only removes runs, those with a zero
challenge where the guest divides.
-/

namespace LeanVM.Guest.Limits

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Node

@[expose] public section

/-! ## The deferring program refusing a zero challenge -/

theorem foldRoundNZ_refines (s : WhirState) : Refines (foldRoundNZ s) (foldRound s) := by
  unfold foldRoundNZ foldRound
  repeat refine Refines.bind (Refines.refl _) fun _ ↦ ?_
  exact Refines.require_bind (Refines.refl _)

theorem foldRoundsNZ_refines : ∀ (n : ℕ) (s : WhirState),
    Refines (foldRoundsNZ n s) (foldRounds n s)
  | 0, s => Refines.refl _
  | n + 1, s => by
    unfold foldRoundsNZ foldRounds
    exact Refines.bind (foldRoundNZ_refines s) fun p ↦
      Refines.bind (foldRoundsNZ_refines n _) fun _ ↦ Refines.refl _

theorem sumcheckNZ_refines (count : ℕ) : ∀ (eqs : List (Option E)) (claim : E),
    Refines (sumcheckNZ claim count eqs) (sumcheck claim count eqs)
  | [], claim => Refines.refl _
  | e :: eqs, claim => by
    unfold sumcheckNZ sumcheck
    refine Refines.bind (Refines.refl _) fun m ↦ ?_
    refine Refines.bind (Refines.refl _) fun c ↦ ?_
    exact Refines.require_bind (Refines.bind (sumcheckNZ_refines count eqs _) fun _ ↦ Refines.refl _)

/-- The first program of a bind: the same, or a refining one. -/
local macro "refines_head" : tactic => `(tactic| first
  | with_reducible exact Refines.refl _
  | exact foldRoundsNZ_refines _ _
  | exact sumcheckNZ_refines _ _ _)

/-- One step of a refinement proof between two programs written alike. -/
local macro "refines_step" : tactic => `(tactic| first
  | with_reducible exact Refines.refl _
  | (refine Refines.bind ?h fun _ ↦ ?k; case h => refines_head)
  | apply Refines.require_bind
  | split
  | dsimp only
  | exact Refines.refl _)

theorem whirLevelsNZ_refines (logN laneFolds : ℕ) (eb : List E → E) (levels : List Whir.Level) :
    ∀ (index : ℕ) (s : WhirState),
      Refines (whirLevelsNZ logN laneFolds eb index levels s)
        (whirLevels logN laneFolds eb index levels s) := by
  induction levels with
  | nil => intro index s; exact Refines.refl _
  | cons level rest ih =>
    intro index s
    unfold whirLevelsNZ whirLevels
    apply Refines.bind (foldRoundsNZ_refines _ _)
    intro p
    obtain ⟨s', lf⟩ := p
    dsimp only
    cases rest with
    | nil =>
      dsimp only
      repeat refines_step
    | cons next rest' =>
      dsimp only
      repeat (first | exact ih _ _ | refines_step)

theorem verifyWhirNZ_refines (logN logInvRate : ℕ) (target : E) (eb : List E → E) :
    Refines (verifyWhirNZ logN logInvRate target eb) (verifyWhir logN logInvRate target eb) := by
  unfold verifyWhirNZ verifyWhir
  repeat (first | exact whirLevelsNZ_refines _ _ _ _ _ _ | refines_step)

theorem verifyStackedOpeningNZ_refines (stackLog logInvRate : ℕ) (claims : List StackClaim) :
    Refines (verifyStackedOpeningNZ stackLog logInvRate claims)
      (verifyStackedOpening stackLog logInvRate claims) := by
  unfold verifyStackedOpeningNZ verifyStackedOpening
  repeat (first | exact verifyWhirNZ_refines _ _ _ _ | refines_step)

theorem deferredProgramNZ_refines (c : BytecodeClaim) (bytecode : List K) (publicInput : Digest) :
    Refines (deferredProgramNZ c bytecode publicInput) (deferringVerifierProgram c bytecode publicInput) := by
  unfold deferredProgramNZ deferringVerifierProgram
  refine Refines.bind ?_ fun _ ↦ Refines.refl _
  unfold verifyExecutionNZ verifyExecution
  repeat (first | exact verifyStackedOpeningNZ_refines _ _ _ | refines_step)

/-- **The zero-challenge refusal only restricts**: the deferring verifier refusing a zero challenge
accepts only proofs the Spec's deferring verifier accepts. -/
theorem verifyDeferred_of_nz {bytecode : List K} {iv publicInput : Digest} {c : BytecodeClaim}
    {π : Proof} (h : verifyDeferredNZ bytecode iv publicInput c π = true) :
    verifyDeferred bytecode iv publicInput c π = true := by
  unfold verifyDeferredNZ at h
  rw [verifyDeferred_eq_withHash]
  unfold verifyDeferredWithHash
  exact runProof_refines (deferredProgramNZ_refines c bytecode publicInput) _ π h

end
end LeanVM.Guest.Limits
