/-
  LeanVM.Guest.B1.VsC.VkPacked

  `verifyKeccak` reads and draws no packed scalars, so its accepting runs are carried runs.
-/

module

public import LeanVM.Guest.B1.Tables.RunF
public import LeanVM.Guest.B1.KeccakGkr.VkSpec

/-!
# `verifyKeccak` is packed-free

`PackedFree.bind`: a sequence of packed-free programs is packed-free. The transcript's reads,
draws, grinds and checks are (`pf_readScalars`, `pf_sampleChallenges`, `pf_grind`, `pf_require`),
so the sumcheck, a layer, the layers, an opening and `verifyKeccak` are (`pf_verifyKeccak`).
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

theorem PackedFree.bind {α β : Type} {p : VerifierProgram α} {f : α → VerifierProgram β}
    (hp : PackedFree p) (hf : ∀ a, PackedFree (f a)) : PackedFree (p >>= f) := by
  induction hp with
  | ret a => exact hf a
  | fail => exact .fail
  | read _ ih => exact .read fun x ↦ ih x
  | sample _ ih => exact .sample fun x ↦ ih x
  | grind _ ih => exact .grind ih
  | commit _ ih => exact .commit ih
  | query _ ih => exact .query fun r ↦ ih r

theorem pf_pure {α : Type} (a : α) : PackedFree (pure a : VerifierProgram α) := .ret a

theorem pf_require (c : Prop) [Decidable c] : PackedFree (VerifierProgram.require c) := by
  unfold VerifierProgram.require; split
  · exact .ret _
  · exact .fail

theorem pf_readScalar : PackedFree VerifierProgram.readScalar := .read fun _ ↦ .ret _

theorem pf_sampleChallenge : PackedFree VerifierProgram.sampleChallenge := .sample fun _ ↦ .ret _

theorem pf_readScalars : ∀ n, PackedFree (VerifierProgram.readScalars n)
  | 0 => .ret _
  | n + 1 => PackedFree.bind pf_readScalar fun _ ↦ PackedFree.bind (pf_readScalars n) fun _ ↦ .ret _

theorem pf_sampleChallenges : ∀ n, PackedFree (VerifierProgram.sampleChallenges n)
  | 0 => .ret _
  | n + 1 => PackedFree.bind pf_sampleChallenge fun _ ↦
      PackedFree.bind (pf_sampleChallenges n) fun _ ↦ .ret _

theorem pf_grind (b : ℕ) : PackedFree (VerifierProgram.grindProofOfWork b) := by
  unfold VerifierProgram.grindProofOfWork; split
  · exact .ret _
  · exact .grind (.ret _)

/-- The tactic: a program built of packed-free pieces is packed-free. -/
macro "pf_tac" : tactic => `(tactic| repeat' (first
  | exact pf_pure _ | exact pf_require _ | exact pf_readScalar | exact pf_sampleChallenge
  | exact pf_readScalars _ | exact pf_sampleChallenges _ | exact pf_grind _
  | refine PackedFree.bind ?_ ?_ | intro _ | split))

theorem pf_sumcheckRoundPoly (count : ℕ) (claim : E) (e : Option E) :
    PackedFree (sumcheckRoundPoly count claim e) := by
  cases e <;> unfold sumcheckRoundPoly <;> pf_tac

theorem pf_sumcheck (claim : E) (count : ℕ) (eqs : List (Option E)) :
    PackedFree (sumcheck claim count eqs) := by
  induction eqs generalizing claim with
  | nil => exact .ret _
  | cons e es ih =>
    unfold sumcheck
    refine PackedFree.bind (pf_sumcheckRoundPoly _ _ _) fun _ ↦ ?_
    refine PackedFree.bind pf_sampleChallenge fun _ ↦ ?_
    refine PackedFree.bind (ih _) fun _ ↦ ?_
    split
    exact .ret _

/-- `pf_tac` with the sumcheck. -/
macro "pf_tac1" : tactic => `(tactic| repeat' (first
  | exact pf_sumcheck _ _ _ | exact pf_pure _ | exact pf_require _ | exact pf_readScalar
  | exact pf_sampleChallenge | exact pf_readScalars _ | exact pf_sampleChallenges _
  | exact pf_grind _ | refine PackedFree.bind ?_ ?_ | intro _ | split))

theorem pf_layer (logSteps step : ℕ) (claim : KeccakClaim) :
    PackedFree (verifyKeccakLayer logSteps step claim) := by
  unfold verifyKeccakLayer
  pf_tac1

theorem pf_layers (logSteps : ℕ) : ∀ (steps : List ℕ) (claim : KeccakClaim),
    PackedFree (keccakLayers logSteps steps claim)
  | [], _ => .ret _
  | step :: steps, claim => PackedFree.bind (pf_layer logSteps step claim) fun c ↦ pf_layers logSteps steps c

theorem pf_open (logSteps : ℕ) (claim : KeccakClaim) (first count : ℕ) (value : E) :
    PackedFree (keccakOpen logSteps claim first count value) := by
  unfold keccakOpen
  pf_tac1

/-- **`verifyKeccak` reads and draws no packed scalars**, past its shape check. -/
theorem pf_verifyKeccak {τ : ℕ} {inst outs : List E}
    (hs : inst.length = τ ∧ outs.length = keccakStateLanes ∧ 4 ≤ τ) :
    PackedFree (verifyKeccak τ inst outs) := by
  rw [VerifySub.verifyKeccak_body τ inst outs hs]
  refine PackedFree.bind (pf_sampleChallenges _) fun _ ↦ ?_
  refine PackedFree.bind (pf_sampleChallenges _) fun _ ↦ ?_
  refine PackedFree.bind pf_readScalar fun _ ↦ ?_
  refine PackedFree.bind (pf_layers _ _ _) fun _ ↦ ?_
  refine PackedFree.bind (pf_open _ _ _ _ _) fun _ ↦ ?_
  refine PackedFree.bind pf_readScalar fun _ ↦ ?_
  refine PackedFree.bind (pf_require _) fun _ ↦ ?_
  refine PackedFree.bind (pf_sumcheck _ _ _) fun _ ↦ ?_
  refine PackedFree.bind (pf_open _ _ _ _ _) fun _ ↦ ?_
  refine PackedFree.bind (pf_readScalars _) fun _ ↦ ?_
  refine PackedFree.bind (pf_require _) fun _ ↦ ?_
  exact pf_pure _

end
end LeanVM.Guest.B1.Tables
